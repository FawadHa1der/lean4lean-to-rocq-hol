# Honest Forensic Assessment & End-to-End Implementation Tracker: `lean4lean` → Rocq & HOL Light

**Branch**: `feat/complete-end-to-end-port`  
**Upstream Reference**: [`digama0/lean4lean`](https://github.com/digama0/lean4lean) (`8223d223ed98661882e95d9d6a7126df7097cd76` & `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`)  
**Toolchains**: OCaml `4.14.2`, Rocq `9.2.0` (`rocq-stdlib 9.1.0`), HOL Light `3.1.0`  
**Zero-Shortcut Policy**: `0` Rocq axioms (`* Axioms: <none>`), `0` `Admitted`/`admit`, `0` unsafe casts (`Obj.magic`, `vm_cast_no_check`), `0` added HOL Light axioms (`List.length (axioms ()) = 3`, `check_axioms ()` OK, `0` `mk_thm`/`new_axiom`).

---

## 1. Brutally Honest Assessment of All Gaps Found at Baseline (`a212d76`)

Line-by-line comparison of all non-experimental modules in upstream `digama0/lean4lean` (~33,845 LOC across Executable Kernel, `Theory/`, and `Verify/`) against `rocq/`, `hol/kernel_v3_complete/`, `hol/`, and `frontend/`, combined with live benchmarking against all **219 published Lean Kernel Arena** `.ndjson` exports (including 30 soundness bug cases), uncovered the following concrete gaps and defects beyond what historical reports acknowledged:

### 1.1 Declarative Metatheory Gaps (`Lean4Lean/Theory/`, 6,506 LOC upstream)

1. **~65% of upstream `Theory/` was unported in both Rocq and HOL Light**:
   - **`Theory/LevelSat.lean` (450L, 0 `sorry`s)**: CoNP-hardness reduction from 3-CNF SAT to `VLevel.Equiv` and `VLevel.LE` (`equiv_iff_unsat`, `le_iff_unsat`, `size_big`) was 100% missing in both ports.
   - **`Theory/VExpr.lean` (remaining ~55%, 0 `sorry`s) & `Ctx.SubstEq` (`Lemmas.lean:901–988`)**: Structured renamings (`Lift`, `lift'`, `Skips`, `Ctx.Lift'`), simultaneous substitutions (`VExpr.Subst`, `subst_subst`, `ClosedN.subst_eq`, `subst_inst`), and simultaneous context substitution (`Ctx.SubstEq`: `nil`, `cons`, `left`, `lookup`, `skip`, `lift`, `lift_at`, `wf`, `id`) were missing in both ports.
   - **`Theory/Typing/Strong.lean` (1,180L, 0 `sorry`s)**: Sort-annotated `IsDefEqStrong`, `HasTypeStrong`, `EqUpToLevels`, `HasTypeStratified`, `IsDefEq.strong`, syntactic typing inversions modulo `IsDefEq` (`HasType.app_inv`, `lam_inv`, `const_inv`, `bvar_inv`), and simultaneous definitional-equality substitution (`IsDefEq.substDF`) were 100% missing in both ports.
   - **`Theory/{VDecl,Quot,Inductive}.lean` & `Theory/Typing/{Env,QuotLemmas,InductiveLemmas,EnvLemmas}.lean`**: Declaration-history `VDecl`/`VEnv.WF`, semantic quotient consistency (`addQuot_WF` + `Quot.ind` ι-soundness), constructive semantic inductive extension (`VInductDecl.WF` / `addInduct_WF`), and multi-constant/defeq extension (`addConsts_ordered`, `addDefEqs_ordered`, `VEnv.WF.ordered`) were missing in both ports.
   - **`Theory/Typing/{Pattern,Injectivity,UniqueTyping,ChurchRosser,HeadReduction}.lean` (~2,627L)**: Pattern-matching rewrite rules (`Pattern.lean`), unique typing up to conversion (`IsDefEq.uniq`, `IsDefEqU.trans`, `HasType.defeqU_l/r`, `weakN_iff`), typed `NormalEq` / `ParRed` / `IsDefEq.church_rosser`, and `WHRed` determinism + Kashima standardization (`ParRedS.standard`, `InferType.determ/exists`) were missing in both ports (`DeclarativeTyping.v` and `declarative_typing961.ml` only proved untyped pure-β `VParRed` and conversion-free `VSynHasType`).
2. **Concrete HOL Light `Theory/` defects**:
   - **Missing constant-name freshness in `l4_venv_wf966` (`typing_lemmas966.ml:1255–1258`)**: Unlike upstream `VEnv` and Rocq `VEnvWF`, `l4_venv_wf_const966` omitted `~(?ci0. l4_venv_lookup_const961 env n ci0)`, allowing duplicate constant names with conflicting types/arities inside a "well-formed" HOL `VEnv`.
   - **Missing Takahashi confluence in `declarative_typing961.ml`**: Despite advertising `(Takahashi diamond)` in its header, `declarative_typing961.ml` omitted `vcomplete_dev`, `VParRed_triangle`, `VParRed_diamond`, `VParRedStar_ChurchRosser`, and `VSynHasType_unique`.

### 1.2 Executable Kernel, Caching, Fuel, & Arena CLI Gaps

1. **Live Lean Kernel Arena (`219` cases, Lean `4.36.0`) exposed 3 concrete failure classes in `build/rocq-check`** (while passing **30 / 30** soundness `bugs/*`):
   - **8 false rejections (`UnknownConstant` on `Nat.mod`)** in `init-prelude` and 7 `perf/*` exports: Lean `4.36.0` refactored `Decidable` into single-constructor `Decidable.intro` over `Bool.Reflects` and moved `Decidable.isTrue`, `Decidable.isFalse`, and `Bool.decEq` *after* `Nat.mod` in `Init.Prelude`. `Primitives.v` (and HOL `primitive_reflection621.ml`) hardcoded `Decidable.isTrue`/`isFalse` and `Bool.decEq`, failing when `Nat.mod` precedes them.
   - **12 `OutOfFuel` declines**:
     - 6 cases (`perf/args-before-unfold`, `church-numerals`, `folded-constant-first/last`, `shared-subterm`, `unroll-versus-evaluate`) declined solely because CLI default `--fuel` was `512` rather than upstream `FuelConfig.recDepth = 50000`.
     - 3 cases (`perf/proj-applied-struct`, `proj-applied-struct-bad`, `proj-applied-struct-arg-bad`) declined because `Checker.v` (and HOL `kernel_conversion597.ml`) lacked `lazyDeltaProjReduction` (`TypeChecker.lean:798–812`).
     - 3 cases (`perf/unfold-before-literal`, `unfold-before-literal-fallback`, `unfold-before-literal-bad`) declined because `Nat.pow` / `Nat.shiftLeft` / `Nat.shiftRight` returned `Decline OutOfFuel` when `b > fuel` instead of returning `Accept None` above `2^24` so conversion falls back to symbolic delta unfolding (`TypeChecker.lean:471–477`).
   - **5 per-case timeouts** (`perf/app-lam`, `beta-ladder`, `fueled-chain`, `proj-cheap-struct`, `refute-cheap-last`): caused by zero runtime `EquivManager` / `WHNF` / `Infer` / `Failure` memoization in `Checker.v`.
2. **Dead / Unwired Standalone Models & Behavioral Deviations**:
   - `DefEqCache.v` (`equiv_manager964.ml`) was unwired and keyed only by `(length bound_context, t, s)` without binder types/let-values/`free_context` (which would be unsound on `bugs/open-term-cache-context` if wired naively).
   - `FuelConfig.v` (`fuel_config965.ml`) had 5 fields instead of upstream's 6 (`whnf`, `whnfEager`, `lazyDelta`, `etaExpand`, `recDepth`, `inductiveFuel`), collapsed to `min_fuel_of_config`, and was unwired.
   - Missing `TypeChecker.etaExpand` (`TypeChecker.lean:946–966`), missing `reduceNative` (`Lean.reduceBool`/`Lean.reduceNat` rejection), `.proj` head comparison checking owner name instead of field index, `Safety.v` omitting `safety_environment InputPartial` on single partial definitions, and `Primitives.v` `eraseMData` (`67f63b0`) stripping metadata in non-domain positions.
3. **HOL Light External CLI (`frontend/hol_check.ml` & `scripts/hol-check.py`) Disconnected from `kernel_v3_complete`**:
   - External Arena CLI still ran 10-constructor `v0` (`hol/*.ml`), declining 8 `Nat` primitives, `Mutual` blocks, nested inductives, and `unsafe`/`partial` defs, and mapping all semantic proof failures to exit code `2` (`decline`) rather than theorem-backed `1` (`reject`).
   - Inside `hol/kernel_v3_complete/hol/`: `inference586.ml:99–103` still returned `Decline UnsupportedExpression` instead of `Reject TypeMismatch` on non-inductive projection owners (`GAP_ANALYSIS.md` §2.4 had only fixed Rocq!); `full_input610.ml:197` rejected non-empty `mdata` payloads; and `File_certificate649` was not exposed via a warm fork server CLI.

### 1.3 Kernel-to-Theory Verification Bridge Gaps (`Lean4Lean/Verify/`, 24,150 LOC upstream)

1. **`InferSoundness.v` (661L) & `infer_soundness967.ml` (1,009L) covered only 7 of 13 constructors and left `CheckerMethodsSound` unproved**:
   - `trE` / `l4_tr_e967` returned `None` on `EFVar`, `ELet`, `ELit (LitNat _)`, `ELit (LitString _)`, and `EProj`, restricted `infer_step` to `checking = true` over let-free bound contexts, and left `CheckerMethodsSound` (`whnf` + `defeq` + `eager_defeq`) and environment-admission preservation completely open.
2. **`CheckerSoundness.v` (895L) & `checker_soundness962.ml` (480L) had vacuous/broken predicates**:
   - `CheckerSoundness.v` lacked hybrid `VLCtx`, mapped `ELit` to any well-typed term, left `TrProj` unconstrained to field `idx`, and stated reduction bridges with no `TrExpr` link between executable terms and semantic `VDefEq`s.
   - `checker_soundness962.ml` dropped both `TrExpr` conjuncts in `l4_tr_typing_bridge962`, omitted `vlift` on `fvars` under binders in `l4_tr_expr_s962`, omitted `NatLit`/`StrLit`/`Let(T)`, and left `e`/`rhs` unused in `l4_core_reduce_recursor_sound_bridge962`.
3. **0% of `WHNF`, `Reduce`, `IsDefEq`, `EquivManager`, `Primitives` (`HasPrimitives`), `Quot`, `Inductive`, or `Environment`/`PersistentAdmission` (`VEnvs.WF`) was proved semantically sound end-to-end.**

---

## 2. End-to-End Implementation & Verification Tracker

Each milestone below is implemented with **zero axioms / zero admits**, verified by the Rocq 9.2.0 or HOL Light 3.1.0 kernel, marked `[x]` here, committed, and pushed to `origin/feat/complete-end-to-end-port`.

- [x] **Milestone 1 — Complete Rocq `Theory/` Metatheory Port (`rocq/`)**:
  - Ported `LevelSat.v` (`628L`, `LevelSat.lean`), `SubstTheory.v` (`1,393L`, `VExpr.lean` `Lift`/`Subst` + `Ctx.SubstEq`), `StrongTyping.v` (`1,926L`, `Strong.lean` incl. `VIsDefEq_strong`, `app`/`lam`/`const`/`bvar` inversions & `VIsDefEq_substDF`), `EnvDeclTheory.v` (`1,667L`, `VDecl`, `Quot`/`addQuot_WF`/`quotInd_iota`, constructive `VInductDecl`/`addInduct_WF`, `VEnvDeclsWF_to_VEnvWF`), and `PatternConfluence.v` (`6,354L`, `Pattern.lean`, `UniqueTyping.lean` `VIsDefEq_uniq`/`VIsDefEqU_trans`, `ChurchRosser.lean` `VIsDefEq_church_rosser` closing upstream `.extra` cases axiom-free, `HeadReduction.lean` Kashima standardization & `VInferType`, plus unconditional `venv_empty` non-vacuity); registered in `rocq/_CoqProject` and verified `119 / 119` `.vo` objects via `build-rocq.sh` + `audit-build.sh` (`* Axioms: <none>`).
- [ ] **Milestone 2 — Complete HOL Light `Theory/` Metatheory Port (`hol/kernel_v3_complete/hol/`)**:
  - Fix constant-name freshness in `typing_lemmas966.ml` (`l4_venv_wf_lookup_unique966`); port Takahashi confluence + `LevelSat` (`level_sat968.ml`), `Lift`/`VSubst`/`Ctx.SubstEq` (`subst_theory969.ml`), `Strong.lean` + `substDF` (`strong_typing970.ml`), `VDecl`/`Quot`/`Induct`/`EnvLemmas` (`env_decl_theory971.ml`), and `Pattern`/`UniqueTyping`/`ChurchRosser`/`HeadReduction` (`pattern_confluence972.ml`); register in `verify_all_v3.ml` and verify `AXIOMS=3` & `check_axioms ()`.
- [ ] **Milestone 3 — Rocq Executable Kernel Parity, Lean 4.33+4.36 Primitives, 6-Axis `FuelConfig`, & Context-Sound `EquivManager` Caches**:
  - Fix `Nat.pow` (`<= 2^24` fallback to `None` instead of `Decline OutOfFuel`) & unbounded shifts, implement `lazyDeltaProjReduction`, `etaExpand`, `reduceNative`, `.proj` index comparison, `Safety.v` partial view, dual Lean `4.33`/`4.36` (`Decidable.intro`/`Bool.Reflects` + `Decidable.isTrue`/`isFalse`) & `67f63b0` `eraseMData` in `Primitives.v`, 6-axis `FuelConfig.v`, and context-sound `EquivManager` + `WHNF`/`Infer`/`Failure` memoization wired into `build/rocq-check`; verify all native suites and 219 live Arena cases.
- [ ] **Milestone 4 — HOL Light `v3` Executable Kernel Parity, 6-Axis `FuelConfig`, `EquivManager` Caches, & Theorem-Backed `v3` Arena CLI/Server**:
  - Fix `L4KProj447` non-inductive owner rejection in `inference586.ml`, `Nat.pow`/shifts fallback (`Accept NONE`), `lazyDeltaProjReduction`, `etaExpand`, `reduceNative`, dual Lean `4.33`/`4.36` primitive reflection & `67f63b0` `eraseMData`, 6-axis `fuel_config965.ml`, context-sound `equiv_manager964.ml`, Arena-ready `mdata` quotation, optimized `Kernel_compute646`, and upgrade `frontend/hol_check.ml` + `hol_server.ml` + `scripts/hol-check.py` to run 13-constructor `kernel_v3_complete` producing closed HOL theorems (`|- ... = 0 | 1 | 2`) for `Accept`, `Reject`, and `Decline`.
- [ ] **Milestone 5 — End-to-End Rocq `Verify/` Kernel-to-Theory Soundness**:
  - Formalize hybrid `VLCtx` (`vlam` + `vlet` for `EBVar` and `EFVar`), genuine structure-recursor/spec `TrProj`, literal translations (`natLit`, `trStrLit`), `PrimSpec`/`HasPrimitives`, and 12-constructor `TrExprS`/`TrExpr`/`TrTyping`; prove `Reduce`, `WHNF`, `InferType` (all 13 constructors, both modes), `IsDefEq`, and `EquivManager` soundness, **discharging `CheckerMethodsSound` end-to-end**; prove `Primitives` (`HasPrimitives`) and `Environment`/`PersistentAdmission` (`VEnvs.WF` across `safe`/`partial`/`unsafe` for `Axiom`, `Definition`, `Theorem`, `Opaque`, `Mutual`, `Quot`, `Inductive`) soundness with `0` axioms.
- [ ] **Milestone 6 — End-to-End HOL Light `Verify/` Kernel-to-Theory Soundness**:
  - Replace vacuous `checker_soundness962.ml` bridges and extend `infer_soundness967.ml` with full hybrid `VLCtx`, genuine `TrProj`, literal translations, `HasPrimitives`, and 12-constructor `TrExprS`/`TrExpr`/`TrTyping`; prove `Reduce`, `WHNF`, `InferType` (all 13 constructors, both modes), `IsDefEq`, and `EquivManager` soundness, **discharging `l4_checker_methods_sound` end-to-end**; prove `Primitives` and `Environment`/`l4_check_file642` (`VEnvs.WF`) soundness with `AXIOMS=3` and `check_axioms ()` OK.
- [ ] **Milestone 7 — Final Full-Suite Audit, Arena Benchmark, & Documentation Synchronization**:
  - Run `scripts/build-rocq.sh`, `scripts/audit-build.sh`, `hol/kernel_v3_complete/verify_all_v3.sh`, `hol/test.sh`, `hol/test-quotient.sh`, and Lean Kernel Arena suites on both `build/rocq-check` and HOL Light `v3`; synchronize `GAP_ANALYSIS.md`, `README.md`, `FINAL_REPORT.md`, and `hol/kernel_v3_complete/VERIFICATION_STATUS.md`; commit and push final verified state.
