# Lean4Lean in Rocq and HOL Light — Formal Verification Report

**Upstream Reference**: [`digama0/lean4lean`](https://github.com/digama0/lean4lean) (`8223d223ed98661882e95d9d6a7126df7097cd76` & `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`)  
**Toolchains**: OCaml `4.14.2`, Rocq `9.2.0` (`rocq-stdlib 9.1.0`), HOL Light `3.1.0` (macOS arm64 & Linux x86_64)  
**Companion Documents**:
- **[`END_TO_END_PORT_REPORT.md`](END_TO_END_PORT_REPORT.md)**: Full 7-milestone end-to-end implementation and verification tracker.
- **[`GAP_ANALYSIS.md`](GAP_ANALYSIS.md)**: Honest engineering assessment of implemented subsystems, verified scope, and transparent remaining boundaries.
- **[`hol/kernel_v3_complete/VERIFICATION_STATUS.md`](hol/kernel_v3_complete/VERIFICATION_STATUS.md)**: Three-session cold verification report for all 141 `hol/kernel_v3_complete/hol/*.ml` modules and 104 entry cases.

**Verification Status**:
- **Rocq Port ([`rocq/`](rocq/))**: **123 / 123 Vernacular modules (`.vo`) compiled and verified** via `rocq check -Q . LeanPort -o` (`bash scripts/audit-build.sh`) with **zero axioms (`* Axioms: <none>`)**, zero `Admitted`, and zero `Unsafe` flags. Native extracted cached checker (`build/rocq-check`, `--fuel 50000`) passes **24 / 24 native regression suites** (`scripts/build-rocq.sh`) and **215 / 225 live Lean 4.36.0 Kernel Arena exports** (**183 / 183** non-perf incl. `init-prelude` in `1.52s`, **30 / 30** `bugs/*`, **141 / 141** `tutorial/*`, **10 / 10** `other/*`, **1 / 1** `corner-cases/*`, **32 / 42** `perf/*`; **`0` wrong verdicts, `0` declines**, `10` extreme `perf/*` timeouts at 35s).
- **HOL Light Port ([`hol/README.md`](hol/README.md): [`hol/kernel_v3_complete/`](hol/kernel_v3_complete/), [`hol/kernel_v2_full_file/`](hol/kernel_v2_full_file/), [`hol/kernel_v1_core_only/`](hol/kernel_v1_core_only/), and legacy [`hol/*.ml`](hol/))**: **141 / 141 full-kernel `v3` modules + 104 / 104 `v3` entry cases** across three fresh sequential HOL Light sessions (`sh hol/kernel_v3_complete/verify_all_v3.sh`), **67 / 67** OCaml transport checks (`scripts/build-hol-frontend.sh`), and **11 legacy `v0` suites** (1,524 assertions across `hol/test.sh` & `hol/test-quotient.sh`) machine-checked with **zero added axioms** (`List.length (axioms ()) = 3`: only `INFINITY_AX`, `SELECT_AX`, `ETA_AX`, plus `check_axioms ()`), zero `mk_thm`, and zero `new_axiom`. Warm fork-isolated `scripts/hol-server.sh --kernel v3` passes **11 / 12** live Lean 4.36.0 Arena smoke cases (**6 / 6** `tutorial/*` accepts `|- verdict = 0`, **5 / 6** `bugs/*` semantic rejects `|- verdict = 1`, `axioms=3`, `0` wrong verdicts, `1` 30s timeout).

---

## 1. Executive Summary

This repository provides two independent, zero-axiom machine-checked formalizations of the **Lean 4 kernel (`lean4lean`)** in **Rocq 9.2.0** and **HOL Light 3.1.0**:

1. **Executable Kernel Specification, Lean 4.33/4.36 Parity, & Extraction**:
   - 13-constructor kernel syntax (`BVar`, `FVar`, `MVar`, `Sort`, `Const`, `App`, `Lam`, `Pi`, `Let`, `NatLit`, `StrLit`, `Proj`, `MData`), universe decision procedures, local contexts, constant/inductive/constructor/recursor/quotient declarations, nested inductive elimination, dual Lean 4.33/4.36 `Decidable` reflection, `67f63b0` domain-only `eraseMData`, `Nat.pow`/shifts `<= 2^24` fallback, `reduceNative`, `etaExpand`, `lazyDeltaProjReduction`, and three-valued outcomes (`Accept`, `Reject`, `Decline OutOfFuel/Unsupported`).
   - Verified 6-axis `FuelConfig` (`rocq/FuelConfig.v` / `fuel_config965.ml`) and full-context union-find `EquivManager` (`rocq/DefEqCache.v` / `equiv_manager964.ml`), plus DAG-indexed cached Rocq kernel (`rocq/CachedChecker.v`, 2,930L) linked into `build/rocq-check` and theorem-backed `frontend/hol_check_v3.ml` linked into `scripts/hol-server.sh --kernel v3`.
2. **Complete Declarative Metatheory (`Lean4Lean/Theory/`, `14,589L` Rocq / `21,354L` HOL Light)**:
   - `SemanticModel.v` / `DeclarativeTyping.v` / `TypingLemmas.v` (`declarative_typing961.ml` / `typing_lemmas966.ml`): `VLevel`/`VExpr`/`VDecl`/`VEnv`, 13-rule `VIsDefEq`/`VHasType`, constant-name uniqueness (`VEnvWF` / `l4_venv_wf_lookup_unique966`), and full `Theory/Typing/Lemmas.lean` metatheory (`instL`, `closedN`, `levelWF`, `weakN`, `instN`, `defeqDFC`, `sort_inv'`, `forallE_inv`, regularity `isType`, `instDF`).
   - `LevelSat.v` (`628L`) / `level_sat968.ml` (`974L`): Takahashi β-confluence (`VParRedStar_ChurchRosser` / `l4_vpar_red_star_church_rosser968`) and full 3-CNF CoNP-hardness reduction for `VLevel.Equiv` and `VLevel.LE`.
   - `SubstTheory.v` (`1,393L`) / `subst_theory969.ml` (`1,376L`): structured renamings (`Lift`/`Skips`), simultaneous substitutions (`VSubst`), and simultaneous context substitution (`Ctx.SubstEq`).
   - `StrongTyping.v` (`1,926L`) / `strong_typing970.ml` (`3,559L`): `IsDefEqStrong`, `HasTypeStrong`, `EqUpToLevels`, `HasTypeStratified`, `IsDefEq.strong`, syntactic typing inversions (`app_inv`, `lam_inv`, `const_inv`, `bvar_inv`), and simultaneous definitional substitution (`IsDefEq.substDF`).
   - `EnvDeclTheory.v` (`1,667L`) / `env_decl_theory971.ml` (`1,766L`): `VDecl`, semantic quotient consistency (`addQuot_WF` + `Quot.ind` ι-soundness), constructive semantic inductive extension (`VInductDecl.WF` / `addInduct_WF`), and declaration-history `VEnvDeclsWF_to_VEnvWF`.
   - `PatternConfluence.v` (`6,353L`) / `pattern_confluence972.ml` (`11,314L`): `Pattern.lean`, `UniqueTyping.lean` (`VIsDefEq_uniq`, `VIsDefEqU_trans`), `ChurchRosser.lean` (`VIsDefEq_church_rosser`, axiom-free), `HeadReduction.lean` (Kashima standardization & `VInferType`), and unconditional `venv_empty` / `l4_venv_empty961` non-vacuity.
3. **Complete End-to-End Executable Soundness (`Lean4Lean/Verify/`, `10,507L` Rocq / `18,834L` HOL Light)**:
   - `VerifyExpr.v` (`3,164L`) / `verify_expr973.ml` (`5,645L`, 178 theorems): universe-decision soundness, hybrid `VLCtx` (both lambda and let entries for `BVar`/`FVar`), genuine structure-projection specification (`VTrProj`/`VProjTelescope`), literal translations, `HasPrimitives`, `VEnvSound` (incl. `VEnvSound_empty`), and full 12-constructor `VTrExprS`/`VTrExpr`/`VTrTyping` metatheory.
   - `VerifyTypeChecker.v` (`5,602L`) / `verify_typechecker974.ml` (`10,716L`, 149 theorems): mutual induction on `fuel` proving `FullMethodsSound` (`l4_full_methods_sound974`) across all reductions, `whnf`, `infer` (all 13 constructors, both modes), and full `defeq`, unconditionally discharging `CheckerMethodsSound` (`InferSoundness.v`) and `l4_checker_methods_sound967` (`infer_soundness967.ml`), and composing with `DefEqCache`/`equiv_manager964.ml` and `FuelConfig`/`fuel_config965.ml`.
   - `VerifyEnvironment.v` (`1,741L`) / `verify_environment975.ml` (`2,473L`, 63 theorems): `env_extends` monotonicity, `check_header/proposition/value_sound`, `Primitives` (`classify_primitive_sound`), `admit_sound`/`VEnvSound_pure_admit`, safety & mutual-block isolation (`VEnvSound_prepend_restricted`, `admit_mutual_sound`, `admit_inductive_extended_unsafe_sound`), exact computational `Quotient` ↔ `EnvDeclTheory` bridge (`admit_quotient_sound`, `l4_initialize_quotient_sound975`), `declarative_inductive_admit_sound`, and end-to-end pure stream / persistent-admission / file-driver soundness (`state_stream_from_initial_sound`, `l4_check_declarations620_from_empty_sound975`, `l4_check_file_pure_sound975`). *(See [`GAP_ANALYSIS.md`](GAP_ANALYSIS.md) §3.2 for exact `DefEqInjectivity` and pure-stream vs full inductive/quotient stream scope boundaries.)*

---

## 2. Upstream `lean4lean` to Rocq & HOL Light Architecture Matrix

| Upstream `lean4lean` File(s) | Rocq Formalization (`rocq/`) | HOL Light Formalization (`hol/kernel_v3_complete/hol/`) | Key Verified Theorems & Invariants |
| :--- | :--- | :--- | :--- |
| `Theory/{VLevel,VExpr,VEnv}.lean`, `Typing/Basic.lean` | `SemanticModel.v` (874L), `DeclarativeTyping.v` (702L) | `declarative_typing961.ml` (505L) | `VIsDefEq`, `VHasType`, `VEnvOrdered_preserve_VIsDefEq`, `vlevel_inst_eval`, `VParRedStar_ChurchRosser` |
| `Theory/Typing/Lemmas.lean` | `TypingLemmas.v` (1,046L) | `typing_lemmas966.ml` (1,860L) | `VIsDefEq_instL`, `closedN`, `levelWF`, `weak0`, `instN`, `defeqDFC`, `VIsDefEq_isType`, `VIsDefEq_instDF`, `l4_venv_wf_lookup_unique966` |
| `Theory/LevelSat.lean` | `LevelSat.v` (628L) | `level_sat968.ml` (974L) | `vlevel_equiv_iff_unsat`, `vlevel_le_iff_unsat`, `l4_vpar_red_star_church_rosser968`, `l4_vsyn_has_type_unique968` |
| `Theory/VExpr.lean` (`Lift`/`Subst`), `Ctx.SubstEq` | `SubstTheory.v` (1,393L) | `subst_theory969.ml` (1,376L) | `vsubst_vsubst`, `vsubst_vinst`, `VCtxSubstEq` (`nil`, `cons`, `lift`, `wf`, `id`), `l4_vctx_subst_eq969` |
| `Theory/Typing/Strong.lean` | `StrongTyping.v` (1,926L) | `strong_typing970.ml` (3,559L) | `VIsDefEq_strong`, `VHasType_app_inv`, `lam_inv`, `const_inv`, `bvar_inv`, `VIsDefEq_substDF`, `l4_vis_defeq_substDF970` |
| `Theory/{VDecl,Quot,Inductive}.lean`, `Typing/{Env,Quot,Inductive,EnvLemmas}.lean` | `EnvDeclTheory.v` (1,667L) | `env_decl_theory971.ml` (1,766L) | `addQuot_WF`, `quotInd_iota`, `addInduct_WF`, `VEnvDeclsWF_to_VEnvWF`, `l4_add_quot_wf971`, `l4_add_induct_wf971` |
| `Theory/Typing/{Pattern,Injectivity,UniqueTyping,ChurchRosser,HeadReduction}.lean` | `PatternConfluence.v` (6,353L) | `pattern_confluence972.ml` (11,314L) | `VIsDefEq_uniq`, `VIsDefEqU_trans`, `VIsDefEq_church_rosser`, Kashima standardization, `VInferType`, `l4_vis_defeq_church_rosser972` |
| `Verify/{VLCtx,Expr,LocalContext}.lean` | `VerifyExpr.v` (3,164L) | `verify_expr973.ml` (5,645L) | `VLCtx`, `VTrProj`, `HasPrimitives`, `VEnvSound`, `VEnvSound_empty`, 12-ctor `VTrExprS`/`VTrExpr`, `l4_vtr_expr973` |
| `Verify/TypeChecker/{Reduce,WHNF,InferType,IsDefEq,EquivManager}.lean` | `VerifyTypeChecker.v` (5,602L), `InferSoundness.v` (661L) | `verify_typechecker974.ml` (10,716L), `infer_soundness967.ml` (1,009L) | `FullMethodsSound`, `checker_sound`, `cached_defeq_full_sound`, `l4_full_methods_sound974`, `l4_checker_methods_sound967` discharged |
| `Verify/Environment/*.lean`, `Quot.lean`, `FuelConfig.lean`, `EquivManager.lean` | `VerifyEnvironment.v` (1,741L), `QuotientTransaction.v`, `DefEqCache.v` (619L), `FuelConfig.v` (297L), `CachedChecker.v` (2,930L) | `verify_environment975.ml` (2,473L), `quotient_transaction963.ml` (101L), `equiv_manager964.ml` (279L), `fuel_config965.ml` (235L) | `admit_sound`, `VEnvSound_pure_admit`, `admit_mutual_sound`, `admit_quotient_sound`, `state_stream_from_initial_sound`, `l4_initialize_quotient_sound975`, `l4_check_file_pure_sound975` |
| Executable Kernel (`TypeChecker`, `Inductive`, `Quot`, `Primitive`, `Environment`) | `Syntax.v`, `Universes.v`, `Checker.v`, `LookupCore.v`, `CachedChecker.v`, `Declarations.v`, `Inductive.v`, `Nested*.v`, `Quotient.v`, `Primitives.v`, `Persistent*.v` | `kernel_syntax447.ml`..`file_certificate649.ml`, `quotient_dependencies839.ml`, `frontend/hol_check_v3.ml` | Full 13-constructor Lean 4.33/4.36 kernels; 24/24 Rocq native suites; 104/104 HOL `v3` entry cases; live Arena verified |

---

## 3. Measured Verification & Benchmark Evidence

### 3.1 Rocq Proof, Audit, Native Suites, & Live Lean 4.36.0 Arena

- **Build & Native Regression Suites (`sh scripts/build-rocq.sh`)**:
  - **123 / 123 `.vo` modules** compiled cleanly (`rocq/_CoqProject`).
  - **24 / 24 native test suites PASS** (including `31` wire checks, `279` replay checks, `129,520` lookup/hash assertions, `52,776` persistent-stream assertions, `28,534` depth/linear-cache assertions, `35,592` reduction assertions, and `12M+` universe semantic/completeness/instantiation/expression assertions).
- **Kernel Recheck & Zero-Escape Audit (`bash scripts/audit-build.sh`)**:
  - `Rocq objects selected: 123`
  - `* Axioms: <none>`
  - `Kernel recheck: PASS`
  - All 66 bundled stock HOL Light 3.1.0 files byte-identical to upstream `hol_light 3.1.0`; zero forbidden constructs across all Rocq, HOL Light, and OCaml sources.
- **Live Lean `4.36.0` Kernel Arena (`./build/rocq-check`, 225 exports, 35s per-case limit)**:
  - **Total**: **215 / 225 PASS** (`0` wrong verdicts, `0` declines, `10` extreme `perf/*` timeouts >35s)
  - **`init-prelude`**: **1 / 1 PASS** (`1.52s`)
  - **`bugs/*`**: **30 / 30 PASS** (`0` wrong, `0` decline, `0` timeout)
  - **`tutorial/*`**: **141 / 141 PASS** (`0` wrong, `0` decline, `0` timeout)
  - **`other/*`**: **10 / 10 PASS** (`0` wrong, `0` decline, `0` timeout)
  - **`corner-cases/*`**: **1 / 1 PASS** (`0` wrong, `0` decline, `0` timeout)
  - **`perf/*`**: **32 / 42 PASS** (`0` wrong, `0` decline, `10` timeouts >35s)

### 3.2 HOL Light Cold Verification, Legacy Suites, & Live Lean 4.36.0 Arena (`v3`)

- **Full `kernel_v3_complete` Cold Verification (`sh hol/kernel_v3_complete/verify_all_v3.sh`)**:
  - Session 1 (`verify_all_v3.ml`): **130 / 130** modules (`447`–`972`), `AXIOMS=3`, `V3_CHECK_AXIOMS_OK`, `V3_LOAD_DONE`.
  - Session 2 (`verify_entries_v3.ml`): **8 / 8** pristine-session `655` entry modules + **104 / 104** entry cases, `AXIOMS=3`, `V3_CHECK_AXIOMS_OK`, `V3_LOAD_DONE`.
  - Session 3 (`verify_soundness_v3.ml`): **3 / 3** soundness modules (`verify_expr973.ml`, `verify_typechecker974.ml`, `verify_environment975.ml`, 390 proved theorems), `AXIOMS=3`, `V3_CHECK_AXIOMS_OK`, `V3_LOAD_DONE`.
  - Exact disk coverage: **`verified=141 expected=141`**, **`V3_ALL_MODULES_VERIFIED`**.
- **HOL Light OCaml Transport Frontend (`sh scripts/build-hol-frontend.sh`)**: **67 / 67** transport checks PASS.
- **Legacy `v0` HOL Light Suites (`hol/test.sh` & `hol/test-quotient.sh`, 1,524 assertions across 11 suites)**:
  - `HOL_CORE_TESTS_PASSED 91`, `HOL_ADMISSION_TESTS_PASSED 38`, `HOL_ENVIRONMENT_TESTS_PASSED 95`, `HOL_INDUCTIVE_TESTS_PASSED 194`, `HOL_NAT_LITERAL_TESTS_PASSED 63`, `HOL_FAMILY_TESTS_PASSED 154`, `HOL_INDEXED_TESTS_PASSED 92`, `HOL_PROJECTION_CORE_TESTS_PASSED 569`, `HOL_PROJECTION_TESTS_PASSED 88`, `HOL_STRUCTURE_TESTS_PASSED 66`, `HOL_QUOTIENT_TESTS_PASSED 74`.
- **Live Lean `4.36.0` Kernel Arena via Warm Fork-Isolated `scripts/hol-server.sh --kernel v3`**:
  - **11 / 12 PASS** across representative `good/tutorial/*` and `bad/bugs/*` exports (`0` wrong verdicts):
    - **6 / 6** `good/tutorial/*` (`001_basicDef`, `015_levelComp1`, `026_levelMaxIdem`, `004_dependentType`, `033_letType`, `024_levelMaxComm`) accepted in `0.60–1.02s` each with closed HOL theorem `|- l4_file_verdict649 ... = 0` (`axioms=3`).
    - **5 / 6** `bad/bugs/*` (`orphan-rec`, `pi-closure-context`, `open-term-cache-context`, `loose-bvar-value`, `level-imax-leq`) semantically rejected in `0.73–8.56s` each with closed HOL theorem `|- l4_file_verdict649 ... = 1` (`axioms=3`).
    - **1 / 6** `bad/bugs/*` (`proj-non-structure`) safely declined on 30s per-case wall timeout (fork worker killed and reaped).
