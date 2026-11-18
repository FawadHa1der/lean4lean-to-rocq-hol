# Gap Analysis: lean4lean → Rocq / HOL Light

This document is an honest engineering audit of how far this repository ports
[`digama0/lean4lean`](https://github.com/digama0/lean4lean) at pinned commit
`8223d223ed98661882e95d9d6a7126df7097cd76`, what was implemented and fixed in
this revision to close major metatheoretic and verification gaps, and what
remains open. Where historical reports or comments were overly optimistic, this
document states the exact machine-checked scope.

Every claim below was verified against the sources, against a clean build on
Linux x86_64 (Debian 12, OCaml 4.14.2, Rocq 9.2.0 with Stdlib 9.1.0, HOL Light
3.1.0), and against upstream `lean4lean` at commit `8223d22`.

---

## 1. Summary Matrix

| Area | Upstream `lean4lean` (`8223d22`) | Rocq Port (`rocq/`) | HOL Light Port (`hol/kernel_v3_complete/` & `hol/`) |
| :--- | :--- | :--- | :--- |
| **Executable kernel** (WHNF, infer, defeq, inductives, nested inductives, quotients, Nat/String primitives) | `TypeChecker.lean`, `Inductive/*`, `Quot.lean`, `Primitive.lean` | **Substantially complete.** Extracted to `build/rocq-check`; passes 24/24 native suites and 100% of available functional Arena cases (`bugs/*`, `tutorial/*`, `other/*`, `corner-cases/*`). Deviations in §3.1. | **Split across two layers.** `kernel_v3_complete` formalizes the full 13-constructor kernel and passes 104/104 in-prover entry cases (`verify_entries_v3.ml`). The external Arena CLI (`frontend/hol_check.ml`) still runs baseline v0 (`hol/*.ml`), which accepts via closed theorems, cannot reject with a theorem, and declines unsupported features (§3.3). |
| **Declarative theory** (`VLevel`/`VExpr`/`VEnv`, 13-rule `IsDefEq` / `HasType`) | `Theory/{VLevel,VExpr,VDecl,VEnv}.lean`, `Theory/Typing/Basic.lean` | **Complete** (`SemanticModel.v`, `DeclarativeTyping.v`). | **Complete** (`declarative_typing961.ml`, `typing_lemmas966.ml`). |
| **Core typing metatheory** (`instL`, `closedN`, `levelWF`, `weakN`/`weak0`, `instN`/`inst0`, `defeqDFC`, `VEnvWF`, inversions, regularity `isType`, `instDF`) | `Theory/Typing/Lemmas.lean` (sorry-free upstream) | **Ported end-to-end** (`TypingLemmas.v`, 1,046 lines, 0 axioms). | **Ported end-to-end** (`typing_lemmas966.ml`, 1,829 lines, 0 added axioms). |
| **Typed Church–Rosser, Π-injectivity & type uniqueness for `VIsDefEq`** | `Theory/Typing/{ChurchRosser,Injectivity,UniqueTyping}.lean` (contain 6 `sorry`s upstream) | **Not ported for `VIsDefEq`.** `DeclarativeTyping.v` proves untyped β-only confluence (`VParRedStar_ChurchRosser`) and syntactic uniqueness (`VSynHasType_unique`), neither of which is connected to the 13-rule `VIsDefEq` judgment (§3.2). | **Not ported for `l4_vis_defeq961`.** `declarative_typing961.ml` proves multi-step head inversions and `Sort`/`Π` disjointness for untyped β-only `l4_vpar_red_star961` (§3.3). |
| **Kernel → theory soundness** | `Verify/**` (~20k lines, several `sorry`s in `WHNF.lean` / `IsDefEq.lean` / `Expr.lean`) | **Partial.** Non-circular relative soundness of `infer_step` / `infer` over syntactic `trE` + executable non-vacuity witness (`InferSoundness.v`, 661 lines). Discharging `CheckerMethodsSound` for fuelled `whnf`/`defeq` remains open; older `CheckerSoundness.v` bridges are conditional (§2.2, §3.2). | **Partial.** Matching non-circular relative soundness of `l4_infer_step586` / `l4_infer597` over syntactic `l4_tr_e967` + executable non-vacuity witness (`infer_soundness967.ml`, 1,009 lines). Discharging `l4_checker_methods_sound967` remains open; older `checker_soundness962.ml` is conditional (§2.3, §3.3). |
| **Caches** (`EquivManager`, `inferType` / `whnf` / failure caches) | `EquivManager.lean`, `TypeChecker.lean` | **Standalone model only** (`DefEqCache.v`), not wired into `Checker.v`. | **Standalone model only** (`equiv_manager964.ml`), not wired into `kernel_checker597.ml`. |
| **Multi-axis fuel** | `FuelConfig.lean` | **Standalone model only** (`FuelConfig.v`); production `Checker.v` uses a single coupled `nat` fuel (default 512). | **Standalone model only** (`fuel_config965.ml`); `kernel_checker597.ml` uses a single coupled `num` fuel. |

---

## 2. Implemented and Fixed in This Revision

### 2.1 `rocq/TypingLemmas.v` (1,046 lines): Port of `Theory/Typing/Lemmas.lean`

Unconditional and axiom-free (`rocq check` reports `* Axioms: <none>`). Establishes
the full structural metatheory of the 13-rule declarative `VIsDefEq` / `VHasType`
system over `SemanticModel.v` and `DeclarativeTyping.v`:

| Upstream `lean4lean` | Rocq (`rocq/TypingLemmas.v`) | HOL Light (`hol/kernel_v3_complete/hol/typing_lemmas966.ml`) |
| :--- | :--- | :--- |
| `VLevel.inst_inst`, `inst_wf`, `params` | `vlevel_inst_inst`, `vlevel_inst_wf_any`, `vlevel_params`, `vlevel_inst_params` | `l4_vlevel_inst_inst966`, `l4_vlevel_inst_wf_any966`, `l4_vlevel_params966`, `l4_vlevel_inst_params966` |
| `IsDefEq.instL` | `VIsDefEq_instL`, `VHasType_instL`, `VIsType_instL`, `VIsDefEqU_instL` | `l4_vis_defeq_instL966`, `l4_vhas_type_instL966`, `l4_vis_type_instL966` |
| `IsDefEq.closedN'` | `VIsDefEq_closedN`, `VCtxClosed`, `VLookup_closed` | `l4_vis_defeq_closedN966`, `l4_vctx_closed966`, `l4_vlookup_closed966` |
| `IsDefEq.levelWF` | `VIsDefEq_levelWF`, `VCtxLevelWF`, `VLookup_levelWF` | `l4_vis_defeq_level_wf966`, `l4_vctx_level_wf966`, `l4_vlookup_level_wf966` |
| `Ordered.closed`, `constWF`, `defEqWF` | `VEnvWF_closed`, `VEnvWF_const_wf`, `VEnvWF_defeq_wf` | `l4_venv_wf_closed966`, `l4_venv_wf_const_wf966`, `l4_venv_wf_defeq_wf966` |
| `IsDefEq.weakN`, `weak0`, `const0`, `extra0` | `VIsDefEq_weak0`, `VHasType_weak0`, `VHasType_const0`, `VIsDefEq_extra0` | `l4_vis_defeq_weakN966`, `l4_vis_defeq_weak0966`, `l4_vhas_type_const0966`, `l4_vis_defeq_extra0966` |
| `Ctx.InstN`, `IsDefEq.instN`, `inst0` | `VCtxInstN`, `VIsDefEq_instN`, `VHasType_instN`, `VIsDefEq_inst0` | `l4_vctx_instN966`, `l4_vis_defeq_instN966`, `l4_vis_type_instN966`, `l4_vis_defeq_inst0966` |
| `OnCtx`, `IsType.lookup` | `VCtxWF`, `VIsType_lookup` | `l4_vctx_wf966`, `l4_vis_type_lookup966` |
| `IsDefEq.defeqDF_l`, `IsDefEqCtx`, `defeqDFC` | `VIsDefEq_defeqDF_l`, `VIsDefEqCtx`, `VIsDefEq_defeqDFC`, `VIsDefEqCtx_symm` | `l4_vis_defeq_defeqDF_l966`, `l4_vis_defeq_ctx966`, `l4_vis_defeq_defeqDFC966`, `l4_vis_defeq_ctx_symm966` |
| `IsDefEq.sort_inv`, `forallE_inv` | `VIsDefEq_sort_inv'`, `VHasType_forallE_inv`, `VIsType_forallE_inv` | `l4_vis_defeq_sort_inv'966`, `l4_vis_defeq_forall_inv_ind966`, `l4_vis_type_forall_inv966` |
| `IsDefEq.isType` (regularity) | `VIsDefEq_isType`, `VIsDefEq_sort_r` | `l4_vis_defeq_is_type966`, `l4_vis_defeq_sort_r966` |
| `IsDefEq.instDF` | `VIsDefEq_instDF` | `l4_vis_defeq_instDF966` |

### 2.2 `rocq/InferSoundness.v` (661 lines): Non-Circular Inference Soundness

Axiom-free Rocq counterpart to `Lean4Lean/Verify/TypeChecker/InferType.lean`:

- **`trE` / `vlevel_of_level` / `trLs`**: Purely syntactic functions from executable
  `expr` / `level` to `VExpr` / `VLevel` with no typing premises baked into the
  translation (eliminating vacuous constructors such as `TrExprS_lit` / `TrProj`).
  Proved to commute with lifting, de Bruijn substitution/instantiation, and
  universe level instantiation (`trE_lift`, `trE_subst`, `trE_instantiate`,
  `trL_subst`, `trLs_subst`, `trE_subst_levels`).
- **`TrBCtx` & `KernelEnvSyntacticBridge`**: Relate the executable bound context
  and constant table to `VCtxWF` and `VEnvWF` through syntactic translations.
- **`MethodsSound`**: Constrains **only** the WHNF and conversion callbacks
  (`whnf_method`, `defeq_method`, `eager_defeq_method`) passed to `infer_step`;
  nothing is assumed about `infer_step` itself.
- **`infer_step_sound`, `check_step_sound`, `infer_sound`**: Proved by structural
  induction on `e` over `BVar`, `Sort`, `Const`, `App`, `Lam`, `Pi`, and `MData`
  in checking mode (`infer_only = false`).
- **Executable non-vacuity (`syntactic_methods_sound`, `syntactic_infer_sound`)**:
  Instantiates `MethodsSound` unconditionally with identity WHNF and the real
  kernel alpha-equality check (`alpha_eq`), yielding a complete, non-vacuous
  soundness theorem for an executable inferencer.
- **Explicit open obligation (`CheckerMethodsSound`)**: States the exact
  remaining proof obligation for the full fuelled `checker_methods` (`whnf` +
  `defeq`), corresponding to upstream's `sorry`s in `Verify/TypeChecker/WHNF.lean`
  and `IsDefEq.lean`.

### 2.3 HOL Light End-to-End Verification (`verify_all_v3.sh`) & New Metatheory (`966`–`967`)

1. **`hol/kernel_v3_complete/hol/typing_lemmas966.ml` (1,829 lines)** and
   **`hol/kernel_v3_complete/hol/infer_soundness967.ml` (1,009 lines)**:
   Full HOL Light ports of `Theory/VExpr.lean` + `Theory/Typing/Lemmas.lean` and
   non-circular `Verify/TypeChecker/InferType.lean` (`l4_tr_e967`, `l4_tr_l967`,
   `l4_methods_sound967`, `l4_infer_step_sound967`, `l4_check_step_sound967`,
   `l4_infer_sound967`, open `l4_checker_methods_sound967`, and unconditional
   `l4_syntactic_methods_sound967` / `l4_syntactic_infer_sound967` over
   `l4_core_alpha_eq538`), proved with zero added axioms (`AXIOMS=3`).
2. **Executing `hol/kernel_v3_complete/` end-to-end (`verify_all_v3.sh`)**:
   `MANIFEST839.json` originally recorded `proofs_executed: 0` and
   `target_compiled: false`. Building a full two-session verification harness
   (`verify_all_v3.ml` for the 125 core/metatheory/property/regression modules +
   `verify_entries_v3.ml` for the 8 pristine-session `655` entry modules and
   104 entry cases) exposed three defects in previously unexecuted modules:
   - `hol/kernel_v3_complete/hol/entry_flatten650655.ml`: Camlp5 type-parse error on
     unparenthesized `:(num list)list list` (fixed to `:((num list)list)list`).
   - `hol/kernel_v3_complete/hol/primitive_inverses620.ml`: Missing `MESON_TAC []`
     after `SIMP_TAC` in `l4_kr_bind_accept_inverse620` and `SPEC` instead of
     polymorphic `ISPEC` in `l4_classify_primitive_metadata_requires_certificate620`.
   - `hol/kernel_v3_complete/hol/primitive_recursors_properties622.ml`: Exponential
     `LET_DEF` blowup inside the unreached body of `l4_primitive_unfold_nat_well_founded622`
     in `l4_primitive_wf_wrong_fix_name622` and `l4_primitive_wf_wrong_fix_arity622`
     (fixed via outer `let_CONV` + `MATCH_CONV`).
   With these fixes, **all 133 / 133** `hol/*.ml` modules and **104 / 104**
   entry cases verify cleanly with `AXIOMS=3` and `check_axioms ()` passing; see
   [`hol/kernel_v3_complete/VERIFICATION_STATUS.md`](hol/kernel_v3_complete/VERIFICATION_STATUS.md).

### 2.4 Executable Rocq Projection Owner Fix

In [`rocq/Checker.v`](rocq/Checker.v) and [`rocq/LookupCore.v`](rocq/LookupCore.v),
inferring a projection `EProj s idx e` whose owner `s` is missing or not an
inductive declaration previously returned `Decline UnsupportedExpression`
instead of rejecting. Upstream `lean4lean` (`inferProj`) throws `invalidProj`.
Both modules now return `Reject TypeMismatch`, extracted `.ml` artifacts were
regenerated, and all 24 native regression suites and Arena bug/tutorial suites
pass.

### 2.5 Explicit `STATUS` Caveat Headers & Portable Audit Hardening

- Added explicit `STATUS` scope headers to conditional/standalone modules in
  both ports: `rocq/{CheckerSoundness,DefEqCache,FuelConfig}.v` and
  `hol/kernel_v3_complete/hol/{declarative_typing961,checker_soundness962,equiv_manager964,fuel_config965}.ml`.
- Made toolchain setup, test runners, and build auditing work natively on
  **Linux x86_64** as well as **macOS arm64** (`scripts/{setup-toolchains,toolchain-env,setup-toolchain-perl,audit-build,hol-check,test_metadata_mutations}.sh/.py`,
  `hol/{test,test-quotient,test-quotient-syntax}.sh`, `toolchain/installed-packages.Linux.txt`).
- Hardened [`scripts/audit-build.sh`](scripts/audit-build.sh) to verify all 66
  bundled stock HOL Light 3.1.0 files in `hol/kernel_v2_full_file/` and
  `hol/kernel_v3_complete/` byte-for-byte against the toolchain's `lib/hol_light`
  while scanning every handwritten `.v` and `.ml`/`.mli` project file for proof
  escapes.

---

## 3. Remaining Gaps (Not Closed by This Revision)

### 3.1 Rocq Executable Kernel vs Upstream `lean4lean`

| Gap | Effect |
| :--- | :--- |
| No runtime `EquivManager` and no `inferType` / `whnfCore` / failure caches in `Checker.v` (alpha fastpath capped at 256 nodes). | Performance only: large exports (`init`, `std`, `cslib`, `perf/magma-*`, `perf/fueled-chain`) time out under Arena per-case limits. |
| Single coupled `nat` fuel (default 512) instead of upstream's multi-axis `FuelConfig`. | Causes `Decline OutOfFuel` on deep reductions where upstream succeeds; never produces wrong `Accept`/`Reject` verdicts. |
| `Nat.pow` and `Nat.shiftLeft` reduce only when the exponent/shift is `<= fuel`, declining otherwise (upstream allows `pow` up to `2^24` and unbounded `shiftLeft`). | Deliberate memory guard because extracted `N`/`Pos.pow` unary-step exponentiation can blow up; causes declines, never wrong verdicts. |
| `lazyDeltaProjReduction` is not implemented in `Checker.v`. | Potential declines or timeouts on projection-heavy lazy unfolding. |
| Non-upstream reductions in `Checker.v`: native `Nat.pred`, `Nat.zero` → `0` normalization in WHNF, and `core_erasing_delta`. | Sound definitional unfoldings of standard `Nat` constants, but not step-for-step identical to upstream `lean4lean`. |
| Unverified OCaml frontend TCB (`frontend/wire.ml` and `frontend/replay.ml`). | NDJSON parsing, topological sorting, mutual block grouping, and `10^6` input size caps live in unverified OCaml. |

### 3.2 Rocq Metatheory & Verification Bridge

- **`CheckerMethodsSound` is open**: `InferSoundness.v` proves `infer_step` /
  `infer` sound relative to `MethodsSound`, and proves `MethodsSound` for
  `syntactic_methods`, but does not discharge `MethodsSound` for the full fuelled
  `whnf` / `defeq` (δ, ι, ζ, η, proof irrelevance, Nat/String primitives,
  quotients, projections, lazy delta), nor extend `trE` to free variables,
  `let`, literals, or projections. Upstream `lean4lean` also still has `sorry`s
  in `Verify/TypeChecker/WHNF.lean` and `IsDefEq.lean`.
- **Declaration admission soundness is conditional**: `CheckerSoundness.v`
  packages `checked_constant_extends_venv_wf` under explicit semantic typing
  hypotheses, and models ι/δ rules as pre-populated `VDF_extra` assumptions
  rather than deriving recursor/quotient/inductive soundness end-to-end from
  `addInductive` / `addQuot`.
- **Typed Church–Rosser, Π-injectivity, and unique typing for `VIsDefEq` are not
  ported**: `DeclarativeTyping.v` proves confluence (`VParRedStar_ChurchRosser`)
  and `Sort`/`Π` head disjointness/injectivity for **untyped β-only** parallel
  reduction `VParRed` (omitting δ, ι, η, and proof irrelevance), and proves
  `VSynHasType_unique` for a deterministic syntax-directed auxiliary relation
  without conversion. Upstream `lean4lean` itself has 6 `sorry`s across
  `ChurchRosser.lean`, `Injectivity.lean`, and `UniqueTyping.lean`.
- `Theory/Typing/{Strong,EnvLemmas,Meta}.lean` and `Ctx.SubstEq` are not ported.

### 3.3 HOL Light Port

- **Arena CLI (`frontend/hol_check.ml`) runs baseline v0, not `kernel_v3_complete`**:
  The socket/CLI checker used by `scripts/hol-check.py` loads the 9-constructor
  baseline `hol/*.ml` development rather than `hol/kernel_v3_complete/`.
- **No theorem-backed semantic rejection in `hol_check.ml`**: Only wire/input
  validation errors return exit code `1` (`reject`); semantic kernel rejections
  in the v0 Arena path map to `decline` (only 6 of 71 expected Arena rejects are
  rejected, all via input validation). By contrast, in-prover `v3` entry fixtures
  (`file_verdict649.ml` / `entry_serialized649655.ml`) do certify 3-way verdicts
  (`0` accept, `1` reject, `2` decline) on small fixtures.
- **Internal timeouts reported as declines in v0**: In the historical 216-case
  Arena run of `hol-check.py`, 47 of the 120 declines were per-case internal
  timeouts (due to unary `SUC` Nat terms, linear environment lookup, no lazy δ,
  and per-fuel cache resets).
- **Missing v0 features**: `gcd`, `mod`, `div`, `land`, `lor`, `xor`,
  `shiftRight`, `bitwise`, unsafe/partial definitions, mutual definition groups,
  and nested inductives decline in the v0 Arena bridge (`frontend/hol_input.ml`).
- **HOL metatheory open items**: Mirrors §3.2 — `l4_checker_methods_sound967` in
  `infer_soundness967.ml` is open, `checker_soundness962.ml` is conditional, and
  `declarative_typing961.ml` proves multi-step inversions only for untyped
  β-only `l4_vpar_red_star961` (not full Takahashi confluence or typed
  `l4_vis_defeq961` Church–Rosser).

---

## 4. Corrections to Historical Documentation

| Earlier Claim in `README.md` / `FINAL_REPORT.md` | Actual State (Corrected Across Docs) |
| :--- | :--- |
| "Rocq 9.0.0" | Toolchain pins **Rocq 9.2.0** (`rocq-prover 9.2.0`, `rocq-stdlib 9.1.0`). |
| "104 Rocq modules" / "131 HOL v3 modules" | `rocq/_CoqProject` has **114** `.v` modules (112 prior + `TypingLemmas.v` + `InferSoundness.v`); `hol/kernel_v3_complete/hol/` has **133** `.ml` modules (131 prior + `typing_lemmas966.ml` + `infer_soundness967.ml`). |
| Nonexistent Rocq filenames (`NestedInductive.v`, `Primitive.v`, `Partition.v`, `DAGAdmission.v`, `Soundness.v`, `KernelSoundness.v`, `StringParity.v`, `NatProbeOrder.v`, `FailureCache162.v`, `NewInductive.v`, `PersistentEnvironment.v`) | Replaced with actual files (`NestedAdmission.v`/`NestedTransform.v`, `Primitives.v`, `DagAdmission.v`, `StringParityRegression.v`, `NatProbeDispatch.v`, `PersistentIndex.v`/`PersistentAdmission.v`, `InferSoundness.v`, `CheckerSoundness.v`). |
| Nonexistent HOL v3 filenames (`inductive_admission632.ml`, `file_certificate644.ml`) | Replaced with actual v3 files (`checked_inductives629.ml`/`checked_admission631.ml`, `file_certificate649.ml`/`closed_goals644.ml`). |
| Nonexistent Rocq lemma names (`VLookup_weakN`, `VIsDefEq_weaken0`, `TrLevel_wf`, `TrLevel_eval`, `VIsDefEq_has_type_both`) | Replaced with actual names (`VCtxLiftN_lookup`, `VIsDefEq_weak0`, `vlevel_of_level_wf`, `vlevel_of_level_eval`, `VIsDefEq_hasType_both`). |
| Misstated line counts (`SemanticModel.v` 842, `DeclarativeTyping.v` 854, `CheckerSoundness.v` 495) | Corrected to actual `wc -l` counts (`SemanticModel.v` 874, `DeclarativeTyping.v` 702, `CheckerSoundness.v` 895, `TypingLemmas.v` 1,046, `InferSoundness.v` 661). |
| Unqualified claims of full Church–Rosser, Π-injectivity, type uniqueness, and unconditional end-to-end kernel soundness | Qualified everywhere to distinguish unconditional `TypingLemmas`/`966`, relative `InferSoundness`/`967` (+ `syntactic_methods` non-vacuity), untyped β-only `VParRed`, conditional `CheckerSoundness`/`962`, and standalone `DefEqCache`/`FuelConfig` models. |
| "216 locally available Arena files" out of the box | `arena/corpus/` is gitignored; the small published tarball provides 196 files (`172/172` available functional cases pass on `build/rocq-check`), while 15 `outcome=either` corner-cases and 5 large exports require separate Lean export/acquisition scripts (`scripts/fetch_arena_generate.py`, `scripts/acquire_*_arena.py`). |

---

## 5. Reproducing Verification End-to-End

```sh
# 1. Initialize or verify pinned toolchains (macOS arm64 or Linux x86_64)
sh scripts/setup-toolchains.sh

# 2. Compile all 114 Rocq modules, extract OCaml, link build/rocq-check, and run 24 native suites
sh scripts/build-rocq.sh

# 3. Recheck all 114 Rocq .vo objects with rocq check + static escape & stock-HOL byte audit
bash scripts/audit-build.sh

# 4. Verify all 133 HOL Light v3 modules + 104 entry cases in fresh HOL sessions (AXIOMS=3)
sh hol/kernel_v3_complete/verify_all_v3.sh

# 5. Run baseline HOL Light v0 regression suites
sh scripts/toolchain-exec.sh sh hol/test.sh
sh scripts/toolchain-exec.sh sh hol/test-quotient.sh

# 6. Run Arena soundness bug and tutorial suites against build/rocq-check
python3 -B scripts/test_arena.py --checker ./build/rocq-check --select 'bugs/*'
python3 -B scripts/test_arena.py --checker ./build/rocq-check --select 'tutorial/*'
```
