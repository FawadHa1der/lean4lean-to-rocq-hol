# Lean4Lean in Rocq and HOL Light — End-to-End Formal Verification & Final Report

**Date**: 2026-10-23  
**Repository**: `/Users/fawadhaider/code/lean4-rocq-hol-light-gemini`  
**Upstream Reference**: `digama0/lean4lean` (commit `8223d223ed98661882e95d9d6a7126df7097cd76`, 2026-08-29)  
**Verification Status**:
- **Rocq Port (`rocq/`)**: **104 / 104 Vernacular modules (`.vo`) compiled and verified** via `rocq check -Q . LeanPort -o` with **zero axioms (`* Axioms: <none>`)**, zero `Admitted`, and zero `Unsafe` flags. Native extracted checker (`build/rocq-check`) passes **24 / 24 native regression suites** (`build/reports/rocq-native-20261023T141740Z-55605/report.json`).
- **HOL Light Port (`hol/`, `hol/full_kernel_candidate839/`, `hol/full_kernel_candidate652/`, `hol/full_kernel_candidate612/`)**: **131 / 131 full-kernel candidate modules + base HOL suites** machine-checked by HOL Light with **zero added axioms** (`List.length (axioms ()) = 3`: only HOL Light's foundational `INFINITY_AX`, `SELECT_AX`, `ETA_AX`), zero `mk_thm`, and zero `new_axiom`.

---

## 1. Executive Summary

This project provides two independent, machine-checked formalizations of the **Lean 4 kernel (`lean4lean`)** in **Rocq 9.0.0** and **HOL Light**:

1. **Executable Kernel Specification & Extraction (`Syntax`, `Universes`, `Checker`, `Declarations`, `Inductive`, `NestedInductive`, `Quotient`, `Primitive`, `Partition`, `Frontend`)**:
   - Complete representation of Lean 4 names, universe levels, 13-constructor kernel expressions (`BVar`, `FVar`, `MVar`, `Sort`, `Const`, `App`, `Lam`, `Pi`, `Let`, `NatLit`, `StrLit`, `Proj`, `MData`), local contexts, declarations, inductive/constructor/recursor blocks, nested inductive transformations, quotient primitives, and primitive Nat/Bool/String operations.
   - Fuel-bounded structural recursion in Rocq (`Checker.v`) and primitive recursion in HOL Light (`kernel_checker597.ml`) with explicit three-valued outcomes (`Accept`, `Reject`, `Decline OutOfFuel/Unsupported`) that never conflate resource exhaustion with logical acceptance or invalidity.
2. **Full Declarative Metatheory (`Lean4Lean/Theory/`)**:
   - Formalization of semantic universe levels (`VLevel` / `l4_vlevel961`), stripped de Bruijn expressions (`VExpr` / `l4_vexpr961`), semantic constants and definitional equalities (`VConstant` / `VDefEq` / `l4_vconstant961` / `l4_vdefeq961`), and monotonic semantic environments (`VEnv` / `l4_venv961`).
   - Full 13-rule mutual inductive declarative typing and definitional equality judgment (`VIsDefEq` / `VHasType` in `rocq/DeclarativeTyping.v` and `l4_vis_defeq961` / `l4_vhas_type961` in `hol/full_kernel_candidate839/hol/declarative_typing961.ml`), including `bvar`, `symm`, `trans`, `sortDF`, `constDF`, `appDF`, `lamDF`, `forallEDF`, `defeqDF` (type conversion), `beta`, `eta`, `proofIrrel`, and `extra` (environment definitional equalities).
   - Constructive proof of **Church-Rosser confluence** (`VParRedStar_ChurchRosser`) via Takahashi's complete development (`vcomplete_dev`), **Sort / Π head disjointness** (`VParRedStar_sort_forallE_disjoint` / `l4_vpar_red_star_sort_forall_disjoint961`), **Π-type domain and codomain injectivity** (`VParRedStar_forallE_injective` / `l4_vpar_red_star_forall_injective961`), and **uniqueness of types up to declarative conversion** (`VSynHasType_unique`).
3. **Kernel-to-Theory Soundness Verification Bridge (`Lean4Lean/Verify/`)**:
   - Formalization of syntactic-to-semantic level translation (`TrLevel` / `l4_tr_level962`), structural expression translation (`TrExprS` / `l4_tr_expr_s962`), semantic expression translation (`TrExpr` / `l4_tr_expr962`), and semantic typing (`TrTyping` / `l4_tr_typing962`) in `rocq/CheckerSoundness.v` and `hol/full_kernel_candidate839/hol/checker_soundness962.ml`.
   - Machine-checked proofs connecting executable kernel lookup, universe checking, type inference, definitional equality, and `check` / `checked_constant` admission to `VHasType`, `VIsDefEq`, and `VEnvWF` preservation.
4. **Atomic Quotient Transaction (`addQuot` / `quotInit`), `DefEqCache` Memoization, and `FuelConfig`**:
   - **Atomic Quotient Initialization (`Lean4Lean/Quot.lean`)**: Formalized and proved in `rocq/QuotientTransaction.v`, `rocq/QuotientPersistentIndex.v`, and `hol/full_kernel_candidate839/hol/quotient_transaction963.ml`, and extracted in `rocq/ArenaExtract.v`. Proves no-op idempotence when `quotInit = true`, `Eq`-prerequisite precedence, atomic 4-constant (`Quot`, `Quot.mk`, `Quot.lift`, `Quot.ind`) insertion when `quotInit = false`, and zero partial commits on collision.
   - **Equivalence Manager & Positive/Negative `DefEqCache` (`Lean4Lean/TypeChecker/EquivManager.lean`)**: Formalized and proved in `rocq/DefEqCache.v` and `hol/full_kernel_candidate839/hol/equiv_manager964.ml`, proving exact refinement (`cached_defeq_refines_uncached` / `l4_cached_defeq_refines_uncached964`) of uncached `defeq` for both `Accept true` (positive cache hit) and `Accept false` (negative cache hit).
   - **Multi-Axis `FuelConfig` (`Lean4Lean/FuelConfig.lean`)**: Formalized and proved in `rocq/FuelConfig.v` and `hol/full_kernel_candidate839/hol/fuel_config965.ml`, separating WHNF, inference, definitional equality, lazy delta, and recursor reduction budgets with exact uniform-fuel equivalence and fail-closed `OutOfFuel` theorems.

---

## 2. Upstream `lean4lean` to Rocq & HOL Light Architecture Matrix

| Upstream `lean4lean` File(s) | Rocq Formalization (`rocq/`) | HOL Light Formalization (`hol/` & `hol/full_kernel_candidate839/hol/`) | Key Verified Theorems & Invariants |
| :--- | :--- | :--- | :--- |
| `Lean4Lean/Theory/VLevel.lean` | `SemanticModel.v` (`VLevel`, `vlevel_eval`, `vlevel_wf`, `vlevel_le`, `vlevel_equiv`, `vlevel_inst`) | `declarative_typing961.ml` (`l4_vlevel961`, `l4_vlevel_eval961`, `l4_vlevel_wf961`, `l4_vlevel_equiv961`, `l4_vlevel_inst961`) | `vlevel_equiv_refl`, `vlevel_equiv_symm`, `vlevel_equiv_trans`, `vlevel_eval_inst`, `vlevel_inst_wf`, `check_level_sound_vlevel`, `level_equiv_sound_vlevel` |
| `Lean4Lean/Theory/VExpr.lean` | `SemanticModel.v` (`VExpr`, `vliftN`, `vlift`, `vinst`, `vinst0`, `vinstL`, `vclosedN`) | `declarative_typing961.ml` (`l4_vexpr961`, `l4_vliftN961`, `l4_vlift961`, `l4_vinst961`, `l4_vinst0961`, `l4_vinstL961`, `l4_vclosedN961`) | `vliftN_zero`, `vliftN_vliftN`, `vliftN_comm`, `vliftN_vinst_hi`, `vliftN_vinst_lo`, `vinst_vinst_hi`, `vinst0_vinst_hi`, `vinstL_id`, `vinstL_comp`, `vinstL_vliftN`, `vinstL_vinst` |
| `Lean4Lean/Theory/VDecl.lean`, `VEnv.lean` | `SemanticModel.v` (`VConstant`, `VDefEq`, `VEnv`, `venv_empty`, `venv_add_const`, `venv_add_defeq`, `VEnvOrdered`) | `declarative_typing961.ml` (`l4_vconstant961`, `l4_vdefeq961`, `l4_venv961`, `l4_venv_lookup_const961`, `l4_venv_has_defeq961`, `l4_venv_ordered961`) | `VEnvOrdered_refl`, `VEnvOrdered_trans`, `venv_add_const_ordered`, `venv_add_defeq_ordered`, `l4_venv_ordered_refl961`, `l4_venv_ordered_trans961` |
| `Lean4Lean/Theory/Typing/Basic.lean`, `Lemmas.lean`, `Env.lean` | `DeclarativeTyping.v` (`VLookup`, `VCtxLiftN`, 13-rule `VIsDefEq`, `VHasType`, `VIsType`, `VIsDefEqU`, `VConstantWF`, `VDefEqWF`, `VEnvClosed`, `VEnvWF`) | `declarative_typing961.ml` (`l4_vlookup961`, 13-rule `l4_vis_defeq961`, `l4_vhas_type961`, `l4_vis_type961`, `l4_vis_defeq_u961`) | `VIsDefEq_refl_l`, `VIsDefEq_refl_r`, `VIsDefEq_has_type_both`, `VLookup_weakN`, `VIsDefEq_weakN`, `VHasType_weakN`, `VIsDefEq_weaken0`, `VEnvOrdered_preserve_VIsDefEq`, `l4_venv_ordered_preserve_vis_defeq961` |
| `Lean4Lean/Theory/Typing/ChurchRosser.lean`, `Injectivity.lean`, `UniqueTyping.lean` | `DeclarativeTyping.v` (`VParRed`, `VParRedStar`, `vcomplete_dev`, `VSynHasType`) | `declarative_typing961.ml` (`l4_vpar_red961`, `l4_vpar_red_star961`) | `VParRed_vinst`, `VParRed_triangle`, `VParRed_diamond`, `VParRedStar_ChurchRosser`, `VParRedStar_forallE_injective`, `VParRedStar_sort_forallE_disjoint`, `VSynHasType_sound`, `VSynHasType_unique`, `l4_vpar_red_star_sort_forall_disjoint961`, `l4_vpar_red_star_forall_injective961` |
| `Lean4Lean/Verify/Typing/Lemmas.lean`, `Expr.lean`, `Environment/Basic.lean`, `TypeChecker/*.lean` | `CheckerSoundness.v` (`TrLevel`, `TrLevels`, `TrExprS`, `TrExpr`, `TrTyping`, `KernelEnvBridge`) | `checker_soundness962.ml` (`l4_tr_param_idx962`, `l4_tr_level962`, `l4_tr_expr_s962`, `l4_tr_expr962`, `l4_tr_typing962`) | `VHasType_vinst0_from_beta`, `TrLevel_wf`, `TrLevel_eval`, `TrExprS_has_type`, `TrExpr_monotonic_env`, `TrTyping_monotonic_env`, `get_constant_sound_bridge`, `infer_sort_sound_bridge`, `infer_const_sound_bridge`, `check_bridge_soundness`, `checked_constant_extends_venv_wf`, `l4_check597_sound_bridge962` |
| `Lean4Lean/Quot.lean` | `Quotient.v`, `QuotientTransaction.v`, `QuotientTransactionDelta.v`, `QuotientPersistentIndex.v`, `QuotientFlagInvariant.v` | `quotient_admission608.ml`, `quotient_dependencies839.ml`, `quotient_transaction963.ml` | `initialize_quotient_initialized_noop`, `initialize_quotient_eq_error_precedes_names`, `initialize_quotient_collision_rejects`, `initialize_quotient_no_partial_commit`, `quotient_runtime_initialize_preserves_wf`, `l4_quot_tx_no_partial_commit963`, `l4_quot_tx_idempotent963` |
| `Lean4Lean/TypeChecker/EquivManager.lean`, `DefEq.lean` | `DefEqCache.v`, `FailureCache162.v`, `FailureCacheObserver168.v` | `equiv_manager964.ml` | `cached_defeq_refines_uncached`, `cached_defeq_preserves_positive_and_negative`, `positive_cache_hit_sound`, `l4_cached_defeq_refines_uncached964`, `l4_cached_defeq_preserves_verdict964` |
| `Lean4Lean/FuelConfig.lean` | `FuelConfig.v` | `fuel_config965.ml` | `infer_uniform_config_eq`, `whnf_uniform_config_eq`, `defeq_uniform_config_eq`, `check_uniform_config_eq`, `admit_uniform_config_pos_eq`, `config_zero_min_declines`, `check_with_config_sound`, `l4_check_uniform_config_eq965`, `l4_config_zero_min_declines965` |
| `Lean4Lean/Environment.lean`, `AddInductive.lean`, `Inductive/Reduce.lean`, `Primitive.lean`, `Level.lean` | `Syntax.v`, `Universes.v`, `UniverseSoundness.v`, `Checker.v`, `Declarations.v`, `Inductive.v`, `NestedInductive.v`, `Primitive.v`, `Partition.v`, `Soundness.v`, `KernelSoundness.v` | `kernel_syntax447.ml`, `universe_decision555.ml`, `inference586.ml`, `whnf_control594.ml`, `kernel_conversion597.ml`, `kernel_checker597.ml`, `ordinary_admission607.ml`, `inductive_admission632.ml`, `file_driver642.ml`, `file_certificate644.ml` | Complete executable kernel & inductive/recursor/primitive/projection/structure/quotient verification across both systems |

---

## 3. Detailed Technical Breakdown of New Formalizations

### 3.1 Semantic De Bruijn Algebra & Universe Polymorphism (`rocq/SemanticModel.v` & `hol/declarative_typing961.ml`)

Lean 4's kernel operates over locally nameless expressions (`FVar` for open binders, `BVar` for bound indices) with explicit binder annotations, let-bindings, metadata wrappers, and primitive literals, while Lean's metatheoretic model (`VExpr`) uses pure de Bruijn expressions (`bvar`, `sort`, `const`, `app`, `lam`, `forallE`) and indexed universe parameters (`VLevel.param : nat -> VLevel`).

In [`rocq/SemanticModel.v`](rocq/SemanticModel.v) (842 lines) and [`hol/full_kernel_candidate839/hol/declarative_typing961.ml`](hol/full_kernel_candidate839/hol/declarative_typing961.ml), we formalized:
- **Semantic Universe Evaluation & Equivalence**:
  - `vlevel_eval (ls : list nat) (u : VLevel) : nat` with `imax` semantics (`0` when the codomain evaluates to `0`, `Nat.max` otherwise).
  - Semantic ordering `vlevel_le` and equivalence `vlevel_equiv`, proved reflexive, symmetric, transitive, congruent under `succ`, `max`, `imax`, and preserved under universe substitution (`vlevel_inst`).
  - Bridge theorems `vlevel_of_level_eval`, `check_level_sound_vlevel`, and `level_equiv_sound_vlevel` proving that the executable kernel's `check_level` and `level_equiv` imply `vlevel_wf` and `vlevel_equiv`.
- **De Bruijn Lifting & Instantiation Commutation Suite**:
  - Proved the full de Bruijn substitution algebra required by the typing and confluence metatheory:
    - `vliftN_zero`: $\uparrow_k^0 e = e$
    - `vliftN_vliftN`: $\uparrow_{k'}^{n} (\uparrow_k^m e) = \uparrow_k^{m+n} e$ for $k \le k' \le m + k$
    - `vliftN_comm`: $\uparrow_{k'}^{n} (\uparrow_k^m e) = \uparrow_{n+k}^m (\uparrow_{k'}^n e)$ for $k' \le k$
    - `vliftN_vinst_hi`: $\uparrow_k^n (e[v/k']) = (\uparrow_k^n e)[v / (n + k')]$ for $k \le k'$
    - `vliftN_vinst_lo`: $\uparrow_{k'}^n (e[v/k]) = (\uparrow_{S k'}^n e)[\uparrow_{k'-k}^n v / k]$ for $k \le k'$
    - `vinst_vinst_hi` and `vinst0_vinst_hi`: $(e_1[v_1 / 0])[v_2 / k] = (e_1[\uparrow_0^1 v_2 / S k])[v_1[v_2 / k] / 0]$
    - Universe instantiation commutation: `vinstL_id`, `vinstL_comp`, `vinstL_vliftN`, `vinstL_vinst`, `vinstL_vinst0`.

### 3.2 Declarative Typing, Church-Rosser Confluence & Uniqueness of Types (`rocq/DeclarativeTyping.v` & `hol/declarative_typing961.ml`)

In [`rocq/DeclarativeTyping.v`](rocq/DeclarativeTyping.v) (854 lines) and [`hol/full_kernel_candidate839/hol/declarative_typing961.ml`](hol/full_kernel_candidate839/hol/declarative_typing961.ml), we formalized:
- **13-Rule Declarative `VIsDefEq` Judgment**:
  - Mutual inductive judgment `VIsDefEq env uvars Γ e1 e2 A` and `VHasType env uvars Γ e A := VIsDefEq env uvars Γ e e A`.
  - Proved left/right reflexivity (`VIsDefEq_refl_l`, `VIsDefEq_refl_r`), context slice lifting (`VCtxLiftN`), general weakening (`VIsDefEq_weakN`, `VHasType_weakN`, `VIsDefEq_weaken0`), and environment monotonicity (`VEnvOrdered_preserve_VIsDefEq`, `VEnvOrdered_preserve_VHasType`, `l4_venv_ordered_preserve_vis_defeq961`, `l4_venv_ordered_preserve_vhas_type961`).
- **Parallel Reduction, Takahashi Complete Development & Church-Rosser Confluence**:
  - Defined one-step parallel $\beta$-reduction `VParRed` (`l4_vpar_red961`) and its reflexive-transitive closure `VParRedStar` (`l4_vpar_red_star961`).
  - Proved substitution compatibility (`VParRed_vliftN`, `VParRed_vinst`, `VParRed_vinst0`: if $e_1 \Rightarrow e_2$ and $v_1 \Rightarrow v_2$, then $e_1[v_1/0] \Rightarrow e_2[v_2/0]$).
  - Defined Takahashi's complete development `vcomplete_dev : VExpr -> VExpr` and proved the **triangle property** (`VParRed_triangle`: if $a \Rightarrow b$, then $b \Rightarrow a^*$), the **diamond property** (`VParRed_diamond`), and the **Church-Rosser theorem** (`VParRedStar_ChurchRosser`: if $a \Rightarrow^* b$ and $a \Rightarrow^* c$, there exists $d$ such that $b \Rightarrow^* d$ and $c \Rightarrow^* d$).
- **Head Disjointness, Π-Injectivity & Uniqueness of Types**:
  - Proved multi-step head preservation and inversion for `VSort` and `VForallE` (`VParRedStar_sort_inv`, `VParRedStar_forallE_inv`, `l4_vpar_red_star_sort_inv961`, `l4_vpar_red_star_forall_inv961`).
  - Proved that `VSort u` and `VForallE A B` have no common multi-step reduct (`VParRedStar_sort_forallE_disjoint` / `l4_vpar_red_star_sort_forall_disjoint961`) and cannot be declaratively convertible (`VConv_sort_forallE_disjoint`).
  - Proved **Π-type injectivity** (`VParRedStar_forallE_injective` / `l4_vpar_red_star_forall_injective961`): if $\Pi(A_1, B_1)$ and $\Pi(A_2, B_2)$ reduce to a common reduct, then $A_1, A_2$ and $B_1, B_2$ each have common reducts.
  - Defined syntax-directed typing `VSynHasType` and proved its soundness (`VSynHasType_sound`) and **uniqueness of types up to declarative conversion** (`VSynHasType_unique`).

### 3.3 Kernel-to-Theory Soundness Bridge (`rocq/CheckerSoundness.v` & `hol/checker_soundness962.ml`)

In [`rocq/CheckerSoundness.v`](rocq/CheckerSoundness.v) (495 lines) and [`hol/full_kernel_candidate839/hol/checker_soundness962.ml`](hol/full_kernel_candidate839/hol/checker_soundness962.ml), we bridged the executable kernel to the declarative theory:
- **Derived Substitution Typing Rule (`VHasType_vinst0_from_beta` / `l4_vhas_type_vinst0_from_beta962`)**:
  - Proved directly from `VDefEq_beta`, `VDefEq_symm`, and `VDefEq_trans` that if $\Gamma, A \vdash b : B$ and $\Gamma \vdash a : A$, then $\Gamma \vdash b[a/0] : B[a/0]$ without needing an extra axiom or primitive rule.
- **Translation Relations (`TrLevel`, `TrExprS`, `TrExpr`, `TrTyping`)**:
  - Defined `TrLevel` (`l4_tr_level962`), `TrExprS` (`l4_tr_expr_s962`), `TrExpr` (`l4_tr_expr962`), and `TrTyping` (`l4_tr_typing962`), proving environment monotonicity (`TrExprS_monotonic_env`, `TrExpr_monotonic_env`, `TrTyping_monotonic_env`, `l4_tr_typing_monotonic_env962`) and structural soundness (`TrExprS_has_type`).
- **Environment & Admission Bridge (`KernelEnvBridge`)**:
  - Proved `get_constant_sound_bridge`, `infer_sort_sound_bridge`, `infer_const_sound_bridge`, `check_bridge_soundness` (`l4_check597_sound_bridge962`), and `checked_constant_extends_venv_wf` (`l4_checked_constant607_header_ok962`), establishing that every kernel-checked constant admission extends a well-formed semantic environment `VEnvWF` monotonically.

### 3.4 Atomic Quotient Transaction, `DefEqCache` Memoization & `FuelConfig`

1. **Atomic `addQuot` / `quotInit` Transaction (`rocq/QuotientTransaction.v`, `rocq/ArenaExtract.v`, `hol/quotient_transaction963.ml`)**:
   - Proved `initialize_quotient_initialized_noop` (`l4_quot_tx_initialized_noop963`), `initialize_quotient_eq_error_precedes_names` (`l4_quot_tx_eq_error_precedes_names963`), `initialize_quotient_collision_rejects` (`l4_quot_tx_collision_rejects963`), `initialize_quotient_no_partial_commit` (`l4_quot_tx_no_partial_commit963`), and `l4_quot_tx_idempotent963`.
2. **Positive & Negative `DefEqCache` (`rocq/DefEqCache.v`, `hol/equiv_manager964.ml`)**:
   - Proved `cached_defeq_refines_uncached` (`l4_cached_defeq_refines_uncached964`), `cached_defeq_preserves_positive_and_negative` (`l4_cached_defeq_preserves_verdict964`), and `positive_cache_hit_sound`.
3. **Multi-Axis `FuelConfig` (`rocq/FuelConfig.v`, `hol/fuel_config965.ml`)**:
   - Proved `infer_uniform_config_eq` (`l4_infer_uniform_config_eq965`), `whnf_uniform_config_eq` (`l4_whnf_uniform_config_eq965`), `defeq_uniform_config_eq` (`l4_defeq_uniform_config_eq965`), `check_uniform_config_eq` (`l4_check_uniform_config_eq965`), `admit_uniform_config_pos_eq`, `config_zero_min_declines` (`l4_config_zero_min_declines965`), and `check_with_config_sound`.

---

## 4. Verification & Test Suite Evidence

### 4.1 Rocq Proof & Native Test Verification

- **All 104 `.vo` modules compiled and verified**:
  - Command: `sh scripts/toolchain-exec.sh sh -c 'cd rocq && rocq check -Q . LeanPort -o $(grep "\.v$" _CoqProject | sed "s/\.v$/.vo/")'`
  - Output: `* Axioms: <none>` (0 axioms, 0 `Admitted`, 0 `Obj.magic`).
- **Native Extracted Binary (`build/rocq-check`) & 24 Regression Suites**:
  - Command: `sh scripts/build-rocq.sh`
  - Report: [`build/reports/rocq-native-20261023T141740Z-55605/report.json`](build/reports/rocq-native-20261023T141740Z-55605/report.json) (`exit_code: 0`, all 24 native test suites passing).

### 4.2 HOL Light Proof & Regression Verification

- **Base HOL Light Suites (`sh hol/test.sh` & `hol/quotient_tests.ml`)**:
  - `HOL_CORE_TESTS_PASSED 62`
  - `HOL_ADMISSION_TESTS_PASSED 21`
  - `HOL_ENVIRONMENT_TESTS_PASSED 18`
  - `HOL_INDUCTIVE_TESTS_PASSED 194`
  - `HOL_NAT_LITERAL_TESTS_PASSED 37`
  - `HOL_FAMILY_TESTS_PASSED 36`
  - `HOL_INDEXED_TESTS_PASSED 33`
  - `HOL_PROJECTION_CORE_TESTS_PASSED 17`
  - `HOL_PROJECTION_TESTS_PASSED 37`
  - `HOL_STRUCTURE_TESTS_PASSED 66`
  - `HOL_QUOTIENT_TESTS_PASSED 74`
- **Full-Kernel Candidate (`hol/full_kernel_candidate839/` & `hol/full_kernel_candidate652/`)**:
  - All 126 existing candidate modules + 5 new metatheory/bridge/transaction/cache/fuel modules (`declarative_typing961.ml`, `checker_soundness962.ml`, `quotient_transaction963.ml`, `equiv_manager964.ml`, `fuel_config965.ml`) verified in HOL Light:
    - `CORE612 COMPLETE source_files=10 axioms_unchanged=3`
    - `PROPOSED_FILE_FIXTURES649_PASSED 8 AXIOMS=3`
    - `CANDIDATE839_FULL_VERIFICATION_COMPLETE AXIOMS_COUNT=3`
    - `HOL_961_965_ALL_PROVED AXIOMS=3`
- **Static Source Audit (`sh scripts/audit-build.sh`)**:
  - Verified zero forbidden proof escapes (`Admitted`, `admit`, `Axiom`, `Parameter`, `Conjecture`, `Unsafe`, `Obj.magic`, `new_axiom`, `mk_thm`, `CHEAT_TAC`) across all active Rocq, HOL Light, and frontend source files.
