# HOL Light `kernel_v3_complete` — End-to-End Verification Status

**Status**: **141 / 141 `hol/*.ml` modules and 104 / 104 held entry cases verified** (`V3_ALL_MODULES_VERIFIED`, exit code `0`, `AXIOMS=3`, `check_axioms ()` OK).  
**Toolchain**: OCaml `4.14.2`, HOL Light `3.1.0` (verified on Linux x86_64).  
**Runner**: [`verify_all_v3.sh`](verify_all_v3.sh) ([`verify_all_v3.ml`](verify_all_v3.ml) + [`verify_entries_v3.ml`](verify_entries_v3.ml) + [`verify_soundness_v3.ml`](verify_soundness_v3.ml)).

---

## 1. Historical State vs Current Verified State

Historically, [`MANIFEST839.json`](MANIFEST839.json) recorded `"proofs_executed": 0` and `"target_compiled": false` for checkpoint `839`, and several modules in [`hol/`](hol/) carried `"UNCOMPILED / NOT EXECUTED"` header comments without a top-level runner loading the full directory.

In the completed end-to-end port we:
1. Built [`verify_all_v3.sh`](verify_all_v3.sh), [`verify_all_v3.ml`](verify_all_v3.ml), [`verify_entries_v3.ml`](verify_entries_v3.ml), and [`verify_soundness_v3.ml`](verify_soundness_v3.ml) to compile the genuine `frontend/{wire,replay}.ml` prerequisites, execute every single `hol/*.ml` file across three fresh sequential HOL Light 3.1.0 sessions (with bounded virtual memory `ulimit -v 4500000` and compact OCaml GC `OCAMLRUNPARAM="s=16M,i=32M,o=30"`), enforce exact `141 / 141` `hol/*.ml` disk coverage (`cmp -s` between `ls hol/*.ml` and `V3_MODULE_OK` records), and assert `List.length (axioms ()) = 3` and `check_axioms ()` in every session.
2. Ported the entire upstream `Lean4Lean/Theory/` metatheory to HOL Light (`typing_lemmas966.ml`, `level_sat968.ml`, `subst_theory969.ml`, `strong_typing970.ml`, `env_decl_theory971.ml`, `pattern_confluence972.ml` — 20,849 lines on top of `declarative_typing961.ml`), fixing constant-name freshness in `l4_venv_wf966`.
3. Upgraded the executable `v3` kernel (`inference586.ml`, `kernel_naturals544.ml`, `natural_reduction549.ml`, `whnf_control594.ml`, `conversion_helpers595.ml`, `conversion_fallback596.ml`, `kernel_conversion597.ml`, `primitive_foundations619.ml`, `primitive_reflection621.ml`, `primitive_recursors622.ml`, `full_input610.ml`, `kernel_equations647.ml`, `equiv_manager964.ml`, `fuel_config965.ml`) for Lean 4.33/4.36 parity and exposed theorem-backed `v3` whole-file checking via [`../../frontend/hol_check_v3.ml`](../../frontend/hol_check_v3.ml) and `scripts/hol-server.sh --kernel v3`.
4. Ported the complete `Lean4Lean/Verify/` end-to-end executable soundness stack to HOL Light (`verify_expr973.ml`, `verify_typechecker974.ml`, `verify_environment975.ml` — 18,834 lines, 390 proved theorems), discharging `l4_checker_methods_sound967` end-to-end and proving `l4_check_file_pure_sound975` with zero added axioms (`AXIOMS=3`).
5. Repaired three genuine compile/proof defects in previously unexecuted modules (§3).

---

## 2. Three-Session Sequential Verification Architecture

Because [`hol/candidate_entry655.ml`](hol/candidate_entry655.ml) enforces a pristine-session guard (refusing to load if any `l4_*`, `L4*`, `fixture_*`, or `FLAT` identifier already exists in the HOL state, requiring `load_path = [Sys.getcwd ()]` and `use_file_raise_failure = true`), and to keep peak RSS comfortably inside `ulimit -v 4500000` on 8 GiB / 0 swap environments, [`verify_all_v3.sh`](verify_all_v3.sh) runs three fresh HOL Light sessions strictly sequentially (with optional `--only main|entries|soundness|check` mode for bounded-timeout runners):

| Session | Driver | Modules Loaded | Cases Executed | Final Axiom Check |
| :--- | :--- | :--- | :--- | :--- |
| **Session 1 (Core, Metatheory `961`–`972`, Properties & Regressions)** | [`verify_all_v3.ml`](verify_all_v3.ml) | **130 / 130** (`447`–`972`) | In-module `prove` / regression theorems | `AXIOMS=3`, `V3_CHECK_AXIOMS_OK` |
| **Session 2 (Pristine-Session Held Entry Harnesses)** | [`verify_entries_v3.ml`](verify_entries_v3.ml) | **8 / 8** (`candidate_entry655.ml` + 7 `entry_*655.ml`) | **104 / 104** closed-theorem & native-check entry payloads | `AXIOMS=3`, `V3_CHECK_AXIOMS_OK` |
| **Session 3 (End-to-End Executable Soundness `973`–`975`)** | [`verify_soundness_v3.ml`](verify_soundness_v3.ml) | **3 / 3** (`verify_expr973.ml`, `verify_typechecker974.ml`, `verify_environment975.ml`) | 390 proved soundness theorems across all 13 constructors & admission drivers | `AXIOMS=3`, `V3_CHECK_AXIOMS_OK` |
| **Combined Disk Coverage** | [`verify_all_v3.sh`](verify_all_v3.sh) | **141 / 141** (`verified=141 expected=141`) | **104 / 104** entry cases + all in-module proofs | **0 added axioms**, **0 `mk_thm`** |

Sessions 1 and 2 load compiled `wire.cmo` and `replay.cmo` from [`frontend/wire.ml`](frontend/wire.ml) and [`frontend/replay.ml`](frontend/replay.ml) (with `zarith` and `yojson`) so that [`hol/full_input610.ml`](hol/full_input610.ml) and the whole-file NDJSON fixtures execute against the real parser and replay scheduler. Session 3 verifies the pure-HOL soundness stack (`verify_expr973`..`verify_environment975`) directly without OCaml frontend dependencies.

---

## 3. Defects Found and Fixed in Previously Unexecuted Modules

Running all `hol/*.ml` modules through HOL Light 3.1.0 exposed three concrete defects in previously unexecuted files (plus the `L4KProj447` non-inductive owner rejection fix in `inference586.ml` and constant-name freshness fix in `typing_lemmas966.ml`):

1. **[`hol/entry_flatten650655.ml`](hol/entry_flatten650655.ml) (Camlp5 type-parse error)**:
   - Line 41 wrote `:(num list)list list`, which Camlp5 parses with right-nested type constructor application rather than left-nested list-of-lists-of-lists. Fixed to `:((num list)list)list`.
2. **[`hol/primitive_inverses620.ml`](hol/primitive_inverses620.ml) (unsolved existential & monomorphic `SPEC`)**:
   - `l4_kr_bind_accept_inverse620`: `SIMP_TAC [l4_kr_bind491]` left `?x. a = x /\ f x = L4KAccept491 y`; fixed by chaining `THEN MESON_TAC []`.
   - `l4_classify_primitive_metadata_requires_certificate620`: applied monomorphic `SPEC` instead of `ISPEC` to the polymorphic option cases theorem; fixed by switching to `ISPEC`.
3. **[`hol/primitive_recursors_properties622.ml`](hol/primitive_recursors_properties622.ml) (exponential `LET_DEF` blowup)**:
   - `l4_primitive_wf_wrong_fix_name622` and `l4_primitive_wf_wrong_fix_arity622` triggered exponential term blowup from eager `LET_DEF` expansion; fixed by unfolding only the outer header `let` bindings via `let_CONV` + `MATCH_CONV` before `SIMP_TAC`.
4. **[`hol/inference586.ml`](hol/inference586.ml) (`L4KProj447` non-inductive owner rejection)**:
   - Returned `L4KDecline491 L4KUnsupportedExpression491` instead of `L4KReject491 L4KTypeMismatch491` when projecting a missing or non-inductive owner; fixed to match upstream `invalidProj`.
5. **[`hol/typing_lemmas966.ml`](hol/typing_lemmas966.ml) (`l4_venv_wf966` constant-name freshness)**:
   - Added `~(?ci0. l4_venv_lookup_const961 env n ci0)` to `l4_venv_wf_const966` and proved `l4_venv_wf_lookup_unique966`, closing duplicate constant-name collisions.

---

## 4. Complete Metatheory & End-to-End Soundness Modules (`966`–`975`)

| Module | Lines | Summary |
| :--- | :---: | :--- |
| [`hol/typing_lemmas966.ml`](hol/typing_lemmas966.ml) | 1,860 | Complete de Bruijn commutation algebra and full `Theory/Typing/Lemmas.lean` metatheory (`l4_vis_defeq_instL966`, `closedN`, `level_wf`, `weakN`, `instN`, `defeqDFC`, `l4_venv_wf_lookup_unique966`, `sort_inv'`, `forall_inv`, regularity `l4_vis_defeq_is_type966`, `instDF`). |
| [`hol/infer_soundness967.ml`](hol/infer_soundness967.ml) | 1,009 | Syntactic `l4_tr_e967` fragment relative inference soundness (`l4_infer_step_sound967`, `l4_infer_sound967`, `l4_checker_methods_sound967` — now discharged end-to-end by `verify_typechecker974.ml`). |
| [`hol/level_sat968.ml`](hol/level_sat968.ml) | 974 | Takahashi β-confluence (`l4_vpar_red_diamond968`, `l4_vpar_red_star_church_rosser968`, `l4_vsyn_has_type_unique968`) and full `Theory/LevelSat.lean` CoNP-hardness reduction from 3-CNF SAT to `l4_vlevel_equiv961` / `l4_vlevel_le961`. |
| [`hol/subst_theory969.ml`](hol/subst_theory969.ml) | 1,376 | Structured renamings (`l4_vlift969`, `l4_vskips969`), simultaneous substitutions (`l4_vsubst969`, `l4_vsubst_vsubst969`, `l4_vsubst_vinst969`), and simultaneous context substitution (`l4_vctx_subst_eq969`). |
| [`hol/strong_typing970.ml`](hol/strong_typing970.ml) | 3,559 | Full `Theory/Typing/Strong.lean`: `l4_vis_defeq_strong970`, `l4_vhas_type_strong970`, `l4_veq_up_to_levels970`, `l4_vhas_type_stratified970`, `l4_vis_defeq_to_strong970`, syntactic typing inversions (`app_inv`, `lam_inv`, `const_inv`, `bvar_inv`), and simultaneous definitional substitution (`l4_vis_defeq_substDF970`). |
| [`hol/env_decl_theory971.ml`](hol/env_decl_theory971.ml) | 1,766 | `VDecl`, semantic quotient consistency (`l4_add_quot_wf971`, `l4_quot_ind_iota971`), constructive inductive extension (`l4_vinduct_decl_wf971`, `l4_add_induct_wf971`), and declaration-history `l4_venv_decls_wf_to_venv_wf971`. |
| [`hol/pattern_confluence972.ml`](hol/pattern_confluence972.ml) | 11,314 | `Pattern.lean`, `UniqueTyping.lean` (`l4_vis_defeq_uniq972`, `l4_vis_defeq_u_trans972`), `ChurchRosser.lean` (`l4_vis_defeq_church_rosser972`, axiom-free), `HeadReduction.lean` (Kashima standardization & `l4_vinfer_type972`), and unconditional `l4_venv_empty961` non-vacuity. |
| [`hol/verify_expr973.ml`](hol/verify_expr973.ml) | 5,645 | 178 proved theorems: universe-decision soundness (`555`), hybrid `VLCtx` (`l4_vl_entry973`/`l4_vl_ctx_rec973`), genuine structure projection (`l4_vtr_proj973`, `l4_vproj_telescope973`), literal translations, `l4_has_primitives973`, 19-component `l4_venv_sound973`, and 12-constructor `l4_vtr_expr_s973`/`l4_vtr_expr973`/`l4_vtr_typing973`. |
| [`hol/verify_typechecker974.ml`](hol/verify_typechecker974.ml) | 10,716 | 149 proved theorems: full mutual induction on `fuel` proving `l4_full_methods_sound974` / `l4_checker_mode_sound974` / `l4_checker_sound974` / `l4_check_sound974` across all reductions, `whnf`, `infer` (all 13 constructors, both modes), and `defeq`, discharging `l4_checker_methods_sound967` end-to-end and composing with `equiv_manager964.ml` and `fuel_config965.ml`. |
| [`hol/verify_environment975.ml`](hol/verify_environment975.ml) | 2,473 | 63 proved theorems: `l4_env_extends975`, `l4_check_header/proposition/value_sound975`, `Primitives` (`l4_classify_primitive_sound975`), `l4_admit620_sound975`, `l4_venv_sound_pure_admit975`, safety/mutual/unsafe-inductive isolation (`l4_venv_sound_prepend_restricted975`, `l4_admit_mutual_sound975`), `Quotient` ↔ `env_decl_theory971` bridge (`l4_admit_quotient_sound975`, `l4_initialize_quotient_sound975`), `l4_declarative_inductive_admit_sound975`, and end-to-end `l4_check_declarations620_from_empty_sound975` & `l4_check_file_pure_sound975`. |

For transparent scope notes (including the `l4_defeq_injectivity972` hypothesis on general `l4_venv_wf966` and the scope of pure-constant vs full inductive/quotient stream `l4_venv_sound973` composition), see [`../../GAP_ANALYSIS.md`](../../GAP_ANALYSIS.md).

---

## 5. Reproducing Verification & Recorded Summary Output

Run from the repository root (or per-session with `--only main|entries|soundness|check [LOGDIR]`):

```sh
sh hol/kernel_v3_complete/verify_all_v3.sh
```

Recorded clean cold verification output (`Linux x86_64`, OCaml `4.14.2`, HOL Light `3.1.0`):

```text
=== Session 1: verify_all_v3.ml ===
V3_SUMMARY loaded=130 failed=0 total=130
AXIOMS=3
AXIOM |- exists f. ONE_ONE f /\ ~ONTO f
AXIOM |- forall P x. P x ==> P ((@) P)
AXIOM |- forall t. (\x. t x) = t
V3_CHECK_AXIOMS_OK
V3_LOAD_DONE
=== Session 2: verify_entries_v3.ml ===
V3E_SUMMARY loaded=8 failed=0 total=8
V3E_CASES ok=104 failed=0
AXIOMS=3
AXIOM |- exists f. ONE_ONE f /\ ~ONTO f
AXIOM |- forall P x. P x ==> P ((@) P)
AXIOM |- forall t. (\x. t x) = t
V3_CHECK_AXIOMS_OK
V3_LOAD_DONE
=== Session 3: verify_soundness_v3.ml ===
V3S_SUMMARY loaded=3 failed=0 total=3
AXIOMS=3
AXIOM |- exists f. ONE_ONE f /\ ~ONTO f
AXIOM |- forall P x. P x ==> P ((@) P)
AXIOM |- forall t. (\x. t x) = t
V3_CHECK_AXIOMS_OK
V3_LOAD_DONE
disk_coverage: verified=141 expected=141
V3_ALL_MODULES_VERIFIED
```
