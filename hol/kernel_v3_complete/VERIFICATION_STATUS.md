# HOL Light `kernel_v3_complete` — End-to-End Verification Status

**Status**: **133 / 133 `hol/*.ml` modules and 104 / 104 held entry cases verified** (`V3_ALL_MODULES_VERIFIED`, exit code `0`, `AXIOMS=3`, `check_axioms ()` OK).  
**Toolchain**: OCaml `4.14.2`, HOL Light `3.1.0` (verified on Linux x86_64).  
**Runner**: [`verify_all_v3.sh`](verify_all_v3.sh) ([`verify_all_v3.ml`](verify_all_v3.ml) + [`verify_entries_v3.ml`](verify_entries_v3.ml)).

---

## 1. Historical State vs Current Verified State

Historically, [`MANIFEST839.json`](MANIFEST839.json) recorded `"proofs_executed": 0` and `"target_compiled": false` for checkpoint `839`, and several modules in [`hol/`](hol/) carried `"UNCOMPILED / NOT EXECUTED"` header comments without a top-level runner loading the full directory.

In this revision we:
1. Added [`verify_all_v3.sh`](verify_all_v3.sh), [`verify_all_v3.ml`](verify_all_v3.ml), and [`verify_entries_v3.ml`](verify_entries_v3.ml) to compile the genuine `frontend/{wire,replay}.ml` prerequisites, execute every single `hol/*.ml` file in fresh HOL Light 3.1.0 sessions, enforce 100% `hol/*.ml` disk coverage (`cmp -s` between `ls hol/*.ml` and `V3_MODULE_OK` records), and assert `List.length (axioms ()) = 3` and `check_axioms ()`.
2. Ported upstream `Lean4Lean/Theory/VExpr.lean` + `Theory/Typing/Lemmas.lean` to [`hol/typing_lemmas966.ml`](hol/typing_lemmas966.ml) (1,829 lines) and non-circular `Verify/TypeChecker/InferType.lean` to [`hol/infer_soundness967.ml`](hol/infer_soundness967.ml) (1,009 lines).
3. Uncovered and repaired three genuine compile/proof defects in previously unexecuted modules (§3).

---

## 2. Two-Session Verification Architecture

Because [`hol/candidate_entry655.ml`](hol/candidate_entry655.ml) enforces a pristine-session guard (refusing to load if any `l4_*`, `L4*`, `fixture_*`, or `FLAT` identifier already exists in the HOL state, requiring `load_path = [Sys.getcwd ()]` and `use_file_raise_failure = true`), a single HOL Light process cannot load both the main development and the eight `655` held-entry harnesses. [`verify_all_v3.sh`](verify_all_v3.sh) therefore runs two fresh HOL Light sessions in parallel:

| Session | Driver | Modules Loaded | Cases Executed | Final Axiom Check |
| :--- | :--- | :--- | :--- | :--- |
| **Session 1 (Core, Metatheory, Properties & Regressions)** | [`verify_all_v3.ml`](verify_all_v3.ml) | **125 / 125** (`447`–`967`) | In-module `prove` / regression theorems | `AXIOMS=3`, `V3_CHECK_AXIOMS_OK` |
| **Session 2 (Pristine-Session Held Entry Harnesses)** | [`verify_entries_v3.ml`](verify_entries_v3.ml) | **8 / 8** (`candidate_entry655.ml` + 7 `entry_*655.ml`) | **104 / 104** closed-theorem & native-check entry payloads | `AXIOMS=3`, `V3_CHECK_AXIOMS_OK` |
| **Combined Disk Coverage** | [`verify_all_v3.sh`](verify_all_v3.sh) | **133 / 133** (`verified=133 expected=133`) | **104 / 104** | **0 added axioms**, **0 `mk_thm`** |

Both sessions load compiled `wire.cmo` and `replay.cmo` from [`frontend/wire.ml`](frontend/wire.ml) and [`frontend/replay.ml`](frontend/replay.ml) (with `zarith` and `yojson`) so that [`hol/full_input610.ml`](hol/full_input610.ml) and the whole-file NDJSON fixtures execute against the real parser and replay scheduler.

---

## 3. Defects Found and Fixed in Previously Unexecuted Modules

Running all `hol/*.ml` modules through HOL Light 3.1.0 exposed three concrete defects in previously unexecuted files:

1. **[`hol/entry_flatten650655.ml`](hol/entry_flatten650655.ml) (Camlp5 type-parse error)**:
   - Line 41 wrote `:(num list)list list`, which Camlp5 parses with right-nested type constructor application rather than left-nested list-of-lists-of-lists. Fixed to `:((num list)list)list`.
2. **[`hol/primitive_inverses620.ml`](hol/primitive_inverses620.ml) (unsolved existential & monomorphic `SPEC`)**:
   - `l4_kr_bind_accept_inverse620`: `SIMP_TAC [l4_kr_bind491]` simplified the `L4KAccept491 a` branch to `?x. a = x /\ f x = L4KAccept491 y` without discharging the existential witness; fixed by chaining `THEN MESON_TAC []`.
   - `l4_classify_primitive_metadata_requires_certificate620`: applied monomorphic `SPEC` instead of `ISPEC` to the polymorphic cases theorem `prove_cases_thm option_INDUCT`, raising `Failure "SPEC"`; fixed by switching to `ISPEC`.
3. **[`hol/primitive_recursors_properties622.ml`](hol/primitive_recursors_properties622.ml) (exponential `LET_DEF` blowup)**:
   - `l4_primitive_wf_wrong_fix_name622` and `l4_primitive_wf_wrong_fix_arity622` included `LET_DEF; LET_END_DEF` inside `SIMP_TAC` after unfolding `l4_primitive_unfold_nat_well_founded622`. Because the unreached success branch of `l4_primitive_unfold_nat_well_founded622` contains nine nested `let` bindings over large terms, eager `LET_DEF` beta-expansion duplicated those subterms exponentially and hung. Fixed by unfolding only the five outer header `let` bindings via `ONCE_REWRITE_CONV [l4_primitive_unfold_nat_well_founded622] THENC REPEATC (CHANGED_CONV (TOP_DEPTH_CONV let_CONV THENC DEPTH_CONV MATCH_CONV))` before `SIMP_TAC` (`cpu=10.4s` for the entire file).

---

## 4. New Metatheory & Soundness Modules (`966`–`967`)

| Module | Lines | CPU Time | Summary |
| :--- | :---: | :---: | :--- |
| [`hol/typing_lemmas966.ml`](hol/typing_lemmas966.ml) | 1,829 | `7.5s` | Complete de Bruijn commutation algebra (`l4_vliftN_vliftN966`, `l4_vliftN_comm966`, `l4_vliftN_vinst_hi966`, `l4_vliftN_vinst_lo966`, `l4_vinst_vinst_hi966`, `l4_vinst0_vinst_hi966`, `l4_vinstL_vinstL966`) and full `Theory/Typing/Lemmas.lean` metatheory (`l4_vis_defeq_instL966`, `l4_vis_defeq_closedN966`, `l4_vis_defeq_level_wf966`, `l4_vis_defeq_weakN966`, `l4_vis_defeq_instN966`, `l4_vis_defeq_defeqDFC966`, `l4_venv_wf_closed966`, `l4_vis_defeq_sort_inv'966`, `l4_vis_type_forall_inv966`, `l4_vis_defeq_is_type966`, `l4_vis_defeq_instDF966`). |
| [`hol/infer_soundness967.ml`](hol/infer_soundness967.ml) | 1,009 | `4.9s` | Non-circular syntactic translation (`l4_tr_l967`, `l4_tr_e967`), substitution/lifting/level commutation (`l4_tr_e_lift967`, `l4_tr_e_subst967`, `l4_tr_e_inst967`, `l4_tr_e_subst_levels967`), `l4_methods_sound967`, relative soundness (`l4_infer_step_sound967`, `l4_check_step_sound967`, `l4_infer_sound967`), explicit open obligation `l4_checker_methods_sound967`, and unconditional executable non-vacuity (`l4_syntactic_methods_sound967`, `l4_syntactic_infer_sound967`). |

For scope caveats on `declarative_typing961.ml`, `checker_soundness962.ml`, `equiv_manager964.ml`, `fuel_config965.ml`, and open `l4_checker_methods_sound967`, see [`../../GAP_ANALYSIS.md`](../../GAP_ANALYSIS.md).

---

## 5. Reproducing Verification & Recorded Summary Output

Run from the repository root:

```sh
sh hol/kernel_v3_complete/verify_all_v3.sh
```

Recorded clean output (`Linux x86_64`, `wall_clock_seconds=220`):

```text
wall_clock_seconds=220
=== Session 1: verify_all_v3.ml (/tmp/v3-verify-logs-clean/verify_all_v3.log) ===
V3_SUMMARY loaded=125 failed=0 total=125
AXIOMS=3
AXIOM |- exists f. ONE_ONE f /\ ~ONTO f
AXIOM |- forall P x. P x ==> P ((@) P)
AXIOM |- forall t. (\x. t x) = t
V3_CHECK_AXIOMS_OK
V3_LOAD_DONE
=== Session 2: verify_entries_v3.ml (/tmp/v3-verify-logs-clean/verify_entries_v3.log) ===
V3E_SUMMARY loaded=8 failed=0 total=8
V3E_CASES ok=104 failed=0
AXIOMS=3
AXIOM |- exists f. ONE_ONE f /\ ~ONTO f
AXIOM |- forall P x. P x ==> P ((@) P)
AXIOM |- forall t. (\x. t x) = t
V3_CHECK_AXIOMS_OK
V3_LOAD_DONE
disk_coverage: verified=133 expected=133
V3_ALL_MODULES_VERIFIED
```
