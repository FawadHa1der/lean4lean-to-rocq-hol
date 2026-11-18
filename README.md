# Lean4Lean in Rocq and HOL Light

Independent, machine-verified formalizations of the **Lean 4 kernel (`lean4lean`)** in **Rocq 9.2.0** (`Stdlib 9.1.0`) and **HOL Light 3.1.0**, with executable type checkers, declarative metatheory (`VLevel`, `VExpr`, `VEnv`, 13-rule `VIsDefEq` / `VHasType`, and full `Theory/Typing/Lemmas.lean` structural metatheory), non-circular inference soundness (`InferSoundness.v` / `infer_soundness967.ml`), atomic quotient initialization (`addQuot` / `quotInit`), standalone models of `DefEqCache` and `FuelConfig`, and **Lean Kernel Arena** validation harnesses.

- **[Honest Gap Analysis (`GAP_ANALYSIS.md`)](GAP_ANALYSIS.md)**: Subsystem-by-subsystem engineering audit comparing both ports against upstream `digama0/lean4lean`, documenting what is unconditionally proved, what is relative/conditional or standalone, and what remains open.
- **[Final Verification Report (`FINAL_REPORT.md`)](FINAL_REPORT.md)**: Architecture matrix, theorem-by-theorem inventory, and verification metrics.
- **[HOL Light v3 Verification Status (`hol/kernel_v3_complete/VERIFICATION_STATUS.md`)](hol/kernel_v3_complete/VERIFICATION_STATUS.md)**: Two-session verification report for all 133 `hol/kernel_v3_complete/hol/*.ml` modules and 104 entry cases.
- **[HOL Light Directory & Stage Guide (`hol/README.md`)](hol/README.md)**: Guide to the four HOL Light kernel layers (`hol/kernel_v3_complete/`, `hol/kernel_v2_full_file/`, `hol/kernel_v1_core_only/`, and baseline `hol/*.ml`).
- **[Toolchain Setup (`docs/TOOLCHAINS.md`)](docs/TOOLCHAINS.md)**: Pinned OCaml 4.14.2, Rocq 9.2.0, and HOL Light 3.1.0 setup on macOS arm64 and Linux x86_64.

---

## 1. Repository Overview & Directory Structure

| Path | Description |
| :--- | :--- |
| **[`rocq/`](rocq/)** | **Rocq 9.2.0 formalization (114 Vernacular `.v` modules listed in [`rocq/_CoqProject`](rocq/_CoqProject))**. Contains the executable Lean 4 kernel (`Syntax.v`, `Universes.v`, `Checker.v`, `LookupCore.v`, `Declarations.v`, `Inductive.v`, `InductiveUtils.v`, `InductiveSafety.v`, `NestedTransform.v`, `NestedAdmission.v`, `Quotient.v`, `Primitives.v`), runtime data structures & models (`EnvironmentIndex.v`, `DagAdmission.v`, `PersistentIndex.v`, `PersistentAdmission.v`, `QuotientTransaction.v`, `QuotientPersistentIndex.v`, `DefEqCache.v`, `FuelConfig.v`), declarative metatheory (`SemanticModel.v`, `DeclarativeTyping.v`, `TypingLemmas.v`), soundness proofs (`UniverseSoundness.v`, `SubstitutionProof.v`, `InferSoundness.v`, `CheckerSoundness.v`), and OCaml extraction (`Extract.v`, `ArenaExtract.v`). |
| **[`hol/`](hol/)** | **HOL Light formalization** (see [`hol/README.md`](hol/README.md)). Organized into [`hol/kernel_v3_complete/`](hol/kernel_v3_complete/) (**133 `hol/*.ml` modules**: canonical 13-constructor kernel, whole-file admission, `Compute` registry, quotient dependency authentication, and `961`–`967` declarative metatheory, typing lemmas, and inference soundness), [`hol/kernel_v2_full_file/`](hol/kernel_v2_full_file/), [`hol/kernel_v1_core_only/`](hol/kernel_v1_core_only/), and the 97-file baseline 9-constructor LCF checker in [`hol/*.ml`](hol/). |
| **[`frontend/`](frontend/)** | Unverified OCaml NDJSON wire parser (`wire.ml`), topological declaration replay scheduler (`replay.ml`), Rocq native CLI entrypoint (`rocq_main.ml`, `rocq_adapter.ml`, `dag_adapter.ml`, `persistent_adapter.ml`), and baseline HOL Light v0 CLI/socket bridge (`hol_input.ml`, `hol_check.ml`, `hol_server.ml`). |
| **[`arena/`](arena/)** | Pinned **Lean Kernel Arena** corpus manifest ([`arena/manifest.json`](arena/manifest.json), 220 published cases) and adversarial manifest ([`arena/adversarial/manifest.json`](arena/adversarial/manifest.json)). Note: `arena/corpus/` is gitignored and populated via tarball/acquisition scripts (§3.3). |
| **[`scripts/`](scripts/)** | Toolchain setup, build, extraction, verification, audit, and Arena runner scripts (`setup-toolchains.sh`, `build-rocq.sh`, `audit-build.sh`, `test_rocq_native.py`, `test_arena.py`, `hol-check.py`, `hol-server.sh`, `toolchain-exec.sh`). |
| **[`tests/`](tests/)** | Unit, regression, differential, and Arena runner test suites. |
| **[`docs/`](docs/)** | Design and verification documentation for Rocq ([`docs/ROCQ.md`](docs/ROCQ.md), [`docs/ROCQ_UNIVERSE_SOUNDNESS.md`](docs/ROCQ_UNIVERSE_SOUNDNESS.md), [`docs/ROCQ_DAG_RUNTIME.md`](docs/ROCQ_DAG_RUNTIME.md)) and HOL Light ([`docs/HOL_LIGHT.md`](docs/HOL_LIGHT.md), [`docs/HOL_DERIVED_LEMMAS.md`](docs/HOL_DERIVED_LEMMAS.md), [`docs/HOL_QUOTIENTS.md`](docs/HOL_QUOTIENTS.md), [`docs/HOL_SAFETY.md`](docs/HOL_SAFETY.md)). |

---

## 2. How to Verify Faithfulness & Scope Against Upstream `lean4lean`

This repository targets [`digama0/lean4lean`](https://github.com/digama0/lean4lean) at pinned reference commit `8223d223ed98661882e95d9d6a7126df7097cd76`. See [`GAP_ANALYSIS.md`](GAP_ANALYSIS.md) for the exact scope and open obligations of each subsystem.

### 2.1 Module-by-Module Mapping to Upstream `lean4lean`

| Upstream `lean4lean` Module | Rocq Module(s) (`rocq/`) | HOL Light Module(s) (`hol/kernel_v3_complete/hol/`) | Scope Note |
| :--- | :--- | :--- | :--- |
| **`Lean4Lean/Level.lean`** *(Universe operations & decision procedures)* | [`Universes.v`](rocq/Universes.v), [`UniverseSoundness.v`](rocq/UniverseSoundness.v) | [`kernel_universes488.ml`](hol/kernel_v3_complete/hol/kernel_universes488.ml), [`universe_decision555.ml`](hol/kernel_v3_complete/hol/universe_decision555.ml), [`universe_properties562.ml`](hol/kernel_v3_complete/hol/universe_properties562.ml) | Complete |
| **`Lean4Lean/Expr.lean`, `Instantiate.lean`, `LiftVar.lean`** *(13-constructor syntax & locally nameless / de Bruijn ops)* | [`Syntax.v`](rocq/Syntax.v), [`SubstitutionProof.v`](rocq/SubstitutionProof.v) | [`kernel_syntax447.ml`](hol/kernel_v3_complete/hol/kernel_syntax447.ml), [`kernel_locals489.ml`](hol/kernel_v3_complete/hol/kernel_locals489.ml), [`nested_keys480.ml`](hol/kernel_v3_complete/hol/nested_keys480.ml) | Complete |
| **`Lean4Lean/TypeChecker/{WHNF,InferType,DefEq,Reduce,TypeChecker}.lean`** | [`Checker.v`](rocq/Checker.v), [`LookupCore.v`](rocq/LookupCore.v) | [`inference586.ml`](hol/kernel_v3_complete/hol/inference586.ml), [`whnf_control594.ml`](hol/kernel_v3_complete/hol/whnf_control594.ml), [`conversion_helpers595.ml`](hol/kernel_v3_complete/hol/conversion_helpers595.ml), [`conversion_fallback596.ml`](hol/kernel_v3_complete/hol/conversion_fallback596.ml), [`kernel_conversion597.ml`](hol/kernel_v3_complete/hol/kernel_conversion597.ml), [`kernel_checker597.ml`](hol/kernel_v3_complete/hol/kernel_checker597.ml) | Substantially complete; uncached single-fuel execution (see [`GAP_ANALYSIS.md`](GAP_ANALYSIS.md) §3.1) |
| **`Lean4Lean/TypeChecker/EquivManager.lean`** *(Positive/negative `DefEq` caching)* | [`DefEqCache.v`](rocq/DefEqCache.v) | [`equiv_manager964.ml`](hol/kernel_v3_complete/hol/equiv_manager964.ml) | Standalone verified model; not wired into runtime `Checker.v` / `kernel_checker597.ml` |
| **`Lean4Lean/FuelConfig.lean`** *(Multi-axis fuel budgets)* | [`FuelConfig.v`](rocq/FuelConfig.v) | [`fuel_config965.ml`](hol/kernel_v3_complete/hol/fuel_config965.ml) | Standalone verified model; production checkers use single coupled fuel |
| **`Lean4Lean/Environment.lean`, `Declaration.lean`** *(Constant & declaration admission, safety/opaques)* | [`Declarations.v`](rocq/Declarations.v), [`EnvironmentIndex.v`](rocq/EnvironmentIndex.v), [`DagAdmission.v`](rocq/DagAdmission.v), [`PersistentIndex.v`](rocq/PersistentIndex.v), [`PersistentAdmission.v`](rocq/PersistentAdmission.v) | [`kernel_declarations493.ml`](hol/kernel_v3_complete/hol/kernel_declarations493.ml), [`ordinary_admission607.ml`](hol/kernel_v3_complete/hol/ordinary_admission607.ml), [`safety_admission624.ml`](hol/kernel_v3_complete/hol/safety_admission624.ml), [`checked_admission631.ml`](hol/kernel_v3_complete/hol/checked_admission631.ml), [`file_driver642.ml`](hol/kernel_v3_complete/hol/file_driver642.ml) | Complete |
| **`Lean4Lean/Inductive/{Add,Reduce,Nested}.lean`** *(Inductives, constructors, recursors, $\iota$-reduction, nested elimination)* | [`Inductive.v`](rocq/Inductive.v), [`InductiveUtils.v`](rocq/InductiveUtils.v), [`InductiveSafety.v`](rocq/InductiveSafety.v), [`NestedTransform.v`](rocq/NestedTransform.v), [`NestedAdmission.v`](rocq/NestedAdmission.v) | [`inductive_derivation516.ml`](hol/kernel_v3_complete/hol/inductive_derivation516.ml), [`recursor_construction522.ml`](hol/kernel_v3_complete/hol/recursor_construction522.ml), [`recursor_conversion585.ml`](hol/kernel_v3_complete/hol/recursor_conversion585.ml), [`checked_inductives629.ml`](hol/kernel_v3_complete/hol/checked_inductives629.ml), [`inductive_safety633.ml`](hol/kernel_v3_complete/hol/inductive_safety633.ml), [`nested_admission634.ml`](hol/kernel_v3_complete/hol/nested_admission634.ml) | Complete |
| **`Lean4Lean/Quot.lean`** *(Quotient types, $\iota$-reduction, atomic `addQuot`/`quotInit`)* | [`Quotient.v`](rocq/Quotient.v), [`QuotientTransaction.v`](rocq/QuotientTransaction.v), [`QuotientPersistentIndex.v`](rocq/QuotientPersistentIndex.v), [`QuotientFlagInvariant.v`](rocq/QuotientFlagInvariant.v) | [`projection_quotient550.ml`](hol/kernel_v3_complete/hol/projection_quotient550.ml), [`quotient_admission608.ml`](hol/kernel_v3_complete/hol/quotient_admission608.ml), [`quotient_dependencies839.ml`](hol/kernel_v3_complete/hol/quotient_dependencies839.ml), [`quotient_transaction963.ml`](hol/kernel_v3_complete/hol/quotient_transaction963.ml) | Complete |
| **`Lean4Lean/Primitive.lean`, `Strings.lean`** *(Nat/Bool/String literal & primitive operations)* | [`Primitives.v`](rocq/Primitives.v), [`StringParityFixtures.v`](rocq/StringParityFixtures.v), [`StringParityRegression.v`](rocq/StringParityRegression.v), [`NatProbeDispatch.v`](rocq/NatProbeDispatch.v), [`NatProbeRegression.v`](rocq/NatProbeRegression.v) | [`kernel_strings539.ml`](hol/kernel_v3_complete/hol/kernel_strings539.ml), [`kernel_naturals544.ml`](hol/kernel_v3_complete/hol/kernel_naturals544.ml), [`natural_reduction549.ml`](hol/kernel_v3_complete/hol/natural_reduction549.ml), [`primitive_foundations619.ml`](hol/kernel_v3_complete/hol/primitive_foundations619.ml)–[`primitive_recursors622.ml`](hol/kernel_v3_complete/hol/primitive_recursors622.ml) | Complete (`pow`/`shiftLeft` exponent fuel guard in Rocq) |
| **`Lean4Lean/Theory/{VLevel,VExpr,VDecl,VEnv}.lean`, `Theory/Typing/Basic.lean`** *(Semantic model & 13-rule `VIsDefEq`/`VHasType`)* | [`SemanticModel.v`](rocq/SemanticModel.v), [`DeclarativeTyping.v`](rocq/DeclarativeTyping.v) | [`declarative_typing961.ml`](hol/kernel_v3_complete/hol/declarative_typing961.ml) | Complete |
| **`Lean4Lean/Theory/Typing/Lemmas.lean`** *(Core typing metatheory: `instL`, `closedN`, `levelWF`, `weakN`/`weak0`, `instN`/`inst0`, `defeqDFC`, `VEnvWF`, inversions, regularity `isType`, `instDF`)* | [`TypingLemmas.v`](rocq/TypingLemmas.v) | [`typing_lemmas966.ml`](hol/kernel_v3_complete/hol/typing_lemmas966.ml) | Complete & unconditional |
| **`Lean4Lean/Theory/Typing/{ChurchRosser,Injectivity,UniqueTyping}.lean`** | [`DeclarativeTyping.v`](rocq/DeclarativeTyping.v) *(untyped $\beta$-only `VParRed` confluence & syntactic `VSynHasType_unique`)* | [`declarative_typing961.ml`](hol/kernel_v3_complete/hol/declarative_typing961.ml) *(untyped $\beta$-only `l4_vpar_red_star961` head inversions & disjointness)* | Partial: typed 13-rule `VIsDefEq` confluence/injectivity not ported (6 `sorry`s upstream) |
| **`Lean4Lean/Verify/TypeChecker/InferType.lean` & `Verify/**`** *(Kernel-to-Theory soundness)* | [`InferSoundness.v`](rocq/InferSoundness.v), [`CheckerSoundness.v`](rocq/CheckerSoundness.v) | [`infer_soundness967.ml`](hol/kernel_v3_complete/hol/infer_soundness967.ml), [`checker_soundness962.ml`](hol/kernel_v3_complete/hol/checker_soundness962.ml) | Partial: non-circular `infer` soundness relative to `MethodsSound` + `syntactic_methods` witness; `CheckerMethodsSound` for full `whnf`/`defeq` open |

### 2.2 Auditing Zero Axioms, Zero `Admitted`, and Zero Unsafe Casts

Every proved theorem in this repository is machine-checked with **zero axioms or proof escapes** (open obligations such as `CheckerMethodsSound` are stated transparently as `Definition`s / hypotheses rather than `Axiom` or `Admitted`):

1. **Automated Full Build & Escape Audit (`scripts/audit-build.sh`)**:
   ```sh
   bash scripts/audit-build.sh
   ```
   This rechecks all **114** `.vo` objects with `rocq check -Q . LeanPort -o` (confirming `* Axioms: <none>` and zero `Unsafe` flags), verifies all **66** bundled stock HOL Light 3.1.0 files in `hol/kernel_v2_full_file/` and `hol/kernel_v3_complete/` byte-for-byte against `toolchain/opam-root/lean4lean/lib/hol_light/`, and scans every handwritten `.v`, `.ml`, and `.mli` file for proof escapes.
2. **HOL Light Axiom Audit (`axioms ()` & `check_axioms ()`)**:
   Stock HOL Light has exactly **3 foundational axioms** (`INFINITY_AX`, `SELECT_AX`, `ETA_AX`). Both `sh hol/kernel_v3_complete/verify_all_v3.sh` and `hol/test.sh` verify `List.length (axioms ()) = 3` and `check_axioms ()` at completion with zero calls to `new_axiom` or `mk_thm`.
3. **Standalone Static Source Scan**:
   ```sh
   python3 -c '
   import re
   from pathlib import Path
   vernac = re.compile(r"(^|[.][ \t\r\n])[ \t\r\n]*((Local|Global|Polymorphic|Monomorphic)[ \t\r\n]+)*(Admitted[ \t\r\n]*[.]|(Axioms?|Parameters?)[ \t\r\n]|Unset[ \t\r\n]+(Guard|Positivity|Universe|Elimination)[ \t\r\n]+Checking|Extract[ \t\r\n]+(Constant|Inductive|Inlined[ \t\r\n]+Constant))", re.M)
   tactics = re.compile(r"(^|[;{}]|[.][ \t\r\n]+)[ \t\r\n]*admit[ \t\r\n]*([.;}]|$)|\b(vm_cast_no_check|native_cast_no_check|exact_no_check)\b", re.M)
   ocaml = re.compile(r"\b(new_axiom|mk_thm)\b|\bObj[ \t\r\n]*[.][ \t\r\n]*(magic|obj|set_field|set_tag)\b", re.M)
   for p in sorted(Path("rocq").glob("*.v")):
       assert not vernac.search(p.read_text()) and not tactics.search(p.read_text()), f"Escape in {p}"
   hol_project = (
       sorted(Path("hol").glob("*.ml"))
       + sorted(Path("hol/kernel_v1_core_only").rglob("*.ml"))
       + sorted(Path("hol/kernel_v2_full_file/hol").glob("*.ml"))
       + sorted(Path("hol/kernel_v3_complete/hol").glob("*.ml"))
       + [Path("hol/kernel_v3_complete/verify_all_v3.ml"), Path("hol/kernel_v3_complete/verify_entries_v3.ml")]
       + sorted(Path("frontend").glob("*.ml"))
   )
   for p in hol_project:
       assert not ocaml.search(p.read_text()), f"Escape in {p}"
   print("AUDIT PASSED: 0 axioms, 0 admits, 0 unsafe casts across all Rocq, HOL Light, and frontend sources.")
   '
   ```

### 2.3 Auditing Oracle-Free Execution on Lean Kernel Arena

- **No Expected-Answer Oracle**: When `scripts/test_arena.py` invokes a checker on an Arena `.ndjson` export, it passes **only** the input file path or stdin stream. The manifest (`arena/manifest.json`) containing expected `accept`/`reject`/`either` outcomes is read exclusively by the test harness after the checker process exits.
- **Pure Extracted Decision Logic in Rocq**: `build/rocq-check` links the OCaml wire/replay frontend (`frontend/wire.ml`, `frontend/replay.ml`) to code extracted from [`rocq/ArenaExtract.v`](rocq/ArenaExtract.v).
- **Theorem-Producing Checking in HOL Light**: The external Arena socket checker (`frontend/hol_check.ml` over baseline `v0`) constructs a closed HOL Light `thm` (`|- l4_evalid policy env`) before returning `0` (`accept`), while in-prover `v3` entry fixtures (`file_certificate649.ml` / `entry_serialized649655.ml`) certify 3-way whole-file verdicts (`0` accept, `1` reject, `2` decline).

---

## 3. How to Build and Run the Tests

All commands use the project-local toolchain wrapper `scripts/toolchain-exec.sh` (run `sh scripts/setup-toolchains.sh` once on macOS arm64 or Linux x86_64; see [`docs/TOOLCHAINS.md`](docs/TOOLCHAINS.md)).

### 3.1 Build & Test the Rocq Port

1. **Compile all 114 Rocq modules, extract OCaml, link `build/rocq-check`, and run all 24 native test suites**:
   ```sh
   sh scripts/build-rocq.sh
   ```
2. **Run the native Rocq test suites standalone**:
   ```sh
   sh scripts/toolchain-exec.sh python3 -B scripts/test_rocq_native.py
   ```
3. **Run the Rocq kernel recheck & static escape audit**:
   ```sh
   bash scripts/audit-build.sh
   ```

### 3.2 Run the HOL Light Verification & Test Suites

1. **Verify all 133 modules + 104 held entry cases of `hol/kernel_v3_complete/`**:
   ```sh
   sh hol/kernel_v3_complete/verify_all_v3.sh
   ```
   Runs two fresh HOL Light sessions in parallel (`verify_all_v3.ml` for the 125 core/metatheory/property/regression modules including `961`–`967`, and `verify_entries_v3.ml` for the 8 pristine-session `655` entry modules and 104 entry cases) and checks 100% disk coverage, `AXIOMS=3`, and `check_axioms ()`.
2. **Run the baseline HOL Light v0 regression suites (`hol/test.sh` & `hol/test-quotient.sh`)**:
   ```sh
   sh scripts/toolchain-exec.sh sh hol/test.sh
   sh scripts/toolchain-exec.sh sh hol/test-quotient.sh
   ```
3. **Verify the self-contained 13-constructor v1 core proof bundle (`hol/kernel_v1_core_only/`)**:
   ```sh
   cd hol/kernel_v1_core_only && LINE_EDITOR=env sh ../../scripts/toolchain-exec.sh hol.sh < run_proofs612.ml
   ```

### 3.3 Run the Lean Kernel Arena Benchmark Suite

`arena/corpus/` is gitignored; the small published Arena tarball populates 196 of the 220 manifest cases (`bugs/*`, `tutorial/*`, `other/*`, `perf/*`, and 4 static `corner-cases/*`), while 15 generated `outcome=either` corner-cases and 5 large library exports have dedicated acquisition scripts (`scripts/fetch_arena_generate.py`, `scripts/acquire_*_arena.py`).

1. **Check local Arena corpus inventory**:
   ```sh
   python3 -B scripts/test_arena.py --inventory
   ```
2. **Run the Rocq checker on the Arena corpus**:
   ```sh
   python3 -B scripts/test_arena.py --checker ./build/rocq-check --select 'bugs/*' --report /tmp/rocq-bugs.json
   python3 -B scripts/test_arena.py --checker ./build/rocq-check --select 'tutorial/*' --report /tmp/rocq-tutorial.json
   python3 -B scripts/test_arena.py --checker ./build/rocq-check --report /tmp/rocq-full-arena.json
   ```
3. **Run the baseline HOL Light v0 warm-server checker on the Arena corpus**:
   ```sh
   sh scripts/build-hol-frontend.sh
   # Start the warm HOL Light v0 server in one terminal (prints JSON with --socket PATH):
   python3 -B scripts/hol-check.py serve
   # In another terminal, run Arena cases against the socket path printed above:
   python3 -B scripts/test_arena.py \
     --checker 'python3 -B scripts/hol-check.py client --socket /tmp/hol-run-XXXX/s' \
     --select 'tutorial/*' \
     --report /tmp/hol-tutorial.json
   ```
4. **Run the Arena runner schema, adversarial, and unit tests**:
   ```sh
   python3 -B scripts/test_arena_schema.py
   python3 -B scripts/test_arena_adversarial.py
   PYTHONPATH=tests/arena python3 -B -m unittest test_runner test_cleanup test_streaming
   ```

---

## 4. Summary of Verification & Arena Results

| Verification Dimension | Rocq Port (`rocq/`, `build/rocq-check`) | HOL Light Port (`hol/kernel_v3_complete/` & `hol/`) |
| :--- | :--- | :--- |
| **Formal Proof Modules** | **114 / 114 `.vo` modules** verified by `rocq check` + **24 / 24** native regression suites | **133 / 133 `v3` modules** + **104 / 104 `v3` entry cases** (`verify_all_v3.sh`) + **11 baseline `v0` suites** (`test.sh` & `test-quotient.sh`) |
| **Axioms / Proof Escapes** | **`0` axioms** (`* Axioms: <none>`), `0` `Admitted`, `0` unsafe casts | **`0` added axioms** (`List.length (axioms ()) = 3` stock HOL axioms, `check_axioms ()` OK), `0` `mk_thm` |
| **Declarative Metatheory & Bridge** | `VLevel`/`VExpr`/`VEnv`, 13-rule `VIsDefEq`/`VHasType`, complete `TypingLemmas.v` (`Theory/Typing/Lemmas.lean`), non-circular `InferSoundness.v` (relative to `MethodsSound` + `syntactic_methods` witness), conditional `CheckerSoundness.v`, untyped $\beta$-only `VParRedStar_ChurchRosser` | `l4_vlevel961`/`l4_vexpr961`/`l4_venv961`, 13-rule `l4_vis_defeq961`, complete `typing_lemmas966.ml`, non-circular `infer_soundness967.ml` (relative to `l4_methods_sound967` + `l4_syntactic_methods967` witness), conditional `checker_soundness962.ml`, untyped $\beta$-only `l4_vpar_red_star961` inversions |
| **Arena Functional Suites** (`tutorial/*`, `bugs/*`, `corner-cases/*`, `other/*`) | **172 / 172 (100%)** on small-tarball cases (`141/141` `tutorial`, `18/18` `bugs`, `9/9` `other`, `4/4` static `corner-cases`; **187 / 187** with generated `either` cases), **`0` wrong verdicts** | Baseline `v0` CLI (`hol_check.ml`): **95 / 187 passing** (`84/94` valid `tutorial` accepts proved as closed HOL theorems, `6` input-validation rejects, `5` `corner-cases`/`other`) + `92` safe declines, **`0` wrong verdicts** (semantic rejects & unsupported features decline in `v0`; see [`GAP_ANALYSIS.md`](GAP_ANALYSIS.md) §3.3) |
| **Full Arena Corpus** | **206 / 216 (95.4%)** across acquired corpus (`10` `timeout` on large/exponential stress cases without runtime `EquivManager`, **`0` wrong verdicts**) | Baseline `v0` CLI: **96 / 216 passing** + `120` declines (`0` wrong verdicts); In-prover `v3` (`verify_entries_v3.ml`): **104 / 104** 13-constructor entry cases verified |
