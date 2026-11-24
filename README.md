# Lean4Lean in Rocq and HOL Light

Independent, machine-verified end-to-end formalizations of the **Lean 4 kernel (`lean4lean`)** in **Rocq 9.2.0** (`Stdlib 9.1.0`) and **HOL Light 3.1.0**, spanning:
- **Executable 13-constructor Lean 4.33/4.36 kernels** (cached Rocq native binary `build/rocq-check` and theorem-producing HOL Light `v3` fork-isolated server `scripts/hol-server.sh --kernel v3`),
- **Complete `Theory/` declarative metatheory** (`VLevel`, `VExpr`, `VDecl`, `VEnv`, 13-rule `VIsDefEq`/`VHasType`, `LevelSat`, `SubstTheory`, `StrongTyping`, `EnvDeclTheory`, and `PatternConfluence` — typed Church–Rosser, unique typing, Kashima standardization),
- **Complete `Verify/` kernel-to-theory soundness** (`VerifyExpr`, `VerifyTypeChecker`, `VerifyEnvironment` / `verify_expr973`, `verify_typechecker974`, `verify_environment975`), discharging `CheckerMethodsSound` end-to-end with **zero axioms** (`* Axioms: <none>` in Rocq; `AXIOMS=3`, `check_axioms ()` OK in HOL Light), and
- **Lean Kernel Arena** live validation harnesses (`215 / 225` live Lean 4.36.0 Arena cases passing on `build/rocq-check`, `0` wrong verdicts, `0` declines; `11 / 12` live Arena smoke cases passing with closed HOL `v3` theorems `|- l4_file_verdict649 ... = 0 | 1`).

- **[End-to-End Port Report (`END_TO_END_PORT_REPORT.md`)](END_TO_END_PORT_REPORT.md)**: Full 7-milestone implementation and verification tracker.
- **[Honest Gap Analysis (`GAP_ANALYSIS.md`)](GAP_ANALYSIS.md)**: Subsystem-by-subsystem engineering audit comparing both ports against upstream `digama0/lean4lean`, with exact verified scope and transparent remaining boundaries.
- **[Final Verification Report (`FINAL_REPORT.md`)](FINAL_REPORT.md)**: Architecture matrix, theorem-by-theorem inventory, and measured verification metrics.
- **[HOL Light v3 Verification Status (`hol/kernel_v3_complete/VERIFICATION_STATUS.md`)](hol/kernel_v3_complete/VERIFICATION_STATUS.md)**: Three-session cold verification report for all 141 `hol/kernel_v3_complete/hol/*.ml` modules and 104 held entry cases.
- **[HOL Light Directory & Stage Guide (`hol/README.md`)](hol/README.md)**: Guide to the four HOL Light kernel layers (`hol/kernel_v3_complete/`, `hol/kernel_v2_full_file/`, `hol/kernel_v1_core_only/`, and baseline `hol/*.ml`).
- **[Toolchain Setup (`docs/TOOLCHAINS.md`)](docs/TOOLCHAINS.md)**: Pinned OCaml 4.14.2, Rocq 9.2.0, and HOL Light 3.1.0 setup on macOS arm64 and Linux x86_64.

---

## 1. Repository Overview & Directory Structure

| Path | Description |
| :--- | :--- |
| **[`rocq/`](rocq/)** | **Rocq 9.2.0 formalization (123 Vernacular `.v` modules in [`rocq/_CoqProject`](rocq/_CoqProject))**. Contains the executable Lean 4.33/4.36 kernel (`Syntax.v`, `Universes.v`, `Checker.v`, `LookupCore.v`, `CachedChecker.v`, `Declarations.v`, `Inductive.v`, `InductiveUtils.v`, `InductiveSafety.v`, `NestedTransform.v`, `NestedAdmission.v`, `Quotient.v`, `Primitives.v`), runtime data structures (`EnvironmentIndex.v`, `DagAdmission.v`, `PersistentIndex.v`, `PersistentAdmission.v`, `QuotientTransaction.v`, `QuotientPersistentIndex.v`, `DefEqCache.v`, `FuelConfig.v`), complete `Theory/` metatheory (`SemanticModel.v`, `DeclarativeTyping.v`, `TypingLemmas.v`, `LevelSat.v`, `SubstTheory.v`, `StrongTyping.v`, `EnvDeclTheory.v`, `PatternConfluence.v`), complete `Verify/` soundness proofs (`UniverseSoundness.v`, `SubstitutionProof.v`, `InferSoundness.v`, `CheckerSoundness.v`, `VerifyExpr.v`, `VerifyTypeChecker.v`, `VerifyEnvironment.v`), and OCaml extraction (`Extract.v`, `ArenaExtract.v`). |
| **[`hol/`](hol/)** | **HOL Light 3.1.0 formalization** (see [`hol/README.md`](hol/README.md)). Organized into [`hol/kernel_v3_complete/`](hol/kernel_v3_complete/) (**141 `hol/*.ml` modules**: canonical 13-constructor Lean 4.33/4.36 kernel, whole-file admission, `Compute` registry, quotient dependency authentication, `961`–`972` complete `Theory/` metatheory, and `973`–`975` complete `Verify/` executable soundness), [`hol/kernel_v2_full_file/`](hol/kernel_v2_full_file/), [`hol/kernel_v1_core_only/`](hol/kernel_v1_core_only/), and the 97-file baseline 9-constructor LCF checker in [`hol/*.ml`](hol/). |
| **[`frontend/`](frontend/)** | Unverified OCaml NDJSON wire parser (`wire.ml`), topological declaration replay scheduler (`replay.ml`), Rocq native CLI entrypoint (`rocq_main.ml`, `rocq_adapter.ml`, `dag_adapter.ml`, `persistent_adapter.ml`), theorem-backed HOL Light `v3` bridge (`hol_check_v3.ml`), and legacy `v0` CLI/socket bridge (`hol_input.ml`, `hol_check.ml`, `hol_server.ml`). |
| **[`arena/`](arena/)** | Pinned **Lean Kernel Arena** corpus manifest ([`arena/manifest.json`](arena/manifest.json)) and adversarial manifest ([`arena/adversarial/manifest.json`](arena/adversarial/manifest.json)). Note: `arena/corpus/` is gitignored and populated via tarball/acquisition scripts (§3.3). |
| **[`scripts/`](scripts/)** | Toolchain setup, build, extraction, verification, audit, and Arena runner scripts (`setup-toolchains.sh`, `build-rocq.sh`, `audit-build.sh`, `build-hol-frontend.sh`, `test_rocq_native.py`, `test_arena.py`, `hol-check.py`, `hol-server.sh`, `toolchain-exec.sh`). |
| **[`tests/`](tests/)** | Unit, regression, differential, and Arena runner test suites. |
| **[`docs/`](docs/)** | Design and verification documentation for Rocq ([`docs/ROCQ.md`](docs/ROCQ.md), [`docs/ROCQ_UNIVERSE_SOUNDNESS.md`](docs/ROCQ_UNIVERSE_SOUNDNESS.md), [`docs/ROCQ_DAG_RUNTIME.md`](docs/ROCQ_DAG_RUNTIME.md)) and HOL Light ([`docs/HOL_LIGHT.md`](docs/HOL_LIGHT.md), [`docs/HOL_DERIVED_LEMMAS.md`](docs/HOL_DERIVED_LEMMAS.md), [`docs/HOL_QUOTIENTS.md`](docs/HOL_QUOTIENTS.md), [`docs/HOL_SAFETY.md`](docs/HOL_SAFETY.md)). |

---

## 2. Faithfulness & Scope Against Upstream `lean4lean`

This repository targets [`digama0/lean4lean`](https://github.com/digama0/lean4lean) (`8223d223ed98661882e95d9d6a7126df7097cd76` & `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3`). See [`GAP_ANALYSIS.md`](GAP_ANALYSIS.md) for the exact scope of each subsystem.

### 2.1 Module-by-Module Mapping to Upstream `lean4lean`

| Upstream `lean4lean` Module | Rocq Module(s) (`rocq/`) | HOL Light Module(s) (`hol/kernel_v3_complete/hol/`) | Scope Note |
| :--- | :--- | :--- | :--- |
| **`Lean4Lean/Level.lean`** *(Universe operations & decision procedures)* | [`Universes.v`](rocq/Universes.v), [`UniverseSoundness.v`](rocq/UniverseSoundness.v) | [`kernel_universes488.ml`](hol/kernel_v3_complete/hol/kernel_universes488.ml), [`universe_decision555.ml`](hol/kernel_v3_complete/hol/universe_decision555.ml), [`universe_properties562.ml`](hol/kernel_v3_complete/hol/universe_properties562.ml) | Complete |
| **`Lean4Lean/Expr.lean`, `Instantiate.lean`, `LiftVar.lean`** *(13-constructor syntax & locally nameless / de Bruijn ops)* | [`Syntax.v`](rocq/Syntax.v), [`SubstitutionProof.v`](rocq/SubstitutionProof.v) | [`kernel_syntax447.ml`](hol/kernel_v3_complete/hol/kernel_syntax447.ml), [`kernel_locals489.ml`](hol/kernel_v3_complete/hol/kernel_locals489.ml), [`nested_keys480.ml`](hol/kernel_v3_complete/hol/nested_keys480.ml) | Complete |
| **`Lean4Lean/TypeChecker/{WHNF,InferType,DefEq,Reduce,TypeChecker}.lean`** | [`Checker.v`](rocq/Checker.v), [`LookupCore.v`](rocq/LookupCore.v), [`CachedChecker.v`](rocq/CachedChecker.v) | [`inference586.ml`](hol/kernel_v3_complete/hol/inference586.ml), [`whnf_control594.ml`](hol/kernel_v3_complete/hol/whnf_control594.ml), [`conversion_helpers595.ml`](hol/kernel_v3_complete/hol/conversion_helpers595.ml), [`conversion_fallback596.ml`](hol/kernel_v3_complete/hol/conversion_fallback596.ml), [`kernel_conversion597.ml`](hol/kernel_v3_complete/hol/kernel_conversion597.ml), [`kernel_checker597.ml`](hol/kernel_v3_complete/hol/kernel_checker597.ml) | Complete (`lazyDeltaProjReduction`, `etaExpand`, `reduceNative`, `Nat.pow`/shifts `<= 2^24` fallback, cached Rocq CLI) |
| **`Lean4Lean/TypeChecker/EquivManager.lean`** *(Context-sound `DefEq` caching)* | [`DefEqCache.v`](rocq/DefEqCache.v), [`CachedChecker.v`](rocq/CachedChecker.v) | [`equiv_manager964.ml`](hol/kernel_v3_complete/hol/equiv_manager964.ml) | Full-context keys & union-find soundness proved in `VerifyTypeChecker.v` / `verify_typechecker974.ml`; wired in `CachedChecker.v` |
| **`Lean4Lean/FuelConfig.lean`** *(6-axis fuel budgets)* | [`FuelConfig.v`](rocq/FuelConfig.v) | [`fuel_config965.ml`](hol/kernel_v3_complete/hol/fuel_config965.ml) | All 6 upstream axes formalized & composed in `VerifyTypeChecker`/`VerifyEnvironment`; CLI default `--fuel 50000` |
| **`Lean4Lean/Environment.lean`, `Declaration.lean`** *(Constant & declaration admission, safety/opaques)* | [`Declarations.v`](rocq/Declarations.v), [`EnvironmentIndex.v`](rocq/EnvironmentIndex.v), [`DagAdmission.v`](rocq/DagAdmission.v), [`PersistentIndex.v`](rocq/PersistentIndex.v), [`PersistentAdmission.v`](rocq/PersistentAdmission.v) | [`kernel_declarations493.ml`](hol/kernel_v3_complete/hol/kernel_declarations493.ml), [`ordinary_admission607.ml`](hol/kernel_v3_complete/hol/ordinary_admission607.ml), [`safety_admission624.ml`](hol/kernel_v3_complete/hol/safety_admission624.ml), [`checked_admission631.ml`](hol/kernel_v3_complete/hol/checked_admission631.ml), [`file_driver642.ml`](hol/kernel_v3_complete/hol/file_driver642.ml) | Complete |
| **`Lean4Lean/Inductive/{Add,Reduce,Nested}.lean`** *(Inductives, constructors, recursors, $\iota$-reduction, nested elimination)* | [`Inductive.v`](rocq/Inductive.v), [`InductiveUtils.v`](rocq/InductiveUtils.v), [`InductiveSafety.v`](rocq/InductiveSafety.v), [`NestedTransform.v`](rocq/NestedTransform.v), [`NestedAdmission.v`](rocq/NestedAdmission.v) | [`inductive_derivation516.ml`](hol/kernel_v3_complete/hol/inductive_derivation516.ml), [`recursor_construction522.ml`](hol/kernel_v3_complete/hol/recursor_construction522.ml), [`recursor_conversion585.ml`](hol/kernel_v3_complete/hol/recursor_conversion585.ml), [`checked_inductives629.ml`](hol/kernel_v3_complete/hol/checked_inductives629.ml), [`inductive_safety633.ml`](hol/kernel_v3_complete/hol/inductive_safety633.ml), [`nested_admission634.ml`](hol/kernel_v3_complete/hol/nested_admission634.ml) | Complete |
| **`Lean4Lean/Quot.lean`** *(Quotient types, $\iota$-reduction, atomic `addQuot`/`quotInit`)* | [`Quotient.v`](rocq/Quotient.v), [`QuotientTransaction.v`](rocq/QuotientTransaction.v), [`QuotientPersistentIndex.v`](rocq/QuotientPersistentIndex.v), [`QuotientFlagInvariant.v`](rocq/QuotientFlagInvariant.v) | [`projection_quotient550.ml`](hol/kernel_v3_complete/hol/projection_quotient550.ml), [`quotient_admission608.ml`](hol/kernel_v3_complete/hol/quotient_admission608.ml), [`quotient_dependencies839.ml`](hol/kernel_v3_complete/hol/quotient_dependencies839.ml), [`quotient_transaction963.ml`](hol/kernel_v3_complete/hol/quotient_transaction963.ml) | Complete |
| **`Lean4Lean/Primitive.lean`, `Strings.lean`** *(Nat/Bool/String primitives, Lean 4.33 & 4.36 `Decidable` reflection)* | [`Primitives.v`](rocq/Primitives.v), [`StringParityFixtures.v`](rocq/StringParityFixtures.v), [`StringParityRegression.v`](rocq/StringParityRegression.v), [`NatProbeDispatch.v`](rocq/NatProbeDispatch.v), [`NatProbeRegression.v`](rocq/NatProbeRegression.v) | [`kernel_strings539.ml`](hol/kernel_v3_complete/hol/kernel_strings539.ml), [`kernel_naturals544.ml`](hol/kernel_v3_complete/hol/kernel_naturals544.ml), [`natural_reduction549.ml`](hol/kernel_v3_complete/hol/natural_reduction549.ml), [`primitive_foundations619.ml`](hol/kernel_v3_complete/hol/primitive_foundations619.ml)–[`primitive_recursors622.ml`](hol/kernel_v3_complete/hol/primitive_recursors622.ml) | Complete (dual Lean 4.33/4.36 reflection + `67f63b0` domain-only `eraseMData`) |
| **`Lean4Lean/Theory/{VLevel,VExpr,VDecl,VEnv,LevelSat}.lean`, `Theory/Typing/{Basic,Lemmas,Strong,Env,Quot,Inductive,Pattern,Injectivity,UniqueTyping,ChurchRosser,HeadReduction}.lean`** | [`SemanticModel.v`](rocq/SemanticModel.v), [`DeclarativeTyping.v`](rocq/DeclarativeTyping.v), [`TypingLemmas.v`](rocq/TypingLemmas.v), [`LevelSat.v`](rocq/LevelSat.v), [`SubstTheory.v`](rocq/SubstTheory.v), [`StrongTyping.v`](rocq/StrongTyping.v), [`EnvDeclTheory.v`](rocq/EnvDeclTheory.v), [`PatternConfluence.v`](rocq/PatternConfluence.v) | [`declarative_typing961.ml`](hol/kernel_v3_complete/hol/declarative_typing961.ml), [`typing_lemmas966.ml`](hol/kernel_v3_complete/hol/typing_lemmas966.ml), [`level_sat968.ml`](hol/kernel_v3_complete/hol/level_sat968.ml), [`subst_theory969.ml`](hol/kernel_v3_complete/hol/subst_theory969.ml), [`strong_typing970.ml`](hol/kernel_v3_complete/hol/strong_typing970.ml), [`env_decl_theory971.ml`](hol/kernel_v3_complete/hol/env_decl_theory971.ml), [`pattern_confluence972.ml`](hol/kernel_v3_complete/hol/pattern_confluence972.ml) | Complete & axiom-free (general `VEnvWF` confluence parameterized by `DefEqInjectivity`; proved unconditionally for `venv_empty`) |
| **`Lean4Lean/Verify/{VLCtx,Expr,LocalContext,TypeChecker/*,Environment/*}.lean`** | [`VerifyExpr.v`](rocq/VerifyExpr.v), [`VerifyTypeChecker.v`](rocq/VerifyTypeChecker.v), [`VerifyEnvironment.v`](rocq/VerifyEnvironment.v) *(superseding [`InferSoundness.v`](rocq/InferSoundness.v) & [`CheckerSoundness.v`](rocq/CheckerSoundness.v))* | [`verify_expr973.ml`](hol/kernel_v3_complete/hol/verify_expr973.ml), [`verify_typechecker974.ml`](hol/kernel_v3_complete/hol/verify_typechecker974.ml), [`verify_environment975.ml`](hol/kernel_v3_complete/hol/verify_environment975.ml) *(discharging [`infer_soundness967.ml`](hol/kernel_v3_complete/hol/infer_soundness967.ml))* | Complete 13-constructor type-checker soundness (`FullMethodsSound`) + environment/quotient/inductive/file-driver soundness (scope notes in [`GAP_ANALYSIS.md`](GAP_ANALYSIS.md) §3.2) |

### 2.2 Auditing Zero Axioms, Zero `Admitted`, and Zero Unsafe Casts

Every proved theorem in this repository is machine-checked with **zero axioms or proof escapes**:

1. **Automated Full Build & Escape Audit (`scripts/audit-build.sh`)**:
   ```sh
   bash scripts/audit-build.sh
   ```
   This rechecks all **123** `.vo` objects with `rocq check -Q . LeanPort -o` (confirming `* Axioms: <none>` and zero `Unsafe` flags), verifies all **66** bundled stock HOL Light 3.1.0 files in `hol/kernel_v2_full_file/` and `hol/kernel_v3_complete/` byte-for-byte against `toolchain/opam-root/lean4lean/lib/hol_light/`, and scans every handwritten `.v`, `.ml`, and `.mli` file for proof escapes.
2. **HOL Light Axiom Audit (`axioms ()` & `check_axioms ()`)**:
   Stock HOL Light has exactly **3 foundational axioms** (`INFINITY_AX`, `SELECT_AX`, `ETA_AX`). `sh hol/kernel_v3_complete/verify_all_v3.sh`, `hol/test.sh`, and `hol/test-quotient.sh` verify `List.length (axioms ()) = 3` and `check_axioms ()` with zero calls to `new_axiom` or `mk_thm`.
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
       + [Path("hol/kernel_v3_complete/verify_all_v3.ml"), Path("hol/kernel_v3_complete/verify_entries_v3.ml"), Path("hol/kernel_v3_complete/verify_soundness_v3.ml")]
       + sorted(Path("frontend").glob("*.ml"))
   )
   for p in hol_project:
       assert not ocaml.search(p.read_text()), f"Escape in {p}"
   print("AUDIT PASSED: 0 axioms, 0 admits, 0 unsafe casts across all Rocq, HOL Light, and frontend sources.")
   '
   ```

### 2.3 Auditing Oracle-Free Execution on Lean Kernel Arena

- **No Expected-Answer Oracle**: When `scripts/test_arena.py` invokes a checker on an Arena `.ndjson` export, it passes **only** the input file path or stdin stream. The manifest containing expected `accept`/`reject`/`either` outcomes is read exclusively by the test harness after the checker process exits.
- **Pure Extracted Decision Logic in Rocq**: `build/rocq-check` links the OCaml wire/replay frontend (`frontend/wire.ml`, `frontend/replay.ml`) to code extracted from [`rocq/ArenaExtract.v`](rocq/ArenaExtract.v) (running [`rocq/CachedChecker.v`](rocq/CachedChecker.v) with default `--fuel 50000`).
- **Theorem-Producing Checking in HOL Light `v3`**: `scripts/hol-server.sh --kernel v3` (loading `frontend/hol_check_v3.ml`) forks a clean worker per case and proves a closed HOL Light `thm` (`|- l4_file_verdict649 ... = 0` for `accept`, `|- l4_file_verdict649 ... = 1` for semantic `reject`, `axioms=3`) before returning the verdict.

---

## 3. How to Build and Run the Tests

All commands use the project-local toolchain wrapper `scripts/toolchain-exec.sh` (run `sh scripts/setup-toolchains.sh` once on macOS arm64 or Linux x86_64; see [`docs/TOOLCHAINS.md`](docs/TOOLCHAINS.md)).

### 3.1 Build & Test the Rocq Port

1. **Compile all 123 Rocq modules, extract OCaml, link `build/rocq-check`, and run all 24 native test suites**:
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

1. **Verify all 141 modules + 104 held entry cases of `hol/kernel_v3_complete/`**:
   ```sh
   sh hol/kernel_v3_complete/verify_all_v3.sh
   ```
   Runs three fresh HOL Light sessions sequentially under `ulimit -v 4500000` and `OCAMLRUNPARAM="s=16M,i=32M,o=30"` (`verify_all_v3.ml` for the 130 core/metatheory/property/regression modules `447`–`972`, `verify_entries_v3.ml` for the 8 pristine-session `655` entry modules and 104 entry cases, and `verify_soundness_v3.ml` for the 3 end-to-end soundness modules `973`–`975`) and enforces 100% disk coverage (`141/141`), `AXIOMS=3`, and `check_axioms ()`. Individual sessions can also be invoked via `--only main|entries|soundness|check [LOGDIR]`.
2. **Build and test the HOL Light OCaml transport frontend & legacy `v0` regression suites**:
   ```sh
   sh scripts/build-hol-frontend.sh
   OCAMLRUNPARAM="s=16M,i=32M,o=30" sh hol/test.sh
   OCAMLRUNPARAM="s=16M,i=32M,o=30" sh hol/test-quotient.sh
   ```

### 3.3 Run the Lean Kernel Arena Benchmark Suite

1. **Run the Rocq checker (`build/rocq-check`, default `--fuel 50000`) on Arena exports**:
   ```sh
   ./build/rocq-check path/to/export.ndjson
   python3 -B scripts/test_arena.py --checker ./build/rocq-check --select 'bugs/*' --report /tmp/rocq-bugs.json
   python3 -B scripts/test_arena.py --checker ./build/rocq-check --select 'tutorial/*' --report /tmp/rocq-tutorial.json
   ```
2. **Run the warm fork-isolated HOL Light `v3` theorem-proving server on Arena exports**:
   ```sh
   sh scripts/build-hol-frontend.sh
   # Start the warm HOL Light v3 server in one terminal (prints JSON with "socket"):
   sh scripts/hol-server.sh --kernel v3
   # In another terminal, check Arena files against the socket path printed above:
   python3 -B scripts/hol-check.py --socket /tmp/hol-run-XXXX/s path/to/export.ndjson
   ```
   *(Pass `--kernel v0` to `hol-server.sh` for the legacy 9-constructor baseline server.)*

---

## 4. Summary of Verification & Live Arena Results

| Verification Dimension | Rocq Port (`rocq/`, `build/rocq-check`) | HOL Light Port (`hol/kernel_v3_complete/` & `hol/`) |
| :--- | :--- | :--- |
| **Formal Proof Modules** | **123 / 123 `.vo` modules** verified by `rocq check` + **24 / 24** native regression suites | **141 / 141 `v3` modules** (3 sequential sessions) + **104 / 104 `v3` entry cases** (`verify_all_v3.sh`) + **67** transport checks + **11 legacy `v0` suites** (1,524 assertions) |
| **Axioms / Proof Escapes** | **`0` axioms** (`* Axioms: <none>`), `0` `Admitted`, `0` unsafe casts | **`0` added axioms** (`List.length (axioms ()) = 3` stock HOL axioms, `check_axioms ()` OK), `0` `mk_thm` |
| **Declarative `Theory/` Metatheory** | Complete port (`14,589L`): `SemanticModel`, `DeclarativeTyping`, `TypingLemmas`, `LevelSat`, `SubstTheory`, `StrongTyping`, `EnvDeclTheory`, `PatternConfluence` | Complete port (`21,354L`): `declarative_typing961`, `typing_lemmas966`, `level_sat968`, `subst_theory969`, `strong_typing970`, `env_decl_theory971`, `pattern_confluence972` |
| **Executable `Verify/` Soundness** | End-to-end (`10,507L`): `VerifyExpr.v`, `VerifyTypeChecker.v` (discharging `CheckerMethodsSound`), `VerifyEnvironment.v` (`state_stream_from_initial_sound`) | End-to-end (`18,834L`, 390 theorems): `verify_expr973.ml`, `verify_typechecker974.ml` (discharging `l4_checker_methods_sound967`), `verify_environment975.ml` (`l4_check_file_pure_sound975`) |
| **Live Lean `4.36.0` Kernel Arena** | **215 / 225 PASS** (**183 / 183** non-perf incl. `init-prelude` in `1.52s`, **30 / 30** `bugs/*`, **141 / 141** `tutorial/*`, **10 / 10** `other/*`, **1 / 1** `corner-cases/*`, **32 / 42** `perf/*`; **`0` wrong verdicts, `0` declines**, `10` extreme `perf/*` timeouts at 35s) | Warm `hol-server.sh --kernel v3`: **11 / 12 PASS** on live Arena smoke suite (**6 / 6** `tutorial/*` accepts `|- verdict = 0`, **5 / 6** `bugs/*` semantic rejects `|- verdict = 1`, `axioms=3`, **`0` wrong verdicts**, `1` safe 30s timeout on `proj-non-structure`); **104 / 104** in-prover `v3` entry cases verified |
