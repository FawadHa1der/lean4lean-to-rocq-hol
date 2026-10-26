# Lean4Lean in Rocq and HOL Light

Independent, machine-verified ports of the **Lean 4 kernel (`lean4lean`)** to **Rocq 9.0.0** and **HOL Light**, complete with executable type checkers, declarative metatheory (`VLevel`, `VExpr`, `VEnv`, 13-rule `VIsDefEq` / `VHasType`), Church-Rosser confluence, $\Pi$-injectivity, kernel-to-theory soundness bridges (`TrLevel`, `TrExprS`, `TrExpr`, `TrTyping`), atomic quotient initialization (`addQuot` / `quotInit`), definitional-equality memoization (`DefEqCache`), multi-axis fuel budgets (`FuelConfig`), and full **Lean Kernel Arena** validation harnesses.

- **[Final Verification Report (`FINAL_REPORT.md`)](FINAL_REPORT.md)**: Detailed architecture, theorem-by-theorem inventory, and Arena benchmark results.
- **[HOL Light Directory & Stage Guide (`hol/README.md`)](hol/README.md)**: Guide to the four HOL Light kernel layers (`hol/kernel_v3_complete/`, `hol/kernel_v2_full_file/`, `hol/kernel_v1_core_only/`, and baseline `hol/*.ml`).
- **[Toolchain Setup (`docs/TOOLCHAINS.md`)](docs/TOOLCHAINS.md)**: Pinned OCaml, Rocq, and HOL Light environment configuration.

---

## 1. Repository Overview & Directory Structure

| Path | Description |
| :--- | :--- |
| **[`rocq/`](rocq/)** | **Rocq 9.0.0 formalization (104 Vernacular `.v` modules listed in [`rocq/_CoqProject`](rocq/_CoqProject))**. Contains the executable Lean 4 kernel (`Syntax.v`, `Universes.v`, `Checker.v`, `Declarations.v`, `Inductive.v`, `NestedInductive.v`, `Quotient.v`, `Primitive.v`, `Partition.v`), runtime data structures (`EnvironmentIndex.v`, `DAGAdmission.v`, `DefEqCache.v`, `FuelConfig.v`, `QuotientTransaction.v`, `QuotientPersistentIndex.v`), declarative metatheory (`SemanticModel.v`, `DeclarativeTyping.v`), soundness proofs (`UniverseSoundness.v`, `Soundness.v`, `KernelSoundness.v`, `CheckerSoundness.v`), and OCaml extraction (`Extract.v`, `ArenaExtract.v`). |
| **[`hol/`](hol/)** | **HOL Light formalization** (see [`hol/README.md`](hol/README.md)). Organized into [`hol/kernel_v3_complete/`](hol/kernel_v3_complete/) (canonical 13-constructor kernel, whole-file admission, `Compute` registry, quotient dependency authentication, and `961`–`965` declarative metatheory & soundness bridge), [`hol/kernel_v2_full_file/`](hol/kernel_v2_full_file/), [`hol/kernel_v1_core_only/`](hol/kernel_v1_core_only/), and the baseline 9-constructor LCF checker in [`hol/*.ml`](hol/). |
| **[`frontend/`](frontend/)** | Shared OCaml NDJSON wire parser (`wire.ml`), topological declaration replay scheduler (`replay.ml`), Rocq native CLI entrypoint (`rocq_main.ml`, `rocq_adapter.ml`, `dag_adapter.ml`, `persistent_adapter.ml`), and HOL Light CLI/socket bridge (`hol_input.ml`, `hol_check.ml`, `hol_server.ml`). |
| **[`arena/`](arena/)** | Pinned **Lean Kernel Arena** corpus manifest ([`arena/manifest.json`](arena/manifest.json), 220 published cases) and adversarial manifest ([`arena/adversarial/manifest.json`](arena/adversarial/manifest.json)). |
| **[`scripts/`](scripts/)** | Build, extraction, verification, audit, and Arena runner scripts (`build-rocq.sh`, `audit-build.sh`, `test_rocq_native.py`, `test_arena.py`, `hol-check.py`, `hol-server.sh`, `toolchain-exec.sh`). |
| **[`tests/`](tests/)** | Unit, regression, differential, and Arena runner test suites. |
| **[`docs/`](docs/)** | Design and verification documentation for Rocq ([`docs/ROCQ.md`](docs/ROCQ.md), [`docs/ROCQ_UNIVERSE_SOUNDNESS.md`](docs/ROCQ_UNIVERSE_SOUNDNESS.md), [`docs/ROCQ_DAG_RUNTIME.md`](docs/ROCQ_DAG_RUNTIME.md)) and HOL Light ([`docs/HOL_LIGHT.md`](docs/HOL_LIGHT.md), [`docs/HOL_DERIVED_LEMMAS.md`](docs/HOL_DERIVED_LEMMAS.md), [`docs/HOL_QUOTIENTS.md`](docs/HOL_QUOTIENTS.md), [`docs/HOL_SAFETY.md`](docs/HOL_SAFETY.md)). |

---

## 2. How to Verify Faithfulness to Upstream `lean4lean`

This repository is a standalone formalization of [`digama0/lean4lean`](https://github.com/digama0/lean4lean) (pinned reference commit `8223d223ed98661882e95d9d6a7126df7097cd76`). A reader or auditor can independently verify that both ports are faithful, self-contained, and axiom-free through four concrete checks:

### 2.1 Module-by-Module Mapping to Upstream `lean4lean`

Every subsystem of upstream `lean4lean` has an explicit counterpart in both `rocq/` and `hol/kernel_v3_complete/hol/`:

| Upstream `lean4lean` Module | Rocq Module(s) (`rocq/`) | HOL Light Module(s) (`hol/kernel_v3_complete/hol/`) |
| :--- | :--- | :--- |
| **`Lean4Lean/Level.lean`** *(Universe operations & decision procedures)* | [`Universes.v`](rocq/Universes.v), [`UniverseSoundness.v`](rocq/UniverseSoundness.v) | [`kernel_universes488.ml`](hol/kernel_v3_complete/hol/kernel_universes488.ml), [`universe_decision555.ml`](hol/kernel_v3_complete/hol/universe_decision555.ml), [`universe_properties562.ml`](hol/kernel_v3_complete/hol/universe_properties562.ml) |
| **`Lean4Lean/Expr.lean`, `Instantiate.lean`, `LiftVar.lean`** *(13-constructor syntax & locally nameless / de Bruijn ops)* | [`Syntax.v`](rocq/Syntax.v), [`SubstitutionProof.v`](rocq/SubstitutionProof.v) | [`kernel_syntax447.ml`](hol/kernel_v3_complete/hol/kernel_syntax447.ml), [`kernel_locals489.ml`](hol/kernel_v3_complete/hol/kernel_locals489.ml), [`nested_keys480.ml`](hol/kernel_v3_complete/hol/nested_keys480.ml) |
| **`Lean4Lean/TypeChecker/{WHNF,InferType,DefEq,Reduce,TypeChecker}.lean`** | [`Checker.v`](rocq/Checker.v), [`Soundness.v`](rocq/Soundness.v), [`KernelSoundness.v`](rocq/KernelSoundness.v) | [`inference586.ml`](hol/kernel_v3_complete/hol/inference586.ml), [`whnf_control594.ml`](hol/kernel_v3_complete/hol/whnf_control594.ml), [`conversion_helpers595.ml`](hol/kernel_v3_complete/hol/conversion_helpers595.ml), [`conversion_fallback596.ml`](hol/kernel_v3_complete/hol/conversion_fallback596.ml), [`kernel_conversion597.ml`](hol/kernel_v3_complete/hol/kernel_conversion597.ml), [`kernel_checker597.ml`](hol/kernel_v3_complete/hol/kernel_checker597.ml) |
| **`Lean4Lean/TypeChecker/EquivManager.lean`** *(Positive/negative `DefEq` caching)* | [`DefEqCache.v`](rocq/DefEqCache.v), [`FailureCache162.v`](rocq/FailureCache162.v) | [`equiv_manager964.ml`](hol/kernel_v3_complete/hol/equiv_manager964.ml) |
| **`Lean4Lean/FuelConfig.lean`** *(Multi-axis fuel budgets)* | [`FuelConfig.v`](rocq/FuelConfig.v) | [`fuel_config965.ml`](hol/kernel_v3_complete/hol/fuel_config965.ml) |
| **`Lean4Lean/Environment.lean`, `Declaration.lean`** *(Constant & declaration admission, safety/opaques)* | [`Declarations.v`](rocq/Declarations.v), [`EnvironmentIndex.v`](rocq/EnvironmentIndex.v), [`DAGAdmission.v`](rocq/DAGAdmission.v), [`PersistentEnvironment.v`](rocq/PersistentEnvironment.v) | [`kernel_declarations493.ml`](hol/kernel_v3_complete/hol/kernel_declarations493.ml), [`ordinary_admission607.ml`](hol/kernel_v3_complete/hol/ordinary_admission607.ml), [`safety_admission624.ml`](hol/kernel_v3_complete/hol/safety_admission624.ml), [`checked_admission631.ml`](hol/kernel_v3_complete/hol/checked_admission631.ml), [`file_driver642.ml`](hol/kernel_v3_complete/hol/file_driver642.ml) |
| **`Lean4Lean/Inductive/{Add,Reduce,Nested}.lean`** *(Inductives, constructors, recursors, $\iota$-reduction, nested elimination)* | [`Inductive.v`](rocq/Inductive.v), [`NewInductive.v`](rocq/NewInductive.v), [`InductiveUtils.v`](rocq/InductiveUtils.v), [`NestedInductive.v`](rocq/NestedInductive.v) | [`inductive_derivation516.ml`](hol/kernel_v3_complete/hol/inductive_derivation516.ml), [`recursor_construction522.ml`](hol/kernel_v3_complete/hol/recursor_construction522.ml), [`recursor_conversion585.ml`](hol/kernel_v3_complete/hol/recursor_conversion585.ml), [`checked_inductives629.ml`](hol/kernel_v3_complete/hol/checked_inductives629.ml), [`inductive_safety633.ml`](hol/kernel_v3_complete/hol/inductive_safety633.ml), [`nested_admission634.ml`](hol/kernel_v3_complete/hol/nested_admission634.ml) |
| **`Lean4Lean/Quot.lean`** *(Quotient types, $\iota$-reduction, atomic `addQuot`/`quotInit`)* | [`Quotient.v`](rocq/Quotient.v), [`QuotientTransaction.v`](rocq/QuotientTransaction.v), [`QuotientPersistentIndex.v`](rocq/QuotientPersistentIndex.v), [`QuotientFlagInvariant.v`](rocq/QuotientFlagInvariant.v) | [`projection_quotient550.ml`](hol/kernel_v3_complete/hol/projection_quotient550.ml), [`quotient_admission608.ml`](hol/kernel_v3_complete/hol/quotient_admission608.ml), [`quotient_dependencies839.ml`](hol/kernel_v3_complete/hol/quotient_dependencies839.ml), [`quotient_transaction963.ml`](hol/kernel_v3_complete/hol/quotient_transaction963.ml) |
| **`Lean4Lean/Primitive.lean`, `Strings.lean`** *(Nat/Bool/String literal & primitive operations)* | [`Primitive.v`](rocq/Primitive.v), [`StringParity.v`](rocq/StringParity.v), [`NatProbeOrder.v`](rocq/NatProbeOrder.v) | [`kernel_strings539.ml`](hol/kernel_v3_complete/hol/kernel_strings539.ml), [`kernel_naturals544.ml`](hol/kernel_v3_complete/hol/kernel_naturals544.ml), [`natural_reduction549.ml`](hol/kernel_v3_complete/hol/natural_reduction549.ml), [`primitive_foundations619.ml`](hol/kernel_v3_complete/hol/primitive_foundations619.ml)–[`primitive_recursors622.ml`](hol/kernel_v3_complete/hol/primitive_recursors622.ml) |
| **`Lean4Lean/Theory/{VLevel,VExpr,VDecl,VEnv}.lean`** *(Semantic model & de Bruijn substitution algebra)* | [`SemanticModel.v`](rocq/SemanticModel.v) | [`declarative_typing961.ml`](hol/kernel_v3_complete/hol/declarative_typing961.ml) |
| **`Lean4Lean/Theory/Typing/{Basic,Lemmas,Env,ChurchRosser,Injectivity,UniqueTyping}.lean`** *(13-rule declarative `VIsDefEq`/`VHasType`, confluence, $\Pi$-injectivity, type uniqueness)* | [`DeclarativeTyping.v`](rocq/DeclarativeTyping.v) | [`declarative_typing961.ml`](hol/kernel_v3_complete/hol/declarative_typing961.ml) |
| **`Lean4Lean/Verify/{Typing,Environment,TypeChecker}/*.lean`** *(Kernel-to-Theory soundness bridge)* | [`CheckerSoundness.v`](rocq/CheckerSoundness.v) | [`checker_soundness962.ml`](hol/kernel_v3_complete/hol/checker_soundness962.ml) |

### 2.2 Auditing Zero Axioms, Zero `Admitted`, and Zero Unsafe Casts

Unlike upstream `lean4lean` (which still contains `sorry` placeholders in parts of `Verify/Typing/Expr.lean` and `Verify/TypeChecker/`), every theorem in this repository is machine-checked with **zero axioms or proof escapes**:

1. **Rocq Kernel Audit (`rocq check`)**:
   ```sh
   sh scripts/toolchain-exec.sh sh -c 'cd rocq && rocq check -Q . LeanPort -o $(grep "\.v$" _CoqProject | sed "s/\.v$/.vo/")'
   ```
   Verify that the final summary prints:
   ```text
   * Axioms: <none>
   * Constants/Inductives relying on type-in-type: <none>
   * Constants/Inductives relying on unsafe (co)fixpoints: <none>
   * Inductives whose positivity is assumed: <none>
   ```
2. **HOL Light Axiom Count Audit (`axioms ()`)**:
   Stock HOL Light has exactly **3 foundational axioms** (`INFINITY_AX`, `SELECT_AX`, `ETA_AX`). Every HOL Light test script and proof bundle in this repo verifies `List.length (axioms ()) = 3` at completion and contains zero calls to `new_axiom` or `mk_thm`.
3. **Static Source Scan for Proof Escapes**:
   To verify that no `.v` or project `.ml` file uses `Admitted`, `admit`, `Axiom`, `Parameter`, `Unset Guard Checking`, `Obj.magic`, `new_axiom`, or `mk_thm`:
   ```sh
   python3 -c '
   import re
   from pathlib import Path
   vernac = re.compile(r"(^|[.][ \t\r\n])[ \t\r\n]*((Local|Global|Polymorphic|Monomorphic)[ \t\r\n]+)*(Admitted[ \t\r\n]*[.]|(Axioms?|Parameters?)[ \t\r\n]|Unset[ \t\r\n]+(Guard|Positivity|Universe|Elimination)[ \t\r\n]+Checking|Extract[ \t\r\n]+(Constant|Inductive|Inlined[ \t\r\n]+Constant))", re.M)
   tactics = re.compile(r"(^|[;{}]|[.][ \t\r\n]+)[ \t\r\n]*admit[ \t\r\n]*([.;}]|$)|\b(vm_cast_no_check|native_cast_no_check|exact_no_check)\b", re.M)
   ocaml = re.compile(r"\b(new_axiom|mk_thm)\b|\bObj[ \t\r\n]*[.][ \t\r\n]*(magic|obj|set_field|set_tag)\b", re.M)
   for p in sorted(Path("rocq").glob("*.v")):
       assert not vernac.search(p.read_text()) and not tactics.search(p.read_text()), f"Escape in {p}"
   for p in sorted(Path("hol").glob("*.ml")) + sorted(Path("hol/kernel_v3_complete/hol").glob("*.ml")) + sorted(Path("frontend").glob("*.ml")):
       assert not ocaml.search(p.read_text()), f"Escape in {p}"
   print("AUDIT PASSED: 0 axioms, 0 admits, 0 unsafe casts across all Rocq, HOL Light, and frontend sources.")
   '
   ```

### 2.3 Auditing Oracle-Free Execution on Lean Kernel Arena

- **No Expected-Answer Oracle**: When `scripts/test_arena.py` invokes a checker on an Arena `.ndjson` export, it passes **only** the input file path (`IN`) or stdin stream. The manifest (`arena/manifest.json`) containing expected `accept`/`reject`/`either` outcomes is read exclusively by the test harness after the checker process exits.
- **Pure Extracted Decision Logic in Rocq**: The Rocq executable `build/rocq-check` links the OCaml parser (`frontend/wire.ml`, `frontend/replay.ml`) directly to the code extracted from [`rocq/ArenaExtract.v`](rocq/ArenaExtract.v). Every typing, conversion, inductive, quotient, and primitive check is computed by the extracted Gallina functions.
- **Theorem-Producing LCF Checking in HOL Light**: The HOL Light checker constructs a closed HOL Light `thm` (`|- l4_evalid policy env` or `|- l4_file_verdict649 ...`) inside the HOL Light kernel before returning exit code `0` (`accept`).

---

## 3. How to Build and Run the Tests

All commands use the project-local toolchain wrapper `scripts/toolchain-exec.sh` (see [`docs/TOOLCHAINS.md`](docs/TOOLCHAINS.md) to initialize `toolchain/` if setting up on a new machine via `sh scripts/setup-toolchains.sh`).

### 3.1 Build & Test the Rocq Port

1. **Compile all 104 Rocq modules, extract OCaml, link `build/rocq-check`, and run all 24 native test suites**:
   ```sh
   sh scripts/build-rocq.sh
   ```
   This compiles every `.v` file in `rocq/` in dependency order, extracts `lean_arena.ml` and `lean_core.ml`, links `build/rocq-check`, and runs `python3 scripts/test_rocq_native.py` (24 native regression suites covering core typing, conversion, universes, inductives, nested inductives, quotients, primitives, strings, persistent environment indexing, and DAG admission).
2. **Run the native Rocq test suites standalone**:
   ```sh
   python3 scripts/test_rocq_native.py
   ```

### 3.2 Run the HOL Light Verification & Test Suites

1. **Run the baseline HOL Light regression suites (`hol/test.sh` & `hol/test-quotient.sh`)**:
   ```sh
   sh scripts/toolchain-exec.sh sh hol/test.sh
   sh scripts/toolchain-exec.sh sh hol/test-quotient.sh
   ```
   This runs 11 fresh-process HOL Light test suites (`core`, `admission`, `environment`, `inductive`, `nat_literal`, `family`, `indexed`, `projection_core`, `projection`, `structure`, and `quotient`—595+ theorem assertions) and verifies that the axiom count remains `3`.
2. **Verify the HOL Light Full Kernel + Declarative Metatheory & Soundness Bridge (`hol/kernel_v3_complete/`)**:
   ```sh
   cd hol/kernel_v3_complete && LINE_EDITOR=env sh ../../scripts/toolchain-exec.sh hol.sh <<'EOF'
   needs "hol/declarative_typing961.ml";;
   needs "hol/checker_soundness962.ml";;
   needs "hol/quotient_transaction963.ml";;
   needs "hol/equiv_manager964.ml";;
   needs "hol/fuel_config965.ml";;
   needs "hol/proposed_file_fixtures649.ml";;
   Printf.printf "HOL_V3_VERIFIED AXIOMS=%d\n%!" (List.length (axioms ()));;
   exit 0;;
   EOF
   ```
3. **Verify the self-contained 13-constructor core proof bundle (`hol/kernel_v1_core_only/`)**:
   ```sh
   cd hol/kernel_v1_core_only && LINE_EDITOR=env sh ../../scripts/toolchain-exec.sh hol.sh < run_proofs612.ml
   ```

### 3.3 Run the Lean Kernel Arena Benchmark Suite

1. **Verify the local Arena corpus inventory (220 pinned cases, 216 locally available)**:
   ```sh
   python3 -B scripts/test_arena.py --inventory
   ```
2. **Run the Rocq checker on the Arena corpus**:
   ```sh
   # Run a specific category (e.g., all 18 soundness bug tests or all 141 tutorial tests):
   python3 -B scripts/test_arena.py --checker ./build/rocq-check --select 'bugs/*' --report /tmp/rocq-bugs.json
   python3 -B scripts/test_arena.py --checker ./build/rocq-check --select 'tutorial/*' --report /tmp/rocq-tutorial.json

   # Run the full available Arena corpus:
   python3 -B scripts/test_arena.py --checker ./build/rocq-check --report /tmp/rocq-full-arena.json
   ```
3. **Run the HOL Light warm-server checker on the Arena corpus**:
   ```sh
   sh scripts/build-hol-frontend.sh
   # Start the warm HOL Light server in one terminal (prints a JSON readiness record with --socket PATH):
   python3 -B scripts/hol-check.py serve
   # In another terminal, run Arena cases against the socket:
   python3 -B scripts/test_arena.py \
     --checker 'python3 -B scripts/hol-check.py client --socket /private/tmp/hol-run-XXXX/s' \
     --select 'tutorial/*' \
     --report /tmp/hol-tutorial.json
   ```
4. **Run the Arena runner unit & adversarial tests**:
   ```sh
   python3 -B scripts/test_arena_schema.py
   python3 -B scripts/test_arena_adversarial.py
   python3 -B -m unittest discover -s tests/arena -p 'test_*.py' -v
   ```

---

## 4. Summary of Verification & Arena Results

| Verification Dimension | Rocq Port (`rocq/`, `build/rocq-check`) | HOL Light Port (`hol/kernel_v3_complete/` & `hol/`) |
| :--- | :--- | :--- |
| **Formal Proof Modules** | **104 / 104 `.vo` modules** verified by `rocq check` | **131 / 131 full-kernel modules** (`v3`) + **75 baseline modules** (`v0`) verified by `hol.sh` |
| **Axioms / Proof Escapes** | **`0` axioms** (`* Axioms: <none>`), `0` `Admitted`, `0` unsafe casts | **`0` added axioms** (`List.length (axioms ()) = 3` stock HOL axioms), `0` `mk_thm` |
| **Declarative Metatheory & Bridge** | Full `VLevel`/`VExpr`/`VEnv`, 13-rule `VIsDefEq`/`VHasType`, Church-Rosser confluence, $\Pi$-injectivity, type uniqueness, and `TrExpr`/`TrTyping` bridge | Full `l4_vlevel961`/`l4_vexpr961`/`l4_venv961`, 13-rule `l4_vis_defeq961`, multi-step confluence inversions, $\Pi$-injectivity, and `l4_tr_typing962` bridge |
| **Arena Functional Suites** (`tutorial/*`, `bugs/*`, `corner-cases/*`, `other/*`) | **187 / 187 (100%) passing** (`141/141` `tutorial`, `18/18` `bugs`, `19/19` `corner-cases`, `9/9` `other`), **`0` wrong verdicts** | **95 / 187 passing** (`84/94` valid `tutorial` accepts proved as closed HOL theorems, `6` rejects, `5` `corner-cases`/`other`) + `92` safe declines, **`0` wrong verdicts** |
| **Full Available Arena Corpus (216 files)** | **206 / 216 (95.4%) passing** (`117` `correct_accept`, `71` `correct_reject`, `18` `acceptable_either`, `10` `timeout` on large/exponential stress cases, **`0` wrong verdicts**) | **96 / 216 passing** (`88` `correct_accept`, `6` `correct_reject`, `2` `acceptable_either`, `120` safe `declined`, **`0` timeouts, `0` wrong verdicts**) + **100% of in-prover `v3` NDJSON/full-file suites** |
