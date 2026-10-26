# HOL Light Lean 4 Kernel Architecture & Directory Guide

This directory contains the HOL Light formalization of the Lean 4 kernel (`lean4lean`), organized into **four evolutionary stages** so that earlier verified checkpoints and their SHA-256 manifests remain immutable while newer layers add full-syntax coverage, whole-file admission, quotient dependency authentication, and declarative metatheory.

## Quick Navigation: Which Directory Should I Use?

| Stage | Primary Directory | Legacy Alias (Symlink) | Expression Syntax | What It Contains & When to Use It |
| :--- | :--- | :--- | :--- | :--- |
| **v3 (Canonical & Complete)** | [`hol/kernel_v3_complete/`](kernel_v3_complete/) | `hol/full_kernel_candidate839/` | **13-constructor** full Lean 4 syntax (`l4_kexpr447`) | **The complete, canonical HOL Light implementation.** Includes the full 13-constructor kernel, ordinary/inductive/nested/quotient/primitive/safety declaration admission, whole-file NDJSON driver (`642`/`644`/`649`), HOL `Compute` registry (`646`/`647`), quotient dependency authentication (`839`/`941`), and the full declarative metatheory, soundness bridge, atomic `addQuot`/`quotInit` transaction, `DefEqCache`, and `FuelConfig` (`961`–`965`). |
| **v2 (Full-File & Compute)** | [`hol/kernel_v2_full_file/`](kernel_v2_full_file/) | `hol/full_kernel_candidate652/` | **13-constructor** full Lean 4 syntax (`l4_kexpr447`) | Historical checkpoint (`652`) that expanded `v1` with whole-file admission (`ordinary_admission607.ml`, `inductive_admission632.ml`, `nested_admission634.ml`, `file_driver642.ml`), primitive reflection (`619`–`622`), `FLAT` prelude compatibility (`650`), and the `Compute` registry (`646`–`649`), synchronized with the `961`–`965` metatheory modules. |
| **v1 (13-Constructor Core Only)** | [`hol/kernel_v1_core_only/`](kernel_v1_core_only/) | `hol/full_kernel_candidate612/` | **13-constructor** full Lean 4 syntax (`l4_kexpr447`) | Self-contained 43-module core bundle (`612`, verified via [`run_proofs612.ml`](kernel_v1_core_only/run_proofs612.ml)) covering full-syntax WHNF (`594`), conversion (`595`–`597`), inference (`586`), projections (`577`), recursor reduction (`585`), and universe decision procedures (`555`/`562`) without whole-file I/O or environment admission. |
| **v0 (Baseline 9-Constructor Core & Fast CLI)** | [`hol/*.ml`](.) *(root files)* | — | **9-constructor** baseline syntax (`l4_expr` in [`syntax.ml`](syntax.ml)) | Initial LCF theorem-producing checker ([`core.ml`](core.ml), [`admission.ml`](admission.ml), [`environment.ml`](environment.ml)) used by the fast baseline CLI ([`../frontend/hol_check.ml`](../frontend/hol_check.ml)) and the 10 modular regression suites run by [`test.sh`](test.sh) (`inductive_tests.ml`, `structure_tests.ml`, `quotient_tests.ml`, `reflection_validation.ml`). |

## Why Are Multiple Versions Retained?

1. **HOL Light Global Namespace Isolation**: Unlike Rocq (where each `.v` file compiles into its own `.vo` module namespace), HOL Light loads `.ml` scripts into a single flat OCaml/HOL top-level state where constants and theorems cannot be redefined in the same session. Isolating each evolutionary stage in its own directory (and suffixing internal module families with checkpoint numbers like `447`, `597`, `607`, `839`, `961`–`965`) prevents constant-name collisions.
2. **Self-Contained Reproducibility**: Both [`kernel_v2_full_file/`](kernel_v2_full_file/) and [`kernel_v3_complete/`](kernel_v3_complete/) bundle exact copies of their 35 stock HOL Light kernel and library files (`fusion.ml`, `bool.ml`, `arith.ml`, `lists.ml`, `compute.ml`, etc.) so that `needs "hol/..."` resolves deterministically from the bundle directory.
3. **Immutable Audit Provenance**: Each stage's SHA-256 file manifest ([`MANIFEST612.json`](kernel_v1_core_only/MANIFEST612.json), [`MANIFEST652.json`](kernel_v2_full_file/MANIFEST652.json), [`MANIFEST839.json`](kernel_v3_complete/MANIFEST839.json)) preserves the exact cryptographic provenance referenced by historical verification logs.

## Running the HOL Light Verification Suites

- **Baseline v0 regression suites (`hol/*.ml`)**:
  ```sh
  sh scripts/toolchain-exec.sh sh hol/test.sh
  ```
- **v1 Core-only proof bundle (`hol/kernel_v1_core_only/`)**:
  ```sh
  cd hol/kernel_v1_core_only && LINE_EDITOR=env sh ../../scripts/toolchain-exec.sh hol.sh < run_proofs612.ml
  ```
- **v3 Complete kernel + declarative metatheory & soundness bridge (`hol/kernel_v3_complete/`)**:
  ```sh
  cd hol/kernel_v3_complete && LINE_EDITOR=env sh ../../scripts/toolchain-exec.sh hol.sh <<'EOF'
  needs "hol/declarative_typing961.ml";;
  needs "hol/checker_soundness962.ml";;
  needs "hol/quotient_transaction963.ml";;
  needs "hol/equiv_manager964.ml";;
  needs "hol/fuel_config965.ml";;
  Printf.printf "AXIOMS=%d\n%!" (List.length (axioms ()));;
  exit 0;;
  EOF
  ```
