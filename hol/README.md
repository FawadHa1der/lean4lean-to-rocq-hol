# HOL Light Lean 4 Kernel Architecture & Directory Guide

This directory contains the HOL Light formalization of the Lean 4 kernel (`lean4lean`), organized into **four evolutionary stages** so that earlier verified checkpoints remain reproducible while newer layers add full-syntax coverage, whole-file admission, quotient dependency authentication, and declarative metatheory.

For an honest engineering comparison with upstream `lean4lean` and full verification logs, see [`../GAP_ANALYSIS.md`](../GAP_ANALYSIS.md) and [`kernel_v3_complete/VERIFICATION_STATUS.md`](kernel_v3_complete/VERIFICATION_STATUS.md).

## Quick Navigation: Which Directory Should I Use?

| Stage | Primary Directory | Legacy Alias (Symlink) | Expression Syntax | What It Contains & When to Use It |
| :--- | :--- | :--- | :--- | :--- |
| **v3 (Canonical & Complete)** | [`hol/kernel_v3_complete/`](kernel_v3_complete/) | `hol/full_kernel_candidate839/` | **13-constructor** full Lean 4 syntax (`l4_kexpr447`) | **The canonical in-prover HOL Light formalization (133 `hol/*.ml` modules, all machine-checked via [`verify_all_v3.sh`](kernel_v3_complete/verify_all_v3.sh)).** Includes the 13-constructor kernel, ordinary/inductive/nested/quotient/primitive/safety declaration admission (`607`–`634`), whole-file NDJSON driver (`642`/`644`/`649`), HOL `Compute` registry (`646`/`647`), held entry harnesses (`655`), quotient dependency authentication (`839`/`941`), declarative metatheory (`declarative_typing961.ml`, `typing_lemmas966.ml`), non-circular inference soundness (`infer_soundness967.ml`), conditional constant-header bridge (`checker_soundness962.ml`), atomic `addQuot`/`quotInit` transaction (`quotient_transaction963.ml`), and standalone `DefEqCache` / `FuelConfig` models (`equiv_manager964.ml`, `fuel_config965.ml`). |
| **v2 (Full-File & Compute)** | [`hol/kernel_v2_full_file/`](kernel_v2_full_file/) | `hol/full_kernel_candidate652/` | **13-constructor** full Lean 4 syntax (`l4_kexpr447`) | Historical checkpoint (`652`) that expanded `v1` with whole-file admission (`ordinary_admission607.ml`, `checked_inductives629.ml`, `checked_admission631.ml`, `nested_admission634.ml`, `file_driver642.ml`), primitive reflection (`619`–`622`), `FLAT` prelude compatibility (`650`), and the `Compute` registry (`646`–`649`), plus earlier `961`–`965` snapshots. |
| **v1 (13-Constructor Core Only)** | [`hol/kernel_v1_core_only/`](kernel_v1_core_only/) | `hol/full_kernel_candidate612/` | **13-constructor** full Lean 4 syntax (`l4_kexpr447`) | Self-contained 43-module core bundle (`612`, verified via [`run_proofs612.ml`](kernel_v1_core_only/run_proofs612.ml)) covering full-syntax WHNF (`594`), conversion (`595`–`597`), inference (`586`), projections (`577`), recursor reduction (`585`), and universe decision procedures (`555`/`562`) without whole-file I/O or environment admission. |
| **v0 (Baseline 9-Constructor Core & External CLI)** | [`hol/*.ml`](.) *(97 root `.ml` files)* | — | **9-constructor** baseline syntax (`l4_expr` in [`syntax.ml`](syntax.ml)) | Initial LCF theorem-producing checker ([`core.ml`](core.ml), [`admission.ml`](admission.ml), [`environment.ml`](environment.ml)) used by the external Arena socket/CLI checker ([`../frontend/hol_check.ml`](../frontend/hol_check.ml)) and the modular regression suites run by [`test.sh`](test.sh) and [`test-quotient.sh`](test-quotient.sh). Note: `hol_check.ml` runs this `v0` baseline (certifying accepts as closed HOL theorems, rejecting wire/input errors, and declining unsupported features), not `kernel_v3_complete`. |

## Why Are Multiple Versions Retained?

1. **HOL Light Global Namespace Isolation**: Unlike Rocq (where each `.v` file compiles into its own `.vo` module namespace), HOL Light loads `.ml` scripts into a single flat OCaml/HOL top-level state where constants and theorems cannot be redefined in the same session. Isolating each evolutionary stage in its own directory (and suffixing internal module families with checkpoint numbers like `447`, `597`, `607`, `839`, `961`–`967`) prevents constant-name collisions.
2. **Self-Contained Reproducibility & Verified Stock Files**: Both [`kernel_v2_full_file/`](kernel_v2_full_file/) and [`kernel_v3_complete/`](kernel_v3_complete/) bundle exact copies of **33 stock HOL Light 3.1.0** kernel and library files (`fusion.ml`, `bool.ml`, `arith.ml`, `lists.ml`, `compute.ml`, etc.), which [`../scripts/audit-build.sh`](../scripts/audit-build.sh) verifies byte-for-byte against `toolchain/opam-root/lean4lean/lib/hol_light/`. `kernel_v3_complete/` additionally includes the two verification drivers [`verify_all_v3.ml`](kernel_v3_complete/verify_all_v3.ml) and [`verify_entries_v3.ml`](kernel_v3_complete/verify_entries_v3.ml).
3. **Audit Provenance**: Historical checkpoint manifests ([`MANIFEST612.json`](kernel_v1_core_only/MANIFEST612.json), [`MANIFEST652.json`](kernel_v2_full_file/MANIFEST652.json), [`MANIFEST839.json`](kernel_v3_complete/MANIFEST839.json)) are retained alongside [`kernel_v3_complete/VERIFICATION_STATUS.md`](kernel_v3_complete/VERIFICATION_STATUS.md), which documents the end-to-end execution of all 133 `v3` modules.

## Running the HOL Light Verification Suites

- **v3 Complete kernel — all 133 modules + 104 held entry cases (`hol/kernel_v3_complete/`)**:
  ```sh
  sh hol/kernel_v3_complete/verify_all_v3.sh
  ```
- **Baseline v0 regression suites (`hol/*.ml`)**:
  ```sh
  sh scripts/toolchain-exec.sh sh hol/test.sh
  sh scripts/toolchain-exec.sh sh hol/test-quotient.sh
  ```
- **v1 Core-only proof bundle (`hol/kernel_v1_core_only/`)**:
  ```sh
  cd hol/kernel_v1_core_only && LINE_EDITOR=env sh ../../scripts/toolchain-exec.sh hol.sh < run_proofs612.ml
  ```
