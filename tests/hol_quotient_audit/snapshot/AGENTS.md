# Project Instructions

This is an independent port of Lean4Lean to Rocq and HOL Light. It has no Solidity dependency.

- Keep all changes local. Do not commit, push, open pull requests, publish artifacts, or alter the Solidity project.
- Implement actual checker logic in the requested proof assistant. Wrappers that delegate logical verdicts to Lean, another checker, a test manifest, or a precomputed answer are not ports.
- Keep logical soundness, executable compatibility, and end-to-end runtime verification claims separate.
- Never hide unsupported features, fuel exhaustion, test skips, proof admissions, axioms, or trust-expanding flags. Return decline for inability to decide; do not label it acceptance or proven invalidity.
- Do not introduce `Admitted`, `sorry`, `new_axiom`, disabled termination/positivity/elimination checks, or unchecked casts to discharge correctness obligations.
- Preserve provenance and licensing for adapted upstream code. Pin upstream snapshots and corpus manifests.
- Coordinate disjoint write scopes with the parent agent. Use apply_patch for hand edits.
- Work under this directory; temporary build/source downloads may use /private/tmp. This directory is outside the initial writable root, so request narrowly scoped escalated tool execution when needed rather than bypassing a permission denial.
