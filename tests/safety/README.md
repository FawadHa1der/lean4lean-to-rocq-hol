# Unsafe Declaration Boundary

`UnsafeInductives.lean` is a small independent source, not an Arena case. Its
export includes an empty unsafe type, a genuinely non-positive unsafe inductive,
an unsafe identity, and mutually recursive unsafe functions. Generation uses
the locally pinned Lean 4.34.1 toolchain and exporter revision recorded under
`arena/generation.lock.json` (`tutorial_exporter_revision`, directory prefix
`777c921eba89`). Lean is used only to produce test input, never by either port
to decide a verdict.

From this directory, regenerate with:

```sh
../../arena/generation/toolchain/lean-4.34.1-darwin_aarch64/bin/lean \
  -o UnsafeInductives.olean UnsafeInductives.lean
env LEAN_PATH=.:../../arena/generation/exporter-777c921eba89 \
  ../../arena/generation/toolchain/lean-4.34.1-darwin_aarch64/bin/lean \
  --run ../../arena/generation/exporter-777c921eba89/Main.lean \
  --export-unsafe UnsafeInductives -- UEmpty UNeg uId uA uB > unsafe-inductives.ndjson
```

From the project root, run `python3 -m unittest discover -s tests/safety -v`.
The valid baseline must accept before any mutation is tested. Wrong safety,
positivity, constructor metadata, recursor metadata and group consistency must
reject, not decline. Reordering and noncontiguous mutual groups must accept.
Each test verifies that the checker binary did not change during execution.
Expected answers exist only in this test driver, never in the checker.
