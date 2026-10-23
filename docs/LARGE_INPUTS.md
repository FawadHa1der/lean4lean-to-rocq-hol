# Large Arena Inputs

This bounded acquisition covers only the published `init` and `std` cases.
It does not fetch the remaining Cedar, Con-Leche, CSLib, Mathlib, or
Navier-Stokes exports. Lean is used only to reproduce test inputs, never to
decide the Rocq checker's verdict.

The subsequent, separately pinned Con-Leche acquisition is documented in
[CON_LECHE_INPUT.md](CON_LECHE_INPUT.md). Its Lean version and build recipe
are distinct from this Init/Std recipe.
The next bounded candidate review and Cedar acquisition are documented in
[CEDAR_INPUT.md](CEDAR_INPUT.md).
The following exact CSLib acquisition review and bounded recipe are documented
in [CSLIB_INPUT.md](CSLIB_INPUT.md). Cedar's complete nonmatching native and
interpreted streams are preserved as supplemental-only source-pinned inputs,
not official Arena coverage.
CSLib subsequently matched all published bytes/lines/SHA-256 and is staged at
`arena/large/cslib/exports/cslib.ndjson`, awaiting parent-coordinated import.
The Init/Std generation and checker results below are historical snapshots.

## Pins

`arena/large/acquisition.lock.json` records the immutable source/configuration
hashes, Lean revision, exporter revision, and exact published output targets.
The script cross-checks these against the existing generation/provenance locks
and hash-verified published `results.json`, not an unpinned web response.

| Case | Exact Bytes | Lines | Upstream Checker Timeout |
| --- | ---: | ---: | ---: |
| init | 347,555,345 | 6,487,065 | 500 seconds |
| std | 596,655,086 | 10,826,639 | 590 seconds |

SHA-256 targets:

```text
init 620502ac9e63ba4a2dea9d46386c2f6aebc49faf8848ea3aaa18a77a09491a6a
std  289ed65a367abdc7388a855d2acf59cc1f401f5e06295acbb8a420682d9f00bd
```

Arena revision: `03b21e119045304d38249f426fcd86171fc253c5`.
Exporter revision: `66f1fb4bc256072069767fce52d39480e4524869` (format 3.1.0).
Lean: 4.34.1, revision `5045d0056413266e57c625dcd7c365b10e377c52`.

## Reproduction

Prerequisites are the already acquired `arena/upstream` and
`arena/exporter-source` commit objects, existing locked published results,
Python 3, Git, macOS `sandbox-exec`, and the isolated toolchain at
`arena/generation/toolchain/lean-4.34.1-darwin_aarch64`. No global elan change,
package installation, network access, or Lake build hooks are needed.

Review `scripts/acquire_large_arena.py`, the pinned `Export.lean`/`Main.lean`,
and both import-only Lean source files before executing:

```sh
python3 -B scripts/acquire_large_arena.py
python3 -B scripts/acquire_large_arena.py --execute-reviewed --step-timeout 600
```

The first command performs read-only preflight. The second creates a new run
directory below `arena/large/runs`, copies exact Git source blobs and the
exporter license, and compiles only those copies. The exporter receives module
`Test` without a `--` declaration selection, matching the full-export recipe.
An empty declaration selection would produce the wrong export.

Generation runs under a network-denying macOS sandbox that permits writes only
under `arena/large` and `/dev/null`. A failed sandbox probe stops execution;
there is no unsandboxed fallback. Relative PATH/LEAN_PATH entries avoid the
colon in the project directory name. Each subprocess has a 600-second default
wall timeout and its process group is killed/reaped when it completes or
times out. Generation is sequential. There is no hard memory limit.

Final outputs are `arena/large/exports/init.ndjson` and `std.ndjson`. They are
promoted from a per-run temporary output only when size, SHA-256, and line count
all match. Existing final outputs are verified, not silently overwritten.
Mismatches and failed-run logs are retained. Run reports record exact commands,
exit codes, timeouts, timings, source/toolchain/script hashes, and comparisons.
The generated subset manifest is compatible with `scripts/test_arena.py`.
Use `-B` to avoid writing Python bytecode caches into other workers' directories.

## Main Manifest

The acquisition script changes only `arena/large`; it does not edit the shared
manifest or overwrite another worker's generated inputs. After exact matches
are confirmed, coordinate with the manifest owner before this existing,
reviewed import operation:

```sh
python3 -B scripts/fetch_arena.py \
  --import-generated init=arena/large/exports/init.ndjson \
  --import-generated std=arena/large/exports/std.ndjson
```

The importer independently verifies published hashes/sizes/line counts, copies
the files to `arena/corpus`, preserves earlier generated imports, and atomically
updates `arena/manifest.json`. It also re-verifies/recreates the existing static
corpus. No schema change or handwritten manifest patch is necessary.

## Bounded Rocq Run

Review `scripts/check_large_arena.py` and the existing `scripts/test_arena.py`
before running:

```sh
python3 -B scripts/check_large_arena.py --timeout 30
```

This snapshots the current parent-built `build/rocq-check` into a unique
`arena/large/checker-runs` directory and checks its hash before/after copying,
so subsequent parent recompilations do not replace the executable being tested.
No checker source, fuel setting, or implementation is changed. The existing
runner verifies each input and invokes the snapshot with just its input path;
expected outcomes stay inside the runner.

Each input receives an explicit 30-second wall-clock limit, overriding the
published 500/590-second limits for this bounded smoke run. Logs are drained
with a 16 KiB retained prefix per stream; timeout kills the process group,
including descendants. A timeout, decline, fault, or wrong rejection is not
acceptance or full validation. The runner is not a security sandbox or hard
memory limiter. Binary/manifest/runner hashes and results are retained per run.

## Execution Status

Verified locally on 2026-09-29. Generation finished at 18:15:16 UTC, with exact
SHA-256, byte-count, and line-count matches for both inputs. No subprocess timed
out. Exporter compilation took 9.537 seconds; the Init and Std export steps took
30.034 and 51.930 seconds respectively. All steps, including the sandbox probe
and source compilation, returned exit 0.

Generation report:
`arena/large/runs/1790705622871052000-74246/generation-report.json`.
`arena/large/latest-generation.json` points to the latest successful run.

After a coordination notice to Kepler, the documented existing importer command
completed with exit 0. The shared manifest now contains **215 available cases
and 5 missing downloads**, totaling **1,002,779,534 available bytes**. The two
new inputs account for 944,210,431 bytes and 17,313,704 lines. The remaining
Cedar, Con-Leche, CSLib, Mathlib, and Navier-Stokes inputs remain missing; this
assignment does not claim their prerequisites are installed or their inputs
are generated. No source or script owned by another worker was edited.

The bounded checker command completed at 18:18:14 UTC with runner exit 2:

| Case | Elapsed | Exit | Outcome | Diagnostic |
| --- | ---: | ---: | --- | --- |
| init | 10.576613 s | 2 | decline | line=7639 checked=219 unsupported declaration: primitive/unsafe/partial |
| std | 17.618179 s | 2 | decline | line=8528 checked=223 unsupported declaration: primitive/unsafe/partial |

Neither case timed out under the 30-second per-case cap. Neither was accepted,
rejected, or fully validated. These are checker-declared coverage gaps, not
proof verdicts. Both published expected outcomes are acceptance, but the runner
does not pass those expectations to the checker.

The tested executable snapshot has SHA-256
`36803ed088fb518d9b716103179b25610e77cd48e651e5c15406798f770febb1` and was unchanged
after the run. Full results and provenance are under
`arena/large/checker-runs/1790705866185296000-21203/`; the convenience pointer is
`arena/large/latest-checker.json`. Later parent builds may differ, so these
results describe only that snapshot. No checker implementation was changed.

Post-import verification passed all three selected existing corpus tests,
including hash/size verification of every available input:

```sh
python3 -B -m unittest \
  tests.arena.test_corpus.CorpusTests.test_complete_published_inventory \
  tests.arena.test_corpus.CorpusTests.test_every_available_input_hash_and_size \
  tests.arena.test_corpus.CorpusTests.test_large_and_either_omissions_are_not_skips
```

Read-only acquisition preflight was rerun successfully. Three additional
in-memory policy tests passed: exact output acceptance, independent rejection
of wrong size/line-count/hash, and source-blob pin checking. These were focused
helper tests, not a full structural scan or checker-correctness proof.
