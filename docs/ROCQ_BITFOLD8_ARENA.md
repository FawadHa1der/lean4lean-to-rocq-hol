# Frozen Bitfold8 Arena Validation

## Scope

This is private validation of the frozen hybrid64 `suffix_bitfold8` candidate
from [the admission A/B](ENVIRONMENT_INDEX_ADMISSION_AB.md), not production
integration. Its binary SHA-256 is:

`22d330fc7d45c16676f236c836e5559e867be35c74428fcddb89d1b174f50050`

The binary remains at
`/private/tmp/rocq-index-suffix-ab-20260929T212700Z/bitfold8/build/rocq-check`.
Its frozen source, six assumption-free refinement proofs, standard extraction,
and cast audit are unchanged. It does not include subsequent parent changes.
No candidate source, binary, production build, or main manifest was edited for this run.

New validation artifacts are under
`/private/tmp/rocq-bitfold8-full-validation-20260929T214616Z`.
The manifest was held stable throughout the requested sequential workflow.

## Full Arena At 30 Seconds

The current manifest contains 220 cases: 216 available and four missing
downloads. All 216 available cases were attempted once, at fuel 16384 and a
30-second per-case wall deadline. No case was selected out or explicitly
skipped. The invocation used `--progress 100` and the unchanged checker binary.

| Status | Count |
| --- | ---: |
| Correct accept | 115 |
| Correct reject | 71 |
| Acceptable either | 18 |
| Timeout | 12 |
| Missing download | 4 |
| Resource/checker decline | 0 |
| Wrong verdict, fault, input error, execution error | 0 |
| Integrity failures | 0 |

Report: `build/reports/rocq-private-indexed-bitfold8-arena.json`.
The run lasted from 2026-09-29 21:49:40.787 UTC to 21:56:11.420 UTC, about
390.63 seconds. Peak sampled process-group RSS was 3,172.70MiB. Every native
checker was killed when necessary and waited for; no sampler failed.

There are **no per-case status or exit-code differences** from the parent's archived
`build/reports/rocq-private-indexed-hybrid64-arena.json`. Thus the cheaper hash's
prefix speedup did not change coverage under this 30-second cap. The earlier
leaf16 report is a different-time measurement without this RSS-sampling adapter;
small timing differences are not controlled performance estimates.

The twelve timeouts are `cslib`, `init`, `std`, `perf/app-lam`,
`perf/fueled-chain`, `perf/grind-ring-5`, `perf/magma-list-deep-n21`,
`perf/magma-list-deep-n36`, `perf/magma-list-pair-n21`,
`perf/magma-list-pair-n7`, `perf/magma-string-n4`, and
`perf/magma-string-pair-n9`. Missing downloads are `cedar`, `con-leche`,
`mathlib`, and `navier-stokes-euler`; diagnostic partial exports are not supplied
as exact inputs. CSLib received only this 30-second attempt, with no long retry.

The 30-second Init attempt reached scheduling but emitted no check-phase event.
Its short-cap timeout is not evidence of a kernel bottleneck or logical failure.

## Full-Budget Init And Std

These attempts follow the full Arena run, sequentially, at fuel 16384. The
published limits are read from `arena/large/manifest.json`: Init 500 seconds,
Std 590 seconds. They match the main manifest's budgets and input pins.

| Input | Exact bytes | Lines | SHA-256 |
| --- | ---: | ---: | --- |
| Init | 347,555,345 | 6,487,065 | `620502ac9e63ba4a2dea9d46386c2f6aebc49faf8848ea3aaa18a77a09491a6a` |
| Std | 596,655,086 | 10,826,639 | `289ed65a367abdc7388a855d2acf59cc1f401f5e06295acbb8a420682d9f00bd` |

Only the existing complete exact files are supplied. No prefix, truncated
export, generated substitute, or expected verdict is passed to a checker.
Supplying and hashing a full file does not establish full logical acceptance;
that requires actual checker exit 0.

| Input | Budget s | Result | Elapsed s | Sampled peak RSS MiB | Last completed-count checkpoint |
| --- | ---: | --- | ---: | ---: | --- |
| Init | 500 | Timeout; no logical verdict | 500.008449 | 697.27 | 3,200, source line 249099 |
| Std | 590 | Timeout; no logical verdict | 590.026248 | 1,180.47 | 2,500, source line 205510 |

Init entered parsing at 0.003 CPU seconds, scheduling at 8.368, and kernel
checking at 33.667. Parsing therefore took about 8.365 CPU seconds and scheduling
25.299. Its final recorded checkpoint was at 76.378 CPU seconds / 76.713 wall
seconds, `stage=declaration line=249099 checked=3200`. No subsequent 100-declaration
checkpoint arrived before the wall deadline. This confirms a substantial actual
kernel attempt beyond transport, but **does not identify the exact stalled
declaration**: at least 3,200 completed, and the next unreported interval may
contain multiple declarations. No per-declaration or full-file acceptance is
inferred from this checkpoint. The native process was killed at the deadline and
waited for; the memory/disk guard did not fire.

Std entered parsing at 0.002 CPU seconds, scheduling at 14.972, and kernel
checking at 57.945. Parsing took about 14.970 CPU seconds and scheduling 42.973.
Its final recorded checkpoint was at 83.767 CPU seconds / 84.115 wall seconds,
`stage=declaration line=205510 checked=2500`. No later progress event arrived
before the deadline. It also received a substantial actual kernel attempt,
without full acceptance or any other logical verdict. The process was killed
and waited for; no resource guard triggered.

The frozen frontend emits a declaration event before admission only when
`checked mod 100 = 0`. Mutual batches can advance the count by more than one,
so an absent subsequent event does not even establish a strict next-hundred
upper bound. The observed 3,200 and 2,500 counts are **lower bounds only**; neither
report identifies an exact stalled declaration or localizes one operation's cost.

Separate reports are
`build/reports/rocq-private-indexed-bitfold8-init.json` and
`build/reports/rocq-private-indexed-bitfold8-std.json`.
Each individual report also retains the other large case as `skipped: not
selected`, following shared-runner accounting. This is not a missing input or
a skip of the selected attempt, and there were no skips in the 216-case run.

## Guard And Provenance

The private `guarded_arena.py` imports the unchanged shared
`scripts/test_arena.py` and calls its `main`. Shared manifest validation,
inventory, verdict classification, file checksum verification, executable/argv
fingerprinting, incremental report writing, and final integrity checks remain
unchanged. Only process execution is replaced with a resource-aware adapter;
resource-stop annotations distinguish guard declines from checker exit 2.

The adapter launches each native checker in its own process group. It samples
aggregate group RSS every approximately 0.25 seconds, stopping at 8GiB, and
checks for at least 64GiB free disk before and during execution. RSS is a
**sampled stop threshold, not a hard operating-system cap**. A triggered
resource limit kills the native process group, waits for its direct child,
retains the native exit status, and maps the outcome to decline/exit 2. It is
not acceptance or rejection. A sampler error maps to fault, not success.

Wall deadlines remain wall timeouts, not resource declines. Cleanup and resource
sampling shutdown can add small reporting overhead beyond the native deadline.
The adapter drains stdout/stderr with bounded 8MiB capture per stream, retains
the final 20 progress observations separately, and records truncation flags.
Progress events precede checking the named declaration; `checked` is a lower
bound on completed work, not acceptance of that declaration. Reported child CPU
includes the small `ps` sampler children and is explicitly labeled accordingly.

Seven focused adapter tests passed: exact exit-code preservation (0/1/2/3),
wall timeout, memory decline with kill/wait, disk preflight without launch,
bounded logs/progress retention, sampler failure, and process-group RSS sums.
They are in the private `test_guard.py`; no checker logic or production tests
were modified.

Each run has a private provenance sidecar pinning the adapter, shared runner,
binary, all frozen candidate sources, both manifests, invocation, and runtime
environment. The shared runner hashes available inputs before and after each
attempt. Manifest and runner snapshots are retained separately. Final source,
binary, input, manifest, and report integrity checks all passed. No captured
stdout/stderr stream was truncated. Disk reserve never triggered; minimum
observed free space was about 877.04GiB, above the 64GiB reserve. The sampled
8GiB RSS threshold never triggered in any of the 218 native attempts.

All 218 native attempts and their samplers finished and were reaped. A final
read-only process-table audit found all 221 recorded checker/driver PIDs absent.
The three reports are copied into the private validation directory, alongside
`summary.json` and an inventory of 16 private artifact hashes. The original
398-file A/B artifact inventory was also rechecked unchanged after validation.
The manifest hold can be released: no checker attempt remains active.

| Artifact | SHA-256 |
| --- | --- |
| Main manifest, unchanged | `d0ef9bd650fa4256cca4e4256ef45eda096e8ad3505945dad9c41a3f3d063b19` |
| Arena report | `af07fa5bf0c1aea8c9284c86d96fb9ad151ccc4bf2c537ec62472eae9002529d` |
| Init report | `16534ed9f075c8c284fa20baabbca3b0f596a09cd22081a3142fc6624692e169` |
| Std report | `3455e8dd755a4ce9b84cd72e4e2d32329ca14de724c32f1ca908e69b46fb1bd4` |
| Private summary.json | `602903ce84728450d22c21102850a0556b7c96da9b991347c2c87d98285f1ebd` |
| Private artifact-sha256.json | `aee6f867e1394b17203b93ef99cef2440768fd58d8a552380fbd9dd4655e5697` |

## Decision Limit

Bitfold8 retains the same 30-second Arena coverage as hybrid64 leaf16 and its
earlier prefix improvement is real for those measured attempts. These full-file
runs do **not** establish sufficient Init/Std throughput or an optimal hash or
index threshold: both still time out after substantial kernel checking. Keep
the candidate private pending the parent's integration decision. No additional
CSLib, full Init/Std retry, source optimization, or production integration was
performed.
