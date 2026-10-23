# Rocq Large-Input Kernel Attempts

These runs use the current native checker snapshot, not the transport-only
profiler, and apply the actual upstream per-case timeouts. They are separate
from the parent's small-case benchmarks and later checker builds.

## Checker Snapshot

Run directory:
`arena/large/checker-runs/20260929T185906Z-upstream-caps/`

The snapshot was taken at `2026-09-29T19:00:30.762414+00:00`, without a build.
Original and copied bytes were hashed before and after copying. The checker
is a 2,182,400-byte Mach-O arm64 native executable.

| Artifact | SHA-256 |
| --- | --- |
| `rocq-check` | `22eb979996c6332400f107217ad95d64d182a11a7d8eb808f6d604ed823bf1f4` |
| `test_arena.snapshot.py` | `a2b4e18804a0a8a522e6901770626e4633fcdd8f2b2c315a6a7c537279c58827` |
| Stable subset manifest | `998cf84342463ad1d218b9857dcf3560d3823831773133d2f334d642abb879fd` |

`snapshot-provenance.json` records source paths, snapshot paths, sizes, and
hashes. `manifest.snapshot.json` is archival only: the runner uses the unchanged
`arena/large/manifest.json` so its `exports/...` paths resolve correctly. It
does not read the main corpus manifest that may change during acquisition.

The parent identified this build as including the positivity fix and complete
current natural-number gates. This report binds claims to the binary hash,
not to later source changes or later builds. It does not establish a semantic
correctness theorem for those features or fingerprint every dynamic library.

## Inputs And Limits

| Case | Bytes | Lines | Upstream timeout |
| --- | ---: | ---: | ---: |
| Init | 347,555,345 | 6,487,065 | 500 seconds |
| Std | 596,655,086 | 10,826,639 | 590 seconds |

Both inputs are exact locally reproduced upstream exports in NDJSON 3.1.0,
using Lean 4.34.1 and pinned exporter
`66f1fb4bc256072069767fce52d39480e4524869`. The subset manifest retains the
upstream Arena revision `03b21e119045304d38249f426fcd86171fc253c5` and recipe
provenance. Input SHA-256 values:

```text
Init 620502ac9e63ba4a2dea9d46386c2f6aebc49faf8848ea3aaa18a77a09491a6a
Std  289ed65a367abdc7388a855d2acf59cc1f401f5e06295acbb8a420682d9f00bd
```

Initial arguments are `--progress 100 --fuel 512`. No `--timeout` override is
supplied: the runner reads 500/590 seconds from the manifest records, covering
parsing, scheduling, and actual logical checking in one subprocess deadline.
Exit 0 is accept, 1 reject, 2 decline, and 3 fault. Timeout is reported separately
from a checker-declared decline. Neither is a proof verdict.

Logs are capped at 1,048,576 bytes per stream per case and continuously drained;
the reports expose truncation flags. The runner kills the checker process group
at its deadline, waits for its leader, and bounds inherited-pipe draining. Input
hashes are checked before and after each case, and checker artifact/manifest
hashes before and after each complete runner invocation.

Quick explicit out-of-fuel declines may be retried at fuel 4096 with the same
timeout records and a separate report. A case already timing out at fuel 512
is not repeated at 4096.

## Results

Both fuel-512 attempts finished. The retained
[runner report](../arena/large/checker-runs/20260929T185906Z-upstream-caps/fuel512.json)
finished at `2026-09-29T19:19:08.320892+00:00`.

| Case | Fuel | Cap | Observed wall seconds | Result | Last progress count |
| --- | ---: | ---: | ---: | --- | ---: |
| Init | 512 | 500 | 500.029289 | Timeout, killed with signal 9; no proof verdict | 1700 |
| Std | 512 | 590 | 590.024968 | Timeout, killed with signal 9; no proof verdict | 2000 |

Native checker phase/progress diagnostics, in process CPU seconds:

| Measurement | Init | Std |
| --- | ---: | ---: |
| Parsing duration | 8.961 | 16.452 |
| Scheduling duration | 38.226 | 42.496 |
| Entry into logical checking, cumulative CPU | 47.190 | 58.950 |
| Last declaration-progress cumulative CPU | 187.632 | 299.047 |
| Last reported input line | 114258 | 134046 |
| Last reported completed record count | 1700 | 2000 |
| Declaration progress events, including zero | 18 | 21 |
| Captured stderr bytes | 1233 | 1427 |

Both runs therefore made **actual extracted-kernel attempts**, not merely
parsing/scheduling attempts. Neither emitted an acceptance, rejection, or
checker-declared decline. Neither stdout nor stderr was truncated; both stdout
streams were empty. CPU phase durations must not be subtracted from the wall
deadline to claim an exact checking duration.

Because progress is emitted only every 100 checked declarations, the counts
are completed-record lower bounds, not proof that the next logged declaration
itself consumed all remaining time. There is no terminal checker diagnostic
identifying the exact stopping declaration: the runner killed each process at
its deadline.

`checked` counts replay declaration records, not every named constant inside a
compound inductive record. A progress event is emitted before attempting the
batch at its reported input line; it does not certify that batch or the whole
input.

## Retry Decision

Neither case was retried at fuel 4096. Both consumed their full upstream wall
allowances at fuel 512, and neither emitted `checker fuel exhausted`. Increasing
recursion fuel under the same exhausted deadline would not be the requested
quick-out-of-fuel retry. There is deliberately no fabricated 4096 report or
claim of a successful large-input check.

## Integrity And Cleanup

The runner reports `integrity_verified=true`, zero integrity failures, and
exactly two executed cases with status `timeout`. Its overall exit code is 1
because timeout is an unsuccessful test outcome; this is not two native
checker faults or two wrong proof verdicts. The native subprocess exit codes
are both `-9`, paired with `timed_out=true`.

Both input hashes and sizes passed the before/after per-case checks. Executed
checker fingerprints match before and after the invocation. An independent
post-run SHA-256 check also confirmed that the checker snapshot, runner
snapshot, archival manifest, and original stable subset manifest still match
the hashes above. Final report SHA-256:

```text
efab556ec0b0f26078e784c96c786e594d82cf87d1705a4700fea2d4d6c3b998
```

The runner completed its process-group termination and wait paths. A subsequent
read-only process audit found **zero matching snapshot-checker or runner
processes**. No validation command from this task remains running. No existing checker binary,
source file, script, or manifest was changed, and no build was performed.
Only the new run directory and this report were added to the shared project.

## Hint-Enabled Init Attempt

A later separate attempt uses the actual-main hint-enabled runtime
`acd3d008970f48ba0fd866dd8977267bedeb19ac057e10761094894d2a60a1db`,
fuel 16,384, and the original 500-second whole-process cap. It reads the full
347,555,345-byte Init input, SHA-256
`620502ac9e63ba4a2dea9d46386c2f6aebc49faf8848ea3aaa18a77a09491a6a`.
Parsing, scheduling and checking all remain inside that one deadline.

The result is a wall timeout at 500.019930 seconds including cleanup, not
acceptance, a logical rejection, or a checker-declared decline. At least 9,546
Wire admission records complete. This is not a count of every generated member
of an inductive block. The last confirmed completed theorem is
`Int64.toInt_toBitVec`, line 1,137,381. The next event starts
`Int64.toBitVec_div`, line 1,137,400, checked=9546; that theorem is not accepted.
Its start arrives at 462.896304 wall seconds, leaving about 37.104 seconds
without a following event. No stack sample or causal hotspot attribution is made.

The old target `Int64.toBitVec_shiftLeft` at line 250275 starts at checked=3224
and the following event reaches checked=3225. Thus the actual full input passes
the previous stopping point, while the whole library still does not finish.
There are 9,550 retained progress events, no output truncation or terminal
checker verdict, and no stdout acceptance.

All 197 frozen holds match; the previous integration's 737 artifacts remain
unchanged. Peak sampled RSS is 1,864,032 KiB, below the unchanged 8 GiB sampled
threshold; the 64 GiB disk reserve does not trigger. These are sampled guards,
not an OS hard memory limit. Native and driver processes are reaped and absent.
No retry, tuning, Std run, or production change is part of this attempt.

Main copies: `build/reports/rocq-shipped-hints-init500.json` and
`build/reports/rocq-shipped-hints-init500-summary.json`. The separate sealed
[checkpoint](/private/tmp/rocq-hints-init500-20260930/CHECKPOINT.md) contains
exact source anchors, loader evidence, output, process audits and source holds.

## Projection-Retry Init Attempt

The subsequent actual-main executable
`b7812ef805a7ad6cd54b88d993986faa6170f309006ab5d6ec503d173c4029cc`
adds the pinned upstream opposite-projection retry. Its fresh 15 native suites,
75-module independent kernel audit and 16 closed-assumption queries pass.
The complete available Arena attempt retains 117 correct accepts, 71 correct
rejects, 18 allowed-either outcomes, ten timeouts and four missing inputs.

One full Init attempt on this runtime, still fuel 16384 and 500 seconds, times
out after 500.039666 seconds with 7,842 completed Wire admission records. The
last started declaration is the internal `Array.toList_reverse.go._unary` at
line 910933. Its final 241.444-second wall interval is right-censored, not a
completed theorem measurement or exclusive CPU time. There is no final acceptance.
See `build/reports/rocq-shipped-projection-init500.json` and
`build/reports/rocq-shipped-projection-validation.md`.

A read-only comparison aligns all 7,842 completed common batch identities with
the earlier hint-enabled trace. Their summed CPU intervals are 206.962 and
208.018 seconds, a difference of 1.056 seconds. The preceding run's completion
of the later theorem cannot be compared directly with the new censored wall
interval. The differing final admission counts do not themselves identify a
checker hotspot or establish a causal performance regression.

## Matched Prefix Pair

One separate old-then-new pair checks the byte-exact first 25,172,051 bytes of
Init through line 497392. Static dependency/group closure and the pinned official
Wire/scheduler transport are checked before execution. No record is rewritten,
dependency deleted, expected verdict supplied, or deadline increased.

Both actual native runtimes accept all 4,400 records at fuel 16384 within their
separate 180-second caps. Old hints takes 161.829770 wall seconds; new projection
retry takes 158.720095. The selected admission interval, from line 487857 /
checked4398 to line 497392 / checked4399, takes 26.281 versus 29.425 CPU seconds.
The final declaration is separately confirmed complete by the final exit-zero
acceptance messages, not merely by its start marker.

Thus this pair observes a local 3.144-second CPU increase but a 3.109675-second
decrease in whole-prefix wall time. One sequential pair on a shared host is not
a controlled repeated performance experiment. The prefix also omits the unused
parsed heap of the complete 347 MB export, which can affect allocation and GC.
It is not a full Init or Arena pass. All source/input/runtime holds remain stable;
both native groups and the driver are reaped/absent, with no resource stop,
monitor error or output truncation. The 8 GiB RSS bound is sampled, not OS-enforced.

Machine-readable comparison: `build/reports/rocq-projection-prefix-comparison.json`.
The [sealed checkpoint](/private/tmp/rocq-array-extract-pair-run-20260930/CHECKPOINT.md)
retains the exact markers, byte/hash identities, caps and cleanup records.

## Nat-Ordering Main Run

The subsequent actual-main `efd4d266...` binary completes only 3,902 Wire
admission records in a fresh full Init attempt, before timing out at
500.019579 seconds with fuel 16384. Last started, not accepted:
`String.utf8EncodeChar_eq_utf8EncodeCharFast`, line 325661. This observed
regression against 7,842 records in the projection run is not hidden by the
unchanged short-budget Arena classification totals. It is not a causal timing
ratio: the progress stream supplies CPU timestamps but no received wall times,
and this run has no continuous RSS sampling or per-case process journal.

All 3,903 progress events and the original full input were retained. Main and
frozen executable hashes remain equal and unchanged. The other 219 manifest
cases were skipped in this separate single-input run, not counted as passes.
See `build/reports/rocq-main-nat-order-init500-20261001/progress-summary.json`
and [the Nat-ordering record](ROCQ_NAT_ORDER.md) for evidence and limitations.

## Eager-Policy Main Run

The subsequent actual-main `a79d1272...` executable completes 9,546 Wire
admission records at fuel 16384, then times out after 500.020294 seconds.
The last started declaration is `Int64.toBitVec_div`, line 1137400; it is not
accepted. The preceding String bottleneck is passed, but the full Init file
still does not pass. Comparing the completed count with the preceding 3,902
records describes observed progress, not a causal or repeatable speedup.

This run records per-batch progress and 452 RSS samples. Maximum observed
checker RSS is 1,337,264 KiB, not an exact peak or an OS-enforced bound. There
are no RSS observation errors. The full progress stream is retained without
truncation; input, executable and frozen-source identities hold, and the owned
checker and driver cleanup are verified. The other 219 entries remain explicitly
unselected in this separate large-input run. The earlier full-Arena grind-ring-5
deadline regression remains unchanged by it.

Evidence: `build/workers/rocq-eager-policy/evidence/main-init500-20261001/progress-summary.json`.
Independent WHNF loop integration is a separate private candidate and is not
part of the executable measured here.
