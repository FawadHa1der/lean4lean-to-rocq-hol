# Dependency Scheduling

The scheduler is an unverified transport component shared by both ports. It
groups explicitly mutual declarations and orders dependencies; it never decides
typing, trusts expected Arena outcomes, or omits declarations from checking.
The reviewed scheduler is now integrated. Historical candidate results below
do not automatically become results for the newly rebuilt executable.

Current main executable SHA-256 is
`853e4eae7d746df50eb9c65d70e094652999c0dec545bee239a8be035720eb29`.
All thirteen native suites pass across 60 bounded steps in
`build/reports/rocq-native-20260930T144114Z-16001/report.json`.
The 74-module audit passes in `toolchain/logs/audit-20260930T144212Z-18766`;
the shared HOL transport rebuild passes 67 checks. The permanent scheduler
comparison has 2,006 assertions; its frozen reference is not linked into the
production checker.

## Actual Shipped Binary

The exact `853e4eae...` executable has now completed one full available-corpus
attempt at fuel 16384 and 30 seconds per case: 116 correct accepts, 71 correct
rejects, 18 allowed-either outcomes, eleven timeouts and four missing inputs.
All 216 available files were launched; all 220 manifest rows are reported.
No wrong logical verdict, checker fault, explicit decline, skip or integrity
failure occurred.

`perf/grind-ring-5` is newly undecided against both references below: it times
out at 30.005683 seconds instead of accepting at 28.103904 (cd06) or 28.841682
(private 3a). This is a real deadline-classification regression in this attempt.
No repeatability, cause, or general slowdown is established by one observation.
There are no other outcome or terminal-diagnostic changes. Raw CPU progress
timestamps differ in 163 rows and remain available in the audit.

The private 3a Init progress described below did not reproduce on the shipped
binary: 853 reports scheduling with zero checked declarations at timeout.
CSLib and Std also time out, during parsing and scheduling respectively.
All complete input files were supplied; no full library verdict is established.

All 300 frozen snapshot files and all inputs held. All native groups, preflight
and driver were reaped and absent in final enumeration. Thirteen guard/evidence
tests pass; peak sampled group RSS was 3,248,848 KiB with no resource stop.
Reports are `build/reports/rocq-shipped-replay-arena-30s.json` and its matching
summary. The full immutable audit is at
`/private/tmp/rocq-shipped-replay-arena-validation-20260930/CHECKPOINT.md`.
This result supersedes private timings as current-executable Arena evidence;
it does not invalidate the transport differential tests.

## Prior Private Composition

A full private composition with the same persistent extraction and scheduler,
binary `3a277830a1b642c3d2bd6244c11db3b38754466a3a1b7f4552b56b252ea8039e`,
records 117 correct accepts, 71 correct rejects, 18 either outcomes, ten timeouts
and four missing inputs. All 216 available files are attempted at fuel 16384
and 30-second caps. Classifications/stdout match the preceding cd06 main run;
all source/input pins hold and children are reaped. Init enters kernel checking
near 29.94 seconds and reports 200 declarations before timeout, not acceptance.
Evidence is in `/private/tmp/rocq-replay-persistent-20260930/reports/arena-v2.json`
and its matching audit. Initial symlink-boundary and patch-format/build failures
remain retained and excluded; no safety or integrity guard was relaxed.

## Bottleneck And Change

A bounded transport-only Init profile parsed 6,132,277 expression nodes and
58,170 declaration records in about 8.5 CPU seconds. Its existing input-order
check then took about 29.5 additional CPU seconds. The physical-identity cache
had a maximum bucket length of 31,843 despite more than four million buckets.

The candidate carries completed child dependency summaries on an explicit
value stack instead of looking them up again. Its physical-key hash examines
a larger but still bounded structural prefix. Physical identity still decides
equality: neither a hash collision nor the dependency summary is a proof.
Both changes are local to transport. All expressions remain in the exact
declarations subsequently sent to the actual checker.

One exploratory combined run took 29.5 wall seconds for all Init transport,
versus 38.6 for the old route. It summarized the same number of nodes and found
the same input order. This is a preliminary local timing, not a controlled
throughput benchmark or an Arena proof-checking pass. End-of-phase reserved
OCaml heap words were higher in the candidate; no memory improvement or
adversarial constant-time bound is claimed.

## Verification

The stable candidate is `/private/tmp/leanport-replay-candidate-20260930`.
Its `replay.ml` SHA-256 is
`1cd3f700309683cdd4c1f858a0dfeb177c22a6e938b17fff5f4868e99901921e`.
The old scheduler is retained separately for exact differential comparisons.

- Existing scheduler suite: 279 checks pass.
- Independent old/new comparisons: 2,006 assertions pass, including generated
  dependency graphs, cycles, 20,000-level syntax, repeated shared subterms,
  exact errors, node-summary counts and ordering classifications.
- All 213 available nonlarge Arena files have identical old/new schedules or
  transport errors. Three large exports and four unavailable files are
  explicitly unselected in that report.
- A separate Init comparison verifies the complete 58,170-record schedule,
  not just its size, with stable input/source/binary hashes. It completes in
  61.3 seconds for both algorithms together.
- The corresponding Std comparison reaches its 120-second wall cap without
  producing a comparison result. It was terminated and reaped; neither Std
  schedule equivalence nor a Std logical verdict has been established by it.
  CSLib has not received this exact large-file differential comparison.
- The candidate HOL transport build passes 67 checks.
- A separately linked Rocq candidate correctly decides all 188 selected Arena
  tests: 101 accepts, 69 rejects and 18 allowed-either outcomes. There are 32
  explicitly unselected entries, no timeout, wrong verdict or integrity failure.

Transport matches are not logical acceptances. The selected logical test report
does not replace the full-corpus report for the shipped executable. Candidate
native SHA-256 is
`e5b193b97068c75a54d03295371fb1f8cc69f1e20d03b7c29eb92fe4a3e65d88`.

Evidence is retained in `validation.json`, `init-exact-comparison.json`,
`std-exact-comparison.json`, and
`rocq-selected-arena.json` below the private candidate directory. Initial
profiling variants and observations are separately retained in
`/private/tmp/leanport-replay-profile-20260930`. A first private link failed
because independently compiled Wire interfaces differed; recompiling both
adapters against the same private Wire interface fixed the build. That was a
build consistency failure, not a logical checker result.
