# Core Performance Findings

Bounded profiles separate transport, environment lookup, query-cache lookup,
and core expression work. They do not establish that a timeout is a logical
rejection or that optimizing a sampled hotspot improves end-to-end checking.

## Closed Substitution Candidate

The immutable private experiment is
`/private/tmp/rocq-core-stall-20260930T1342Z`. It starts from the older
`2daf6e33...` executable, not the later persistent-state runtime.

The original `magma-list-pair-n7` attempt spends substantial sampled time in
lifting, substitution and garbage collection. A candidate classifies beta
arguments by Gallina `scoped 0` and reuses closed replacements under binders.
It proves syntactic equality for arbitrary expressions, argument lists and
indices, then same-fuel complete-result refinement for the lookup checker.
The ordinary Checker is unchanged; no frontend closedness flag is trusted.

All 70 candidate modules pass independent kernel rechecking without added
axioms, type-in-type, unsafe fixpoints or assumed positivity. The candidate
passes 125,888 native substitution comparisons, five Rocq computational
examples and the nine existing native regression suites. A repeated-closed-
argument allocation control uses 7,344 bytes instead of 790,656 bytes.

Nevertheless, the authentic magma input still reaches the 30-second cap at
line 11031, after 275 declarations, in `countermodel`. Sampled peak process-group
RSS is higher (1,080,592 KiB versus 827,168 KiB). Closedness scanning becomes a
new hotspot. These unfinished, sampled executions are not a controlled speed
comparison. **The candidate is not integrated as a performance fix.**

Eager classification scans unused arguments and can revisit shared syntax.
Further work must address this cost rather than counting the allocation
control as resolution of the Arena case. The final audit and all draft proof
failures are retained; 172 recorded processes are reaped, with no surviving
owned process groups.

## Context Query Cache

The same investigation locates `fueled-chain` at line 11792 after 140 checked
declarations, in `chain9_datF`. Its five-second sample contains 4,091 stacks,
with 2,496 top-of-stack observations in positive-key equality and 961 in
context-path equality. The existing cache discriminates by node identity and
path length, then compares entire same-length context paths.

Two private follow-ups are complete, and neither is integrated. Both retain
exact structured-path equality, optional let-value IDs, newest shadowing and
proved same-fuel complete-result refinement. Hashes only choose candidate
buckets; they never authorize a hit or assume collision freedom. This cache is
distinct from the persistent declaration environment index.

The arithmetic discriminator in
`/private/tmp/rocq-path-content-20260930T1424Z` independently checks 77 modules
and passes 35,891 new assertions plus twelve existing native suites. It reaches
`chain12_datF` after 142 admitted declarations, versus the baseline's 140 at
`chain9_datF`, but both whole-case runs time out. Earlier common-prefix CPU and
sampled peak RSS increase, and constructing the discriminator is costly.

The constructor-only replacement in
`/private/tmp/rocq-path-bits-20260930T1500Z` avoids binary-natural arithmetic.
It independently checks 78 selected roots, passes all thirteen existing native
suites and 36,411 new assertions, and proves the fixed-width representation in
Gallina. The old bucket-identity example is explicitly tested against the old
implementation; new collision controls exercise the replacement. It again
reaches 142 declarations while both executions time out. The common earlier
`chain6_datF` segment increases from 0.981 to 1.326 CPU seconds, and sampled
peak RSS from 1,401,568 to 2,631,840 KiB. Its predeclared acceptance policy
therefore rejects integration. These are single bounded comparisons on an
otherwise uncontrolled host, not repeatable speed measurements.

All authentic executions above use fuel 16384, a 30-second wall cap, an 8 GiB
sampled RSS stop threshold and a 64 GiB disk reserve. Sampled RSS limits are
not OS-enforced bounds. No full-library or full-Arena success is claimed.

## Current Init Attribution

The sealed current-runtime attempt is
`/private/tmp/rocq-853-init-profile-20260930`. It uses native SHA256
`853e4eae7d746df50eb9c65d70e094652999c0dec545bee239a8be035720eb29`,
the complete 347,555,345-byte Init input, fuel 16384, progress on every batch,
and the published 500-second cap. It times out at 500.011677 seconds.

Exactly 3,224 preceding records are admitted. The next singleton theorem is
`Int64.toBitVec_shiftLeft`, line 250275, name 21037, type 225902, value 225905.
It starts at 40.240 CPU / 40.446691 received-wall seconds and never emits a
later progress event. Checking begins at 30.763 CPU / 30.924602 wall seconds.
The target is not admitted. The earlier progress-100 run's anchor at record
3200 was a lower bound, so this does not show a newly passed earlier stall.

All 317 snapshot pins hold; peak sampled aggregate RSS is 872,864 KiB. The
native checker, driver and sampler are reaped. A byte-exact source-only prefix
package retains the first 250,275 lines, 13,083,032 bytes and 3,225 batches;
its SHA256 is
`1ce2a34881013b1793fcb6c9c8ef14108af919a612b1dff7ea756507e55db453`.
The package itself was not executed in this full-input run.

### Truncated Sample Correction

The sampler exited zero but reported `fwrite: File too large` and inability
to write its output. Its 16,777,216-byte file ends inside the call graph.
**The sealed report's leaf counts and percentages are unreliable and must not
be used as a quantitative performance result.** The original evidence remains
unchanged. Exact declaration attribution above comes from native progress,
not from those percentages. Visible repeated recursor/WHNF frames are useful
qualitative observations only; callback return addresses are not evidence of
exclusive CPU spent in the named caller.

The old summarizer completed pending tree nodes at EOF, incorrectly assigning
missing descendants to their ancestors. Its leaf-total/root-total equality
could still hold on this incomplete tree. The repaired helper requires the
explicit call-graph terminator and rejects partial or unknown graph lines.
Twenty-five helper tests pass, including seven new completeness controls.
`build/reports/rocq-profile-completeness-audit-20260930.json` additionally
records read-only checks: the actual truncated sample is rejected, all four
complete historical repository samples parse successfully, and all five input
hashes remain unchanged. This fix changes reporting only, not either checker.

## Direct Callback Diagnostic

`/private/tmp/rocq-init-callback-diagnostic-20260930` preserves exactly one
60-second run of the current executable on the dependency-audited 13 MB prefix,
and one 60-second diagnostic-only instrumented build. Both admit 3,224 batches,
start the target theorem, and time out. Neither accepts the prefix. All 74
Gallina files and the frontend remain unchanged; only a private generated
OCaml implementation is instrumented, and it is not a production payload.

In the instrumented target interval, 21,365,004 method calls begin and
21,364,468 complete at the last checkpoint. Nearly all are WHNF/core-WHNF;
there are only 167 defeq starts. The observer records 168,165 repeated queries
with a prior completion and an exactly identical complete physical key.
It reuses no result. Heavy eviction and distinct allocations make this a
lower bound, not a cache-hit forecast or a measurement of potential savings.

All 25,758,636 observed declaration lookups use actual indexed collision
buckets, with 1,466,518,204 visited nodes: 56.93 per call on average, maximum
194. No direct whole-environment route is observed in this target interval.
These counters establish bucket work but do not attribute exclusive CPU time.
The diagnostic changes allocation and timing. Thirty-eight observer assertions
and 19,152 small complete-result comparisons pass; all forty recorded process
groups are reaped. The truncated stack percentages above are not used.

The investigation identified a separate source-level gap: `frontend/wire.ml`
parsed reducibility hints, but the Rocq representation did not retain them. The
old ordinary and accessor lazy-delta loops therefore unfolded both delta heads,
unlike pinned upstream's hint-based priority. The target theorem is an `rfl`
lemma in upstream `Init/Data/SInt/Bitwise.lean`. The subsequent hint integration
below addresses this gap; the original observation alone did not diagnose it.

## Existing Parent2 Index Experiment

The sealed `/private/tmp/rocq-parent2-prefix-20260930/REVIEW.md` evaluates the
already defined `suffix_parent2` hash, with ordinary extraction and the existing
arbitrary-hash refinement proofs. All 76 modules, thirteen existing native
suites, and 584 added assertions pass. Exact name comparison still resolves
collisions; no hash equality is used as an equality witness.

The sole 60-second authentic prefix run again admits 3,224 records and starts
`Int64.toBitVec_shiftLeft`, without admitting it. Its progress sequence matches
the held exact-853 run. Target-start CPU changes from 10.019 to 14.283 seconds;
sampled peak RSS changes from 85,568 to 78,096 KiB. There is no additional
authentic progress, so the candidate is rejected for integration. The held
baseline was not rerun. These single-run observations do not establish stable
performance ratios or measured reductions in collision work.

All 156 recorded build/test/audit/run groups are reaped, and main plus earlier
holds remain unchanged. The candidate introduces no new hash design, result
cache, or reducibility change. Hint transport and lazy-delta priority were
implemented and reviewed separately, without importing this rejected hash change.

## Integrated Hint Strategy

The hint candidate retains exact declaration metadata and implements upstream
two-head delta priority and the regular-hint congruence restriction. Its sole
60-second private prefix attempt completes all 3,225 declarations in 10.8658s,
including `Int64.toBitVec_shiftLeft`. The input is the same pinned13 MB prefix,
not full Init. No component-isolated or whole-library speedup is inferred.

The actual main rebuild produces `acd3d008...`, byte-identical extraction to
the reviewed candidate, fifteen passing native suites and an independent
75-module audit. The full available inventory records117accepts,71rejects,
18either,10timeouts and4missing. Only `grind-ring-5` crosses the30-second
deadline to acceptance; full Init still times out at that exploratory cap.
A separate 500-second actual-runtime Init attempt completes 9,546 Wire admission
records and times out after starting `Int64.toBitVec_div` at line 1,137,400.
The old `Int64.toBitVec_shiftLeft` target demonstrably completes in this full
input, not just in the prefix. The final 37.104 seconds have no next-batch event;
that is a censored active batch, not a stack-profile attribution or full pass.
See [the complete hint integration report](ROCQ_HINTS.md), including remaining
upstream scheduling differences and the distinction between new-ordinary
refinement and an overall Lean soundness theorem.
