# Replay Dependency Scheduling

`frontend/replay.ml` performs transport scheduling and mutual-definition
batching. It does not type-check, authorize a declaration, infer a logical
verdict, or consult Arena expectations. Every input declaration record must
reach the kernel exactly once, either singly or in its checked mutual batch.

## Preparation

Preparation indexes every declared name, including all members of an inductive
record. It rejects duplicate declaration names and validates the existing
partial/unsafe mutual-group rules before choosing a scheduling strategy.
Noncontiguous mutual definitions are collected into a single batch; each
original row receives that batch's owner index. Missing members, duplicate
members, overlapping groups, and inconsistent member lists remain errors.
Safe definitions' and opaque declarations' `all` lists do not create admission
groups. This optimization does not change those rules or safety decisions.

## Checked Input Order

The fast path computes this summary for each physically shared expression:

```text
summary(e) = maximum batch-owner index referenced anywhere in e
             (-1 when no declared dependency occurs)
```

The cache is local to one scheduling call. It cannot leak summaries between
exports or between different owner maps for the same expression objects.
An iterative postorder traversal computes each reachable expression summary
once, reusing summaries across declaration roots. It does not consume the
native call stack in proportion to expression depth. No wire representation
or parser change is needed.

For batch `i`, all declaration roots and declaration-level implicit dependencies
must have summary at most `i`. Then every non-self dependency precedes that
batch, so returning the input batch order is topologically valid. Self edges
are allowed here exactly as in the original scheduler; the kernel still checks
self-reference and mutual-recursion legality. Unknown names contribute no
transport edge and remain unknown-constant obligations for the kernel.

This is a check of the actual parsed DAG and complete declaration-owner map,
not an assumption that the exporter emits dependencies first. In particular,
a later source row belonging to the same noncontiguous mutual block is a
self edge, while a dependency on another later batch forces graph scheduling.

The dependency roots are unchanged:

- Every declaration header type, including inductive, constructor, and
  recursor header types.
- Definition values, theorem proofs, and opaque bodies.
- Every recursor rule right-hand side.
- All expression children: application, lambda/Pi domains and bodies, all
  three let children, projection arguments and owning type names, and metadata
  wrappers. Constants contribute their declaration owners.
- Natural literals: `Nat`, `Nat.zero`, `Nat.succ`.
- String literals: `String`, `Char`, `Char.ofNat`, `String.ofList`, `List`,
  `List.nil`, `List.cons`.
- Every quotient declaration kind additionally depends on `Eq`.

For a topologically ordered DAG, traversal work is proportional to reachable
nodes, child edges, and declaration roots, assuming ordinary hash-table
behavior. The cache uses physical equality and the existing structural hash;
pathological hash collisions can still degrade this bound. Existing grouping
and name-comparison costs are unchanged.

## Exact Fallback

If any summary identifies a forward dependency, the fast probe stops and the
existing dependency-set/Kahn implementation schedules **all** batches. Its
dependency construction, queue order, self-edge exclusion, and cycle diagnostic
are preserved. It reports a cycle outside a checked mutual block rather than
silently omitting unscheduled records. The summary cache becomes collectible
before fallback graph construction.

A maximum is not an edge set, so it is never used to reconstruct or approximate
the fallback graph. Forward-reference inputs can cost the original graph pass
plus the failed probe prefix. When input order is already topological, returning
it can differ from Kahn's queue order. For example, independent `a`, then `b`
depending on `a`, then independent `c`, can produce `a,b,c` instead of `a,c,b`.
Both orders preserve all declarations and satisfy every dependency.

## Interface And Tests

The production entry point remains `Replay.schedule input : batch list`.
`schedule_with_stats ?force_graph input` additionally reports `Input_order` or
`Dependency_graph` and the number of unique expressions summarized by the
probe. `force_graph=true` is only a diagnostic/test control to select the full
graph path; it cannot force an unchecked fast path. No adapter or main-program
changes are required.

`frontend/test_replay.ml` passes **279 checks**. These include the original 25
checks under both automatic and forced-graph scheduling, all expression forms
and declaration roots, every implicit dependency listed above, self/missing
references, noncontiguous mutual ownership, exact malformed diagnostics,
physical record-identity coverage, and cache isolation across owner maps.
An exponentially expanded shared DAG referenced by 1,000 declarations needs
only 130 unique summaries. Both paths handle depth-20,000 expressions without
recursive traversal. Fifty deterministic generated DAGs are checked in sorted
and shuffled order against independent edge lists and exact record coverage.

These are transport tests, not proof-assistant soundness proofs or logical
Arena results. The kernel receives unchanged declaration payloads, and no
logical validation is skipped.

## Init Profiling

The bounded comparison uses the exact imported Init export:

```text
arena/large/exports/init.ndjson
bytes: 347555345
sha256: 620502ac9e63ba4a2dea9d46386c2f6aebc49faf8848ea3aaa18a77a09491a6a
expression nodes: 6132277
declaration records: 58170
```

Baseline and optimized native frontend binaries are built with the existing
project toolchain in `/private/tmp/replay-benchmark.tNseei`, not in the shared
Rocq or HOL binary locations. Runs are sequential and bounded by 120 seconds
wall time and 110 seconds CPU time per child process group. The profiling
wrapper disables core dumps and kills the process group on wall timeout.
Maximum RSS is measured, not hard-limited. Parsing is included in total time
but separated from scheduling CPU time. A successful profile is explicitly
**not a logical acceptance**.

One clean sequential comparison on 2026-09-29, using identical wire sources:

| Measurement | Saved baseline | Optimized |
| --- | ---: | ---: |
| Parsing CPU seconds | 8.297 | 8.049 |
| Scheduling CPU seconds | 40.099 | 26.531 |
| Total wall seconds | 48.597 | 34.879 |
| Maximum resident memory, MiB | 728.45 | 695.33 |
| Batches / covered declaration records | 58170 / 58170 | 58170 / 58170 |
| Exit status | 0 | 0 |

The optimized run selected `input_order` and summarized all 6,132,277 expression
nodes. Scheduling CPU time was **33.8% lower** in this comparison. This is one
optimized measurement on a shared machine, not a guaranteed speedup. It still
took about 34.9 wall seconds for transport alone: a 30-second Arena test cap
may expire before logical checking begins. That is a resource timeout, not a
logical acceptance, rejection, or completed check.

An earlier baseline completed scheduling in 37.822 CPU seconds, but its
`/usr/bin/time -l` wrapper exited with a sandbox-denied `sysctl` error after
printing the completed profile. It is not the table's baseline. The clean
comparison above uses Python `resource.getrusage` and a monotonic wall clock;
both runs exited zero. No timeout or checker verdict was produced by these
transport-only runs.

Source SHA-256 handoff (optimized source copies match the shared files):

```text
baseline replay.ml
434a26dcdbd92f626f7afc2bbe90497df53a09f4ad0fb3b5895cb8179bbb6801
optimized frontend/replay.ml
4be904adc035610223b13f71479da21969729f40a4142b80374d4b5e50ddb228
frontend/test_replay.ml
55fa611d412cec743b40e8e3393f87e715079eefb3e9b739eb3323dc03082eba
unchanged frontend/wire.ml (both builds)
4e204f626e9dd61a049c5d1bc60b2aaaddab597e7770e0922c68fa017d82d802
baseline/inspect_replay binary
5ab60292e93cdc86fdb0de35ef7a32e0e944c2e718c25a80e47ecab20212d2a5
optimized/profile binary
90acb1884ab9a42b79ede74ace776f8d0c4b387a0e762ef819f2471d5db7abae
```

The input checksum was rechecked after profiling and matches the published
checksum above. The optimized binary, including the summary traversal tested
by all 279 checks, predates the parent's active Arena run. No further source
optimization or native build was performed after the parent requested a build
hold. The already-running baseline profile was allowed to finish; all profiling
subprocesses have now exited.

Build integration remains parent-owned; the parent reports that the integrated
279-check suite passed. The normal frontend build order is
`wire.ml`, `replay.ml`, then `test_replay.ml` or `inspect_replay.ml`. This change
does not edit the build script, wire parser, main program, adapters, or either
proof-assistant core.
