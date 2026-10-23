# Persistent Admission

The default Rocq runtime now retains its declaration environment and lookup
index across successful admissions. The state and its invariant are defined
in Gallina; handwritten OCaml does not supply an index, lookup function, or
list of declarations to commit.

## Invariant And Semantics

`PersistentIndex.v` defines an immutable proof-carrying environment/index
record. Initialization and extension establish lookup equality for every
structured name and every total hash function, including a constant hash.
Collisions are resolved by structured-name equality. Newest-first shadowing
and complete declaration metadata are retained.

`AdmissionDelta.v` obtains precisely the newly admitted declarations from the
ordinary, quotient, inductive and mutual paths. It proves that reattaching the
old environment reconstructs each complete original result. This includes
the transformed-and-restored nested-inductive route, not just simple records.

`PersistentAdmission.v` combines these facts with the DAG refinement. Its
`initialized_stream_refines` theorem holds for arbitrary initial environments,
request streams, fuel and hash functions. It compares complete results,
including error payloads, against the current reference checker. Separate
corollaries connect DAG requests to the corrected ordinary checker and the
new linear-cache implementation. These are not old-String-semantics theorems.
Rejected and declined transactions return exactly their previous state.

The index is used for DAG admission with positive fuel and at least 64 existing
declarations. It is maintained even below that threshold. Other checking paths
retain their ordinary semantics and can still perform linear lookup. No
constant-time complexity, reduced allocation, or whole-checker speedup is proved.

## Extracted Boundary

`ArenaExtract.v` remains the runtime extraction owner. The frontend accesses
state through the abstract `Persistent_adapter.State.t` and commits only the
state returned by an extracted successful admission. Rocq proofs in Prop are
erased by normal extraction; no claim is made for an OCaml caller forging the
erased record through another interface. Parser correctness, compiler and
runtime behavior remain separate trust boundaries. No custom extraction
representation, assumed lookup correctness, or unchecked cast is introduced.

## Verification

The project-directory build compiles 74 Gallina modules and passes twelve
native suites across 56 bounded compile/link/test steps. Before/after source
hashes agree and all children are reaped:

`build/reports/rocq-native-20260930T141052Z-79013/report.json`

Three new suites supply complementary, overlapping regression evidence:

- Persistent refinement: 127,272 assertions, including 2,970 full-result
  comparisons and 123,996 lookup comparisons.
- Abstract runtime adapter: 664 assertions, with accepting, rejecting and
  declining batches and rollback checks.
- Persistent streams: 52,776 assertions, including 1,448 full results and
  51,126 lookups. True nested Box/Tree controls check restored recursor names,
  absence of auxiliary leakage and metadata mutation rollback.

String regressions preserve the seven intentional changed observations against
the frozen old semantics; neither those changes nor overlapping assertion
counts are extra Arena files.

Independent kernel rechecking and conservative source scans pass in
`toolchain/logs/audit-20260930T141200Z-98582`. The assumption summary reports no
axioms, type-in-type, unsafe fixpoints or assumed positivity.

Persistent-only executable SHA-256 for the Arena evidence below:
`cd06e5a0241562d1f79b465ee484e5d32a9f392882e8562025e98fd007baa12e`.
Extraction SHA-256:
`444bfb9f53e0c3c2a7aab2f0c9ef61e97e86e647645670b67503c37e05ed481b`.

The separate all-216-available Arena attempt on an unchanged copy of this exact
executable is complete: 117 correct accepts, 71 correct rejects, 18 allowed-
either outcomes, ten timeouts and four missing inputs. All 220 inventory rows
are reported at fuel 16384 with a 30-second exploratory cap, not the published
library budgets. No wrong verdict, checker fault, explicit decline, skip or
integrity failure was observed. The legacy SIGKILL-derived fault field in timeout
rows is overridden by their explicit timeout status; it is not a checker fault.

`perf/grind-ring-5` is the only changed classification: it checks all 2,273
declarations and accepts in 28.103904 seconds. The private persistent build
and the previous shipped binary timed out in their respective runs. This is
one observed deadline crossing, not a controlled speedup or causal attribution.

The ten unresolved inputs are CSLib, Init, Std, fueled-chain and the six magma
list/string performance cases. Complete large files were supplied, not prefixes;
their last retained events are parsing or scheduling, with zero declarations
checked at the short cap. Cedar, Con-Leche, Mathlib and NavierStokesEuler remain
unavailable. They are not replaced with generated substitutes or counted as passes.

Reports copied into the project are
`build/reports/rocq-shipped-persistent-arena-30s.json` and
`build/reports/rocq-shipped-persistent-arena-summary.json`. The complete immutable
closure and audits remain at
`/private/tmp/rocq-shipped-persistent-arena-validation-20260930`.
All 428 private snapshot files and all available input hashes held. All 216
native groups and the preflight/driver were reaped and absent in the final
process audit. Thirteen guard/evidence tests passed. Peak sampled group RSS was
3,248,752 KiB; the 8 GiB sampled stop threshold is not an OS-enforced bound.

None of these refinement, build or testing results proves overall Lean typing
soundness.

## Full-Budget Init

One complete 347,555,345-byte Init input was subsequently checked using this
frozen `cd06e5a0...` executable, fuel 16384 and the published 500-second budget.
It timed out at 500.010633 seconds after at least 3,200 admitted declaration
records. No logical verdict or out-of-fuel message was emitted. The last
progress event arrived at 48.761267 wall seconds, before the declaration at
line 249099 (`BitVec.sub`). Because progress is reported before admission and
only every 100 admitted records, this is a lower bound, not the exact stalled
declaration, nor evidence that `BitVec.sub` was accepted.

Checking began at 39.394 CPU seconds after 8.812 seconds of parsing and 30.577
seconds of scheduling. The later scheduler executable was not used. The bound
exceeds the historical unindexed 1,703-record point but not the intervening
bitfold8 run's 3,200-record bound; differing implementations and fuels prevent
a causal performance comparison.

All 437 snapshot files and the full input held through final audit. Peak sampled
RSS was 712,672 KiB; no memory/disk stop occurred. All owned processes were
reaped and absent. Seven resource-guard and eight source-attribution tests pass.
No Std/CSLib attempt or retry was made in this experiment. Full evidence is in
`/private/tmp/rocq-shipped-persistent-init-20260930/CHECKPOINT.md`, with the
project copy `build/reports/rocq-shipped-persistent-init.json`.

The later transport scheduler integration retains the Gallina extraction but
rebuilds the executable. See [the scheduler report](REPLAY_SCHEDULER.md) for
its identity, thirteen passing native suites and separate Arena validation.
