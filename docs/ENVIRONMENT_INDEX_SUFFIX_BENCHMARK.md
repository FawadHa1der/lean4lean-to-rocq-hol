# Private Suffix Hash Benchmark

## Result

Six cheaper total Gallina hash candidates were compared with the **unchanged**
leaf16, rolling32, and constant-collision hash, using the same 1,957 actual names
as [the first index benchmark](ENVIRONMENT_INDEX_BENCHMARK.md). Every candidate
still uses the verified index API and complete structured-name equality inside
buckets. No production source, hash, extraction directive, or checker executable
was changed.

Both forward and reverse candidate orders completed successfully, with
**4,037,154 exact full-result comparisons**. The new twelve proof roots are
closed under the global context; `rocqchk` passed. Ordinary extracted ML/MLI
contain no `Obj`, unsafe casts, externals, assertions, failure stubs, or axioms.

On this dataset, **bitfold8 has the lowest lookup CPU cost**, while **last2 has
the lowest query allocation**. **parent2 reduces the worst bucket to 24 entries**
at a modest CPU/allocation premium. These are candidates for private integration
experiments, **not a production selection**. In particular, bitfold8 has only
256 possible string keys, so its collision cost can grow substantially in larger
environments. This experiment does not execute a kernel or establish an Arena
verdict for any new candidate.

## Inputs And Method

The exact 6,253,436-byte Init prefix ends at line 120590 and has SHA-256
`dce08f76af5892eda7110dc6b5d382d2a1a8cc07bcd8a0116b7e4b5d50a23877`.
It contains 1,704 declaration records, 107,797 expression nodes, and **1,957
distinct declared names** after expanding inductive-group member headers. Wire
metadata is NDJSON 3.1.0, Lean 4.34.1. Only names are used for this experiment;
declaration payloads are synthetic, with a serial tag that detects wrong shadow
selection in full-record comparisons.

The base environment is reverse wire/member enumeration, not a claim about the
kernel's internal environment order. The shadowed environment prepends 128 new
records for existing names: 2,085 entries and still 1,957 distinct names.
Each environment has three query groups, 1,957 queries each:

- Present names.
- Absent names formed by appending the original benchmark's fixed string component.
- Absent names preserving the final string/numeric component but replacing the
  parent with a fresh extended parent. This deliberately exercises leaf-hash
  buckets instead of only easy misses into empty buckets.

All expected results come from ordinary extracted `find_decl` over the same
dummy environment. Comparison is complete `option declaration` equality, not
just membership. Baseline construction checks presence/absence and newest-wins
shadowing. Each candidate is also checked after incremental `index_declaration`
updates, against the same shadowed baseline.

A separate **268-name adversarial dataset** includes anonymous and empty-string
names, literal dots versus structured components, string versus numeric zero,
NUL/255 bytes, unequal names sharing `XY`, 4,096-byte components, 128 identical
`mk` leaves under distinct parents, and 128 large numeric names with identical
low 16 bits. Its 536 present/absent queries, plus a replaced anonymous record,
are compared for each of nine hashes in each run. Constant0 forces every name
into one bucket. All comparisons pass.

Both runs use one binary. Candidate order is reversed in the second run; datasets
and query order are otherwise unchanged. Each measured phase performs at least
one workload and up to 32 repetitions, stopping once 0.15 CPU seconds elapse.
Fast phases hit the repetition limit sooner, so these are short measurements,
not confidence intervals. `Gc.full_major` occurs before, outside each timed
phase; collections during a phase are included. Allocation is
`minor_words + major_words - promoted_words`, avoiding double-counted promotion.
On this 64-bit OCaml runtime, one word is eight bytes. These are **total allocated
words, not retained heap or peak memory**.

The build/audit/two-run driver has a 145-second overall wall limit. It finished
in **46.598 seconds**. The measurement subprocesses took **13.221** and
**12.773 seconds**, both actual exit 0, neither timed out. Every child was reaped;
a process-table audit found no recorded child PIDs remaining.

## Candidate Definitions

All new hashes ignore ancestors unless explicitly described. Anonymous names
hash to zero. Numeric final components use `N.land value 65535`, ignoring their
parent, with an explicit bound proof. Collisions remain harmless to correctness.

| Candidate | String computation | Encoded key width |
| --- | --- | ---: |
| last2 | Scan without per-byte allocation; pack the final two bytes | 17 bits |
| last3 | Pack the final three bytes | 25 bits |
| last4 | Pack the final four bytes | 33 bits |
| bitfold8 | Rotate an eight-boolean state one bit and XOR each byte | 9 bits |
| bitfold16 | Alternate two byte states; rotate/XOR the older state with each byte | 17 bits |
| parent2 | Pack final two bytes of immediate string parent and final two leaf bytes | 33 bits |

Short strings are left-padded with zero bytes. Packing directly constructs
`positive` bits with a leading sentinel, avoiding arithmetic and normalization;
the widths include this sentinel. parent2 substitutes two zero bytes for an
anonymous/numeric immediate parent. It does not recursively hash the namespace.
The bit folds allocate one new `ascii` state per scanned byte, then pack only
the final state. No custom extraction mapping, machine-integer substitution,
unchecked cast, memo table, or trusted hash equality is involved.

There are nine bound/width lemmas, one theorem instantiating the generic lookup
refinement for all six candidates, and two computational collision examples.
All twelve roots were separately checked with `Print Assumptions`, reporting
`Closed under the global context`. The generic index theorem continues to hold
for **any** hash; none of these proofs assumes injectivity or collision resistance.

## Query Cost

CPU values are the min-max of forward/reverse runs, in microseconds per query,
for the 1,957-entry base environment. Allocations are forward-run words/query;
rounding includes the small batch-measurement overhead.

| Method | Hit CPU | Appended miss CPU | Same-leaf miss CPU | Hit words | Appended miss words | Same-leaf miss words |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Linear | 8.457-8.595 | 14.993-15.018 | 14.057-14.205 | 2.006 | 0.007 | 0.007 |
| leaf16 | 2.888-2.895 | 5.225-5.278 | 2.498-2.513 | 1707.548 | 6530.006 | 1705.548 |
| rolling32 | 8.614-8.659 | 22.760-22.924 | 24.984-25.222 | 6204.616 | 16203.170 | 17709.125 |
| last2 | 1.051-1.055 | 0.399-0.401 | 0.821-0.851 | 38.005 | 36.005 | 36.005 |
| last3 | 1.038-1.049 | 0.452-0.460 | 0.657-0.670 | 54.005 | 52.005 | 52.005 |
| last4 | 1.240-1.243 | 0.677-0.690 | 0.840-0.842 | 70.005 | 66.005 | 68.005 |
| bitfold8 | 0.782-0.795 | 0.357-0.376 | 0.472-0.472 | 100.495 | 335.005 | 98.495 |
| bitfold16 | 1.195-1.206 | 0.553-0.565 | 0.811-0.828 | 116.495 | 349.005 | 114.495 |
| parent2 | 0.979-1.063 | 0.739-0.770 | 0.796-0.807 | 75.662 | 72.067 | 73.140 |
| constant0 | 9.888-10.250 | 18.115-18.273 | 17.013-17.062 | 4.007 | 2.008 | 2.008 |

With 128 duplicate records prepended, selected hit CPU ranges are linear
9.039-9.216, leaf16 2.912-2.922, last2 1.101-1.112, bitfold8 0.833-0.834,
and parent2 1.052-1.055. Full shadowed results, both measurement orders, GC counts,
and hash-only timings are retained in the raw logs and JSON summary.

## Construction And Collisions

Forward-run index construction includes hashing and bucket-map allocation but
excludes dummy declaration creation. Collision excess is distinct names minus
occupied buckets, **not a pair count**; the 128 duplicate records are excluded
from distinct-name collision excess.

| Hash | Build CPU ms, base/shadow | Build words, base | Buckets | Collision excess | Max entries, base/shadow |
| --- | ---: | ---: | ---: | ---: | ---: |
| leaf16 | 6.662 / 7.013 | 3675064 | 1090 | 867 | 142 / 153 |
| rolling32 | 21.504 / 22.608 | 12576536 | 1957 | 0 | 1 / 2 |
| last2 | 1.343 / 1.434 | 310540 | 171 | 1786 | 288 / 306 |
| last3 | 2.085 / 2.210 | 369484 | 337 | 1620 | 152 / 163 |
| last4 | 2.986 / 3.154 | 435962 | 487 | 1470 | 152 / 163 |
| bitfold8 | 1.359 / 1.422 | 451697 | 252 | 1705 | 147 / 158 |
| bitfold16 | 3.203 / 3.346 | 555553 | 1089 | 868 | 142 / 153 |
| parent2 | 4.103 / 4.198 | 524686 | 923 | 1034 | 24 / 24 |
| constant0 | 0.028 / 0.031 | 21528 | 1 | 1956 | 1957 / 2085 |

bitfold8 is the CPU leader here, but a string-name environment larger than this
prefix must share its 256 string keys. last2 minimizes allocation but has the
largest nonconstant bucket in this sample. parent2 has more occupied buckets and
better worst-bucket size, despite some suffix collisions and extra scan work.
No candidate is adversarially collision resistant, and uniform query averages
do not measure tail latency or the actual kernel's hot-name distribution.
No end-to-end kernel speedup for the new candidates is inferred.

## Artifacts And Reproduction

All new benchmark sources and generated files are private under
`build/environment-index-suffix-benchmark/`; no files were added to shared
`rocq/` or `frontend/`. This document is the only new file outside that directory.

- [Gallina candidates](../build/environment-index-suffix-benchmark/EnvironmentIndexSuffixBenchmark.v).
- [Native benchmark](../build/environment-index-suffix-benchmark/environment_index_suffix_benchmark.ml).
- [Build/run report](../build/environment-index-suffix-benchmark/20260929T210512Z/report.json).
- [Validated summary](../build/environment-index-suffix-benchmark/20260929T210512Z/summary.json).
- [Forward measurements](../build/environment-index-suffix-benchmark/20260929T210512Z/benchmark-forward.log).
- [Reverse measurements](../build/environment-index-suffix-benchmark/20260929T210512Z/benchmark-reverse.log).
- [Assumption audit](../build/environment-index-suffix-benchmark/20260929T210512Z/assumptions.log).

Important SHA-256 values:

| Artifact | SHA-256 |
| --- | --- |
| New Gallina candidate source | `94e9758fac63e8d643d135030a8c39cb026aa292e1ddd15b912f76b19f9fa328` |
| New native benchmark source | `7d11f4142af52fa180825eed6f9feb337698d5f069b1b8f340205ce0d1fd7abf` |
| New extracted ML | `cc32c3dca7e2e839f1ad9e7a11f5650ca84f12d5954c6ce733965bc48fcb5621` |
| New extracted MLI | `5398ff492c113db6c2d37157d718ca8bc995f299c581898fb4fd99b31aca5afe` |
| Native benchmark executable | `7d25b94ed127f08db7a577d442d4d8a7943be3b82f63e2d855442cd1c29ea0e4` |
| Run report | `f5c31a8152641ba4f91eafef7a40a7b18c4e47d6e9c0b043abb461b800db0443` |
| Validated summary | `9daeb3944c9555ca6fb7e71c040644162b95c7cf80467346848b49d2ae7ec126` |

The unchanged baseline source is SHA-256
`6e7824e803e3b8615dca1d1dde7ae7c382f68740779a37eb5449c188daa58b77`;
its ordinary extraction exactly reproduces the first benchmark's ML hash
`e26b862e9842c1dbd4ae8e9b91f160bb7fda8950c1db1b8734ea643bfaf24737`.
Input, executable, and all source hashes matched before/after both runs.
Complete dependency/source hashes and executed commands are in the report.

From the project root, a separately authorized reproduction would run
`python3 -B build/environment-index-suffix-benchmark/run.py`, then
`python3 -B build/environment-index-suffix-benchmark/finish.py BUILD_RUN_DIRECTORY`.
The first command creates a new timestamped directory and enforces a 145-second
overall cap. The second audits assumptions and summarizes existing logs without
executing a checker or another benchmark. No full Init, CSLib, main-manifest,
production binary, production hash, or production module changes occurred.

## Small Environments And Preparation Follow-Up

The parent's corrected observation is important: `perf/refute-cheap-last` has
only seven declaration records. The earlier 1,957-entry build costs therefore
do **not** establish that repeated index construction caused its timeout.
Hashing each lookup in a small environment can also cost more than a linear
scan, even when an index has already been prepared.

A separately bounded private supplement used the **same audited extraction**
and first 7, 32, 64, 512, and 1,957 names of the Init benchmark. These are synthetic
lookup environments, **not a replay of `refute-cheap-last`**, and the size denotes
environment entries rather than wire declaration groups. It measured unchanged
leaf16/rolling32 and last2/last3/bitfold8/parent2 with three modes:
linear lookup, lookup through an already prepared index, and freshly preparing
the entire index before each batch of lookups.

Patterns are newest/middle/oldest single hits, a same-leaf single miss, and
8/64/512 evenly distributed hits. The first three refer to positions in the
reverse-enumerated synthetic environment; query positions are fixed, not a
kernel trace. Batches larger than the environment intentionally repeat names.

To avoid timing only a few nanosecond-scale operations, this supplement uses
adaptive chunks of 1-128 repetitions, targeting 0.04 CPU seconds per phase with
an approximately one-million-call cap. Clock polling is amortized across chunks.
Reported CPU and allocation include batch-loop overhead; they are **per wrapper
call**, not directly interchangeable with the earlier per-query large-batch
numbers. Full major GC remains outside measurement. This is one measurement
order, not a new confidence interval or measured optimal hybrid threshold.

### Seven-Entry Example

Middle-hit results, one query per call:

| Method | Already prepared CPU us | Prepare + lookup CPU us | Prepared allocated words/call | Prepare + lookup words/call |
| --- | ---: | ---: | ---: | ---: |
| Linear, no index | 0.0895 | Not applicable | 10 | Not applicable |
| leaf16 | 1.2429 | 8.3673 | 1608 | 9988 |
| rolling32 | 1.8262 | 19.2743 | 2282 | 23174 |
| last2 | 0.1343 | 1.0062 | 46 | 472 |
| last3 | 0.1919 | 1.5072 | 62 | 620 |
| bitfold8 | 0.1387 | 0.9855 | 102 | 808 |
| parent2 | 0.2282 | 2.1196 | 81 | 830 |

Even eliminating all preparation cost leaves leaf16 much slower than the linear
scan on these small keys. Cheaper hashes reduce that overhead but do not beat
linear in this particular seven-entry middle-hit measurement. This supports a
private small-environment linear-path experiment, not a causal diagnosis of the
actual negative case or proof that 64 is the best threshold.

### Amortization Examples

These CPU times are **microseconds per whole batch**, including a fresh index
for each indexed batch. Prepared-only timings and all other sizes/patterns are
in the raw log.

| Entries | Queries/call | Linear | leaf16 prepare + lookup | last2 prepare + lookup | bitfold8 prepare + lookup | parent2 prepare + lookup |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | 64 | 16.091 | 133.828 | 35.520 | 30.503 | 76.368 |
| 64 | 512 | 124.275 | 538.027 | 128.323 | 107.548 | 248.665 |
| 512 | 64 | 120.794 | 1197.324 | 310.748 | 294.741 | 814.255 |
| 512 | 512 | 936.349 | 1963.381 | 526.935 | 470.918 | 1219.152 |
| 1957 | 8 | 51.517 | 6784.667 | 1432.464 | 1364.633 | 4224.900 |
| 1957 | 64 | 551.781 | 7024.333 | 1469.143 | 1439.214 | 4274.300 |
| 1957 | 512 | 4776.556 | 8250.400 | 2052.300 | 1879.000 | 4782.889 |

At 1,957 entries, middle-hit index preparation plus lookup allocates about 3.68M
words for leaf16, 0.31M for last2, 0.45M for bitfold8, and 0.52M for parent2.
The cheap-hash construction improvements do not eliminate the need to amortize
preparation. Conversely, small-environment already-prepared lookup can still be
slower than linear. Environment size, query count, name structure, and query
distribution are separate factors; this benchmark does not select a production
hash or wrapper threshold.

### Follow-Up Integrity

[Report](../build/environment-index-suffix-benchmark/20260929T211612Z-prepare/report.json)
and [all 247 result rows](../build/environment-index-suffix-benchmark/20260929T211612Z-prepare/benchmark.log)
record **15,462 additional full-record comparisons**, all equal, plus found-count
checks for every timed batch. Full-record comparisons occur separately from
timing; timed batches check returned hit counts, not full records. The original
arbitrary-hash refinement proof is unchanged.

The measurement exited 0 after **19.732 seconds**; compilation and measurement
together took **20.450 seconds**, below the 145-second overall cap. No timeout
occurred. The bounded subprocess helper reaped all children, and a final process
search found no prepare benchmark or driver still running. Input, binary, and
source hashes matched before/after. No kernel or Arena checker was run.

New private files are `environment_index_prepare_benchmark.ml`,
`run_prepare.py`, and the timestamped run directory under the same benchmark
root. The shared Gallina, frontend, hash candidates, and prior reports are untouched.

| Artifact | SHA-256 |
| --- | --- |
| Prepare benchmark source | `331304d8f3acd6fd5608994fef6ea36f3093ac563640da4a5167af88d7ffcbd1` |
| Bounded driver | `6efbe8611441218b65e0bb11f3138e3e39d214608abc02e90b7e3d9ab9054276` |
| Prepare benchmark binary | `fb53abc35c6ef30cefceb63cada7a20283669f28244ef98c12267b9b2f42f77f` |
| Prepare report | `d1bff0ec868d72d253d774c040fd6820de14fedb60576c797c307e8b6f820520` |
| Prepare measurement log | `0d3929731cbe03c12234054b34696b97113abe24c0ef54115f7d45841897fad5` |
