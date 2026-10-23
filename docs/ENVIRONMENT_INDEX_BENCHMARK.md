# Environment Index Benchmark

## Scope And Result

The parent's proved `EnvironmentIndex.v` API was benchmarked in isolation against
ordinary extracted `find_decl`, using actual names from the byte-exact Init
prefix ending at line 120590. **No production environment, Syntax, Checker,
build script, manifest, or checker binary was changed.**

All **164,388 full-record lookup comparisons** matched, including absent names,
constant-hash collisions, duplicate shadowing, and incremental insertion.
The native benchmark finished successfully in **7.447 wall seconds**, with no
timeout. Declaration types/payloads are synthetic: **this is not kernel checking,
an Arena verdict, or additional corpus acceptance.**

Full-name 32-bit hashing eliminated collisions on this dataset but did not give
a useful general lookup improvement: absent queries became slower. Leaf-only
16-bit hashing was fastest, at roughly 3x the linear baseline on uniform queries,
but had substantial collisions and much higher allocation. These measurements
support further design evaluation, not automatic production integration.

## Extraction Safety

The benchmark module uses only `Extraction Language OCaml` and ordinary
`Extraction` of the API and hash definitions. There are **no custom constant,
integer, string, inlining, or representation extraction directives**.
Generated `.ml` and `.mli` files live only under the dedicated build directory.
Their mathematical 16/32-bit hashes use **structurally extracted binary `N`**,
not machine-word OCaml integers.

Before native compilation or execution, both generated files were scanned for
`Obj`, unsafe operations/casts, `external`, `assert`, `failwith`, and unrealized
axiom stubs. **No matches were found.** A second check immediately before native
compilation also verified their hashes. No extraction-cast blocker was found for
this concrete FMapAVL extraction; switching to FMapPositive is not required to
address a cast in this artifact. The eventual production extraction must be
audited independently; this is not a blanket statement about other extraction
roots or the OCaml runtime.

All three copied Gallina modules compiled, and independent `rocqchk` of
`LeanPort.EnvironmentIndexBenchmark` passed in 17.775 seconds. The new module has
eight proved hash-bound lemmas/corollaries and three lookup-refinement corollaries
using the parent's theorem, with no added axioms or trust settings. The parent
module's existing constant-collision/shadowing proofs are also imported and
checked. An initial over-simplified bound proof failed compilation; it was fixed
in the new benchmark module only, and the failed build log is retained.

## Dataset And Method

- Input: 6,253,436 bytes, NDJSON 3.1.0, exported using Lean 4.34.1.
- **1,704 wire declaration records / 1,957 unique declared names**, including
  inductive type, constructor, and recursor member names; 107,797 expression nodes.
- Base environment: one synthetic declaration per name, in reverse wire
  declaration/member enumeration order. This is not a claim of reproducing the
  production environment's exact internal member ordering.
- Shadowed environment: 128 evenly selected source names are prepended again
  with distinct serial payloads; 2,085 entries, still 1,957 distinct names.
- Each dataset has 1,957 present queries and 1,957 absent queries. Each absent
  name appends the fresh string component `_environment_index_benchmark_absent`
  to a real name. The linear baseline verifies that all constructed misses are
  absent and that all duplicates return the newest payload.
- Every candidate result is compared structurally with the complete declaration
  option returned by `find_decl`, not just presence or name. Fresh indexes are
  checked on all 3,914 queries; shadowed indexes are additionally constructed by
  incremental `index_declaration` calls and checked on every query again.
- The 164,388 comparisons comprise 148,732 adaptive repeated validations plus
  15,656 incremental-shadow comparisons. There are eight candidate/dataset pairs.

CPU uses `Sys.time`; wall time uses `Unix.gettimeofday`. Allocation is
`minor_words + major_words - promoted_words` from `Gc.quick_stat`, avoiding
double-counting promoted words. A full major collection precedes each measured
phase and is excluded from it; collections during the phase remain included.
Each phase targets 0.15 CPU seconds, capped at 32 whole-workload repetitions.
Very cheap phases, especially constant-hash builds, therefore have shorter
measurement windows. The raw report includes iterations and collection counts.

Read/transport conversion is outside lookup timings. Index-build timings include
hashing and all index allocations but exclude construction of the synthetic
declarations. Hash-only and validation timings are separately retained in the
raw report. Incremental insertion is correctness-tested, not separately timed.
Host: macOS arm64, OCaml 4.14.2, 64-bit words, Flambda disabled, Rocq 9.2.

## CPU And Allocation

Base environment, 1,957 names. CPU is microseconds per lookup; allocation is
words per lookup. Numbers include small measurement/loop overhead.

| Method | Present CPU us | Absent CPU us | Present words | Absent words |
| --- | ---: | ---: | ---: | ---: |
| `find_decl` | 8.504 | 15.142 | 2.006 | 0.007 |
| Full-name rolling16 | 5.301 | 13.522 | 4146.370 | 10686.320 |
| Full-name rolling32 | 8.402 | 22.481 | 6204.615 | 16203.170 |
| Leaf-component rolling16 | 2.845 | 5.183 | 1707.548 | 6530.006 |
| Constant zero | 9.091 | 16.425 | 4.006 | 2.008 |

Shadowed environment, 2,085 entries. Allocation per query is effectively the
same as above; the raw JSON retains every measurement.

| Method | Present CPU us | Absent CPU us |
| --- | ---: | ---: |
| `find_decl` | 9.151 | 16.329 |
| Full-name rolling16 | 5.201 | 13.544 |
| Full-name rolling32 | 8.804 | 22.603 |
| Leaf-component rolling16 | 2.848 | 5.187 |
| Constant zero | 9.673 | 17.241 |

Hash-only CPU, averaged over present and absent names in the base dataset:
rolling16 8.080 us/name, rolling32 13.099 us/name, leaf16 3.244 us/name. These
separate-phase measurements are not additive decompositions of the lookup table.

## Build Cost And Collisions

Full index construction, not incremental updates. Allocation below is total
allocated words per construction, **not retained index size**.

| Hash | Base build ms | Shadow build ms | Base allocated words | Shadow allocated words |
| --- | ---: | ---: | ---: | ---: |
| Rolling16 | 13.178 | 13.902 | 8,540,525 | 9,103,549 |
| Rolling32 | 20.681 | 22.136 | 12,576,536 | 13,406,414 |
| Leaf16 | 6.453 | 6.994 | 3,675,064 | 3,902,292 |
| Constant zero | 0.028 | 0.032 | 21,528 | 22,936 |

The rolling update is `((h << 5) + h + byte) land mask`, seeded with 5381 and
tagged string/numeric components. Numeric components are traversed as binary
digits. Full-name candidates include parent components; leaf16 deliberately
ignores them. No candidate is cryptographic or assumed collision-free.

| Hash | Buckets | Distinct-name collision excess | Largest base bucket | Largest shadow bucket |
| --- | ---: | ---: | ---: | ---: |
| Rolling16 | 1923 | 34 | 2 | 3 |
| Rolling32 | 1957 | 0 | 1 | 2 |
| Leaf16 | 1090 | 867 | 142 | 153 |
| Constant zero | 1 | 1956 | 1957 | 2085 |

Collision excess means distinct names minus occupied buckets; it is not a count
of colliding pairs and excludes the 128 deliberate duplicate entries. Every
collision is resolved by the original structural name comparison within the
bucket. The constant hash confirms correctness when the entire environment is
one bucket, with the expected approximately linear lookup behavior.

## Limits And Handoff

This is one bounded, uniform-name microbenchmark on a shared machine. Absent
queries are synthetic and longer than their source names; kernel hot-name
frequency, successful/failed query mix, full environment growth, retained heap,
and incremental update cost are not modeled. No kernel speedup is claimed.
The leaf candidate's fast average does not remove its large collision buckets or
allocation cost. Hash choice and production integration remain with the core
owner, and must preserve collision checks and the proved index invariant.

Artifacts: [dedicated successful build/run](../build/environment-index-benchmark/20260929T202031Z/),
including `preparation.json`, `execution.json`, `benchmark.jsonl`, generated
extraction, copied source inputs, compile/rocqchk logs, and compiler-version records.
The earlier failed proof compilation is retained under
`build/environment-index-benchmark/20260929T201950Z/`.

Important SHA-256 identities:

- Parent `EnvironmentIndex.v`: `52e606d9af19d4e32005bea6ddc5833fec594d04d3c83629b94ef5c8b24c3a0b`.
- New Gallina module: `6e7824e803e3b8615dca1d1dde7ae7c382f68740779a37eb5449c188daa58b77`.
- New OCaml frontend: `b095b60e2029a7ff167cc77bb2c0a7380f2200754ef831fc30737a4868e0fb50`.
- Generated implementation: `e26b862e9842c1dbd4ae8e9b91f160bb7fda8950c1db1b8734ea643bfaf24737`.
- Generated interface: `cc0ddf1637fd49d9b4bd1d93d15e6b8379bfd50ed60c4551fcc46d7f67dcb19e`.
- Benchmark executable: `dc091fb88c4ce938ae7148fb9499d0813d0249629299740dae426e1d29d877ca`.
- Prefix: `dce08f76af5892eda7110dc6b5d382d2a1a8cc07bcd8a0116b7e4b5d50a23877`.

The benchmark binary and input matched before/after hashes. Every subprocess was
bounded and reaped: 110 seconds per build/proof-check command, a 100-second
internal benchmark budget, and a 115-second hard execution cap. No command hit
its limit. A final process-table audit found no matching benchmark executable or
driver still running. No production build or Arena checker was executed.

To reproduce without overwriting previous reports, run the dedicated
`build/environment-index-benchmark/prepare.py`, then pass its new work-directory
path to `build/environment-index-benchmark/execute.py`. Compilation and extraction
must remain in that isolated copy, not the handwritten `rocq/` source directory.
