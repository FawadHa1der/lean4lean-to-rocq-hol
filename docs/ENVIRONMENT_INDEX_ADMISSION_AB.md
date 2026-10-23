# Private Hybrid64 Hash Admission A/B

## Result And Recommendation

**Both cheaper hashes accepted the exact 120590-line prefix at fuel 512 and
rejected `perf/refute-cheap-last` at fuel 16384.** Four attempts total, each
executed once. No timeout, decline, fault, driver error, or integrity failure.
No full Arena or full Init run was performed.

| Hybrid64 candidate | Prefix wall s | Prefix child CPU s | Target entry CPU s | Small negative wall s | Actual exits |
| --- | ---: | ---: | ---: | ---: | --- |
| leaf16, archived parent baseline | 57.222 | not recorded | 44.386 | 13.990 | 0 / 1 |
| suffix_last2 | 18.379 | 18.023 | 11.391 | 14.037 | 0 / 1 |
| suffix_bitfold8 | 16.145 | 15.822 | 10.480 | 13.945 | 0 / 1 |

**Recommend bitfold8 for the next bounded private throughput validation**, not
unconditional production integration. In this one A/B sample it reduced prefix
wall time by 12.2% relative to last2, but allocated 18.4% more words. Last2 is the
lower-allocation alternative. Relative to the earlier leaf16 run, measured wall
ratios are 3.11x for last2 and 3.54x for bitfold8; those are observations across
different times on a shared machine, not repeated controlled speedup estimates.

The prefix contains only 1,957 declared names. Bitfold8 has 256 possible string
keys; collision cost at full Init/Std scale remains unmeasured. The earlier
[name-only benchmark](ENVIRONMENT_INDEX_SUFFIX_BENCHMARK.md) found 252 occupied
bitfold8 buckets with maximum length 147, versus 171 last2 buckets with maximum
length 288, on its synthetic declaration environment. Those are not measured
kernel lookup frequencies or runtime bucket occupancy. Both hashes retain full
structured-name comparison within buckets, so collisions affect cost, not
correctness. Hybrid64 is unchanged and is not claimed to be an optimal threshold.

## Isolation And Proof Audit

All experiment sources, binaries, inputs, logs, and reports are under:

`/private/tmp/rocq-index-suffix-ab-20260929T212700Z`

The archived parent is `/private/tmp/rocq-index-admission-20260929`. Its sources
and hybrid64 leaf16 binary were copied before building. Among the parent's
source files, the only modifications in each candidate are the RuntimeChecker
import and its six `benchmark_hash_leaf16` references, changed to the selected
suffix hash. The source audit checks this exact substitution byte for byte;
each candidate has a `runtime-only.diff`.

`EnvironmentIndexSuffixBenchmark.v` is an unchanged copy of the previously
audited, total Gallina candidates. The additional `AuditRuntime.v` only prints
assumptions of the six existing exact-refinement theorems. All six roots report
`Closed under the global context` in each build; proofs, fuel behavior, and the
`at_least 64` guard are unchanged. `rocq check -silent -o` succeeded for
RuntimeChecker, ArenaExtract, AuditRuntime, and their dependencies.

Both builds use ordinary extraction, without custom extraction mappings or
unchecked casts. An audit before native compilation found no `Obj`, `magic`,
externals, assertions, failure stubs, unrealized axioms, or `.unsafe_` operations
in the emitted ML/MLI, including the integrated `lean_arena` extraction. Rocq
9.2 and OCaml 4.14.2 were used. Private builds took 65.979s and 64.719s, each
under its 149s build budget. No parent or production source/binary, existing
build script, or manifest was changed.

## Inputs And Execution

The exact dependency-audited Init prefix has 120,590 lines, 6,253,436 bytes,
1,704 wire declaration records, 107,797 expression nodes, and 1,957 distinct
declared member names. Its final declaration is
`Array.foldlM_toList.aux._unary`. It is a byte-exact prefix, not a regenerated or
modified test and not a full Init acceptance claim. Its SHA-256 is:

`dce08f76af5892eda7110dc6b5d382d2a1a8cc07bcd8a0116b7e4b5d50a23877`

The published `perf/refute-cheap-last` input has 439 lines, 20,975 bytes, and
seven wire declaration records. Its SHA-256 is:

`ea6fdc9ab4986b6a97e494c7af868704a3e15552506ca2014743a91a83a0e2ec`

Both inputs use NDJSON 3.1.0, Lean 4.34.1. Read-only byte-identical private
copies were passed directly to each checker. No expected result or manifest was
passed to a checker. Actual exit 0 establishes the reported acceptance; actual
exit 1 establishes the reported rejection. Both prefix outputs state
`accept: 1704 declarations checked by extracted Gallina`. Both negative runs
report `line=439 checked=6 type mismatch`.

The runs were sequential: last2 prefix, last2 negative, bitfold8 prefix,
bitfold8 negative, starting 2026-09-29 21:37:37 UTC. Arguments were
`--fuel 512 --progress 1` and `--fuel 16384 --progress 1`, respectively.
Authorized caps were 149s/30s; the driver enforces 148s/29s, reserving one second
for cleanup. Each checker owns a process group; deadline/exception handling
kills and reaps it. Every run has a distinct exclusive directory, and the driver
refuses to overwrite an existing attempt. No run was retried.

`OCAMLRUNPARAM=v=0x400` enables exit-GC diagnostics for all four runs. No heap
tuning or frontend instrumentation was added. The parent baseline did not record
allocation statistics and was not rerun. Each child CPU value is its user plus
system CPU time from the fresh driver's child resource usage.

## Phases And Allocation

| Candidate | Parse CPU s | Schedule CPU s | Check start to target CPU s | Target entry to process exit wall s |
| --- | ---: | ---: | ---: | ---: |
| leaf16, archived | 0.135 | 0.147 | 44.102 | not recorded |
| last2 | 0.125 | 0.117 | 11.146 | 6.669 |
| bitfold8 | 0.126 | 0.115 | 10.236 | 5.367 |

Phase durations are differences between start events. The target event is
emitted **before** admission, with `checked=1703`; it is not itself evidence of
acceptance. The target is the last declaration, and the measured entry-to-exit
interval includes its check plus output, exit-GC diagnostics, shutdown, and
observation overhead. No earlier stalled declaration is attributed to the target.

| Candidate / input | Total allocated words | Minor collections | Major collections | Peak RSS MiB |
| --- | ---: | ---: | ---: | ---: |
| last2 / prefix | 5,887,852,660 | 22,518 | 121 | 44.41 |
| bitfold8 / prefix | 6,972,064,887 | 26,663 | 139 | 44.31 |
| last2 / negative | 8,156,466,356 | 32,011 | 1,968 | 24.23 |
| bitfold8 / negative | 8,156,466,355 | 32,049 | 2,044 | 31.13 |

Allocation is the runtime's `allocated_words`, independently checked against
`minor_words + major_words - promoted_words`. One word is eight bytes here.
These are **whole-process cumulative allocations**, including parsing, index
construction, and logical checking, not hash-only cost or retained heap.
Prefix totals are about 47.10GB and 55.78GB of cumulative allocation despite
roughly 44MiB peak RSS. GC counts and peak RSS can vary even when total allocation
is nearly identical, as on the small negative. Its runtime is essentially
unchanged under the retained small-environment guard; no causal claim about its
remaining allocation is made from this test alone.

## Provenance And Handoff

The experiment root contains `prepare.py`, `build.py`, `run_case.py`, and
`finish.py`; the latter only summarizes existing reports and audits provenance.
`snapshot.json` pins the parent inputs/sources. `summary.json` contains the
comparison, toolchain versions, final integrity checks, and process audit.
`artifact-sha256.json` inventories 398 files, including source snapshots,
extraction, binaries, all logs, and four reports. All 45 archived parent files
and both original/private inputs remained unchanged; all candidate source,
binary, and input before/after checks passed. A final process-table check found
none of the 70 recorded build/driver/checker PIDs still present. All tool sessions
were reaped. The observed main manifest hash remained unchanged.

| Artifact | SHA-256 |
| --- | --- |
| Parent hybrid64 leaf16 binary | `81ea2712bece3999e415595a6c35cd62688d7f7a34060fa79cee1c36e837f51e` |
| last2/build/rocq-check | `008472b7e4ddbe87af9d3b425d34efbd06be0c5d7e186525a0d9e8a6fc3f5cb6` |
| bitfold8/build/rocq-check | `22d330fc7d45c16676f236c836e5559e867be35c74428fcddb89d1b174f50050` |
| last2/rocq/RuntimeChecker.v | `89152bf60bf07e8a5985c30143daca01b3e9a3d33a22bf7d9a26fbcc477d4ef4` |
| bitfold8/rocq/RuntimeChecker.v | `f4b808f7214a872f44cb112c5b44fefa068f3dd58597a3f17bed62b9dfc2064a` |
| Shared suffix source | `94e9758fac63e8d643d135030a8c39cb026aa292e1ddd15b912f76b19f9fa328` |
| summary.json | `a73e38e651e1cb861e2797d48421b4899e199a825ea25bba0c83a99afa151dcc` |
| artifact-sha256.json | `f64c165550096e923762e777cfff99a3ada83ef30a89a66081d5a09d76d93034` |

Per-attempt reports are `<candidate>/run-prefix/report.json` and
`<candidate>/run-refute-cheap-last/report.json`, with complete progress JSONL,
raw stdout/stderr, and pre-run provenance alongside each. Each build has its
own `build-report.json`, proof/kernel audit logs, extracted files, and source
diff. These binaries intentionally retain the frozen parent sources; they do
not incorporate later quotient-foundation or other parent changes.
