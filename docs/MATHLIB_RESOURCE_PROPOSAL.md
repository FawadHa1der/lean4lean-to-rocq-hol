# Mathlib Resource And Download Review

Status: **proposal only**, observed 2026-09-29 21:45-21:48 UTC. No exporter,
checker, build, higher-memory attempt, import, source modification, or cleanup
was performed for this review. The parent has reinstated the manifest hold for
Kepler's validation and selected Init/Std runs. All partials remain preserved.

## Recommendation

Do not repeat 8 GiB. Do not start a higher-memory run while the parent's checker
work is active. The next local budget I would propose for explicit review is
**12 GiB aggregate sampled RSS, 300 seconds, two threads, one offline attempt**,
with the additional host-pressure guards below. This is a profiling budget,
not an assertion that Mathlib will finish. **Current measurements do not satisfy
the proposed launch conditions.** I do not recommend 16-24 GiB on the currently
loaded 36 GiB host.

For acquiring the complete exact input rather than profiling, obtaining the
producer's original artifact would avoid this host-memory problem. No public
full-export download was found in the official channels checked below. A
maintainer-provided artifact or a separately authorized higher-headroom host is
preferable to unbounded retries or silently changing the exporter.

## Evidence From The Two Exports

The pinned native binary is unchanged, SHA-256
`17da1e168bf5d41484c940e41c1f68230798ebb38d09174b564e955895279d0f`.
Both runs use exporter commit `66f1fb4bc256072069767fce52d39480e4524869`, Lean
4.34.1 commit `5045d0056413266e57c625dcd7c365b10e377c52`, and the full original
Mathlib source/import set. These are acquisition runs, not port-checker runs.

| Run under `arena/large/mathlib/runs/` | Export Seconds | Sampled Peak RSS KiB | Partial Bytes |
| --- | ---: | ---: | ---: |
| `1790716624648598000-95150` | 122.958 | 8,401,680 | 2,370,822,144 |
| `1790717470241234000-98426` | 96.847 | 8,403,776 | 2,376,306,688 |

Both stopped at the fixed 8,388,608 KiB cap, not the 300-second deadline. Sampling
allows a small overshoot. The second file's prefix exactly matches the whole
first file. Its SHA-256 is
`14a42395312b1d6a1601c97f9231bf9b22e90909c258c9abbf9e5a49ea9391a0`.

Read-only inspection of each file's final 1 MiB found expression indices up to
41,216,732 and 41,317,884 respectively. The second tail also contains name index
1,514,552 and level index 20,748. These are observed lower bounds for the retained
maps at termination, not a measured allocation breakdown. Only peak RSS was
persisted by the original runner; there is no continuous heap/footprint profile
from which to establish the memory needed to finish.

## Why Output Streaming Is Insufficient

The exact source was inspected locally, not executed:

- [Main.lean at the exporter pin](https://github.com/leanprover/lean4export/blob/66f1fb4bc256072069767fce52d39480e4524869/Main.lean#L9)
  imports the full environment, constructs the constant sequence, and retains
  that environment while exporting.
- [Export.lean state and indexing](https://github.com/leanprover/lean4export/blob/66f1fb4bc256072069767fce52d39480e4524869/Export.lean#L35)
  retain global name, universe-level, expression and visited-constant tables.
  `getIdx` assigns indices by first encounter and retains keys for later lookup.
  The expression table therefore keeps references to expressions even after
  their JSON records have been written.
- `getIdx` and `dumpObj` already write individual compressed JSON records through
  `IO.println`; the entire NDJSON file is not accumulated in an output buffer.
  A pipe, gzip, smaller stdout buffer, or faster disk will not remove those maps.
- Important correction to an earlier informal description: `noMDataExprs` is
  **not** an ever-growing whole-export cache. Main clears it between constants,
  and `dumpExpr` clears it before normalizing each root expression. Its transient
  peak can matter, but blaming it alone is unsupported.
- The pinned [hash-map implementation](https://github.com/leanprover/lean4/blob/5045d0056413266e57c625dcd7c365b10e377c52/src/Std/Data/DHashMap/Internal/Defs.lean#L162)
  uses a roughly 0.75 load factor, power-of-two bucket arrays, and doubling on
  growth. Around 41.3 million entries implies 67,108,864 buckets: approximately
  512 MiB for 64-bit bucket slots alone, excluding entry cells, expression keys,
  environment, allocator overhead, and other tables. Growth near 50.3 million
  entries requires another doubling. This is a source-derived estimate, not an
  instrumented attribution of the observed 8 GiB.

A linear extrapolation from bytes or record counts is not a reliable completion
budget: imported-environment cost is fixed, expression sizes vary, and hash-table
growth is discontinuous. Arena's published *checker* memory numbers do not
measure exporter memory and must not be used as such.

### Possible Approaches, Not Implemented

| Approach | Exact-Byte Implications | Assessment |
| --- | --- | --- |
| Same native binary, larger bounded memory | No source, traversal or format change | Lowest compatibility risk; requires explicit resource review |
| Download producer's exact full artifact | Verify published bytes, lines and SHA-256 | Preferred if producer makes it available; none found publicly |
| Run the pinned source interpreted | Same source does not guarantee lower memory or identical output by itself | Unmeasured; not a demonstrated solution and not scheduled |
| Disk-backed global interning | Must preserve full equality, first-encounter indices, traversal and JSON ordering | A separately reviewed exporter derivative, not the unchanged pinned exporter |
| Clear global visited maps or concatenate independent shards | Loses global deduplication/index continuity and may alter dependency order | Not an exact reproduction strategy |
| Resume from the partial byte offset | Original CLI has no checkpoint of its environment/maps/traversal | Partial NDJSON alone is not sufficient state |

A disk-backed design would need collision-resolving structural keys, persistent
name/level/expression/constant indexes, the same normalization and encounter
order, and no unbounded in-memory cache in front of the disk index. Replacing
full equality with hash-only equality is unacceptable. Even a plausible design
would remain a labeled experimental derivative until its complete output matches
the original published digest. No such source changes are authorized or made.

## Host Snapshot

Read-only commands: `sysctl hw.memsize`, `vm_stat`, `memory_pressure -Q`,
`sysctl vm.swapusage`, `sysctl kern.memorystatus_vm_pressure_level`, `ps` with
PID/group/RSS/state/CPU/executable fields, and `df`. Narrow escalation permitted
process inspection; no process was stopped or reconfigured. No full-repo scan
was used.

Physical RAM is **38,654,705,664 bytes = 36 GiB**, with 16,384-byte VM pages.
Three follow-up samples at 21:48:03, :13 and :23 UTC observed:

| Measurement | Observed Value/Range |
| --- | --- |
| Physically free pages | 234,280-270,063 = 3.575-4.121 GiB |
| Speculative pages | 6,691-6,883, approximately 0.10 GiB |
| Inactive pages | About 17.51-17.53 GiB; not all freely discardable |
| File-backed pages | About 13.02-13.06 GiB; overlaps active/inactive classes |
| Anonymous resident pages | About 11.05-11.61 GiB |
| Wired pages | About 3.46 GiB |
| Compressor physical storage | About 3.41 GiB |
| Logical pages stored in compressor | About 23.30 GiB; not additional physical RAM |
| Swap used | 10,972.44 MiB, about 10.72 GiB |
| Swap counters during the 20-second window | 2,851,145 swap-ins; 4,514,215 swap-outs, unchanged |
| Kernel pressure-level query | Raw value `1` throughout |
| Sum of all process RSS | 19.91-20.33 GiB; shared pages can be counted more than once |
| Matching local OCaml/checker RSS | 0.60-1.01 GiB across sampled processes |
| Free disk at final sample | 947,095,142,400 bytes, about 882.05 GiB |

At 21:48:13, local `ocamlrun` PIDs **24997** and **25074** were running at roughly
98-99% CPU, with **434,016** and **414,352 KiB** RSS respectively. PID **84593**
was sleeping with **210,752 KiB** RSS. PID 24997 was gone at the next sample;
25074 remained active. Their executable paths resolve through the local
`/private/tmp/lean4lean-501-e16fccc9822d/opam-root/lean4lean` toolchain. These
measurements account for observed checker/runtime processes without assuming
which parent task owns each one. Generic interpreter/helper processes are also
included in whole-host counters/RSS, though not all can be attributed by their
executable name alone.

The earlier `memory_pressure -Q` summary was **80%**. It is emphatically **not**
28.8 GiB of physically free RAM. Cached/inactive memory may be reclaimable, but
reclaimability, compression and hot file-backed pages make exact allocation
headroom uncertain. Existing swap use is not proof of current thrashing: swap
counters were stable in the follow-up window. See Apple's explanation of
[memory pressure, compression, cached files and swap](https://support.apple.com/guide/activity-monitor/view-memory-usage-actmntr1004/mac).

## Proposed Safety Gates

These are conservative operational heuristics, not OS guarantees. They require
a separately reviewed supervisor change; the existing retry script still has
an immutable **8 GiB** limit and must not be bypassed.

1. Obtain explicit approval for one **12 GiB / 300-second** export-only attempt,
   only after the parent's full and selected checker runs have ended. Recheck
   resources immediately before launch; do not kill other workers or apps.
2. Use the whole-host baseline proxy `H = anonymous resident + wired + physical
   compressor pages`, with each category converted using the reported page size.
   Require **H <= 17 GiB** over a quiet 30-second observation and free plus
   speculative pages >= 4 GiB. This reserves at least 7 GiB beyond a 12 GiB
   exporter for file-backed working sets, kernel variation and sampling delay.
   The observed H was roughly **17.91-18.48 GiB**, so the gate currently fails.
   This proxy is not a precise app-footprint measurement.
3. Require no active competing checker/export/build job and no increasing
   swap-out counter in a fresh 60-second window. Dormant checker RSS still counts
   in the baseline. If resources do not settle, defer rather than force the run.
4. Retain two threads, offline sandbox, at least 64 GiB free disk, and output cap
   of published size plus 1 MiB. Preserve both older partials and reports.
5. Record timestamp/output bytes/aggregate RSS at every memory sample, plus
   host VM/swap deltas. Measure physical footprint where available because RSS
   alone can hide compressed or paged-out private memory. Apply the 12 GiB job
   cap to both aggregate RSS and aggregate physical footprint when measurable.
   Also abort if the kernel pressure level moves away from its quiet baseline
   for two consecutive one-second samples, swap-used growth exceeds 256 MiB,
   cumulative swap-out growth (page delta times page size) exceeds 256 MiB, or
   free-plus-speculative memory is below 1 GiB for two consecutive one-second
   samples. Stop/reap only the owned process group.
6. On any cap, stop with a new report; do not automatically raise the limit or
   retry. Complete output still needs the exact published bytes/lines/hash and
   separate coordination before any shared-manifest import.

This proposal does not establish that 12 GiB is sufficient to finish. A 16 GiB
attempt with the measured baseline would leave too little conservative reserve;
24 GiB is not justified. More memory could become reasonable after a fresh,
substantially quieter host snapshot or on an explicitly authorized isolated host.

## Official Download Assessment

The immutable target remains **6,184,415,052 bytes**, **109,790,519 lines**,
SHA-256 `22c5de83469408950005589a3bc5ef5157c65549b5a802f85d567c29151306a6`.
Only metadata/pages were fetched; no large artifact, new source, or replacement
results/manifest was downloaded.

- The [official Arena download page](https://arena.lean-lang.org/) excludes tests
  larger than 10 MB. At the pinned revision, `lka.py:58` sets the actual threshold
  to **10 MiB**, and `create_test_tarball` skips larger inputs.
- The [pinned packaging code](https://github.com/leanprover/lean-kernel-arena/blob/03b21e119045304d38249f426fcd86171fc253c5/lka.py#L2545)
  stages result JSON and test-stat JSON, not the full `.ndjson` files, into the
  checker/test-stat artifacts. The [pinned workflow](https://github.com/leanprover/lean-kernel-arena/blob/03b21e119045304d38249f426fcd86171fc253c5/.github/workflows/build-and-deploy.yml#L254)
  uploads those and the size-filtered tarball.
- An unauthenticated bounded GET of the [pinned run's artifact metadata](https://api.github.com/repos/leanprover/lean-kernel-arena/actions/runs/36543121707/artifacts?per_page=100)
  returned HTTP 200 and all **33** artifacts. None is a full Mathlib export.
  The `test-tarball` artifact is 3,310,634 bytes; the largest listed artifact is
  `github-pages-1`, 15,564,396 bytes. The artifact names and pinned packaging code
  agree on the absence of a separately published full export.
- The [public release API](https://api.github.com/repos/leanprover/lean-kernel-arena/releases?per_page=100)
  returned HTTP 200 and one release, `round-2026-09`: results JSON (4,219,502 bytes),
  site tarball (4,012,381 bytes), and test tarball (3,497,743 bytes). The pinned
  release workflow reuses the same size-filtered suite for releases/Zenodo, not
  a second unfiltered archive. A different round must not substitute its inputs.
- The pinned flake supplies a development shell, not a published Nix derivation
  for this export. The CI cache action mounts toolchain/build caches; that is
  not a documented public full-export download URL.

Conclusion: **no official public download of this exact full export was found
in the checked channels**, not a claim that no unpublished copy exists. The
precise alternate acquisition requirement is for the Arena producer to provide
the original full Mathlib file (or a compressed version) from this pinned run,
which must decompress to the target above. No message was sent to maintainers
and nothing was published; external access was limited to read-only pages and
metadata requests.

## Preservation

Only this new proposal document was written during the review. Manifest SHA-256
remains `d0ef9bd650fa4256cca4e4256ef45eda096e8ad3505945dad9c41a3f3d063b19`;
provenance lock SHA-256 remains
`990849c6e9216cd1254f2b004f64d8a0e8a1a1694efd05280d519596cdcf39d7`.
Availability remains **216/220**. No tests of port correctness were performed.
