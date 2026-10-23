# Mathlib Exact Acquisition

This is a separate bounded attempt to reproduce the published full `Mathlib`
Arena export. It does not change a checker, expected target, or import graph,
and never invokes a port checker. No Mathlib shared-manifest import is automatic.

## Pins And Reuse

`arena/large/mathlib/lock.json` pins:

- Arena `03b21e119045304d38249f426fcd86171fc253c5`, `tests/mathlib.yaml`.
- [Mathlib source](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612):
  `d13f23b723b8a846827a245b89c10fc7d3f11612`, release recipe `v4.34.1`.
- Lean **4.34.1**, compiler revision `5045d0056413266e57c625dcd7c365b10e377c52`.
- Exporter `66f1fb4bc256072069767fce52d39480e4524869`, format 3.1.0,
  natively compiled from unchanged source with its license retained.
- The entire module **`Mathlib`**, with no declaration selection or bare `--`.

| Measurement | Published Target |
| --- | --- |
| Bytes | 6,184,415,052 |
| Lines | 109,790,519 |
| SHA-256 | `22c5de83469408950005589a3bc5ef5157c65549b5a802f85d567c29151306a6` |

The immutable source archive is **23,846,080 bytes**, SHA-256
`a8c019444a1edd6091d8416e492e218a311db340dafbea96c61c6dc358c28f05`.
Its measured digest is pinned locally; it is not claimed to be a signed archive.
Published output targets are cross-checked against the existing hash-locked
Arena results and definition, never changed to match a generated output.

The eight dependency revisions, Mathlib `lakefile.lean`, manifest, and complete
`Cache/` implementation match the previously reviewed CSLib dependency snapshot.
The Mathlib source revision and `lean-toolchain` differ. Dependency archive pins
are reused through the SHA-256-locked `arena/large/cslib/lock.json`
(`db651d4ec80168986acc4d81718df2cebff79731201566de237ab52202d3954f`).
Resolved pins are also embedded in each run report. Archive bytes are verified
before copying, then independently extracted into **new** Mathlib-local trees.
No source, build output, or cache under CSLib is modified.

The existing isolated toolchain is reused read-only at:

```text
arena/generation/toolchain/lean-4.34.1-darwin_aarch64
```

Its original release archive SHA-256 is
`65f22a4f047738ec742667b3247e836a86ebf06eabc12655c3dee00637e37866`.
Preparation verifies the archive, launcher hashes, actual version and compiler
commit. The host's official macOS ARM build is explicit; no platform or source
substitution is hidden. No global tool or configuration is installed.

**No Lean 4.34.0 compiled artifacts or CSLib cache files are reused.** The changed
`lean-toolchain` file changes Mathlib's cache root hash. A new cache directory
under `arena/large/mathlib/cache` is marked with this recipe's lock hash; an
unrecognized or differently marked cache is rejected rather than repurposed.

## Reviewed Operations

The pinned Arena pre-build action is `lake exe cache get`. The bounded runner
splits it into the unchanged cache tool's offline compilation, its `get-`
download-only action, and the exact toolchain's bundled `leantar -x --jobs 2`.
This makes decompression concurrency explicit without changing artifact bytes
or source. No upstream shell snippet, npm command, linter, test target, or
`lake update` is requested. Mathlib's original ProofWidgets `errorOnBuild`
configuration remains active, and `MATHLIB_NO_CACHE_ON_UPDATE=1` is set.

Package-location overrides and `.lake/packages` links point only to the newly
extracted pinned dependencies. Original manifests and Lake files remain intact.
All source files and archive symlink targets are verified before execution,
after cache/build/export, and when a failed run finishes.

The cache reads the original canonical Mathlib master/legacy chain over HTTPS.
There is no unsafe cache scope, alternate source revision or custom endpoint.
Cache input hashes do **not** authenticate artifact contents. This pinned
implementation hashes configuration, source, imports and the toolchain file;
despite its comment, `getRootHash` does not directly mix `Lean.githash`.
The acquisition therefore checks the compiler pin separately. Downloaded LTAR
SHA-256 values are retained as byte provenance, not semantic validation.

The `inspect_mathlib_cache.lean` helper uses the pinned cache implementation's
own import parser and hash graph to record every required module, cache key and
missing olean. More than **16** missing modules stops the attempt before a full
source rebuild. Up to 16 missing modules may be built from the exact original
sources within the build timeout; their names remain in the report. When all
oleans exist, `lake --no-build build Mathlib` must pass first to reject stale
cache traces instead of silently rebuilding the whole library.

## Resource Limits

Initial host checks: **36 GiB physical RAM**, **897 GiB free disk**. The read-only
macOS memory-pressure query reported 84%; that is not a promise of unused RSS.
Each stage requires a **64 GiB free-disk reserve**. Limits are:

| Stage | Wall Cap |
| --- | ---: |
| Cache tool compilation | 180 s |
| Cache download | 600 s |
| Two-thread decompression | 180 s |
| Cache-closure inspection | 90 s |
| Complete-cache trace check | 90 s |
| Original full Mathlib build | 600 s |
| Native exporter compilation | 180 s |
| Full Mathlib export | 300 s |

Aggregate process-group RSS is sampled about every 0.5 seconds and stopped above
**8 GiB**. This is not a hard OS memory cap and can overshoot between samples.
`LEAN_NUM_THREADS=2`, `RAYON_NUM_THREADS=2`, explicit decompressor jobs=2, and curl
parallel-max=2 are set. These are not a universal child-process-count limit.

Only the reviewed compiled cache downloader gets outbound TCP 443 and the macOS
DNS resolver socket. All builds, decompression, inspection and export deny
networking. Curl permits HTTPS only, a 15-second connection timeout, 60-second
per-transfer timeout, and 128 MiB per artifact. Every stage permits writes only
inside `arena/large/mathlib` and `/dev/null`, with local HOME/TMPDIR/cache paths.
Process groups are killed and reaped on completion or a limit. There is no
unsandboxed fallback, automatic retry loop, or raised memory limit.

Export output is stopped above published size plus 1 MiB; that margin permits
diagnosis of a near match, never acceptance. Only exact size, line count and
SHA-256 promote `exports/mathlib.ndjson`. Failed/partial output is retained with
its hash and never imported or counted as official coverage.

## Commands

Review the scripts and pinned package/cache code before execution:

```sh
python3 -B scripts/prepare_mathlib_arena.py
python3 -B scripts/prepare_mathlib_arena.py --prepare --download
python3 -B scripts/test_mathlib_acquisition.py
python3 -B scripts/acquire_mathlib_arena.py
python3 -B scripts/acquire_mathlib_arena.py --execute-reviewed --allow-cache-download \
  --cache-timeout 600 --build-timeout 600 --export-timeout 300 \
  --memory-mib 8192 --max-missing-modules 16
```

Preparation never executes upstream build code. In the initial local run all
archives were already downloaded or reusable, so the verified preparation
command was `python3 -B scripts/prepare_mathlib_arena.py --prepare`.
Five read-only policy tests passed before the bounded attempt.
`arena/large/mathlib/latest-build.json` points to the most recent completed
attempt; individual reports preserve exact commands, hashes, limits and logs.
No successful export is claimed by preparation or cache availability alone.

## Observed Bounded Result

The first attempt finished on **2026-09-29 at 21:04:50 UTC**. Its report is:

```text
arena/large/mathlib/runs/1790715271412734000-98995/report.json
```

- Preparation verified all nine source archives and **10,122** source files or
  links, plus the existing Lean 4.34.1 toolchain pin.
- Offline compilation of the original cache tool passed in **16.343 seconds**,
  with sampled peak aggregate RSS **1,542,752 KiB**.
- Download-only cache retrieval hit its **600-second wall limit** after
  **600.411 seconds**, and its process group was stopped and reaped. Sampled
  peak RSS was **71,216 KiB**; this was not a memory-limit failure.
- **6,423 / 8,908** complete LTAR files were retained, totaling **321,333,408
  bytes**. Another **2,485** exact cache keys remain missing. Two partial
  transfers total **153,692 bytes** and are not counted as complete files.
- Decompression, the full Mathlib build, exporter compilation and export were
  **not reached**. No Mathlib NDJSON output or checker verdict was produced.
- Original source verification passed again at finish. The shared manifest
  remained at the same `d0ef9bd6...63b19` hash recorded below throughout this
  attempt. No manifest write occurred.

A separate offline cache-inspection run passed in **1.556 seconds**, under a
90-second wall cap and 1 GiB sampled RSS cap. Its report and complete 8,908-module
cache-key plan are in `runs/1790715675740253000-67076/`. This inspection does not
compile Mathlib; before decompression it found 8,907 missing oleans.

The retained-file inventory is adjacent to the failed attempt report:

```text
arena/large/mathlib/runs/1790715271412734000-98995/retained-cache-inventory.json
```

It records every complete/partial file's size and SHA-256, every missing module
and key, the source-lock hash, and hashes of both the attempt report and cache
plan. Its SHA-256 is
`b86c5ed74b47975ca8028124629e8a957aa22ce0dda4b45c79b265b8ee83be25`.
The attempt report SHA-256 is
`229c8002636aba84e377e5990c9cb4aeff134faadcd58f49721b60c6d2fbb88e`.
These records preserve the completed attempt without rewriting its outcome.

**Remaining prerequisite:** retrieve the missing exact-recipe cache files within
a separately bounded network attempt, then establish offline decompression and
build feasibility. This result is a download-budget limitation, not evidence
that the original Mathlib source cannot build. The command above can resume with
the same bounds and fresh per-run logs. Before doing so, verify retained bytes
against the inventory: the upstream `get-` action skips existing files by cache
key, not by an authenticated artifact-content digest. Never reuse the different
Lean 4.34.0 cache, raise the 16-module source-build allowance implicitly, or
change the published export target to work around missing artifacts.

There is no automatic retry. All owned acquisition processes are stopped. The
parent's new private indexed Rocq run now holds **all further manifest imports**;
any eventual exact Mathlib output must remain staged until separately authorized.

## Authorized Single Resume

After the first attempt stopped, the parent explicitly authorized **one** resumed
download with the same limits, conditional on checking every retained hash.
The pre-resume verification passed at **2026-09-29 21:16:39 UTC**:

```text
arena/large/mathlib/resume-verifications/1790716599678251000-94501/report.json
```

It checked all **6,423 complete** files and **two partial** files against the
saved inventory, the inventory/report/cache-plan hashes, source lock, cache
marker, and all previously recorded acquisition-helper hashes. No extra complete
or partial cache files were present. Free disk was **960,227,221,504 bytes**,
above the unchanged 64 GiB reserve. Verification report SHA-256:
`0a055c0679ca308c1dfdbaed1ba641203b7f7ee24627ecca0c6c48948127050a`.

The exact bounded command in the Commands section was invoked once. Its separate
attempt report is:

```text
arena/large/mathlib/runs/1790716624648598000-95150/report.json
```

The downloader announced exactly **2,485** requested files, skipping all verified
complete files. No force-download flag, altered pin, expanded limit, alternate
endpoint or automatic retry was used. The first failure report and inventory
remain unchanged. Five acquisition policy tests passed again in 1.492 seconds.
No manifest import is authorized while the parent's HOL full-Arena run is active.

### Resume Outcome: Export Memory Limit

The authorized resumed attempt ended at **2026-09-29 21:24:21 UTC**. It retrieved
every missing cache file, successfully checked and built the unchanged cached
Mathlib target offline, then stopped during export at the original memory cap.

| Stage | Result | Seconds | Sampled Peak RSS (KiB) |
| --- | --- | ---: | ---: |
| Cache tool target | Passed | 3.116 | 627,184 |
| Missing 2,485 cache downloads | Passed | 223.259 | 66,752 |
| Two-thread decompression | Passed | 37.569 | 92,992 |
| Full cache-closure inspection | Passed; zero missing oleans | 6.881 | 706,960 |
| Cached target trace check | Passed | 12.171 | 843,440 |
| Original Mathlib target build | Passed using the complete cache | 11.142 | 845,536 |
| Native pinned exporter compilation | Passed | 9.014 | 1,417,712 |
| Full Mathlib export | Stopped: `sampled_memory_limit`, exit -9 | 122.958 | 8,401,680 |

The last sample exceeded the **8,388,608 KiB (8 GiB)** cap; the runner stopped and
reaped the process group. The slight overshoot is consistent with the documented
sampling interval, not an increased limit. The 300-second export timeout was not
the limiting factor. No further attempt or larger resource budget was used.

All **8,908** required cache files are retained with per-file content hashes in
the resumed run's `cache-files.json`, SHA-256
`9c95f031cad561ffe0fa624811af55cd75338b7f14d58e95bb503a183b726cf9`.
The complete source set remained unchanged after decompression, after build and
at finish. The 6,423 previously retained complete files were not requested by the
download job; its 2,485-key curl request list had zero overlap with them.

The diagnostic partial export remains at:

```text
arena/large/mathlib/runs/1790716624648598000-95150/mathlib.partial.ndjson
```

Independent `wc -lc` and `shasum -a 256` checks found **2,370,822,144 bytes**,
**42,982,538 newline characters**, SHA-256
`3fc3b468c443bc0611a58b3c159bc3f18df9b227af14c7c4c2673391871fc679`.
This is incomplete and may end inside a record. It is not an exact export,
complete stress input, Arena coverage, or a checker acceptance. Nothing was
promoted to `exports/mathlib.ndjson`.

**Current blocker:** the pinned native full-Mathlib exporter exceeded the
authorized 8 GiB aggregate RSS cap on this host. The source/toolchain/cache/build
prerequisites are now prepared; download availability is no longer the blocker.
Another export would require a separately reviewed and authorized resource or
memory-use solution that preserves the original source, target and exact output
requirements. No larger-memory attempt, substitute exporter or source mutation
is implied by this handoff.

The first timeout report and inventory remain intact. A separate
`resume-integrity.json` records the final cache recheck and manifest preservation
without rewriting either attempt. The shared manifest stayed at **216/220** and
SHA-256 `d0ef9bd650fa4256cca4e4256ef45eda096e8ad3505945dad9c41a3f3d063b19`.
No port checker was invoked. All acquisition processes are stopped; the active
parent HOL run's manifest-import hold remains in force.

## Offline Export-Only Retry

After confirming both parent full-Arena runs had ended, the parent released the
manifest hold and authorized a further bounded Mathlib retry. No larger memory
budget was specified, so the retry retained the **8 GiB sampled RSS**, **300-second
export**, **two-thread**, and **64 GiB disk-reserve** limits. The new command is:

```sh
python3 -B scripts/retry_mathlib_export.py
python3 -B scripts/retry_mathlib_export.py --execute-reviewed
```

The first command is read-only preflight. The second performs exactly one offline
export using the already-built pinned native exporter. It verifies the previous
report's fixed hash, all 8,908 cache-file hashes and cache marker, original source
archives/files, the toolchain, package overrides, exporter sources and binary,
and recorded helper hashes. A 90-second `lake --no-build build Mathlib` check must
pass before export; no dependency download or rebuild is repeated. It cannot
import a manifest and has no flags that increase the resource limits.

The no-rebuild target check passed in **10.463 seconds**. The export again stopped
at `sampled_memory_limit`, exit -9, after **96.847 seconds**, with peak sampled RSS
**8,403,776 KiB**. The attempt ended and was reaped at **2026-09-29 21:33:00 UTC**.
Report:

```text
arena/large/mathlib/runs/1790717470241234000-98426/report.json
```

Report SHA-256:
`c7769c7a8313cfd18457425feb22f0461065d4270e8f2a393679c9d843ec0cea`.
The retained `mathlib.partial.ndjson` contains **2,376,306,688 bytes** and
**43,084,535 newline characters**, SHA-256
`14a42395312b1d6a1601c97f9231bf9b22e90909c258c9abbf9e5a49ea9391a0`.
An independent streaming integrity check confirmed its first **2,370,822,144
bytes** exactly match the entire preserved earlier partial export. Both remain
incomplete diagnostic files, not official Arena inputs. Source and prior-report
hashes remained unchanged. The adjacent `integrity-check.json` records these
measurements; `latest-export-retry.json` points to this new attempt without
overwriting the earlier acquisition report.

The five acquisition policy tests passed again (2.063 seconds), and the new
command's read-only preflight, retained-provenance guards and bounded failure
cleanup were exercised. No checker ran and no manifest was imported: availability
remains **216/220**, with the same manifest hash recorded above. All owned sessions
are reaped. The hold is released as of this retry, but any eventual import still
requires advance coordination before writing the shared manifest.

Two independently bounded export attempts now reproduce the memory-cap blocker
near the same output position. Further unchanged 8 GiB retries are not scheduled.
Continuing requires explicit authorization for a different memory budget or a
separately reviewed lower-memory approach preserving the exact published output;
the memory required to finish has **not** been established.

## CSLib Import Coordination

During preparation, the parent confirmed its full Rocq/HOL runs had ended and
explicitly authorized CSLib import. The unchanged pinned integrity workflow ran:

```sh
python3 -B scripts/fetch_arena.py \
  --import-generated cslib=arena/large/cslib/exports/cslib.ndjson
```

It returned exit 0. Availability became **216/220**, with **3,425,364,332 bytes**.
Every non-CSLib case and the provenance block stayed identical. Historical
reports and their counts/manifests were not rewritten. Before/after snapshots,
the importer hash, command and results are preserved at:

```text
arena/large/cslib/imports/1790714990426594000-69953/report.json
```

Manifest SHA-256 before:
`985cadef081276d8796bc7ee113a47b1f0b2de994f0892dd6027b1f821a52f30`.
Manifest SHA-256 after:
`d0ef9bd650fa4256cca4e4256ef45eda096e8ad3505945dad9c41a3f3d063b19`.

All three selected existing corpus tests passed: complete inventory, every
available file's hash/size, and explicit treatment of large/either omissions.
These are acquisition/integrity tests, **not checker runs**. Kepler was notified.
CSLib is acquired and available, not port-accepted. Mathlib remains unavailable
unless an exact export and a separately coordinated import are confirmed.
