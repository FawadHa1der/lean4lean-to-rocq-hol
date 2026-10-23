# CSLib Exact Acquisition

This acquisition attempts the published full-module `cslib` export, not a
replacement stress example. It changes only acquisition scripts, documentation,
and `arena/large/cslib`. It never edits checker code, compiler interfaces,
expected input hashes, or the shared Arena manifest. Lean generates inputs;
it does not decide a Rocq/HOL port verdict.

## Exact Target

`arena/large/cslib/lock.json` pins all ten source archives and the separate
official macOS ARM Lean 4.34.0 archive, including measured source archive SHA-256
values and the toolchain digest published in GitHub release metadata.

- Arena: `03b21e119045304d38249f426fcd86171fc253c5`, `tests/cslib.yaml`.
- [CSLib source](https://github.com/leanprover/cslib/tree/990e65a685bed413f43b139db900a36ad5322a10):
  `990e65a685bed413f43b139db900a36ad5322a10`.
- [Mathlib source](https://github.com/leanprover-community/mathlib4/tree/5ed2965256430c3649e86755f9576b54eca72435):
  `5ed2965256430c3649e86755f9576b54eca72435`.
- Lean: **4.34.0**, revision `293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`.
  Existing Lean 4.33.0 and 4.34.1 installations are not substituted.
- Exporter: `66f1fb4bc256072069767fce52d39480e4524869`, format 3.1.0,
  compiled natively from unchanged source.
- Module: **`Cslib`**, without a declaration-selection argument or bare `--`.

Expected output is **2,422,584,798 bytes**, **42,689,984 lines**, SHA-256
`bc5c88e028d02a3c0789de6efb9cd96e8506d1e96b3d26672d28ae3bb33d0b30`.
The script cross-checks these values against the existing hash-locked published
results and definition. Only all three exact matches may promote the output to
`arena/large/cslib/exports/cslib.ndjson`; mismatches stay in their run directories.

The host platform is macOS ARM, explicitly using that official release asset.
Published Arena metadata identifies the compiler commit but does not pin the
exporter commit or provide complete platform/cache provenance. Cross-platform
byte identity is tested, never assumed.

## Reviewed Prerequisites

The initial disk check showed **914 GiB free**. Preparation and every build step
require at least **32 GiB free**. No global toolchain, dependency, shell, or
package-manager configuration is changed. Toolchain path:

```text
arena/large/cslib/toolchain/lean-4.34.0-darwin_aarch64
```

CSLib's manifest pins Mathlib plus Plausible, LeanSearchClient, ImportGraph,
ProofWidgets, Aesop, Qq, Batteries, and Cli. Every transitive manifest entry is
checked against those exact source URLs, revisions, and subdirectories.
Archive extraction rejects escaping paths, hard links and special files;
only in-root symlinks are permitted. Licenses stay in the original archives
and extracted source trees. Partial/unrecognized extractions are preserved
and rejected, not deleted.

The root TOML declares the `Cslib` library; its test and linter drivers are not
invoked. Mathlib's Lake configuration, cache downloader, hash computation,
decompression code, and cache security documentation were inspected. Its
`post_update` hook is not needed: no `lake update` runs, and
`MATHLIB_NO_CACHE_ON_UPDATE=1` is set. ProofWidgets' original `errorOnBuild`
configuration remains in effect. Its prebuilt JavaScript and trace are in the
pinned source archive; npm builds/installations are not authorized. Other
dependency configurations are TOML with no shell build hooks.

## Cache Boundary

The Arena pre-build command is `lake exe cache get`. The runner splits that into
a network-denied build of the unchanged `cache` executable, followed by an
explicit invocation of that compiled executable with the same `get` action.
No unreviewed shell snippet is executed. The cache source uses bundled `leantar`
from the exact Lean release; it does not download another decompressor.

Archive sources have no Git remotes. The cache invocation explicitly identifies
`leanprover-community/mathlib4`, the source repository actually pinned. Its
normal master/legacy lookup chain is used; no `--unsafe`, alternate scope,
custom cache endpoint, fork artifacts, or source revisions are substituted.

The inspected cache key combines source/configuration, import hashes and the
`lean-toolchain` file. Its comment mentions `Lean.githash`, but this pinned
`getRootHash` implementation does not mix that value directly. The acquisition
separately checks the release archive digest and running compiler commit.
**The cache does not authenticate downloaded artifact contents.** Mathlib's
upstream cache and Lean release remain an acquisition trust boundary. Every
retained LTAR is hashed in the run's `cache-files.json`; this is byte provenance,
not independent semantic verification. Final Arena SHA/size/line matching is a
separate mandatory gate, and never proves checker correctness.

Dependency location overrides are per-run and versioned. They reference only
unchanged source directories. Original `lakefile` and `lake-manifest.json` files
are not rewritten. Local `.lake/packages` symlinks supply the exact layout used
by upstream dependency cache entries. All archive source files and symlink
targets are verified before execution and after cache/build/export, including
on failed completion. The reviewed header-parser helper uses Lean's own parser
to enumerate the unchanged `Cslib` transitive import closure. Missing required
dependency oleans are an explicit blocker. `lake --no-build` checks their traces
before the actual build, so stale dependencies cannot silently trigger a full
Mathlib source rebuild. Unrelated cache misses remain reported even when not
part of the requested target. No imports are removed or replaced.

## Bounds And Commands

Read the scripts and the pinned source configuration before execution:

```sh
python3 -B scripts/acquire_cslib_arena.py
python3 -B scripts/acquire_cslib_arena.py --prepare --download
python3 -B scripts/test_cslib_acquisition.py
python3 -B scripts/build_cslib_arena.py
python3 -B scripts/build_cslib_arena.py --execute-reviewed --allow-cache-download \
  --cache-build-timeout 180 --cache-timeout 600 --build-timeout 600 \
  --export-timeout 300 --memory-mib 8192
```

Preparation never runs upstream code. All compilation and export steps deny
networking and allow writes only below `arena/large/cslib` and `/dev/null`.
Only the reviewed compiled cache process gets outbound TCP 443 and the macOS
DNS resolver socket. Curl is constrained to HTTPS, two parallel transfers,
15-second connection timeout, 60-second transfer timeout, and 128 MiB per
artifact. Its configuration, HOME, TMPDIR and cache directory are project-local.

`LEAN_NUM_THREADS=2` and `RAYON_NUM_THREADS=2` bound supported worker pools,
not arbitrary child-process counts. Aggregate process-group RSS is sampled
approximately every half-second and execution stops above **8 GiB**. This is
not a hard OS memory cap. Process groups are killed and reaped on completion,
timeout, or resource limit. Native exporter compilation has a separate
180-second timeout. Export output is stopped above target size plus 1 MiB;
the margin preserves small mismatches without accepting them. Import-closure
inspection has a 90-second cap; each of seven no-build dependency batches has
a 60-second cap. These are finite step bounds, not a single overall deadline.

Each run records commands, environment, sandbox profiles, limits, compiler
and helper-script hashes, timings, exit codes, source integrity, and output
comparison. No port-checker test is launched while parent testing is active.
An exact match still requires parent coordination before the existing import
command can update the shared manifest:

```sh
python3 -B scripts/fetch_arena.py \
  --import-generated cslib=arena/large/cslib/exports/cslib.ndjson
```

## Execution Status

Preparation passed for all ten archives and the exact toolchain. Six read-only
policy tests passed. The first bounded run compiled the cache tool successfully
in 10.914 seconds (41 Lake jobs) but DNS resolution failed because the worker's
initial sandbox omitted macOS's resolver socket. That cache process group was
stopped after 64.117 seconds; no source or platform change was made.
Its preserved report is
`arena/large/cslib/runs/1790712272546012000-91166/report.json`.

The exact first cache URL returned HTTP 200 outside that profile. Adding only
the resolver socket, following Apple's installed sandbox profiles, made a
sandboxed HEAD request return HTTP 200 too. A bounded retry reuses all prepared
sources and the compiled tool.

The retry downloaded and decompressed **8,906 of 8,908** cache files in
**288.609 seconds**, sampled peak RSS **86,624 KiB**. The normal master and
legacy endpoints both lacked `Mathlib` and
`Mathlib.Probability.Kernel.Invariance`. The first strict cache gate stopped
before any CSLib build. All 10,419 archive source files/links remained unchanged.
Report: `arena/large/cslib/runs/1790712387390790000-96398/report.json`.

After local helper syntax/API corrections, the read-only Lean header parser
successfully traversed the **unmodified** `Cslib` import closure: **211 CSLib
modules and 3,006 dependency modules**, with zero required oleans missing.
Neither unavailable Mathlib module occurs in that closure; `CslibTests` is not
the requested target. Diagnostic:
`arena/large/cslib/runs/1790712944496263000-13241/logs/000.stdout`.

The runner now preserves all Mathlib-cache misses in its report, but blocks on
missing or stale **required** dependencies. Seven offline `lake --no-build`
batches checked all 3,006 required modules successfully before CSLib compilation.
No source or import mutation was used to avoid a dependency. The fully offline
continuation command was:

```sh
python3 -B scripts/build_cslib_arena.py --execute-reviewed \
  --cache-build-timeout 180 --cache-timeout 120 --build-timeout 600 \
  --export-timeout 300 --memory-mib 8192
```

Its report is `arena/large/cslib/runs/1790713075649957000-16610/report.json`.
`arena/large/cslib/latest-build.json` points to completed build attempts;
preparation/cache status alone is not an exact CSLib export or a port verdict.

### Exact Export Obtained

The offline continuation finished at **2026-09-29 20:22:02 UTC**, exit 0,
with report status **`exact_match`**. All three published values matched:

| Measurement | Actual And Published |
| --- | --- |
| Bytes | 2,422,584,798 |
| Lines | 42,689,984 |
| SHA-256 | `bc5c88e028d02a3c0789de6efb9cd96e8506d1e96b3d26672d28ae3bb33d0b30` |

Final file: **`arena/large/cslib/exports/cslib.ndjson`**.

| Step | Seconds | Sampled Peak RSS (KiB) | Exit |
| --- | ---: | ---: | ---: |
| Original full Cslib build (3,233 Lake jobs) | 136.145 | 3,316,976 | 0 |
| Native exporter compilation | 6.233 | 1,436,928 | 0 |
| Full Cslib export | 83.610 | 5,533,152 | 0 |

All steps stayed within their wall and sampled-memory limits. All 10,419 pinned
source files/links were unchanged after cache use, build, export, and final
verification. The two absent Mathlib cache entries remain accurately reported;
they were not needed by this exact target, and no import was dropped.

The shared manifest SHA-256 before/after remained
`985cadef081276d8796bc7ee113a47b1f0b2de994f0892dd6027b1f821a52f30`.
It still reports **215/220 available**, **1,002,779,534 available bytes**, because
CSLib is staged locally and **not imported**. Kepler was notified of readiness
and explicitly told to retain the parent-coordination hold. The four remaining
unacquired exact inputs are Cedar, Con-Leche, Mathlib and Navier-Stokes-Euler;
CSLib remains one of five missing manifest entries until coordinated import.

No port checker was run while parent tests were active. An exact source export
is not a verified checker or a port acceptance result. All worker subprocesses
have ended. No upstream publication, global configuration, native core, checker
binary or other worker's source was changed.
