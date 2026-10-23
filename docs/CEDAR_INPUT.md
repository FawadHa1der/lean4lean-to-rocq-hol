# Cedar Arena Input

This task attempts the exact published `cedar` Arena export. It does not modify
the native Rocq/HOL core, change target names or expected outcomes, or count
independent stress exports as Arena coverage.

## Selection And Budget

The pinned Cedar and CSLib source/configuration recipes were reviewed before
choosing Cedar. At selection, the project filesystem had **916 GiB free** and
the host had **36 GiB RAM**. The acquisition requires at least 16 GiB free at
build start. This is a local working-space reserve, not an estimated input size.

| Candidate | Exact Output Bytes | Toolchain | Dependencies / Hook |
| --- | ---: | --- | --- |
| Cedar | 872,400,337 | Existing Lean 4.34.1 | Batteries; destructive directory-flattening hook not executed |
| CSLib | 2,422,584,798 | Lean 4.34.0 not yet installed locally | Mathlib plus 8 locked packages; `lake exe cache get` not executed |

CSLib's reviewed source revision is `990e65a685bed413f43b139db900a36ad5322a10`,
with Mathlib `5ed2965256430c3649e86755f9576b54eca72435`. It was not built or acquired
in this bounded task; its source availability is unchanged.

## Pins

`arena/large/cedar/lock.json` preserves the exact source/archive/toolchain pins:

- Arena `03b21e119045304d38249f426fcd86171fc253c5`, definition `tests/cedar.yaml`.
- [Cedar source](https://github.com/cedar-policy/cedar-spec/tree/017c35c3d1f856a0f8b62a66660ee6628870bbcf)
  `017c35c3d1f856a0f8b62a66660ee6628870bbcf`, retaining Apache-2.0 licensing.
- [Batteries source](https://github.com/leanprover-community/batteries/tree/f2effa3d803fda822b1f97b806c47cf2adfbcbc2)
  `f2effa3d803fda822b1f97b806c47cf2adfbcbc2`, exactly as Cedar's manifest specifies.
- Lean 4.34.1, revision `5045d0056413266e57c625dcd7c365b10e377c52`.
  The existing isolated toolchain is reused read-only; no global setup changes.
- Exporter `66f1fb4bc256072069767fce52d39480e4524869`, format 3.1.0.
- Whole module `Cedar`, with no declaration-selection argument.

The target is **872,400,337 bytes**, **15,316,781 lines**, SHA-256
`6b00afb2436da7d8c6e2a94cf70c8f6d41da28831c0ecae0541be9f6123fab82`.
It is cross-checked against the existing hash-locked published results.

| Archive | Bytes | SHA-256 |
| --- | ---: | --- |
| Cedar | 1,069,420 | `a2ccf74282941a07dcd2381400a86ab676572014595517c0d2972e70af10f7f4` |
| Batteries | 363,638 | `1987093d3e0af3c75084f48095a8eb0fac0751b11712c51fb05b31e71d64220b` |

Archive hashes were measured from immutable GitHub codeload URLs, then pinned.
Existing mismatched downloads are rejected, not silently replaced.

## Reviewed Execution

```sh
python3 -B scripts/acquire_cedar_arena.py
python3 -B scripts/acquire_cedar_arena.py --prepare --download
python3 -B scripts/test_cedar_acquisition.py
python3 -B scripts/acquire_cedar_arena.py --execute-reviewed --exporter-mode native \
  --build-timeout 900 --export-timeout 300 --memory-mib 8192
```

The first command is read-only preflight. Preparation bounds HTTPS downloads to
180 seconds and their exact pinned size. Extraction rejects traversal, absolute
paths, hard links and special files. It preserves only symlinks whose normalized
target stays within the source archive root, using tarfile's data filter too.
The three Cedar symlinks were individually inspected; their shell targets are
not executed. Nonempty incomplete/unrecognized extraction directories are
preserved and rejected. No upstream source file is edited.

The Arena hook deletes everything outside `cedar-lean` and moves that directory's
contents up. Instead, this acquisition simply uses the original `cedar-lean`
directory as the Lake working directory. The hook's text hash is pinned for
review drift detection; the hook itself is never passed to a shell.

The reviewed Lake configuration's documentation dependency is enabled only by
the `env=dev` configuration option. That option is not set. The actual Cedar
target uses Batteries, whose own manifest has no dependencies. A per-run
versioned `--packages` override points Lake to the unchanged, hash-verified local
Batteries archive. It changes dependency location only, not revision or source.
The original Cedar and Batteries `lake-manifest.json` files remain unchanged.

The build invokes the pinned `lake --no-cache --no-ansi --packages <override>
build Cedar`, including the target's original static-library facet. It does not
invoke upstream shell helpers, package tests, linters, documentation generators,
solver executables, or the project's other default targets. The reviewed
process-spawning functions are runtime definitions, not calls made by this
acquisition. Batteries' elaboration/initialization code is still upstream code
and runs within the restricted build sandbox, not outside it.

Build/export subprocesses deny networking and allow writes only under
`arena/large/cedar` and `/dev/null`. A sandbox probe must pass, with no unsandboxed
fallback. HOME/TMPDIR are per-run; `LEAN_NUM_THREADS=2` is set, but is not a hard
limit on child-process count. Aggregate process-group RSS is sampled about every
0.5 seconds and stopped above 8 GiB; this is **not a hard OS memory cap**.
Build wall time is capped at 900 seconds, native exporter compilation at 180
seconds (120 for the optional interpreted mode), and export at 300 seconds.
Native is the default exporter mode, matching Arena's execution method. The
exporter's pinned, dependency-free Lake configuration was reviewed before
compilation. Child process groups are killed/reaped on completion
or a limit. Output exceeding the expected byte count is not promoted.

All source files and symlink targets are checked against both archives before
building, after building, and after export. Reports retain source/compiler pins,
exporter hashes, exact commands, environment, timings, limits and logs. Only an
exact SHA/size/line match creates `arena/large/cedar/exports/cedar.ndjson` and the
local subset manifest. Neither script changes the shared Arena manifest.

## Import And Status

After exact verification and coordination with active Arena runs, the compatible
import command is:

```sh
python3 -B scripts/fetch_arena.py \
  --import-generated cedar=arena/large/cedar/exports/cedar.ndjson
```

The initial preparation rejected Cedar's internal symlinks before extraction;
they were inspected and safe in-tree link handling was added. The first build
attempt failed before compilation because the generated package override was an
array; the bundled Lake parser requires a versioned object. That local generator
was corrected without changing source/dependency pins.

### Completed Attempts

The Cedar build completed successfully in **140.662 seconds**, with sampled
aggregate peak RSS **2,993,200 KiB**. Cedar and Batteries source files and symlink
targets remained identical to their pinned archives before/after build and
export. All six read-only acquisition policy tests passed.

The interpreted exporter completed in **63.700 seconds**, exit 0, but produced a
nonmatching stream. Its report and output are at
`arena/large/cedar/runs/1790709601417215000-38505/`.

A bounded retry compiled the exact pinned exporter as a native executable,
matching Arena's execution style:

```sh
python3 -B scripts/acquire_cedar_arena.py --execute-reviewed --exporter-mode native \
  --build-timeout 60 --export-timeout 300 --memory-mib 8192
```

Native exporter compilation passed in **4.191 seconds**, the unchanged cached
Cedar build in **0.525 seconds**, and export in **27.212 seconds**, all exit 0.
Native export sampled peak RSS was **2,493,632 KiB**. Its report and output are
at `arena/large/cedar/runs/1790710068323688000-52480/`.
Both acquisition commands returned exit 1 because exact verification failed,
not because a build, memory limit, or timeout failed.

| Measurement | Published Target | Both Actual Exports |
| --- | ---: | ---: |
| Bytes | 872,400,337 | 872,400,493 |
| Lines | 15,316,781 | 15,316,784 |

Actual SHA-256:
`a83b3527d758581559202a990870c8fb5a997d8f95bbde15e2485cd96fa4db65`.
The expected SHA-256 remains unchanged:
`6b00afb2436da7d8c6e2a94cf70c8f6d41da28831c0ecae0541be9f6123fab82`.
An explicit `cmp -s` of the two complete `cedar.partial.ndjson` files passed.
No bytes/records were stripped, rewritten or selected to force a match.

### Unresolved Exact Reproduction

The two complete exports are preserved unchanged in their run directories as
**SUPPLEMENTAL source-pinned stress inputs**, indexed separately by
`arena/large/cedar/supplemental.json`. Their source integrity, hashes, and
native/interpreted byte equality were checked. They were not promoted to
`exports/cedar.ndjson`, not imported into the corpus, and not run through a port
checker. Source verification is not independent semantic validation, and these
inputs never count as official Arena coverage. All three extra records remain.

The discrepancy is three lines and 156 bytes; its cause has not been established.
The published metadata supplies exporter version 3.1.0 but no exact exporter
commit. The inspected upstream `lka.py` clones exporter `master`, and its test
cache key uses the YAML hash plus a cache-version integer rather than an exporter
commit. This limits provenance, but does not establish that caching caused this
mismatch. Native-vs-interpreted execution has been ruled out for these two local
runs. The original expected byte stream was not obtained; exact upstream build
provenance or that stream is needed to diagnose the difference conclusively.

Final source availability remains **215/220**, **1,002,779,534 available bytes**,
with Cedar, Con-Leche, CSLib, Mathlib, and Navier-Stokes-Euler still missing from
the shared manifest. No shared manifest, expected target, core source, checker
binary, or global configuration was changed. All worker command sessions ended.
