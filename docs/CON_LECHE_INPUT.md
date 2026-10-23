# Con-Leche Arena Input

This acquisition reproduces the published `con-leche` Arena input. It does not
modify a port or run Con-Leche as an oracle for Rocq/HOL. Availability of an input
is separate from whether either port checks it successfully.

## Immutable Recipe

`arena/large/con-leche/lock.json` pins:

- Arena revision `03b21e119045304d38249f426fcd86171fc253c5` and
  `tests/con-leche.yaml` SHA-256
  `53c835e1011d94b4f97a9f331b91cde3ace3f9f7adb53b97b2dff32b2f5a838e`.
- [Con-Leche source](https://github.com/leanprover/con-leche/tree/78ded4b6fc9a4d9ab809e8ca2c75c56537c41bff)
  revision `78ded4b6fc9a4d9ab809e8ca2c75c56537c41bff`, retaining its Apache-2.0 license.
- Lean **4.33.0**, revision `d8b18978322de05a8f3dba51ef03cf5461676c17`.
  The Init/Std acquisition's 4.34.1 toolchain is not substituted.
- Exporter revision `66f1fb4bc256072069767fce52d39480e4524869`, format 3.1.0.
- Module `ConLecheTests`, selecting exactly `ConLeche.model_exists`,
  `ConLeche.no_proof_of_False`, and
  `ConLeche.Frontend.scanLineSpec_eq_scanLineFwd`, in that order.

The expected output is **551,412,545 bytes**, **10,043,114 lines**, SHA-256
`b9ad1d958705760c6eb1c5cf3974ec0a4a3eb9dd765ff0648782fa49dee94a7f`.
These values are checked against the existing hash-locked published results,
not inferred from a local build. The published checker timeout is 720 seconds;
it is not the acquisition build timeout.

## Downloads

| Artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| Immutable source archive | 10,836,546 | `d89ec491c3fab19d7c07da0dd45c76f2f7ad18ee8fac405d5080319917e97c22` |
| macOS ARM Lean 4.33.0 | 556,168,134 | `db5274b669be270af048b5e4f1e0ce571df6750e411956b3e1e6fcc2012410c2` |

The toolchain digest/size came from the official
[Lean 4.33.0 release metadata](https://api.github.com/repos/leanprover/lean4/releases/tags/v4.33.0),
asset ID `508371048`. The source archive digest was measured from the immutable
GitHub codeload URL and then pinned. The acquisition script rejects other bytes.

```sh
python3 -B scripts/acquire_con_leche_arena.py
python3 -B scripts/acquire_con_leche_arena.py --prepare --download
```

The first command is read-only preflight. Preparation verifies existing
downloads instead of refetching them; `--download` allows missing ones to be
fetched over HTTPS, with a 600-second and exact pinned-size limit per download.
Source extraction rejects nonregular members and unsafe paths. Official
toolchain extraction checks member paths and runs under a write-restricted,
network-denying sandbox, with a 180-second timeout. Incomplete/unrecognized
destinations are preserved and cause failure, not overwritten.

Source and toolchain stay below `arena/large/con-leche`. No global elan/opam
configuration is changed. Python 3.11+ with tarfile's data extraction filter,
macOS `sandbox-exec`, `curl`, `tar` with Zstandard support, and `ps` are required.
The existing Arena provenance files and exporter Git objects are prerequisites.

## Reviewed Build

Review both new scripts, the pinned TOML configuration, and compile-time source
operations before invoking:

```sh
python3 -B scripts/build_con_leche_arena.py --execute-reviewed \
  --build-timeout 900 --export-timeout 300 --memory-mib 8192
```

The source has a declarative `lakefile.toml`, no package dependencies, and no
Arena pre-build hook. The inspected Lean sources contain embedded pin/test data
and elaboration-time annotation code; the source scan found no external-process
calls. `Kernel/BasisGen.lean` uses upstream meta evaluation and checked declaration
construction; it is not a new port proof or an extracted Rocq mapping. Upstream
shell helpers and default executables are not run.

The actual build command is the pinned local `lake --no-cache --no-ansi build
ConLecheTests`. Lake's module setup files handle the spaces/colon in the project
path without relocating storage. Exporter compilation and execution use relative
`LEAN_PATH` entries. A generated `#check` probe verifies all three exact selected
declaration names before the large export; it has a 60-second limit and does not
substitute similar names. Source archive members are hash-checked before and after
the build. Lake's `.lake` artifacts are retained for normal incremental retries;
source modifications are not silently accepted.

All build/export child processes run with networking denied and writes allowed
only under this acquisition directory and `/dev/null`. A sandbox probe must pass.
The environment is explicitly constructed, with local HOME/TMPDIR and
`LEAN_NUM_THREADS=2`; this is not a promise of at most two child processes.
The build has a 900-second wall limit; exporter compilation 120 seconds; export
300 seconds. Process groups are killed/reaped after completion or a limit.
Aggregate process-group RSS is sampled approximately every 0.5 seconds, stopping
above 8 GiB. This is a sampled stop threshold, **not a hard OS memory cap**.
An export larger than the published byte count is also stopped and not promoted.

Per-run reports preserve source hashes, compiler/exporter/script hashes, exact
commands, environment, elapsed times, exit codes, limit reasons, and sampled peak
RSS. `arena/large/con-leche/latest-build.json` points to the latest attempt.
Only an exact SHA/size/line-count match creates `exports/con-leche.ndjson` and a
subset manifest. Failed/partial outputs remain in the run directory.

## Availability Import

After exact reproduction and coordination with active test runs:

```sh
python3 -B scripts/fetch_arena.py \
  --import-generated con-leche=arena/large/con-leche/exports/con-leche.ndjson
```

This existing importer independently validates the input and preserves previous
generated imports. Neither new acquisition script changes the shared manifest,
corpus, checker implementation, or checker executable. No checker run is part
of this acquisition command.

## Execution Record

The source/toolchain archives matched their pins and preparation completed on
2026-09-29. The local 4.33.0 compiler successfully compiled the pinned exporter.
The first clean Con-Leche build completed successfully in **236.519 seconds**,
with sampled aggregate peak RSS **5,569,840 KiB**, under the stated limits. Every
source archive member still matched after the build.

However, the exact export failed after **32.964 seconds** with exit **-6**:

```text
Constant ConLeche.no_proof_of_False not found in environment.
```

The pinned source's `ConLeche/MainTheorem.lean:110` instead defines
`ConLeche.no_False_declaration`. No alias with the exact requested name was
found in the pinned Lean sources. The complete build and exporter logs are at
`arena/large/con-leche/runs/1790707262783770000-91152/`. Its partial output is
retained but is **not** an available or verified Arena input. The recipe/source
inconsistency is unresolved; no source change, theorem substitution, or alternate
revision is silently used to bypass it.

The new declaration probe was verified by this bounded incremental retry:

```sh
python3 -B scripts/build_con_leche_arena.py --execute-reviewed \
  --build-timeout 60 --export-timeout 60 --memory-mib 8192
```

The cached build passed in 0.525 seconds. The probe exited 1 after 1.049 seconds:
`model_exists` and `scanLineSpec_eq_scanLineFwd` resolved, while the exact
`no_proof_of_False` identifier was unknown. It stopped before export. Its report
is `arena/large/con-leche/runs/1790707694477323000-5391/report.json`.

Preparation with `--prepare --download` was rerun successfully using the verified
cached archives; no reinstallation or global configuration change occurred.
Four read-only policy tests pass:

```sh
python3 -B scripts/test_con_leche_acquisition.py
```

They check original-source integrity, rejection of a simulated source-hash
mismatch, process-group memory accounting, and rejection of invalid resource
limits. They do not prove checker correctness.

**Final acquisition status:** Con-Leche remains `missing_download`. The shared
manifest was not edited and remains at 215 available inputs and 5 missing
downloads (1,002,779,534 available bytes). A corrected provenance-consistent
source/recipe or the original exact published export is required to resolve
this reproducibility gap. All acquisition command sessions have ended.
