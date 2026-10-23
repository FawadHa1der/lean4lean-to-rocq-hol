# Arena Corpus and Independent Runner

Snapshot acquired on 2026-09-29. Work is local: no commits or publications.
The initial download-only import was extended with a bounded, reviewed,
sandboxed generation pass for 17 missing inputs. This infrastructure does not
decide proofs and does not supply expected outcomes to a checker.

## Provenance

- Source: <https://github.com/leanprover/lean-kernel-arena>, checked out under
  `arena/upstream`, HEAD `893a129cfa670a1bed3dddecd1e7f6d9262cd55d`.
- Published data: <https://arena.lean-lang.org/results.json>, revision
  `03b21e119045304d38249f426fcd86171fc253c5`, timestamp
  `2026-09-29 11:34:41 UTC`, workflow run `36543121707`.
- These source revisions differ, but `schemas/`, `tests/`, and `tutorial/`
  have identical Git content at both revisions. Both commits are retained.
- Published tarball: <https://arena.lean-lang.org/lean-arena-tests.tar.gz>.
  It is 3,577,155 bytes; SHA-256
  `77c5e99d12e154a7e140999bb7dc8eaedc0fcdd35108f0288654f990ec257860`.
- `results.json` is 4,421,096 bytes; SHA-256
  `2f1c2561908250e220bcae7ae359364802483fc889c56fd35698149ec3b46de5`.
- Format documentation is pinned to lean4export
  `66f1fb4bc256072069767fce52d39480e4524869`, `format_ndjson.md`, version 3.1.0.
  All acquired input headers declare NDJSON format 3.1.0. Exporter versions
  are a separate field: handcrafted files can report exporter 0.1.0.
- The tutorial's `lake-manifest.json` pins lean4export to
  `777c921eba89aac5f14cc388717935b5fa2cb739`. This does not establish the
  exporter commit for every published file: those files only record exporter
  version, Lean version, and Lean Git hash. Their exact bytes are SHA-pinned.

`arena/provenance.lock.json` records every download size/hash and revision.
`arena/definitions.json` records all 80 YAML definitions, their original hashes,
and parsed configurations. The bootstrap conversion used Ruby `YAML.safe_load`;
normal fetching, importing, testing, and running require Python 3.9+ stdlib only.
Source definitions are verified against `git show` at the published commit.
No YAML `run`, `pre-build`, or checker command is executed by `fetch_arena.py`.
The separate opt-in `fetch_arena_generate.py` executes only reviewed source
from the bounded scope described below, inside a macOS sandbox.
Original source and upstream notices are retained without modification.

The website URLs are mutable. `--download` rejects changed bytes instead of
silently updating the pin. Preserve the local downloads for exact reproduction;
a future refresh requires a new inventory and deliberately updated hashes.

## Default Inventory

The current manifest has **220 cases, 216 available and four missing exports**.
Available inputs total **3,425,364,332 bytes**. Its SHA-256 is
`d0ef9bd650fa4256cca4e4256ef45eda096e8ad3505945dad9c41a3f3d063b19`.
The three additions since the bootstrap report below are exact reproductions of
Init (347,555,345 bytes), Std (596,655,086 bytes), and CSLib (2,422,584,798 bytes).
There is no 128 KB checker input limit. Cedar, Con-Leche, Mathlib and
Navier-Stokes-Euler remain unavailable locally; acquisition issues are documented
in the corresponding `*_INPUT.md` files and `LARGE_INPUTS.md`.

Both ports have attempted all 216 available inputs in fresh full-inventory runs.
Neither run is complete proof coverage: declines, timeouts and missing exports
are not passes. See the README checkpoint table and individual hashed reports
for checker versions and actual resource limits.

The remaining inventory, schema-audit and transport counts in this document
describe the **initial 213-file bootstrap checkpoint**, not a later scan of the
three recovered library exports. Their historical reports are preserved.

## Newer Publication

The separately pinned 2026-09-30 publication at revision
`4c30c4ac4f14a3a899116beb3ea6131880e79a98` has **221 cases: 217 available,
four missing; 132 expected accepts, 71 rejects, and 18 either outcomes**.
Its manifest is
`build/workers/parent-arena-refresh-20261001/current-arena/manifest.json`, SHA-256
`747668adbac2069bfe65415551a1f7263f46a03ffe4039bc5756ff7fdf13662a`.
The default manifest above and all reports tied to it are unchanged.

The added `perf/proj-stuck-struct` input is 51,334 bytes / 916 lines, with a
published 50-second limit. It exercises conversion under a stuck projection;
the expected acceptance is a test expectation, not evidence that either port
accepts it. Its input SHA-256 is
`b2fed80e90e956f24bcbe898ce7cfef5ae4c92d0f81daf42e0a2a3c817012f6f`.
Cedar's published export also changed: 872,400,160 bytes, SHA-256
`a99bc2f7008185c2fb54b1cd6786c150ffcc50ff9a4a890fbca401f546cf8b39`.
It remains unavailable; the older Cedar bytes must not satisfy this new pin.

No proof execution against this refreshed snapshot is claimed. The attempted
26-case performance batch stopped during preflight on stale RSS evidence,
before starting a checker. All 26 selected cases remain unattempted; the other
195 were unselected. Source-level projection regressions and runner controls
do not replace execution of the complete Arena input. See the refresh's
`snapshot-report.json` and
`build/workers/rocq-arena221-perf26-authorization-01/TIMESTAMP-DIAGNOSIS.md`.

## Initial Inventory

`arena/manifest.json` inventories every published case, not just tutorial tests.
Paths are relative to the manifest and carry no good/bad directory marker.

| Category | Cases |
| --- | ---: |
| Published total | 220 |
| Expected accept / reject / either | 131 / 71 / 18 |
| Downloaded tarball | 193 (122 accept, 71 reject) |
| Additional static source inputs | 3 (`either`) |
| Additional exact local reproductions | 17 (15 `either`, 2 performance cases) |
| Available, hash-verified | 213 (124 accept, 71 reject, 18 either) |
| Missing downloads | 7 large library exports |
| Definitions | 80 |
| Static / leanfile-export / module-export definitions | 16 / 55 / 8 |
| Multiple generator | 1 definition, 141 published tutorial cases |

Available input size: **58,569,103 bytes, 1,146,468 lines**. The downloaded
tarball contributes 23,431,140 uncompressed bytes. The three recovered static
cases are `corner-cases/let-value-type-mismatch`, `corner-cases/positivity-whnf`,
and `corner-cases/proof-param-swap`; all match the published checksums.
The full inventory's published size is **12,593,277,972 bytes**; missing inputs
account for **12,534,708,869 bytes**. Missing files are not skips or declines.

The published tarball excludes files larger than 10 MiB AND all `either` cases.
The site workflow uploads test statistics and this filtered tarball, not the
omitted NDJSON exports. No public individual-input downloads were found in the
site-generation code. This is an acquisition limitation, not a decision to
exclude big cases. The importer accepts exact-match external generated files.

### Missing Large Inputs

| Case | Bytes | Upstream timeout (seconds) |
| --- | ---: | ---: |
| cedar | 872,400,337 | 940 |
| con-leche | 551,412,545 | 720 |
| cslib | 2,422,584,798 | 1800 |
| init | 347,555,345 | 500 |
| mathlib | 6,184,415,052 | 5680 |
| navier-stokes-euler | 1,559,685,706 | 2400 |
| std | 596,655,086 | 590 |

### Recovered Generated `either` Inputs

All 15 now match the published SHA-256 exactly. All have the `corner-cases/` prefix:

```text
alg-conv-trans-acc
alg-conv-trans-acc-left
alg-conv-trans-acc-right
alg-conv-trans-quot
alg-conv-trans-quot-left
alg-conv-trans-quot-left-def
alg-conv-trans-quot-right
eta-ctor
eta-rule-k
imax-right-successor
nested-nonuniform-param
proj-maybe-prop
proj-maybe-prop-past
subject-reduction-redex
subject-reduction-reduct
```

Generator recipes, remote revisions, selected declarations, and source paths
are preserved in each manifest case's `configuration`, including for missing
inputs. `tests/lean-toolchain` and tutorial toolchain currently specify 4.34.1;
external modules can use different toolchains. No generation success is inferred
from the existence of a Lean source file.

### Bounded Generation

`arena/generation.lock.json` pins the official Lean 4.34.1 ARM macOS release
asset (562,038,070 compressed bytes; SHA-256
`65f22a4f047738ec742667b3247e836a86ebf06eabc12655c3dee00637e37866`),
Arena source, current exporter, and the tutorial's separately pinned exporter.
The toolchain lives under `arena/generation/toolchain`, not the global elan
installation or other workers' toolchain directories. It uses about 2.7 GiB
unpacked; retain roughly 3.3 GiB including the compressed archive and outputs.
About 950 GiB was available before acquisition. No 12 GB corpus download or
large library build was attempted.

Source review covered the exporter, the six shared small-case Lean source
files, nested-inductive helper modules, and both magma generators. Existing
upstream kernel-bypass constructs are retained only to generate their intended
adversarial data; they are not checker implementations or soundness proofs.
The explicit macOS sandbox denies networking and confines writes to
`arena/generation` (plus `/dev/null`); it permits file reads and process execution.
The default per-step time limit is 600 seconds, with process-group termination.
There is no 128 KiB cutoff. The script compiles copied exact source blobs with
the pinned Lean binary and runs the exporter via `lean --run`, without invoking
arbitrary Lake hooks or changing the upstream checkouts.

The successful generation pass took **46.882 seconds** across recorded steps,
excluding toolchain acquisition. All 17 exports match published hashes and sizes.
The two larger recovered files are `perf/magma-string-n4` (17,353,248 bytes) and
`perf/magma-string-pair-n9` (17,354,635 bytes), retaining published checker
timeouts of 70 and 130 seconds. Total recovered bytes: **35,129,593**.
`arena/generation-report.json` records commands, runtime, toolchain binary hash,
script hash, sandbox profile, output hashes, and exact-match status.

An initial generation attempt failed because an absolute PATH entry included
the colon in the project name. `arena/generation-initial-path-error.json`
retains that attempt's results; the generator now uses relative PATH and
LEAN_PATH entries. No unsandboxed fallback was used.

```sh
python3 -B scripts/fetch_arena_generate.py --execute-reviewed \
  --toolchain-dir arena/generation/toolchain/lean-4.34.1-darwin_aarch64
```

New outputs are not silently trusted or relabeled. The report compares them
to the published hashes; `fetch_arena.py --import-generated ID=PATH` is the
separate exact-match import step. The main manifest records `origin:
generated_local` and retains each published checksum.

## Usage

Run from the shared project root (whose name includes spaces and a colon).

```sh
# Offline verification, safe extraction, and manifest regeneration.
python3 -B scripts/fetch_arena.py

# Fetch missing locked downloads and source commit objects; no builds.
python3 -B scripts/fetch_arena.py --download --source

# Import an independently generated large file, requiring exact published bytes.
python3 -B scripts/fetch_arena.py --import-generated 'mathlib=/path/to/mathlib.ndjson'

# Any language: append filename to the supplied executable's argv.
python3 -B scripts/test_arena.py --checker ./path/to/checker --report arena/reports/checker.json

# Explicit placeholder; protect $IN from expansion by the invoking shell.
python3 -B scripts/test_arena.py --checker './path/to/checker --input "$IN"'

# For an executable reading IN, or reading standard input.
python3 -B scripts/test_arena.py --checker ./path/to/checker --input-mode env
python3 -B scripts/test_arena.py --checker ./path/to/checker --input-mode stdin

# All nonselected cases remain visible as skips in the report.
python3 -B scripts/test_arena.py --checker ./path/to/checker --select 'bugs/*'
python3 -B scripts/test_arena.py --checker ./path/to/checker --skip 'mathlib=operator-requested omission'

python3 -B scripts/test_arena.py --inventory
python3 -B scripts/test_arena_schema.py
python3 -B scripts/test_arena_adversarial.py
python3 -B -m unittest discover -s tests/arena -p 'test_*.py' -v
```

`--checker` is parsed into argv with `shlex`, never passed to a shell. Quote
paths containing spaces inside the option value. Shell pipes/redirection are
not interpreted; use `--input-mode stdin` instead. `IN` is always set to the
absolute input path. No outcome or manifest path is supplied to the checker.
Checker commands and captured diagnostics are recorded for reproducibility.

Input sizes and SHA-256 are verified before invocation. Outputs are drained
continuously, with only the first 16 KiB of each stream retained by default.
`--max-log-bytes` adjusts this diagnostic cap, not the checker's verdict.
Case-specific published timeouts are retained; otherwise the fallback is
30 seconds (`--default-timeout`). `--timeout` explicitly overrides every case.
On POSIX, cleanup may kill the owned process group only while its directly
owned session leader remains unreaped. After reaping, it performs read-only
PID/group absence checks; a surviving or inaccessible group fails cleanup
verification instead of authorizing a signal to a potentially reused identifier.
Windows supports direct-process termination only. This runner is not a security
sandbox, a hard memory limit, or containment for descendants that escape their
session. Invoke only reviewed local checkers in an appropriately constrained
environment.

The launcher requires the default SIGCHLD disposition and sole-reaper ownership.
It does not reset a caller's signal handler. Primary execution failures and
secondary reader, input-close, signal, reap, and absence-check errors remain
visible separately. Unexpected cleanup failures cannot become checker declines
or logical rejections. If cleanup is unverified, later available cases are not
launched; their rows remain in the report as explicit skips. Successful cleanup
after an ordinary checker timeout does not by itself skip subsequent cases.

The integrated runner's 2026-10-01 validation passes 85 controls: 68 mock-only
tests and 17 real Python-process fixture tests. All 36 direct fixture children
were reaped and their cleanup verified. This count covers `test_runner.py` and
`test_cleanup.py`, not every test discovered under `tests/arena`, and is not a
count of Arena proof files. The first combined mock failure and its path-alias
diagnostic are retained; the fresh passing reports are under
`build/workers/parent-arena-main-validation-05`. No proof checker was launched.

## Verdict Accounting

Checker exit codes remain visible unchanged:

| Exit | Meaning | Runner classification |
| --- | --- | --- |
| 0 | accept | correct_accept, wrong_accept, or acceptable_either |
| 1 | reject | correct_reject, wrong_reject, or acceptable_either |
| 2 | decline | declined, never acceptance or rejection |
| 3 | fault | fault |
| other / signal | unexpected checker failure | fault |

An exit-2 unsupported/resource decline is valid protocol behavior, but not
evidence of completeness or independently verified resource exhaustion. Its
diagnostics are retained; the runner does not invent a more specific cause.
Timeout, execution error, corrupted input, missing download, missing generated
case, and explicit skip have separate statuses. `either` does not contribute
to correct-accept or correct-reject counts. There is no automatic file-size skip.

Runner exit codes (not checker exit codes) are: **0** all cases correctly
decided or acceptable `either`; **1** any wrong verdict, fault, timeout, or
input/execution error; **2** no such failure but coverage gaps remain. Thus
declines, skips, and missing inputs cannot make a full run green. Inventory-only
mode exits zero without claiming execution. JSON reports are atomically updated
after each case; `finished_at: null` identifies a partial run.

## Schema Findings

`arena/schema-audit.json` is an observational audit of all 213 acquired inputs,
not a proof-validity result or a formal NDJSON validator. Its examples preserve
physical source lines. `arena/manifest.schema.json` describes the harness
manifest, not the NDJSON wire schema.

- No blank lines, duplicate indices, or late metadata were observed.
- Names and levels have implicit index 0; no input defines either explicitly.
  Expression index 0 is explicitly defined in 212 files; it is not an implicit
  expression. The sparse-index case starts expressions at 4 instead.
- All 6,482 `def`, 6,171 `thm`, and 24 `opaque` records contain `all`.
  All 1,123 inductive types and 1,131 recursors also contain `all`.
  Axioms/constructors/quotients do not require that field.
- All 1,123 inductive types contain `isReflexive`: 1,100 false, 23 true.
  Optional defaults for these fields are compatibility policy, not a requirement
  demonstrated by this acquired corpus.
- `other/level-index-out-of-order` defines level 2 on line 3 and level 1 on
  line 4, with already-defined references. `other/sparse-name-index` defines
  name 2 on line 2 and expression 4 on line 3. Do not require contiguous IDs.
- No `mdata` expression was observed; absence here is not justification to
  remove support. The seven missing large library inputs have not been scanned.

The inspected parent-owned `frontend/wire.ml` has the corresponding implicit
zero entries, associative indexed tables, and required metadata fields.
After the parent's build finished, `build/frontend/inspect-wire` was run on
every acquired input: **213 parsed, 7 missing, zero parse rejections, declines,
timeouts, or faults**. All 71 published reject cases are syntactically readable;
their rejection remains a logical checker obligation. The parsing-only results
and hashes of the executable, parser source, and input manifest are recorded in
`arena/transport-report.json`. This is not proof acceptance. Frontend edits/tests
remain parent-owned.

## Adversarial Suite and Verification

`arena/adversarial/manifest.json` is separate from the published corpus count.
Its 220 cases comprise 213 canonical-JSON, content-addressed-filename copies
of all acquired inputs and seven local semantic obligations (one accept control,
six rejects). The latter cover universe mismatch, unbound variables, unknown
constants, self-reference, non-proposition theorems, and a valid prefix followed
by an invalid declaration. They are explicitly local generated tests, not
published Arena cases or oracle-confirmed new discoveries. The baseline and
generator hashes are retained. Parent-owned malformed-wire tests are not
duplicated here.

Run the generated suite with the same runner and
`--manifest arena/adversarial/manifest.json`. Its expected outcomes are only
read by the harness. Content-derived input filenames do not expose outcomes.

Verification performed: repeatable offline importer, whole-corpus schema audit,
213-input compiled transport sweep, 17 exact local reproductions, metamorphic generation, and **31 Python
unit/integration tests passed**.
Tests cover all verdict combinations, either accounting, no expected-outcome
argument, filename/env/stdin input, spaces, timeouts and descendant cleanup,
signals, bounded binary logs, missing executables/files, integrity failures,
manifest validation, symlink escapes, unsafe archives, duplicates, wrong archive
buckets, atomic failed imports, all 220 inventory entries, and all 213 checksums.

The parent owns actual Rocq/HOL checker runs and their full reports. The reports
here are corpus/generation/transport results, not logical verdict coverage or
port correctness claims.
