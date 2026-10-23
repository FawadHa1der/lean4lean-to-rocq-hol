# Inductive Metadata Mutation Tests

This is a separate adversarial transport/checker suite. It does not modify the
Arena corpus, its manifest, or `tests/arena`. It is not a proof of soundness,
a verified translation, or an oracle comparison with another checker.

## Inputs and Generation

The five small positive fixtures are Bool (`037_boolType`), actual primitive
Nat (`102_aNatLit`), Eq (`043_eqType`), Prod (`040_prodType`), and Empty
(`036_empty`). `tests/metadata/baseline-pins.json` records each Arena ID, source
path, byte size, and SHA-256 from the local manifest. Generation verifies those
entries and source bytes before reading their NDJSON. It reads no other corpus
inputs. The original manifest hash is recorded for provenance; unrelated new
manifest entries do not change these five pins.

```sh
python3 scripts/test_metadata_mutations.py --generate
python3 scripts/test_metadata_mutations.py --verify
python3 -m unittest discover -s tests/metadata -p test_mutations.py
```

Generation persists exact baseline copies, deterministic NDJSON cases, and a
separate `tests/metadata/manifest.json`. Every case records its expected result,
rationale, coverage dimension, source hash, case hash/size, and one structural
edit (one-based record number, JSON path components, old value, new value).
Each case starts afresh from its baseline: mutations are not accumulated.
Generation refuses to overwrite changed generated files. It never deletes or
rewrites the existing Arena suite. Verification reconstructs the mutation plan
and checks both persisted expectations and bytes against it.

All mutations retain valid JSON, field types, and already-defined wire-table
references. Numeric changes are small, not resource-exhaustion probes. The
matrix covers each exported inductive/constructor/recursor count and flag,
constructor parents and indices, `all` lists, constructor lists, universe header
arity, recursor names/types, missing/extra recursors, and each rule's constructor,
field count and body. Missing/extra rules are tested, and Bool/Nat exercise
reordered rules and constructor lists. Empty has an extra-rule case but no
meaningless missing-rule or reorder no-op.

Acceptance controls change exporter labels, reducibility hints, binder names,
binder-info, consistent universe alpha-names, and (where applicable) constructor
table presentation order. These must not be confused with semantic
constructor-list order or canonical recursor-rule serialization order. Controls guard against rejecting every
changed file. Expectations are solely test-runner data: no expected value,
rationale, manifest, or case hash is passed to the checker.

These expectations test this project's metadata/transport contract, not exact
equivalence to every upstream replay decision. At pinned Lean4Lean revision
`8223d223ed98661882e95d9d6a7126df7097cd76`, `Inductive/Add.lean:425` generates
rules in constructor order and `Replay.lean:245` compares complete recursor
records, including the ordered rule list. Rule lookup during reduction is by
constructor, so rule reordering is a metadata mismatch, not by itself a change
in reduction semantics. Replay reconstructs inductive declarations and does not
compare every supplied inductive flag/count afterward; it also checks only
recursors present in its input map. Thus the suite's complete-block requirement
and some inductive-metadata rejections are stricter than that replay path.
Conversely, consistent universe alpha-renaming is a project transport acceptance
control: upstream's derived record equality compares parameter names literally.
No alternative checker was run to establish these source-reading observations.

## Running a Checker

Options precede `--checker`, which consumes a literal argv list. The runner
appends one absolute NDJSON filename. It does not use a shell, concatenate source
code, or substitute expected verdicts. For a stable native Rocq build:

```sh
python3 scripts/test_metadata_mutations.py \
  --snapshot-binary build/rocq-check \
  --report tests/metadata/rocq-report.json \
  --checker build/rocq-check
```

Arbitrary wrappers and arguments also work, for example:

```sh
python3 scripts/test_metadata_mutations.py \
  --watch-file /absolute/path/checker.py \
  --checker python3 /absolute/path/checker.py --option 'value with spaces'
```

The executable is SHA-hashed before and after every complete run. Optional
`--watch-file` also fingerprints scripts or dependencies. `--snapshot-binary`
copies the first native executable into a temporary private directory and runs
that exact copy; it verifies source hash/stat identity before and after and the
snapshot hash after use. A changed executable/dependency invalidates the report,
sets counted coverage to zero, and exits 3. It cannot be reported as success.
The persisted suite inputs are also revalidated after execution. The temporary
executable is removed afterward. Snapshotting interpreter scripts
is not supported because their relative resources or `$0` can change semantics.

The checker has a per-process timeout (default 10 seconds), process-group cleanup,
and bounded stdout/stderr capture (default 4096 bytes each), using the existing
Arena process helper. The metadata runner does not use that helper's manifest
classification or expected-outcome machinery.

## Coverage Rules

Each exact positive baseline must return 0 before any mutation in that family
is executed. If it rejects, declines, faults, or times out, all of that family's
mutations are `not_covered`; none is credited as a successful rejection. A
baseline rejection remains visible in the report, not reinterpreted as a pass.

- Expected accept: only exit 0 is a successful control; exit 1 is `false_reject`.
- Expected reject: only exit 1 is a successful rejection; exit 0 is `false_accept`.
- Exit 2 is always `declined`, a coverage gap, even for a negative mutation.
- Timeout is a coverage gap; abnormal/unrecognized exits and IO failures are faults.

Unsupported flags or nonzero nested-inductive counts may decline before metadata
comparison in a limited checker. Such declines are visible gaps, not evidence of
invalidity or successful rejection. The negative expectation means that the
unchanged safe baseline must not be admitted with that metadata change; it does
not claim that every unsafe declaration is inherently an invalid Lean proof.

Runner exits: 0 only for complete coverage with no discrepancies; 1 for false
acceptance/rejection or execution faults; 2 for baseline/decline/timeout gaps
without such failures; 3 for harness integrity, configuration, or snapshot errors.
Reports retain all baseline outcomes and each mutation's actual code/diagnostic.

## Recorded Runs

The 2026-09-29 local run generated 237 independent cases: 210 negative mutations
and 27 acceptance controls, plus five exact baseline gates. Bool/Nat each have
57 cases, Eq/Prod each have 45, and Empty has 33. The additional cases cover every
constructor and rule individually instead of sampling a single representative.

### Integrated Snapshot

The run completed at `2026-09-29T18:32:25.517463+00:00`, recorded in
`tests/metadata/rocq-integrated-report.json`. All five baselines accepted, and
the report records valid, unchanged suite inputs and complete coverage:

| Outcome | Cases |
| --- | ---: |
| Correct rejection | 210 |
| Accepted positive control | 27 |
| Explicit decline / coverage gap | 0 |
| False acceptance or false rejection | 0 |
| Fault or timeout | 0 |

The report's source executable identity is identical before and after the run,
and its private native snapshot is also unchanged. Their SHA-256 is
`cea2e634f9d906387f2813dfda85fdf11697ae2eb45799ed2045e2aab6f5f23b`.
The 16 earlier unsafe-flag gaps are covered by correct rejection in this run.
This documentation records the existing report; the audit did not rerun the
checker. Complete coverage here concerns these 237 cases only, not HOL runtime
coverage, upstream verdict equivalence, or a formal soundness result.

### Earlier Snapshot

All five baselines accepted. The earlier native Rocq snapshot produced:

| Outcome | Cases |
| --- | ---: |
| Correct rejection | 194 |
| Accepted positive control | 27 |
| Explicit decline / coverage gap | 16 |
| False acceptance or false rejection | 0 |
| Fault or timeout | 0 |

All 16 declines were `isUnsafe` flag mutations. The run is therefore **incomplete
coverage**, and the runner correctly exits 2. The 194 rejections reported
declaration, duplicate-declaration, or undeclared-universe checks, not invalid
JSON or undefined wire references.

Source and copied executable SHA-256 were unchanged before/after the run:
`36803ed088fb518d9b716103179b25610e77cd48e651e5c15406798f770febb1`.
Full results are in `tests/metadata/rocq-report.json`. These observations apply
only to that executable snapshot; no formal verification claim follows.
