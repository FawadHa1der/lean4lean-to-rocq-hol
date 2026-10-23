# HOL Export Regression Tests

This standalone suite targets the HOL export-to-certificate path, including
wire translation, replay ordering, generated inductive claims, and dependent
conversion. Its inputs are ordinary NDJSON exports; its expectations are runner
data and are never passed to the checker. It neither calls another checker as
a verdict oracle nor modifies HOL, frontend, Arena, metadata, or coherent suites.

## Baselines and Cases

Three small Arena sources are pinned by manifest ID, relative path, size, and
SHA-256 in `tests/hol_exports/source-pins.json`: canonical Nat (`102_aNatLit`),
Bool (`037_boolType`), and Empty (`036_empty`). Relevant upstream admission and
export-parser source files are pinned too. Only those corpus inputs are read;
the source manifest's expected outcomes are not used. Its whole-file hash is
provenance only, so unrelated new entries do not invalidate selected pins.

Seven positive baselines gate 97 cases: 46 acceptance controls and 51 negative
targets. Every generated file, rationale, recipe, baseline identity, and SHA-256
is recorded in `tests/hol_exports/manifest.json`.

| Baseline family | Cases | Construction |
| --- | ---: | --- |
| Nat | 17 | Pinned canonical inductive plus a definition of its type; no literals |
| Bool | 17 | Exact pinned bytes |
| Empty | 15 | Exact pinned bytes |
| Monomorphic tree | 24 | Pinned Empty plus the datatype below |
| Literal at 2^53 | 8 | Canonical Nat plus a dependent identity |
| Literal at 2^63 | 8 | Canonical Nat plus a dependent identity |
| Literal at 2^256 | 8 | Canonical Nat plus a dependent identity |

The derived tree uses only closed data fields and direct recursive fields:

```lean
inductive HolExports.Tree : Type where
  | tip : HolExports.Tree
  | label : Empty -> HolExports.Tree
  | node : HolExports.Tree -> HolExports.Tree -> HolExports.Tree
```

The fixture builder serializes the dependent recursor and all three reduction
rules. A static test independently states the node minor and recursive RHS
using de Bruijn indices. This checks fixture structure, not typing soundness.
The separate tree baseline must actually accept before any tree mutation can
count toward runtime coverage. Derived fixtures are labeled as such, not as
untouched exporter output.

## Acceptance Controls

- Consistent ordinary declaration/family name changes, binder display-name
  erasure, and binder-info changes. Nat family renaming uses the literal-free
  baseline, avoiding an implicit dependency on the primitive name `Nat`.
- Bijective renumbering of name, universe, and expression table IDs, plus
  regrouping table records while retaining backward wire references.
- Reversed declaration records: definitions appear before the inductive blocks
  they use. All table nodes still precede their use. This tests `Replay.schedule`
  rather than invalid forward table references.
- Reversed constructor-table presentation, preserving the logical constructor
  list, indices, and ordered rules. The bridge must connect original supplied
  claims to canonical ordering, not discard or regenerate claims unchecked.
- A dependent tree identity from `P tip` to `P (fold (node tip tip))`, which
  requires recursive iota conversion. Merely returning a well-typed Tree value
  would not test that conversion path.

The supported language subset is intentionally small: monomorphic, single
inductives in Type, closed fields, direct recursion. No polymorphic inductive,
mutual, indexed, nested-family, Prop-elimination, projection, or unsafe support
is presumed. Ordinary declaration types may quantify dependent functions.

## Exact Literal Checks

The export format carries `natVal` as decimal **text**, not a JSON float or
machine integer. Generation uses Python's exact integers only to construct
decimal strings. For each large N, the positive baseline has the shape:

```lean
def literalIdentity : (P : Nat -> Type) -> P N -> P N :=
  fun P h => h
```

Negative targets retain the same body and premise but change the conclusion to
`P (N + 1)`, `P (N - 1)`, or `P (N + 2^64)`. These applications are to an
arbitrary bound P, not a potentially constant definition. Accepting one would
expose a conversion or representation error; checking only `N : Nat` would not
detect truncation. A separate positive uses `N + 1` on both sides. Another
uses decimal leading zeros on only one occurrence, which must denote the same
natural after parsing.

JSON-number and exponent-text variants are explicit malformed **wire** tests,
separate from logical conversion failures. Their JSON syntax remains valid.

## Negative Admission Targets

The suite changes inductive counts/flags, constructor indices, recursor K/minor
metadata, missing/reordered rules, and supplied rule bodies. All non-wire
negative cases preserve defined references and closed expressions. Ordered
recursor-rule metadata is not the same as constructor-table presentation:
upstream generates rules in logical constructor order and replay compares the
complete recursor record, even though reduction searches rules by constructor.

Coherent guard cases are justified by pinned Lean4Lean revision
`8223d223ed98661882e95d9d6a7126df7097cd76`:

- `Primitive.lean:584` and `Environment/Basic.lean:54` require authorized
  primitive shapes and names. Empty Nat/Bool, cross-renamed primitive families,
  and unrelated constructors called hierarchical Nat.add/Nat.zero are negative
  targets even with coherent metadata.
- `Inductive/Add.lean:726` traverses constructor expression constants and
  projection owners for the structural `_nested` prefix. Tree result and field
  types exercise the constant path. For the field case, the empty dependency
  itself remains legal; only the later Tree.label domain is forbidden.
- Empty prefixed families have no constructor expressions and are controls.
  `['_nested', 'T']` differs from the single component `['_nested.T']`;
  similarly `['Nat', 'add']` differs from `['Nat.add']`. Dotted result, field,
  and constructor-name controls catch string-based overblocking.

The suite does not claim the frontend already supports every acceptance control.
A decline on a valid control exposes a support gap, not a proven invalid input.

## Running

```sh
python3 scripts/test_hol_exports.py --generate
python3 scripts/test_hol_exports.py --verify
python3 -m unittest discover -s tests/hol_exports -p test_hol_exports_suite.py
```

After an initialized server is available and exclusively free for this run:

```sh
python3 scripts/test_hol_exports.py \
  --timeout 25 \
  --watch-file scripts/hol-check.py \
  --runtime-note 'Parent-provided warm HOL NatLit checkpoint 434; max case time 10s' \
  --report tests/hol_exports/hol-report.json \
  --checker python3 scripts/hol-check.py \
    --socket /private/tmp/hol-run-shc4uci6/s --timeout 10
```

The shown socket is a task-local example, not a discovery mechanism. Do not
share concurrent suite requests with the parent's sequential server. Do not
start a new server from actively changing HOL sources. The runner does not
start, reload, stop, or edit the server. Generic checker argv also works: options
precede `--checker`, and the runner appends one absolute filename without shell
evaluation. It never sends an expected result, rationale, hash, or manifest.

The outer timeout must exceed the worker limit and client transport grace.
Its default is 45 seconds; the example allows 25 seconds around a 10-second
worker request. Output capture defaults to 4096 bytes per stream. The existing
process helper kills/reaps its checker process group on outer timeout; the warm
server remains responsible for killing/reaping its forked worker. Outer timeout
does not attest server cleanup or prove the input invalid.

The checker client executable, runner dependencies, and optional `--watch-file`
dependencies are hashed before/after. Fixture bytes, source pins, and the full
deterministic plan are rechecked after execution. Changes invalidate the report
and zero counted coverage. Existing suites and changed generated files are
protected from overwrite. Current file hashes cannot attest which bytes a warm
HOL parent loaded earlier: record the actual startup/checkpoint provenance in
`--runtime-note`, and do not describe these hashes as a server attestation.

## Exit Semantics

All seven baselines run first. Only exit 0 without timeout opens a family's
gate. Otherwise its mutations are not run and are `not_covered`, never credited
as successful negative checks. Baseline codes and diagnostics remain visible.

| Checker result | Meaning in this suite |
| --- | --- |
| 0 | Acceptance; success only for an acceptance control, false acceptance for a negative target |
| 1 | Rejection/malformed-input result; success only for a negative target |
| 2 | Decline, including failed HOL proof search; always a coverage gap, never a proven rejection |
| 3 or abnormal exit | Fault, not a logical verdict |
| Outer timeout | Coverage gap, not a rejection |

Manifest `expected: reject` is a negative test target, not a prediction that HOL
can prove rejection or must return 1 rather than decline. In particular, a failed
metadata/conversion proof search may correctly return 2 under the current API.
The report separately counts actual codes 0, 1, and 2 for baselines and mutations;
it never merges code 2 with code 1 or reports all negative nonacceptances as passes.

Runner exits: 0 only for complete accept/reject coverage without discrepancies;
1 for mutation discrepancies or faults; 2 for baseline/decline/timeout gaps
without such failures; 3 for configuration or integrity failures. Raw observed
counts remain present even when report validity is false.

## Verification Status

Infrastructure verification: 14 unit tests passed. They cover reference
resolution, closed-term shapes, independent recursive-rule structure, transport
invariance, reversed declaration order, exact large decimal values, namespace
distinctions, baseline gates, all 0/1/2 mappings, fault/timeout handling, literal
argv, and artifact/dependency integrity.

No alternate checker, newly loaded HOL server, or expected-verdict oracle was
used to assign these expectations. Static fixture verification and exit-0 kernel
certificates are different claims; neither establishes a general soundness
theorem or formal correspondence to upstream Lean.

## Recorded Warm-Server Run

`tests/hol_exports/hol-report.json` records the run completed at
`2026-09-29T19:28:37.044891+00:00`. It reused the parent-provided NatLit checkpoint
434 server, after the Arena runner was no longer active. The parent subsequently
confirmed exclusive access. No mutable HOL source was reloaded. All requests
finished and the server was released back to the parent for shutdown.

| Outcome | Count |
| --- | ---: |
| Baseline accept (0) | 7 |
| Mutation accept (0) | 42 |
| Mutation reject (1) | 6 |
| Mutation decline (2) | 49 |
| Wrong verdict, fault, or outer-process timeout | 0 |

Inputs and watched client/harness identities were unchanged; report validity is
true. Coverage is **incomplete**, with 48 cases covered and 49 gaps. Runner exit
was 2, not success. Client script SHA-256:
`ca8c89f18ea927753669c2f7a5239b2cedaa0a1e0a6d919c7e5031a3d1ed03c8`.
Runner SHA-256:
`0477e754c4a7ba7abfb3a0c576050f5cc9862aedf55812a05049294e27349325`.
These are client/harness identities, not hashes of the loaded HOL kernel state.

Four acceptance controls declined:

- `nat/control-constructor-table-order`, `bool/control-constructor-table-order`,
  and `tree/control-constructor-table-order` returned code 2 with
  `HOL proof construction: TAC_PROOF: Unsolved goals`. This identifies a claim
  presentation/canonical-order transport gap, not an invalid declaration.
- `tree/control-iota-dependent-index` returned code 2 at the worker's 10-second
  wall limit. Its ordinary tree baseline accepted; this dependent conversion
  path remains a resource/coverage gap at that limit.

The other 45 declines were negative targets: 28 metadata cases, eight coherent
primitive/namespace guards, and nine unequal-large-literal comparisons. All nine
unequal-literal comparisons hit the 10-second worker limit. They did not accept,
but this run did **not** establish rejection of unequal large indices or a
complete precision guarantee. Positive equal/next/leading-zero large literals
and forward-declaration controls accepted for all three sizes.

All six code-1 rejections were the malformed JSON-number/exponent `natVal`
transport cases. No semantic negative is credited as a proven rejection here.
There were ten worker wall-limit events total (nine unequal-literal comparisons
and one positive tree conversion). The worker reported each as code 2, with
child-killed-and-reaped diagnostics; these are already included in the 49
declines and are distinct from the zero outer-process timeouts.
