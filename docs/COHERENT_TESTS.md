# Coherent Declaration Mutation Tests

This separate suite tests whole-declaration name changes that single-field
metadata corruption does not cover. It writes only its own artifacts under
`tests/coherent`; it does not modify the Arena corpus, `tests/arena`, or
`tests/metadata`. No HOL/frontend code is changed. Expected outcomes are test
runner data, never checker inputs. This is not a formal soundness result or an
alternative-checker verdict comparison.

## Inputs and Coherence

`tests/coherent/source-pins.json` pins three small Arena files by manifest ID,
path, size, and SHA-256: Empty (`036_empty`), Bool (`037_boolType`), and PUnit
(`042_pUnitType`). Only these corpus files are read. Selected manifest identity
fields are checked, not expected verdicts. The original manifest hash is kept
for provenance; unrelated new corpus entries do not invalidate the three pins.

The fourth positive baseline appends a closed nonrecursive datatype to the
exact Empty seed:

```lean
inductive Coherent.Box : Type where
  | mk : Empty -> Coherent.Box
def Coherent.boxType : Type := Coherent.Box
```

The generator constructs that block's dependent recursor and its single rule,
using a small NDJSON expression interner. The fixture is labeled as derived,
not as an unmodified exporter result. Harness tests independently inspect its
de Bruijn expression shapes. It must also accept as a baseline under the tested
checker before its field mutations count toward coverage. No Lean elaborator
or other checker supplies its expected verdict.

Each mutation starts from its own positive baseline and retargets name-table
nodes, adding explicit parent components where needed. Shared references carry
the change through types, constructors, recursors, rule bodies, declaration
lists, and later definitions. All non-name-table rows remain identical. A
coherent Bool constructor-name swap updates both nodes simultaneously. The
persisted manifest records the requested component-list renames, all affected
name IDs (including descendants), expected verdict, rationale, upstream source
references, and baseline/case SHA-256 and size.

## Upstream Basis

Expected outcomes were selected from source before executing the checker under
test. The clean upstream revision used is
`8223d223ed98661882e95d9d6a7126df7097cd76`; relevant source files are SHA-pinned
alongside the fixtures. Their contents are checked on generation and execution.

- `Lean4Lean/Primitive.lean:584` recognizes canonical Bool and Nat shapes;
  `Environment.lean:127` calls it before inductive admission. Empty Nat/Bool,
  polymorphic singleton impostors, and coherently swapped Bool constructors
  do not meet these requirements.
- `Environment/Basic.lean:34` lists protected primitive names and line 54
  rejects unauthorized use. `Inductive/Add.lean:246` checks constructor names.
  An unrelated PUnit constructor renamed to hierarchical `Nat.add`, `Nat.zero`,
  `Nat.succ`, `Bool.false`, `Bool.true`, `String.ofList`, or `Char.ofNat` must
  therefore be rejected even when all references and rules agree with it.
- `Inductive/Add.lean:726` checks structural `_nested` prefixes in constructor
  expression constants and projection owners; line 740 applies the check to
  each constructor type. A prefixed singleton result or later constructor field
  is forbidden. An empty prefixed type has no constructor types to traverse,
  so that check is vacuous and the corresponding control should accept.
- A constructor's *name alone* is not the constructor expression. A prefixed
  constructor name with an ordinary constructor type is an acceptance control.
  Recursor expressions mentioning that constructor do not change the scope of
  the cited check. This suite exercises constants, not projection-owner cases.

Names are structural. `['_nested', 'T']` and `['_nested.T']` are different names;
the latter is one legal string component, not a reserved namespace. Similarly,
`['Nat', 'add']` is protected but `['Nat.add']` is not. Controls also cover a
non-root `_nested` component, a near-prefix `_nestedSuffix`, an ordinary child
of `Nat`, and a protected-looking suffix below another namespace. These controls
catch text-based overblocking as well as reject-all implementations.

## Matrix

There are 47 mutations, 23 expected rejections and 24 acceptance controls:

| Baseline | Mutations | Purpose |
| --- | ---: | --- |
| Empty | 9 | Empty primitive impostors, reserved operation name, legal empty prefix/dotted controls |
| PUnit | 21 | Singleton prefix, primitive type/constructor names, structural-name controls |
| Bool | 9 | Noncanonical Nat, prefix, coherent constructor swap, ordinary-name controls |
| Empty plus closed-field Box | 8 | Isolated prefixed field, name-shape and constructor-name controls |

These are coherent renamings, not random malformed JSON, dangling references,
metadata count mismatches, or outcomes inferred from the checker being tested.
Harness tests verify every wire reference precedes its use and that constructor
parents, indices, lists, recursor names, rules, and field counts remain coherent.

## Commands

```sh
python3 scripts/test_coherent_mutations.py --generate
python3 scripts/test_coherent_mutations.py --verify
python3 -m unittest discover -s tests/coherent -p test_coherent.py
python3 scripts/test_coherent_mutations.py \
  --snapshot-binary build/rocq-check \
  --report tests/coherent/rocq-report.json \
  --checker build/rocq-check
```

`--checker` consumes the remaining literal argv; one absolute filename is
appended, without shell evaluation. Arbitrary wrappers and arguments work:

```sh
python3 scripts/test_coherent_mutations.py \
  --watch-file /absolute/path/checker.py \
  --checker python3 /absolute/path/checker.py --option 'value with spaces'
```

The runner reuses only the existing process, snapshot, classification, and
artifact-integrity utilities. It does not use existing suite verdicts as an
oracle. Timeouts default to 10 seconds, child process groups are cleaned up, and
stdout/stderr captures are bounded to 4096 bytes each. Native snapshot mode
runs a private executable copy and checks both its SHA-256 and the original
executable's identity before/after. Scripts use `--watch-file` instead. Harness
source dependencies are watched automatically. Inputs and source pins are
verified again after execution; changes invalidate the report and counted
coverage. Changed generated files are never silently overwritten.

All four baselines run first. A family's baseline must return 0 without timeout
before any of its mutations execute. Otherwise those cases are `not_covered`,
never successful rejections. Exit 2 is always a decline/coverage gap. For
mutations, exit 3 or abnormal exits are faults; timeout is a visible gap. Only
0 and 1 satisfy an expected acceptance or rejection respectively.

Runner exits: 0 for complete success; 1 for mutation verdict discrepancies or
faults; 2 for baseline/decline/timeout gaps without such failures; 3 for invalid
configuration or integrity/snapshot failures. Reports retain actual baseline
codes and diagnostics, including baseline faults. Always report the binary
hash with observed results; those results apply only to that snapshot and this
bounded matrix.

## Recorded Native Run

`tests/coherent/rocq-report.json` records the run completed at
`2026-09-29T18:58:58.844626+00:00`:

| Outcome | Count |
| --- | ---: |
| Positive baselines accepted | 4 |
| Correct rejection | 23 |
| Accepted mutation control | 24 |
| Decline, baseline gap, or timeout | 0 |
| False acceptance, false rejection, or fault | 0 |

The runner exited 0. Its source executable, private executable snapshot, watched
harness dependencies, and suite inputs were unchanged. Native executable SHA-256:
`22eb979996c6332400f107217ad95d64d182a11a7d8eb808f6d604ed823bf1f4`.
The three prefixed-field rejections reported `checked=2`: the empty dependency
and its definition were accepted before the later Box declaration was rejected.
All structural-name acceptance controls passed, including empty `_nested`
families, dotted single-component names, and a prefixed constructor name alone.

The 12 harness unit tests passed, including transport-reference/coherence
checks, independent derived recursor shapes, baseline gating, literal argv,
reject-all/accept-all detection, pin/tamper protection, and dependency-change
invalidation. Verification checks 51 persisted inputs (four baselines and 47
mutations). These observations do not establish behavior outside this matrix,
HOL coverage, or formal correctness.
