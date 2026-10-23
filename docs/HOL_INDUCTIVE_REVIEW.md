# HOL Inductive Admission Review

Read-only source audit, 2026-09-29. No HOL, core, frontend, or test files were
modified. The witnesses below are source-derived regression proposals, not
executed checker results. This is a bounded review, not a soundness proof or
an end-to-end compatibility certification.

## Findings

Status at the final source reread: P1 was addressed by a concurrent owner edit
and awaits runtime validation; P2 remains open. The original observations below
refer to the initial hashes recorded at the end, except where the follow-up
explicitly describes the updated sources.

### P1: Missing Primitive Guard in Initial Snapshot

`hol/environment_rules.ml:119` admits any fresh inductive and constructor names
whose generated metadata, field checks, and formation proofs satisfy its
premises. It does not distinguish primitive names. The implementation at
`hol/environment.ml:251` discharges those premises but adds no primitive-name
or primitive-shape check. Exact metadata matching cannot detect this omission:
the supplied claims can faithfully describe the wrong primitive declaration.

A minimal source-derived witness is an empty datatype named `Nat`, at
`Succ Zero`, with no constructors and claims equal to its generated entries.
It is the existing empty-datatype test at `hol/inductive_tests.ml:171`, with
its fresh name consistently changed to `Nat`. The reviewed HOL premises remain
satisfiable: names are fresh, there are no fields, the universe is positive,
and the empty eliminator is well formed. The same construction works for `Bool`.

Pinned upstream differs:

- `vendor/lean4lean/Lean4Lean/Environment.lean:127` invokes
  `Primitive.checkInductive` before inductive admission.
- `vendor/lean4lean/Lean4Lean/Primitive.lean:584` requires the precise Bool/Nat
  constructor shapes for safe, monomorphic, zero-parameter declarations in Type.
  Empty Nat or Bool fails this check.
- `vendor/lean4lean/Lean4Lean/Environment/Basic.lean:34` defines the reserved
  primitive-name set; `checkName` at line 54 rejects other uses unless the
  primitive recognizer authorized the block.
- `vendor/lean4lean/Lean4Lean/Inductive/Add.lean:154`, line 246, and line 486
  apply that name check to inductives, constructors, and recursors respectively.

The gap also permits an unrelated datatype to use a reserved constructor or
operation name, such as `Nat.zero` or `Nat.add`, as one of its constructors.
Freshness alone is insufficient. Existing ordinary admission has the analogous
freshness-only boundary at `hol/environment_rules.ml:112`; fixing only a
frontend inductive recognizer would not strengthen the certified relation.

Impact: the HOL admission certificate can authenticate a declaration that the
pinned Lean4Lean admission rejects. This is false acceptance relative to that
target, not an exhibited inconsistency in HOL or in the current generic
algebraic-datatype calculus. It becomes particularly dangerous if later literal
or primitive reduction rules assume these names already have their upstream
meanings.

Recommended correction: make primitive-name authorization and the supported
primitive shape part of the HOL admission premises. Until supported, decline
such declarations. Cover every generated name and coordinate the corresponding
ordinary-declaration policy. Add positive canonical Nat/Bool cases and negative
empty/mis-shaped Nat/Bool and foreign reserved-constructor cases.

Source follow-up: the owner added `hol/primitive_names.ml:33`, which constrains
Nat/Bool to their canonical universe and constructor shapes and checks every
generated name against the protected primitive-name set. Updated
`hol/environment_rules.ml:127` and line 176 include `l4_primitive_block` in
both admission and the detailed certificate; ordinary and axiom admission also
require an unprotected name. `hol/environment.ml:300` proves the extra premise.
The previously described primitive witnesses no longer satisfy the updated
relation. Source tests at `hol/inductive_tests.ml:174` cover canonical Nat/Bool,
wrong shapes/universe/order, and reserved names in unrelated blocks, axioms,
and definitions. This addresses the finding at source level; this audit did
not execute those new tests or assert that the modified HOL files load.

### P2: The Reserved `_nested` Reference Restriction Is Missing

The same HOL rule has no equivalent of
`vendor/lean4lean/Lean4Lean/Inductive/Add.lean:726`, `checkNoNestedAux`, called
on each constructor type at line 740 before nested-inductive processing. That
upstream check rejects constructor types containing a constant or projection
whose name has the `_nested` prefix.

A source-derived witness is a fresh singleton datatype `_nested.T : Type`, with
one nullary constructor `_nested.T.mk` and exact generated claims. Its constructor
type is `Const _nested.T []`. The reviewed HOL checks treat these as ordinary
fresh names and form the standard singleton eliminator; upstream rejects that
constructor type because its return constant uses the reserved prefix.
Alternatively, a later constructor field referring to an already certified
`_nested`-prefixed type has the same discrepancy.

Impact: another false acceptance relative to the pinned admission policy, not
a demonstrated logical contradiction. A blanket ban on all `_nested` names
would not exactly match upstream either: the cited restriction is a traversal
of constructor types. Mirror the actual restriction in a certified premise or
explicitly decline this unsupported namespace. Test both a prefixed result
type and a prefixed data-field type.

## Checks With No Additional Defect Found

The observations below apply only to the implemented subset: one monomorphic
datatype, no parameters or indices, closed positive result universe, closed
nonrecursive data fields, and direct recursive fields. They do not justify
silently accepting general dependent, mutual, nested, reflexive, or Prop-valued
inductives.

- Metadata coverage: `hol/inductive_syntax.ml:10` represents every modeled
  inductive/constructor/recursor role field. `hol/environment.ml:45` quotes all
  of them. `hol/inductive_entries.ml:24` compares complete entries after erasing
  only expression binder display names. Counts, flags, parents, indices, `all`,
  constructor order, header names/universe lists, types, rule names/field counts,
  ordered rule lists, and rule bodies are retained. No omitted role field was
  found in this path.
- Metadata authority: `hol/environment.ml:262` proves agreement between the
  candidate generator and `l4_generated`; the final premises include equality
  of caller claims with those generated entries. Candidate generation alone
  cannot certify an arbitrary supplied recursor RHS.
- Positivity boundary: data-field formation at
  `hol/environment_rules.ml:95` uses the prior environment, not provisional
  signatures. `hol/environment.ml:270` preserves that distinction. Direct
  recursion is the separate `L4Recursive` case, and global name freshness
  prevents a preexisting declaration from doubling as the new datatype.
  No path for a negative recursive field was identified in this restricted
  grammar. General positivity correctness was not established.
- Universe/elimination boundary: fields require `v <= u`, the result universe
  is closed and strictly positive, and generated recursors have `k = false`.
  This is a restricted implementation of the upstream field bound at
  `Inductive/Add.lean:225` and large-elimination/K decisions at lines 257 and
  289. Removing the nonzero premise without implementing those decisions would
  invalidate this review.
- Recursion shape: `hol/inductive_syntax.ml:72` passes all constructor fields
  to the selected minor and recursively calls only on direct recursive-field
  positions. The field/induction-hypothesis ordering matches the corresponding
  restricted upstream construction at `Inductive/Add.lean:378` and line 419.
  Enum, unary, and tree tests exist; they were read, not rerun for this audit.
- Iota boundary: `hol/environment_rules.ml:73` requires a generated recursor
  role, a rule in its authenticated list, exact universe/prefix/field arities,
  and typing of both sides at the same type. The missing standalone parent-name
  premise was not identified as a bypass: the public checked judgment also
  includes certified environment validity, and generated entries cannot enter
  through ordinary admission (`hol/environment_rules.ml:159`). Raw `l4_edef`
  derivability over an arbitrary unvalidated environment is not acceptance.
- Certificate boundary: `hol/environment.ml:72` checks empty hypotheses and
  the exact expected conclusion. Provisional signatures are used for formation
  only; they do not escape as a certified public environment before all
  admission premises are proved (`hol/environment.ml:286`).

## Integration and Expectation Boundaries

The current HOL metadata relation compares the entire claims list in canonical
generated order and preserves universe-parameter names literally. A transport
layer that accepts reordered constructor-table presentation or consistent
universe alpha-renaming must establish the connection to that canonical list;
it must not discard unrecognized entries or replace supplied metadata with
freshly generated claims and then certify only the replacement.

In contrast, reordering a recursor's rules is not merely table presentation.
Pinned `Replay.lean:153` derives structural record equality and
`Replay.lean:245` compares the full supplied and generated recursor. Upstream
generates rules in constructor order even though reduction searches them by
constructor (`Inductive/Reduce.lean:67`). The negative rule-order expectation is
therefore supported for replay metadata, not as an operational semantic change.

The 237-case Rocq result does not cover the two findings above: those witnesses
change an entire declaration coherently, rather than corrupting one field of
an already valid pinned fixture. Nor does the Rocq result establish HOL runtime
coverage. See `docs/METADATA_TESTS.md` for the recorded snapshot and the
distinction between project transport expectations and exact upstream replay.

No frontend audit, running-checker probe, proof of semantic correspondence to
Lean4Lean, or full audit of core conversion was performed here. Proving
`l4_evalid`/`l4_checked` establishes the defined HOL relation, not independently
that every rule of that relation matches upstream. The findings concern that
specification boundary.

## Reviewed Source Identity

Pinned upstream: clean `vendor/lean4lean` checkout at
`8223d223ed98661882e95d9d6a7126df7097cd76`. No alternative checker was used as an
oracle. Local HOL files were read while their owner was working independently.
The initial snapshot remained unchanged during the main read; the final reread
detected the primitive-guard update described above. Line references outside
that follow-up use the initial snapshot. Subsequent edits require rechecking
the affected findings.

| File | SHA-256 |
| --- | --- |
| `hol/inductive_entries.ml` | `a547097e6851d056c4b3af38ff7391da8f8bad2dd9e1a177dd9bd3aa53c02ec7` |
| `hol/inductive_model.ml` | `628c4e2b7e3eeccadb9d7fe10aac406a569ac456c5e02b17e2f2aedefce04732` |
| `hol/inductive_syntax.ml` | `5fe9f3cc56d043ac5340b4f652cee058de5800b18feac72a6f3b5991a3b30f2f` |
| `hol/inductive_tests.ml` | `6a5f29368dcbd7461ecd5e936feb48abfe911993e39ebd4966b001b9423900bd` |
| `hol/environment_rules.ml` | `ddb8fd238d7dc65d7691327c6213b831f060cc41572dd500b5af104934d4f892` |
| `hol/environment.ml` | `bb5ef96f6af7ec242f3a07d7eb84ec9ca2908757bbe888974485578a9700e20e` |

Primitive-guard follow-up identities; the other three inductive source files
are unchanged:

| File | SHA-256 |
| --- | --- |
| `hol/primitive_names.ml` | `d8c7b446b0dfcfc5b5de71579d80e6102bc89b7d10bb3be07ddba04b0ab8dc3f` |
| `hol/environment_rules.ml` | `eb01d12f622a5ec4464180562b2424e737f3dec3932d75c38bb1355dad83ae07` |
| `hol/environment.ml` | `f516163685707e7c164f7418c0cb8e8c924890e8bf95e4cdcb881e6c25066804` |
| `hol/inductive_tests.ml` | `8b02f2e810263801899cda480b3ab43deb5848f4c99517d64e7285e84507dbfa` |

Integrated Rocq report SHA-256, for the adjacent documentation update only:
`d75c98dc67b131314a93cf7fee5deb462b37531978967746484400dac2e87da1`.
