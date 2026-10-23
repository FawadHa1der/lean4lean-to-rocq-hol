# Indexed HOL Review

## Result And Scope

No concrete false-acceptance defect was identified in this bounded source review.
This is not a soundness, equivalence, or completeness proof. In particular, an
LCF theorem about the defined object judgment does not by itself prove that the
judgment faithfully implements all of Lean's semantics.

Reviewed: the single-family indexed generator, `l4_index_ok`, dependent field
formation, iota rule 19, exact generated metadata, and the frontend candidate
adapter. The source snapshot predates the subsequent neutral-K work. No later
working-tree edits or later server image are covered by this review.

No production, frontend, native, or client files were changed. After the parent
released the matching indexed server, all prepared requests completed and the
parent was notified that the socket was free. No subsequent server is needed.

## Runtime Finding

**P2 compatibility gap, not false acceptance:** two source-justified positive
Prop-only recursors declined with `HOL proof construction: TAC_PROOF: Unsolved
goals`, despite their common positive baseline accepting:

- `sortelim-coherent/hidden-data-prop-only`: constructor result `I b y y`,
  with one hidden Bool-valued field; 3.360 seconds.
- `sortelim-coherent/nested-index-prop-only`: constructor result
  `I b y ((fun z => z) x)`; 3.604 seconds.

Upstream `Inductive/Add.lean:258-276` requires exact field-variable membership,
so both should have a Prop-only recursor. Their constructor types, minor
premises, recursor types/universe lists, and RHS binder types were changed
coherently. The corresponding forged-large variants also declined; they did
not accept.

A likely proof-search site is the negative membership obligation in
`environment.ml:561-564` / `indexed_syntax.ml:122-125`. For the hidden-field case
it must prove `~MEM (L4BVar 1) [L4BVar 0; L4BVar 0]`; for the nested case it must
also distinguish a BVar from an App. The local rewrite lists do not explicitly
include expression-constructor injectivity/disjointness. This is a source-based
lead, **not a confirmed root cause**: the runtime diagnostic does not identify
the failing conjunct. The immutable witnesses and report permit the native
owner to instrument that proof boundary on a later image.

## Runtime Results

[indexed-report.json](../tests/hol_indexed_audit/indexed-report.json) completed at
`2026-09-29T20:35:16.056492+00:00` on the matching 717-checkpoint indexed image,
not the newer K/member-cache working tree.

- **7/7 baselines accepted**, including genuine Eq, dependent PSigma, and both
  independently written iota identities.
- **67 cases executed: 15 accept, 4 reject, 48 decline**; no wrong verdicts,
  faults, integrity changes, outer timeouts, or observed worker timeouts.
- The 48 declines comprise **46 negatives and 2 positive controls**. The four
  code-1 results are frontend duplicate-declaration-name checks. There is no
  claim of 50 logically proven negative rejections.
- All source-name, binder, forward-declaration, and constructor-presentation
  controls accepted; the coherent in-order result-index control also accepted.
- Eq wrong-index/wrong-result and PSigma wrong-dependent-field/wrong-result
  all declined with typed-conversion failures. Both original iota baselines
  and both binder-renamed iota controls accepted.
- Fixture, runner, client, and provenance checks remained intact. Client SHA256:
  `b71273f60ae608b43294530702bf8f6d180deeee6c6916270890039f342f5d8d`.
- Report SHA256: `f54a307f23882d2ca851c6c00fd414dc5278e0044daacdf5cdbe117cebd6092a`.

The suite exits **2** because coverage is incomplete; this is not a suite pass.
All requests have ended and the parent may stop/reap the existing server.

## Identity

The immutable [snapshot manifest](../tests/hol_indexed_audit/snapshot/manifest.json)
records 39 inputs captured at `2026-09-29T20:15:53.097850+00:00`, including four
small Arena exports, upstream reference files, bridge bytecode/interfaces,
project source closure, and selected review-only source files.

- Review manifest SHA256: `7677c7e691c7a42884b0ff7e97577960615396e6d8bfeddb62fba5988c2003fa`.
- Indexed READY provenance SHA256: `19aa5c31e75e63e3859b643f897815b4a46ff6e423b38de3189d7507a99be34d`.
- READY time: `2026-09-29T20:17:19.555805+00:00`.
- Startup snapshot SHA256: `90b7800e195bc392d12ab5a2f81e93e6920280a375b8c5cd56d34dbd2b6f4607`.
- Pinned upstream revision: `8223d223ed98661882e95d9d6a7126df7097cd76`.

All **27** project inputs recorded by that READY manifest match the preserved
review copies. See the [persisted comparison](../tests/hol_indexed_audit/runtime-comparison.json)
and [READY manifest copy](../tests/hol_indexed_audit/indexed-startup-provenance.json).
The old family server was a different source image; its provenance is retained
only as historical comparison, not as evidence for indexed execution.

These hashes identify project filesystem inputs. They do not attest executed
runtime state, external HOL/OCaml libraries, dynamic libraries, semantics, or
correspondence between bridge bytecode and its separately preserved source.

## Checked Boundaries

### Dependent Contexts

[indexed_syntax.ml](../tests/hol_indexed_audit/snapshot/hol/indexed_syntax.ml),
lines 32-51 and 60-115, keeps data domains in their original parameter and
preceding-field context. Inserting `offset` binders uses cutoff `j`, so earlier
fields below `j` are not shifted along with parameters. The independent fixture
decoder checks the genuine PSigma constructor's second field as
`App (BVar 1) (BVar 0)` under `[a, B, A]`; inside its minor premise this becomes
`App (BVar 2) (BVar 0)` under `[a, motive, B, A]`.

For a recursive field at position `pos`, `l4_index_move` first inserts the
remaining `k-pos` constructor fields, then motive/minors above the `k` fields,
then preceding induction hypotheses. Its recursive argument reference is
`k-1-pos+h`. For example, `k=4`, `pos=1`, `offset=3`, `h=1` moves a preceding
field at BVar 0 to BVar 4 and parameter A at BVar 2 to BVar 9; the recursive
argument is BVar 3 and the motive is BVar 7. This agrees with the named context
`[ih0, f3, f2, f1, f0, minor1, minor0, motive, B, A]`.

Upstream `Inductive/Add.lean:335-388,419-446` binds all constructor fields before
induction hypotheses and supplies the actual recursive indices to recursive
calls. No offset discrepancy was found for the direct-recursive representation.
This is a source trace, not exhaustive runtime coverage of recursive indices.

### Positivity And Formation

[environment_rules.ml](../tests/hol_indexed_audit/snapshot/hol/environment_rules.ml),
lines 172-202, requires each field to be a type in the **header plus prior
environment**, extending its context one field at a time. The constructor types
are also formed in this restricted environment. The header itself is formed in
the **prior environment**. Full generated-environment formation is an additional
check, not a replacement for those earlier checks.

Data fields must contain no occurrence of the new family. Direct recursive
fields are reconstructed with uniform parameters; their index count is exact,
and their indices must not contain the new family. Constructor result indices
have the same no-self-occurrence guard and exact arity, and constructor formation
checks their dependent types. Thus same-block constructors or the new recursor
cannot establish field or header formation merely because they appear in the
final generated environment.

This matches the relevant upstream boundaries in `Inductive/Add.lean:157-164,
184-235,452-460`. HOL's syntactic direct-recursive subset is narrower than
upstream's weak-head normalization and positive function-valued recursive
fields. Such differences can cause declines, not evidence of invalidity.

### Large Elimination And K

`indexed_syntax.ml:122-133` checks a non-Prop singleton field using **exact
membership** of `BVar (k-1-j)` among constructor result indices. It does not
search for a nested occurrence. The field-sort list has the same length and
order as the field list because `l4_index_fields_valid` constructs them together.
Uniform parameters are separate variables and cannot substitute for one of
these field references.

This matches upstream `Inductive/Add.lean:258-276`: every non-Prop field must
occur as an exact argument of the constructor result. The suite deliberately
distinguishes `I y x` from `I y ((fun z => z) x)`. For this upstream routine the
latter does not qualify merely because it beta-reduces to the former.

K is true exactly for a universally Prop-valued singleton with **zero fields
beyond parameters**, matching upstream `Add.lean:289-296`. An Eq constructor has
zero such fields even though the family has an index; a constructor with one
proof-valued field is not a K target. Neutral-major K reduction is not present
in this snapshot and is outside this review's runtime claim.

`environment.ml:510-564` uses small ML universe valuations to choose candidate
flags. The admission predicate requires both flag equivalences, proved by HOL.
Positive universe facts go through `level_truth`/`arithmetic`; negative facts
use a certified countervaluation. Sampling alone cannot discharge admission.

### Metadata And Candidate Extraction

[hol_check.ml](../tests/hol_indexed_audit/snapshot/frontend/hol_check.ml),
lines 106-168, recognizes exact applications at declared universe parameters,
uniform parameter BVars, and the expected argument count. Fields retain the
full local context. Although candidate construction drops constructor parameter
prefixes, it retains the original claims, and their agreement with the generated
block is a HOL obligation. A mismatched prefix cannot be silently discarded.

`inductive_entries.ml:27-31` requires equal claim lengths, distinct claim names,
and membership of every anonymized claim in generated entries. Together with
generated-name distinctness in `l4_index_ok`, this admits outer presentation
permutations but not a duplicate substituted for a missing declaration. It
erases binder display names, not recursor flags, indices, types, universe lists,
RHS terms, or rule-list order. Upstream `Replay.lean:153-156,199-218` likewise
reconstructs the inductive and postpones constructor/recursor comparison;
`RecursorRule` and `RecursorVal` use derived equality.

External declaration forward references are a scheduling question. The pinned
`frontend/replay.ml:135-185` schedules inter-block dependencies and rejects
external cycles. It deliberately does not turn same-block dependencies into
prior declarations; the restricted logical formation checks above still apply.

### Iota Rule 19

`environment_rules.ml:113-130` authenticates the safe, one-motive recursor and
selected rule, checks universe/prefix/parameter/field/index counts, and requires
**both the complete redex and the instantiated RHS to have the same type**.
The RHS receives parameters, motive, minors, and constructor fields, not the
recursor indices. That is upstream `Inductive/Reduce.lean:91-106`'s convention.

`environment.ml:185-219` splits that prefix separately from indices and proves
all eight static conditions plus both typing premises. The rule does not rely
solely on matching a constructor name or field count. In particular, arbitrary
incompatible recursor indices or dependent fields must not bypass redex typing.
The suite supplies genuine Eq and PSigma blocks plus independent typed
reduction identities and wrong-index/field/result negatives.

## Witnesses

The [generator](../tests/hol_indexed_audit/witnesses.py) reads only the pinned
copies of `043_eqType`, `086_PSigma.snd`, `076_sortElimPropRec`, and
`095_projDataIndexRec`. It does not run Lean, Rocq, another checker, or an exporter
to obtain expected outcomes. Expected verdicts and rationales exist only in the
runner manifest and are never supplied to the checker.

There are **7 baseline gates and 67 cases: 17 accept controls, 50 negatives**.
PSigma's baseline removes projection definitions but retains its genuine
inductive block. Eq/PSigma iota baselines add independently written named-term
definitions. The coherent SortElimProp baseline is statically compared against
the genuine export, modulo binder display information, before being used to
gate coherent constructor/recursor variants. It is not presumed accepted merely
because that static comparison succeeds.

Coverage includes dependent-field capture/scope errors, constructor parameter
prefixes, recursive index arity/self-occurrence/nonuniformity, field-in-index
large elimination, K including proof-field controls, current-block references,
duplicate/missing claims, ordered rules, forward declaration transport, structural
source renaming, and typed iota. The real two-constructor permutation control is
on the Bool prerequisite; singleton indexed subjects have no nontrivial
constructor-list permutation.

Some negatives intentionally leave other metadata unchanged. Those can expose
false acceptance, but a rejection/decline cannot establish which premise caught
the error. They do not independently certify positivity. The coherent
large-elimination variants change constructor type, minor premise, recursor type,
and rule RHS together to avoid that particular confounder.

Every case is gated on its own positive baseline accepting in that run. Return
0 means accept, 1 reject/malformed, **2 coverage gap**, and 3 fault. A timeout is
not a proven rejection. Reports record all codes and distinguish an unexecuted
case from an executed decline. Fixture hashes and runner/client identities are
checked across execution; reports refuse an existing output path.

Offline validation: **8 tests passed**, covering deterministic hashes, table
references, de Bruijn closure, genuine-export derivation, coherent reconstruction,
dependent-context golden terms, provenance comparison, and baseline/decline
accounting. These tests validate the harness, not HOL or Lean semantics.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 tests/hol_indexed_audit/test_witnesses.py
PYTHONDONTWRITEBYTECODE=1 python3 tests/hol_indexed_audit/witnesses.py --verify
```

The completed run used this command. The report is no-overwrite; any future run
needs a new report path and an explicitly released, matching server:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 tests/hol_indexed_audit/witnesses.py \
  --report tests/hol_indexed_audit/indexed-report.json \
  --runtime-provenance build/reports/hol-indexed-runtime.json \
  --runtime-sha256 19aa5c31e75e63e3859b643f897815b4a46ff6e423b38de3189d7507a99be34d \
  --checker python3 scripts/hol-check.py --socket /private/tmp/hol-run-qxe_b2pj/s --timeout 10
```

## Remaining Limits

No positive recursive indexed Arena export, mutual/nested family, normalized
telescope, or later neutral-K
extension is covered by the new fixture gates. The general connection from the
HOL inductive/iota definitions to Lean semantics remains a separate proof
obligation; no amount of mutation-suite success discharges it.
