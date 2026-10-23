# Nested Inductive Elimination And Admission

`rocq/NestedTransform.v` is a changed Gallina port of
`ElimNestedInductive` in `vendor/lean4lean/Lean4Lean/Inductive/Add.lean`
(approximately lines 550-703), pinned at
`8223d223ed98661882e95d9d6a7126df7097cd76`. The upstream authors are Mario
Carneiro and Lean4Lean contributors; the license is Apache-2.0, preserved in
`rocq/LICENSE` and `rocq/NOTICE`. This module transforms syntax. It is not an
admission procedure or a proof that the transformation preserves semantics.
Restoration and checked admission are implemented separately in
`rocq/NestedAdmission.v`, following the same pinned upstream file's
`Result.restoreNested`, `mkAuxRecNameMap`, and `Environment.addInductive`.
`rocq/NestedRegression.v` supplies independent computational regression proofs
for both modules. Parent-owned extraction and adapter integration are present;
the regression module is not part of the checker implementation.

## API

```coq
eliminate_nested : nat -> environment -> list name -> nat ->
                   list ind_spec -> result nested_elimination
```

Arguments are `fuel env ps nparams specs`. `ind_spec` comes from `Inductive.v`;
local-variable state, fresh locals, application, and telescope helpers come
from `InductiveUtils.v`. The result fields are:

| Field | Meaning |
| --- | --- |
| `nested_params` | Common parameter locals opened from the first original type, in telescope order. |
| `nested_context` | Context containing those locals, including dependent parameter domains. |
| `nested_specs` | Original specs in order, followed by discovered auxiliaries; all constructor bodies rewritten. |
| `nested_mapping` | Discovery-ordered `(existing_inductive_partial_application, auxiliary_name)` pairs. Keys use the original parameter locals, not constructor-specific locals, and exclude indices. |
| `nested_aux_names` | `map snd nested_mapping`, in exactly the same order. |
| `nested_aux_count` | Number of generated auxiliary types, counting every member of each expanded existing mutual family. |

For example, a field `List (Tree A)` becomes `aux A`, with mapping
`(List (Tree original_A), aux)`. The auxiliary's type and constructors are
closed over the common parameters. The mapping keys intentionally retain
the returned original free locals for later restoration.

## Transformation

The transformation opens the first `nparams` raw Pi binders of each constructor
with fresh locals, traverses the remaining expression in preorder, and closes
the telescope afterward. Opening does not normalize or type-check domains:
those domains may mention new constants not yet installed in the environment.

An application is a candidate only when its head names an existing inductive,
it supplies at least that inductive's parameter count, and one of those
parameter arguments contains an `EConst` naming a type in the growing new
mutual block. If it is a candidate, **all** its parameter arguments must have
no loose bound variables. Common parameters are free locals at this point;
bound variables inside a parameter's own lambda or Pi are not loose. Indices
do not participate in this detection and are retained in the replacement.

Parameter applications are canonicalized by simultaneous renaming from the
current constructor's locals to the original locals. Memoization follows
Lean's expression equality within the shared syntax representation: binder
names and binder annotations are ignored, but the let nondependency flag is
compared. The latter needs an additional check because shared `expr_eqb`
ignores it.

A new key expands the old inductive's **entire mutual family**, in its recorded
order, even when the occurrence names a later family member. Each old type and
constructor type is universe-instantiated, has its old common parameters
instantiated with the actual arguments, and is closed over the new common
parameters. Auxiliary names are private numeric names under `_rocq_nested`.
Fresh-name search avoids existing and pending type, constructor, and recursor
names. Constructor names preserve the old suffix after replacing the owner
prefix, including numeric suffix components.

Replacement does not descend beneath the replaced application. Newly appended
auxiliary specs are subsequently visited by the same growing worklist. This
rewrites their still-old constructor references and discovers deeper nested
applications, such as `List (List Tree)`.

## Admission Boundary

The caller supplies an already checked environment and raw closed declaration
syntax, with no preexisting free-local IDs. Existing family and constructor
metadata must be authenticated by admission, not copied unchecked from wire
records. Safety handling remains caller-owned; the regression suite below
exercises safe declarations, not the separate `InductiveSafety.v` wrapper.

`admit_inductive_nested fuel env types ctors recs` implements this sequence:

1. Run `prepare_inductive` on the wire group; retain all original members.
   Reject constructor types that use the reserved `_nested` namespace.
2. Run `eliminate_nested fuel env ps nparams specs`.
3. Run `derive_inductive` on `nested_specs`, including every auxiliary. This
   performs the actual type, parameter, positivity, and elimination checks and
   derives metadata independently of source metadata.
4. Restore the generated types, constructors, recursors, names, and metadata
   using `nested_mapping`, `nested_params`, and `nested_context`.
5. Run mandatory `verify_members` against the complete original wire group.
6. Infer every original nested mapping expression in the restored environment
   and `nested_context`. Return that environment only after all checks succeed.

When no auxiliaries were produced, metadata is still compared before returning
the generated environment. When auxiliaries exist, only the original types
and constructors and the restored recursors are admitted. Auxiliary type and
constructor declarations do not escape into the final environment.

Restoration reopens and recloses common parameter telescopes, substitutes
mapping locals while lifting inserted de Bruijn indices under binders, and
preserves application indices. Auxiliary constructor prefixes revert to the
existing inductive's prefix. Auxiliary recursors become `Main.rec_1`,
`Main.rec_2`, and so on with decimal string suffixes; universe arguments are
preserved. Restored recursor rule constructor names and right-hand sides are
compared along with all other wire metadata.

The implementation visits application arguments before restoring their head,
and substitutes the supplied common parameter arguments into mapping patterns.
Upstream's replacement traversal is preorder and uses the opened common
parameter locals. The closed round-trip and admission tests include dependent
common parameters, but do not establish general equivalence of these choices.

New specs contain **placeholder metadata**, including empty `ind_all`, zero
indices/fields/nested counts, and false recursive/reflexive flags. These are
not derived facts and must never authorize reduction or skip a check. Original
metadata is retained only as source data; it is not an oracle. Do not run wire
preparation on the generated placeholders, or directly insert `nested_specs`
into the admitted environment. No auxiliary trust flag is introduced.

The regression work does not modify restoration, admission, extraction, or
build wiring. Arena execution and full-report ownership remain with the parent;
the closed proofs below are not an independent rerun of that corpus.

## Outcomes And Limits

- `Accept r` means only that this bounded syntax transformation completed.
- Empty groups, missing declared parameter binders, universe arity mismatches,
  and nested parameter arguments containing loose bound variables reject.
- Exhausted transformation, search, or worklist fuel returns `Decline OutOfFuel`.
- Missing/inconsistent existing family records, unexpected existing type
  telescopes, and constructor names lacking the owning inductive's prefix
  return `Decline UnsupportedDeclaration`. The non-prefix case is an explicit
  compatibility limit, not a verdict that the source declaration is invalid.

Every recursive traversal defined in `NestedTransform.v` decreases explicit
fuel. Fuel is a depth/worklist bound, not a global instruction or allocation
counter: sibling branches reuse the smaller budget, and existing
syntax/list/environment utilities retain structural recursion. Restoration's
expression traversal uses fuel; its substitution, lookup, and telescope
helpers use structural recursion on expressions, lists, and counts. External
per-test time and memory limits are still appropriate. No external Lean
checker, expected-result table, new Gallina axiom, proof admission, or unchecked
cast is used. Logical checks and normalization belong to checked derivation,
not the syntax-elimination pass.

## Verification

On 2026-09-29, **64 closed computational regression proofs** compiled and
passed kernel checking: 24 in `NestedTransformRegression` and 40 in the new
`NestedRegression.v`.

The 24 transformation regressions cover
unchanged nonnested types, nested chains, canonical memoization across
constructors, dependent common parameters and universes, indexed types, whole
mutual families including second-member selection, loose versus internally
bound variables, name collisions, constructor prefix handling, let flags,
malformed arity/telescopes, and fuel exhaustion. These are transformation
regressions, not trusted expected outcomes in the checker or a soundness proof.

The 40 transformation/restoration/admission regressions cover:

| Group | Count | Checked behavior |
| --- | ---: | --- |
| Local substitution | 6 | Capture avoidance under lambda, Pi, and let; accumulated depth; unmapped locals; simultaneous substitution. |
| Restoration helpers | 12 | Auxiliary heads, indices, numeric constructor suffixes, parameter/field arguments, arity rejection, recursor universe arguments, decimal names, opened Pi/lambda telescopes, nested argument restoration, and fuel decline. |
| Namespace recognition | 3 | Reserved constants and projection owners; similarly spelled nonreserved prefixes. |
| Empty admission | 5 | Accepting nonnested baseline; forged K flag, nested count, missing recursor, and impossible rule reject. |
| Container admission | 1 | Independently specified `Box` type, constructor, recursor, and iota rule pass checked admission. |
| Nested tree | 10 | Accepting tree with a leaf and `Box Tree` field; one auxiliary; hidden auxiliary declarations; forged nested/field/K metadata, missing auxiliary recursor, forged rule body/constructor name, and reserved namespace mutation reject. |
| Dependent parameters | 3 | Accepting nested tree over `(A : Type) (a : A)`; constructor elimination/restoration round trip with two context locals; forged auxiliary rule rejection. |

The four admission baselines (Empty, Box, Tree, and dependent Tree) must actually
return `Accept`; a decline or an unrelated rejection fails their proofs.
Mutation tests specify exact `Reject MalformedDeclaration` results. Both tree
baselines obtain their environment by first admitting the handwritten Box
declarations; they do not install an unchecked fixture environment. Expected
types, metadata, recursors, and iota rules are handwritten, using syntax and
binder helpers for notation, rather than obtained from `derive_inductive` or
another checker. Symbolic helper fixtures are explicitly not admission tests.

These proofs establish only the stated **closed instances**. They do not prove
a general capture-avoidance theorem, transformation/restoration equivalence,
kernel soundness, unsafe-inductive behavior, or corpus-wide correctness.

Verification used an isolated source snapshot at
`/private/tmp/nested-regression-verify.zvsvcY`, including the parent
`stats_unsafe` extension and the updated checker/primitive dependency stack.
Dependencies were compiled in order: `Syntax`, `Universes`, `Checker`,
`InductiveUtils`, `Primitives`, `Declarations`, `Inductive`, `NestedTransform`,
`NestedAdmission`, `NestedRegression`. An initial snapshot caught a concurrent
primitive/checker record mismatch; a fresh complete snapshot compiled without
that error. Remaining compilation warnings were existing `From Coq`
deprecations.

The new module directly imports `Syntax`, `InductiveUtils`, `Inductive`,
`NestedTransform`, and `NestedAdmission`. Add it after `NestedAdmission` in the
parent-owned build; it does not require another regression module or
`InductiveSafety`.

With dependencies built, the commands from `rocq/` are:

```sh
sh ../scripts/toolchain-exec.sh rocq compile -Q . LeanPort NestedRegression.v
sh ../scripts/toolchain-exec.sh rocq check -silent -o -Q . LeanPort LeanPort.NestedRegression
```

`rocq check` reports no axioms, no type-in-type dependencies, no unsafe
fixpoints, and no inductives with assumed positivity. This certifies the
Gallina definitions and regression proofs, not full Lean-kernel semantic
soundness. `Print Assumptions` for the nested acceptance and forged-rule proofs
also reports that they are closed under the global context.
