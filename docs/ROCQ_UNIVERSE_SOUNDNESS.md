# Universe And Substitution Proofs

The additive `rocq/UniverseSoundness.v` and `rocq/UniverseCompleteness.v` modules
prove properties of the existing
`Universes.v` implementation. The later `UniverseInstantiation.v` and
`UniverseExpression.v` modules prove properties of the existing substitution
functions in `Syntax.v`. These additions do not replace the normalizer or change any
checker result, fuel setting, parser, extraction override or primitive rule.

## Proved Statements

- Successful auxiliary normalization preserves the guarded natural-valued
  interpretation, for arbitrary valuations, guard lists, offsets and fuel.
- Successful outer normalization preserves the universe's interpretation.
- An accepted true universe inequality/equality implies semantic
  inequality/equality for every natural-valued parameter valuation.
- Accepted true list equivalence implies equality of the interpreted lists.
- Meta-free normalization succeeds when fuel covers the syntax-node count;
  two-level comparison returns a Boolean when fuel covers the larger count.

These are eight universally quantified Rocq theorems, not finite examples.
The syntax-node bound concerns recursive depth, not time, memory, guard/name
sizes or generated atom count. Rewriting nested imax can duplicate work.
The sufficient-fuel comparison theorem promises `Accept b`, not `Accept true`.

The existing auxiliary evaluator assigns zero to metavariables. An auxiliary
call may succeed when one occurs in a semantically dead branch. The public
normalizer rejects every syntactic metavariable occurrence before checking
fuel, including `imax meta zero`; the proofs do not weaken that boundary.

The second module adds twelve theorems. Successful normalization produces
positive constant atoms and self-guarded variable atoms. On these well-formed
lists, a failed domination test has one assignment that beats the entire
right-hand list. This establishes negative witnesses and semantic completeness
for scalar inequality, scalar equivalence and list equivalence. At sufficient
syntax-size fuel, meta-free scalar comparisons return the correct Boolean.

No theorem here establishes canonical-form uniqueness, Lean correspondence,
verified parsing/extraction/compilation, or whole-checker logical soundness.
The list result is conditional on an accepted Boolean, not a list-totality
theorem. Length mismatch may precede metadata checking, while a nonempty head
may reject or exhaust fuel before a later length mismatch. The proofs and
golden-result tests preserve these short-circuit priorities.

## Initial Main Validation

The independent read-only review is
`build/workers/hol-rejection-coverage/universe-review.md`. It finds no blocking
proof-statement or production-semantics defect. Its suggested nested-pair/list
test expansion is included. A separate private namespace gate freshly rebuilds
Syntax and Universes, then the identical proof under LeanPort.

Fresh actual-main validation:
`build/workers/parent-universe-soundness/actual-main-20261001T062821Z/report.json`.

- Full build: 118.419s; 21 native suites / 94 steps.
- Universe suite: exactly 626,207 controls, including 1,260 expressions,
  sixteen valuations, selected nested pairs, lists, guards, offsets and fuel.
- Independent audit: 90 local modules, 211.534s; no axioms, type-in-type,
  unsafe fixpoints or assumed positivity reported.
- All 1,596 source pins, pre-run copies and additional holds remain unchanged.
  Owned validation processes are reaped, with no observed survivors.
- Twelve audit-bundle files are copied and hash-verified within the report.
  Audit execution also writes its original logs into the shared toolchain tree.

The final checker SHA-256 remains exactly
`5f9d5e347f5052b85082afbaf8b7ceeb214414e6ad4515cccd4bf01359eb6d3f`.
The preceding actual-main Arena results therefore concern the same executable
bytes. This addition does not claim a new Arena run or additional file accepts.

The native controls use a separate small host-natural evaluator for finite
comparisons. Universal soundness comes from the checked theorems, not from
enumerating those controls. Earlier failed proof scripts and native fixture
compilation are retained in their original private reports.

## Completeness Integration

Independent source review:
`build/workers/hol-rejection-coverage/universe-completeness-review.md`.
No proof-statement or proof-structure blocker was found. The suggested tests
now force a separating value above 1024, pin metadata/fuel/list-length priorities,
and demonstrate why malformed zero and unguarded-variable atoms are excluded.
The twelve reviewed theorem bodies are unchanged.

Fresh actual-main validation:
`build/workers/parent-universe-completeness/actual-main-20261001T070740Z/report.json`.

- Full rebuild: 131.596s; 22 native suites / 99 steps.
- Completeness controls: 786,581 assertions, 126,288 generated separating
  assignments, 92 atoms, 277 atom lists, 180 levels, 27 positive-check valuations.
- Independent audit: 92 local modules, 216.777s; all four unsafe-assumption
  inventories empty. All 1,601 source pins and pre-run snapshots held.
- Checker bytes remain identical to the SHA-256 above. No new Arena run is
  claimed; unresolved proof-file outcomes are unchanged.
- Twelve audit-bundle artifacts and 352 audited source/object inputs are
  preserved and hash-verified in `closure-20261001T071406Z`. Its seal is
  `9673cea6ae125d17e8842a4ac7e62ebde79de3569fdb154652dc1a6e7c86f5f7`.

Both validation roots were reaped, with no observed survivors. These shared-host
timings are observations, not causal performance measurements.

## Universe Instantiation

Seven new public theorems cover the actual simultaneous zipped lookup used by
`Syntax.subst_level`. They do not silently replace it with set substitution.
The semantic equation interprets an instantiated level using the valuation
induced by that lookup: the first duplicate parameter wins, an unmatched
parameter retains its original valuation, and extra replacements are ignored.
Universal positive semantic inequalities and equalities are preserved, without
an arity or uniqueness requirement.

Meta-freedom is preserved when the input and replacements are meta-free.
Universe well-scoping additionally requires matching parameter/replacement
arity and well-scoped replacements. Accepted-true comparison preservation
requires meta-free inputs/replacements and sufficient fuel for the *substituted*
syntax, not the original syntax. No theorem promises preservation of rejected
comparisons, the same fuel budget, term typing or upstream Lean correspondence.

The independently reviewed native suite has 3,366,071 assertions over 336
levels, seven parameter lists, ten replacement lists and 27 valuations. It
includes 7,952 positive inequality and 2,408 positive equality premises, plus
the reviewer-requested positive-law matrix across all parameter lists and
meta-free replacement lists. Source review is recorded in
`build/workers/hol-rejection-coverage/universe-instantiation-review.md`.

## Interaction With Term Binders

Six unconditional syntactic theorems establish that `subst_levels` commutes
with lifting, single/batched term substitution, and single/batched
instantiation, and preserves the Boolean de Bruijn scope check. Both the term
body and the replacement terms are universe-instantiated. Arbitrary parameter
lists, open terms, metavariables, metadata and binder depths are covered.
This scope check is not a typing judgement and does not exclude free variables
or metavariables. These are not beta subject-reduction theorems.

The native suite has 7,264,342 assertions, including 3,290 generated expression
entries in 24 configurations, independent small host implementations and
explicit capture/batch-order checks. Seventeen final review-driven controls
exercise successor/max/imax source levels and distinct numeric/string names.
The read-only review is
`build/workers/rocq-whnf-orientation/resource-launcher/entry-handoff-01/UNIVERSE_EXPRESSION_REVIEW.md`.
Finite testing complements the universal checked proofs; it is not their basis.

## Current Main Validation

The combined addition of these thirteen theorems brings the four modules to
33 public component theorems. Actual-main evidence is
`build/workers/parent-universe-expression/actual-main-20261001T081803Z/report.json`.

- Full rebuild: 138.974s; 24 native suites / 109 steps, all passing.
- Independent audit: 96 local modules, 214.205s; no axioms, type-in-type,
  unsafe fixpoints or assumed positivity reported.
- Main sources, pre-run snapshots and additional holds remain unchanged.
- Twelve audit artifacts and 366 audited source/object inputs are preserved
  and hash-verified in `closure-20261001T082533Z`. Its seal is
  `a7d10abf8651d19b6416523d15fff2cb5d5ec89575f23f71b4893fa2b336fc95`.
- The executable is byte-identical to the SHA-256 above. The recorded
  default-512 and explicit-16384 Arena runs are linked by that exact digest;
  this proof-only addition is not a fresh Arena run or a coverage improvement.

The build and audit completed and their owned processes were reaped. This
closes the component integration, not the overall port or verification goal.
