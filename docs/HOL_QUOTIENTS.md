# HOL Quotient Checking

This work is independent of the Solidity checker. Canonical signatures, guarded
quotient admission and typed quotient reduction are implemented and pass focused
native tests. Full-checkpoint integration and Arena testing remain separate;
no full Lean-compatibility or semantic-soundness theorem is claimed.

## Source And Representation

The source is pinned Lean4Lean `8223d223ed98661882e95d9d6a7126df7097cd76`,
`Lean4Lean/Quot.lean`: `checkEqType`, `Environment.addQuot`, and
`quotReduceRec`. Licensing and adaptation attribution are in `hol/NOTICE`.

`hol/quotient_syntax.ml` defines four quotient kinds, their structured names,
universe arities, and canonical de Bruijn signatures. It also defines the
expected polymorphic equality and reflexivity types required by `checkEqType`.
The helper for nondependent arrows lifts the result across the new binder;
dependent telescopes retain their explicit binder indices. The unused second
universe of the three single-universe kinds is proved irrelevant.

Binder display names and binder-information annotations are not logical
components of this HOL core representation. The comparison preserves all
constant names, universe names and arguments, application structure, and bound
variable indices. It is not an equality of serialized Lean expression bytes.

## Verification

The source fixture is `tutorial/128_quotLiftType`, with SHA-256
`3abbf269039bfe725e22e5ae35438451f87ea200b2434e2e402deac0b9c8faf3`.
It contains all four quotient declarations and the equality family.

`frontend/quotient_signature_dump.ml` reads the fixture through the existing
validated Wire parser and emits data-only HOL quotations. It produces no
typing verdict and does not call Lean or a different checker. Structured names
are quoted as numeric byte lists, rather than inserted as executable text.
The fixture is hash-checked before each reproducible test run.

`hol/quotient_model.ml` independently builds candidate expressions using the
core's fuel-guarded lifting operation. Candidate construction grants no typing
or environment theorem.

`hol/quotient_syntax_tests.ml` passes **59 assertions**, comparing the four
names, universe counts and signatures, plus equality/reflexivity prerequisites,
and the ML candidate generator through actual closed HOL equality theorems.
It checks exact conclusions, empty
hypotheses, no free HOL variables, and unchanged HOL axioms. The tested run log
is `/private/tmp/lean4hol-quotient-syntax-tests.log`; no HOL load errors occur.
An earlier loader run exposed an extra closing parenthesis in the new source;
the extended harness also exposed a lexer-sensitive module alias, a shadowed
numeral conversion name and an incorrect list-destructor API assumption.
All were corrected before this passing run. No failed run is counted as a pass.

Reproduce with `sh hol/test-quotient-syntax.sh`. The driver uses a separate
compile directory, preserves the live HOL bridge bytecode, and kills/reaps the
HOL process group at a 180-second deadline. These assertions are separate from
the earlier 1,384-assertion native projection checkpoint and its Arena run.

## Admission And Reduction

`L4QuotientKind` is neither an ordinary declaration kind nor delta-transparent.
Admission requires a valid existing environment, a fresh canonical name,
distinct universe parameters, the exact canonical signature modulo binder
display names, and a typing certificate for the submitted type. It also
authenticates the Eq inductive and its single constructor, their universe
arities and exact signatures. Dependencies must themselves carry quotient
metadata. Witnesses come from the submitted environment and are proved against
the HOL predicate; ML pattern matching is not the admission certificate.

The appended quotient iota rule requires authenticated eliminator and
constructor entries, correct argument/universe arities, and typing judgments
for both the redex and result. It is not enabled by matching string names.
Major arguments are normalized through typed congruence; extra application
arguments are handled by the existing application reduction engine.

`Env.normalize` returns the actual weak-head result, its type and a closed
`l4_checked` theorem for the exact input/result pair. The test uses this API
for `Quot.ind`, so proof irrelevance alone cannot make an absent computation
implementation appear to pass a conversion test.

`sh hol/test-quotient.sh` passes **74 assertions**, with a 180-second process-group
deadline and complete reaping. Coverage includes all four declarations, both
normalization rules, beta/zeta major expressions, extra arguments, neutral
majors, renamed binders/universes, duplicates, malformed bodies, wrong headers,
resource classification and missing dependencies. Positive-gated attacks check
an ordinary Eq-named axiom, a valid but noncanonical Eq inductive, and an
ordinary Quot.mk-named axiom. The last remains neutral and cannot establish
the lift equation or the authenticated constructor dependency. All successful
certificates are checked for exact conclusions, empty hypotheses and no free
HOL variables. The axiom list is unchanged during the suite.

The axiom-permission invariant initially failed to reprove after the new
admission clause. The missing case is now discharged with a proved lemma that
a quotient-header entry cannot have axiom kind. Another integration failure
was unresolved existential metadata search; supplying explicit checked
witnesses fixed it without weakening any premise. Initial failed runs are not
counted as passes. The passing log is `/private/tmp/lean4hol-quotient-tests.log`.

The bytecompiled transport has **39 focused checks**, including all quotient
kinds and retained original headers. Translation grants no logical verdict.
Current full-suite and Arena checkpoint results must be read separately from
these focused results and from the earlier 1,384-assertion loaded runtime.

The quotient-enabled combined native checkpoint now passes **1,450 assertions**
with all ten suite markers in approximately 382 seconds under a 600-second
process-group deadline. Its passing log is
`/private/tmp/lean4hol-quotient-checkpoint-core-v2.log`. Earlier runs exposed
stale rule-count assertions and a standalone test dependency, and one reached
its 300-second deadline; those incomplete runs remain recorded, not counted
as passes. All six exact Arena quotient tutorials separately accept under a
30-second worker bound. The separate full 216-input Arena attempt now records
83 correct accepts, six correct rejects, two either outcomes, 125 declines and
four missing inputs at a 10-second worker bound, with zero wrong verdicts or
integrity failures. The quotient mutation audit accepts eight gates and 25
controls, rejects one malformed discriminator and declines 42 negative cases.
See `docs/HOL_QUOTIENT_REVIEW.md` for exact assumptions and retained evidence;
negative declines are coverage gaps, not proofs of invalidity.

`Quot.sound` is not one of the four builtin quotient declaration kinds in
`Quot.lean`; ordinary object axioms remain subject to the explicit environment
permission policy. No correspondence theorem to Lean's complete quotient
semantics or metatheoretic soundness proof is claimed by this foundation.
