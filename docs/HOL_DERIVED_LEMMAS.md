# Derived HOL Proof Steps

This library derives typed substitution, closed-syntax computation and arithmetic
evaluation, with opt-in theorem-producing APIs. The derived modules add no
typing/admission rules or HOL axioms. The current model has 29 native and 11
admission clauses; whole Lean compatibility and semantic soundness remain open.
The separately reviewed closed-computation shortcut is now used by the main
engine. The optional arithmetic APIs do not enable default literal dispatch.

## Typed Instantiation

`hol/instantiation_certificates.ml` derives one-binder substitution for the
pure, native-environment, and checked-environment typed-equality judgments.
Given a typed domain A in context g, an equality e = f at type T under A::g,
and a term v of type A in g, substitution produces an equality between
`l4_inst v e` and `l4_inst v f` at `l4_inst v T` in g.

The derivation obtains reflexive endpoint typing by symmetry/transitivity,
abstracts the equality by lambda congruence, applies both lambdas to v, and
composes beta equations on both sides. The checked version retains the exact
environment, policy, and context validity. This avoids assuming a new
substitution rule; the result follows from the existing rules.

The private final regression passes 64 assertions covering exact closed
general conclusions and seven cases: variables, beta, dependent contexts,
capture under a lambda, universe equality, let, and a constant in a nonempty
environment. Wrong domains, substituted values, omitted premises, changed
environments, and changed policies with identical declarations do not match
the rule. Assumed premises remain hypotheses. This lemma does not by itself
prove the separate optimized Nat.add rule conservative.

## Closed Syntax

`hol/closed_syntax.ml` defines `l4_scoped e k`: every free de Bruijn index in e
is below k, with the bound adjusted underneath binders. It proves that lifting
or substituting at that bound leaves the expression unchanged, scope is
monotone in the bound, and closed expressions are unchanged by arbitrary
lifting, substitution, or instantiation.

The six proofs use structural induction and arithmetic, not a host-computed
closedness flag. The private final regression passes 550 assertions over all
expression constructors, multiple cutoffs, open substitution arguments,
arbitrary-precision literals, and three open-variable counterexamples.
Closedness alone does not assert typing, declared constants, universe scope,
or valid String scalars; a deliberately invalid scalar example establishes
only its syntactic binder scope. A later guarded shortcut uses these facts;
see [closed computation](HOL_CLOSED_COMPUTATION.md) for its separate evidence.

## Literal Evaluation

`hol/nat_evaluation.ml` derives literal evaluation from typed recurrence
equations. If a typed unary function f maps zero to m and its successor
equation holds for every natural n, the existing application, symmetry,
transitivity and literal-successor rules plus HOL induction prove
`f (NatLit n) = NatLit (m+n)` for every n. The checked theorem in
`hol/nat_evaluation_checked.ml` retains the exact environment, policy and context.

`hol/add_context_evaluation.ml` connects this result to the original symbolic
addition contract relative to the actual context:
`l4_prim_add_contract (\delta. l4_edef env (APPEND delta g)) body`.
It uses typed instantiation to substitute both de Bruijn arguments, proved
closed substitution for the body, and the recurrence theorem. Explicit premises
include the body's syntactic closedness and typing of Nat, zero and successor.
The conclusion covers all natural pairs in that exact context. No context
weakening or optimized Nat.add clause is assumed. `hol/add_evaluation.ml`
preserves the old empty-context API as an alias of the empty-context corollary.

Private and independently copied main runs each pass 116 assertions: four exact
recurrence checks, 76 admitted-Nat identity/successor checks, four exact addition
checks, and 32 authenticated addition-body checks. The latter includes six
literal pairs, including two 50-digit values. Tests refuse missing premises and
mismatched environments, contexts, bodies and claimed outputs; conditional
inputs retain their hypotheses. These are synthetic checked fixtures, not new
Arena passes. The final audit verifies eight reaped/absent process groups.

The earlier main evidence is `build/reports/hol-composition-20260930T164018Z-3973` and
`build/reports/hol-composition-20260930T164934Z-81073`, with exact markers and
held source/input/log hashes. Private proof source and audit are retained in
`/private/tmp/hol-nat-evaluation-20260930`. The four main group times are
53.743, 60.243, 48.599 and 54.459 seconds, including startup. No full native
matrix or full corpus rerun is claimed for these proof-only additions.

## Optional Evaluation Service

`Lean4hol_derived_add.prepare env gamma body` in `hol/derived_add.ml` checks the
body type and both symbolic addition equations using ordinary environment
checking in the exact required contexts. It proves syntactic scope and returns
an opaque certificate holding a universally quantified `l4_checked` theorem.
`evaluate certificate left right` validates canonical decimal literals and
specializes that theorem using proved HOL numeral arithmetic. It returns the
literal together with its exact closed checked judgment.

The certificate retains its original environment, policy, context and body.
It does not become a certificate about a later environment, and arbitrary
well-typed binary functions do not qualify without the symbolic equations.
Closed named definitions and let wrappers are supported; a function supplied
as an open local variable is intentionally unsupported. Future cache/runtime
consumers must compare the entire requested judgment or prove transport.

Fuel is per delegated query, not aggregate preparation time, arithmetic work,
memory, or proof size. External wall-time/memory supervision remains necessary
for hostile inputs. No default Engine/frontend hook is installed, and this API
is not yet conservativity of a separately proposed accelerator clause.

The sealed contextual private candidate passes 160 selected assertions: 128
new contextual/API checks and 32 preserved closed-context checks. Named/let
wrappers, dependent contexts, huge numerals, wrong typed base equations,
missing declarations, open bodies, malformed numerals, missing premises and
stale-context/environment mismatches are covered. Independent source review
found no integration blocker. The alias self-comparison is not independent
compatibility evidence; the separate old-API expected-formula test is retained.
Evidence: `/private/tmp/hol-add-context-20260930/FINAL_AUDIT.json` and
`/private/tmp/hol-add-context-final-review-20260930.md`.
The fresh actual-main six-group run independently passes 164 assertions:
128 contextual/API and 36 old-API checks, including the independent expected
formula. Each completes in 48.799--61.759 seconds with a 180-second cap.
All six process groups are reaped and absent, copied payload hashes match the
reviewed seal, and source/input/log inventories hold. See
`build/reports/hol-composition-20260930T172430Z-31192` and
`build/reports/hol-add-context-main-audit.json`. The 33 unselected groups are
not new passes; no new Arena outcome is claimed.

## Predecessor Evaluation

`hol/pred_context_evaluation.ml` derives a contextual predecessor theorem and
its empty-context specialization. A closed body must satisfy the existing
symbolic `l4_prim_pred_contract` in the exact ambient context, with explicit
typing of Nat, zero and successor. Typed instantiation replaces the symbolic
argument. Existing literal, application and transitivity rules prove the zero
and successor cases; HOL induction gives `body (NatLit n) = NatLit (PRE n)` for
every natural number. There is no new native computation clause and no assumed
weakening or arbitrary-context transport.

Both the private and actual-main runs pass 75 assertions: four general theorem
checks and 71 concrete checks. These cover zero, one, large numerals, three
contexts including a dependent context, beta/let wrappers, a named ordinary
definition, missing premises, wrong environments/contexts/bodies, typed false
successor laws and an independently typed open-function counterexample.
Assumed contracts retain their hypotheses. The tests also reconstruct exact
checked judgments from the raw conclusion and the original validity proofs.

Actual-main groups take 47.659 and 69.982 seconds under separate 180-second
limits. All 222 captured source pins and both process-group cleanup checks
hold. Evidence: `build/reports/hol-composition-20260930T182331Z-53670` and
`build/reports/hol-pred-main-audit.json`; the private source and audit are under
`/private/tmp/hol-derived-pred-20260930`. The other 39 registered groups were
unselected, not new passes. Default dispatch and Arena results are unchanged.

## Subtraction Evaluation

`hol/sub_context_evaluation.ml` derives truncated natural subtraction from the
existing context-relative subtraction contract, including its actual predecessor
dependency. Both bodies require proved de Bruijn closedness. Nat must be typed
in the current context and under one additional Nat binder; zero and successor
are typed in that same environment. The proof instantiates the two symbolic
arguments in order, applies the induction hypothesis, then uses the predecessor
theorem for the exact dependency. Its conclusion is `NatLit (m - n)` with HOL
natural subtraction, including truncation at zero.

Private and fresh actual-main runs each pass 101 assertions: four independent
general-statement checks and 97 concrete checks. Tests cover three contexts,
eight literal pairs including huge values and underflow, beta/let wrappers,
named dependencies and sources, every missing premise, stale bindings, and
typed impostors that satisfy a base equation but fail the successor law.
The main groups finish in 48.843 and 111.637 seconds under separate 180-second
limits; both groups are reaped/absent and 225 captured source pins hold.
See `build/reports/hol-sub-main-audit.json` and its source snapshot. The other
41 groups were unselected, not new passes. Independent source review of both
predecessor and subtraction found no substantive premise or binding defect;
that review is separate from runtime evidence. No default evaluator changed.

## Multiplication Evaluation

`hol/mul_context_evaluation.ml` derives literal multiplication from the exact
context-relative multiplication contract and its addition dependency. Both
bodies require proved closedness; Nat must be typed in the current context and
under a Nat binder. The proof instantiates the symbolic arguments, transports
the induction hypothesis through typed addition congruence, and applies the
derived addition theorem. HOL arithmetic reconciles the right-successor equation
with the contract's operand order. No literal-multiplication rule is introduced.

Private and fresh main runs each pass 95 assertions: four general-statement
checks and 91 concrete/adversarial checks. These include three contexts, large
numerals, exact checked-certificate reconstruction, beta/let wrappers, ordinary
named dependencies, missing premises, stale bindings and typed false base/step
impostors. The main groups finish in 49.078 and 123.059 seconds at unchanged
180-second limits, with 228 source pins held and both process groups absent.
Evidence: `build/reports/hol-mul-main-audit.json` and its referenced snapshot.
The other 43 groups were unselected. This optional proof module changes neither
default dispatch nor Arena outcomes; its general theorem remains conditional
on the explicitly supplied raw premises.

## Exponentiation Evaluation

`hol/pow_context_evaluation.ml` derives literal natural exponentiation from
the exact nested addition/multiplication/power contracts in the same environment
and context. All three bodies require proved closedness. Typed zero/successor
rules construct the literal-one base, including `0 EXP 0 = 1`; the exponent
induction uses the multiplication theorem with the contract's exact operands.
HOL natural multiplication symmetry only reorders arithmetic inside the result
literal, not an arbitrary object-language multiplication function.

The final private four-group replay passes 106 assertions: 4 general, 33 empty-
context, 61 nonempty-context and 8 wrapper/named-dependency checks. Each group
has a 180-second whole-process cap. The source was independently reviewed
without a substantive finding. Fresh main replay passes the same 106 assertions
in 164.109, 143.030, 174.607 and 148.079 seconds. All 231 captured source pins
hold and all four groups are reaped/absent. See `build/reports/hol-pow-main-audit.json`.
Times include startup and vary with host load; they are not speedup claims.
The other 45 registered groups were unselected. Two failed development attempts are
retained: incorrect defining-theorem binder order in a test, then an interactive
prompt preceding a pass marker. Matching the exact contract term and emitting
a line-anchored marker fixed the tests without relaxing the runner or changing
the production theorem. One failed cleanup probe required a later independent
absence check. See `/private/tmp/hol-derived-pow-20260930/FINAL_AUDIT.json`.

## Evidence And Reproduction

```sh
python3 -B tests/hol_composition/run.py instantiation closed-syntax
python3 -B tests/hol_composition/run.py nat-recurrence-general nat-recurrence
python3 -B tests/hol_composition/run.py add-evaluation-general add-evaluation
python3 -B tests/hol_composition/run.py add-context-general add-context
python3 -B tests/hol_composition/run.py derived-add derived-add-wrappers
python3 -B tests/hol_composition/run.py pred-general pred-cases
python3 -B tests/hol_composition/run.py sub-general sub-cases
python3 -B tests/hol_composition/run.py mul-general mul-cases
python3 -B tests/hol_composition/run.py pow-general pow-empty pow-contexts pow-wrappers
```

The portable runner uses separate 180-second caps and checks exact completion
markers, HOL errors, source hashes, and cleanup. Private originals are retained
at `/private/tmp/hol-derived-instantiation-20260930` and
`/private/tmp/hol-closed-syntax-20260930`. Their final runs took 50.222 and
56.498 seconds, respectively. These include startup, not isolated proof cost.
They are not performance improvements or new Arena passes.

The actual-project snapshot
`build/reports/hol-composition-20260930T160327Z-84225` separately passes both
groups: instantiation 64 assertions in 61.235 seconds, closed syntax 550 in
61.756 seconds. Sources remain held throughout each run, all markers match,
and both child process groups are reaped and absent. All fifteen runner tests
also pass. These results supersede the failed preflight driver-location attempt,
which is preserved at `hol-composition-20260930T160213Z-69892`.

Retained failed attempts include an unconstrained test binder type, a rejected
local module alias, a reused quotation variable with incompatible types, and
a test conversion that simplified an equality into truth before inspecting
it. The first main helper launch also found a misplaced test driver before
starting HOL; the driver now lives in the runner's `drivers/` subtree and a
new unit test checks every registered driver path. Failed attempts are not
included in the final assertion counts. Toolchain/compiler/OS boundaries are
unchanged; the copied runtime is not a hermetic execution proof.

## Private Conversion Experiment

This section records the earlier experiment, not the present main state. A
subsequent locally bounded implementation is integrated and focused-tested;
see [the current record](HOL_CLOSED_COMPUTATION.md). The historical results below
are not retroactively attributed to that newer implementation.

The sealed `/private/tmp/hol-closed-computation-20260930` uses the closed-syntax
lemmas in an experimental conversion prepass. Its host scope scan only selects
candidates: the shortcut requires the exact unconditional HOL scope theorem,
applies a proved conversion lemma, and checks the resulting equality. It adds
no logical rules. This implementation is not integrated into main.

The experiment passes 4,135 old/new conversion assertions and 128 exact
microbenchmark equalities. For the largest tested closed tree, eight repeated
substitutions take about 0.812--0.819 CPU seconds with the existing conversion
and 0.118--0.120 with the candidate, in opposite measurement orders. This is
not an end-to-end speedup claim. The one production-protocol tutorial112 probe
still returns a worker timeout after 10.011 seconds at the unchanged cap.

All 195 captured main-source pins hold and four owned process groups are absent.
Full native/Arena validation and memory-cost review of the extra theorem cache
are not performed. Main's default computation, bootstrap, and corpus outcomes
therefore remain unchanged. The timeout and limitations are preserved in the
private report and final audit, rather than replaced by the microbenchmark.

## Contextual Boolean Comparisons

`hol/bool_context_evaluation.ml` derives `Nat.beq` and `Nat.ble` evaluation for
every pair of natural literals from the complete typed four-case recurrence
contract. `Lean4hol_derived_bool.prepare env gamma Beq body` (or `Ble`) constructs
that contract; `of_contract` consumes an exact, closed checked contract.
`evaluate certificate left right` returns the Boolean expression and its HOL
checked-equality theorem. Operands are canonical nonnegative decimal strings.

Certificates retain the exact environment, policy, context, operation and body.
Preparation also checks closed binder scope of the operation and the necessary
Nat/Bool typing premises. A finite sample of correct answers cannot replace
the universally quantified contract; the regressions include such impostors.
No arbitrary weakening to another context is assumed.

The fresh frozen-main replay passes all 27 groups and 1,185 assertions, including
empty, Nat and dependent contexts, beta/let/named wrappers, each incorrect
recurrence case, missing premises and changed certificate endpoints. Evidence:
`build/reports/hol-composition-20261001T024144Z-50465` and
`build/workers/hol-bool-derived/evidence/fresh-main-native-audit.json`.
All groups retain 180-second caps; these are not additional Arena cases.

## Contextual Shift Left

`hol/shift_left_context_evaluation.ml` derives
`body (NatLit m) (NatLit n) = NatLit (m * 2^n)` from the complete typed
addition/multiplication/shiftLeft contracts in the same environment and context.
The induction over `n` is generalized over `m`, so its recursive step may apply
the induction hypothesis to `2*m`. Operation bodies must be closed; typed
instantiation discharges the symbolic context extensions without assuming a
general context-weakening rule.

`Lean4hol_derived_shift_left.prepare env gamma ~add ~mul body` builds the
contract. `prepare_from_contract` consumes an exact checked contract instead.
`evaluate certificate left shift` returns a literal and a checked theorem;
`check_result` additionally checks the caller's claimed output. No successful
host arithmetic comparison substitutes for constructing that theorem.

The optional `max_output_bits` resource preflight defaults to 4,096 and accepts
limits 1 through 65,536. Inputs are at most 16,384 decimal characters. Its bound
for nonzero inputs is conservative: `4 * digits(left) + shift <= limit`.
Consequently it can decline small answers under very low limits. For zero input,
the proved multiplication rewrite removes exponentiation before numeral
reduction; the returned theorem still mentions the original shift expression.
The preflight itself produces no logical verdict, and it is not a bound on all
runtime or theorem memory.

Three production modules and two drivers are integrated with the separate
`tests/hol_shift_left/run.py` runner. The private ten-group native matrix passes
357 assertions. The fresh frozen-main replay independently passes all ten groups
and 357 assertions, with 291 frozen source files unchanged and all processes
reaped. Ten main offline controls and 64,233 pure budget assertions also pass;
the latter are host resource tests, not HOL theorems. Evidence is
`build/reports/shift-left-main-audit-20261001T032945Z-8917/main-matrix-audit.json`.
See the runner's [instructions](../tests/hol_shift_left/README.md).
