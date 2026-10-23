# HOL Quotient Export Audit

## Scope

This bounded source review and export suite is not a soundness or completeness
proof. It uses authentic Arena tutorial exports 126 through 131, never an
alternate checker or Arena verdict fields as an oracle. No production,
frontend, client, or bridge files were changed. No full Arena run was requested
or performed by this audit.

There are **68 cases: 25 expected accepts and 43 negatives**, plus eight
positive gates. Six gates are byte-identical source exports. Two additional
gates are coherent indexed families named Eq which are admissible inductives
but do not meet the quotient module's equality prerequisite. Both prerequisite
negatives require the genuine quotient gate and their altered-family gate to
accept before running.

## Important Expectation Distinction

Pinned upstream `Lean4Lean/Replay.lean:219-221` treats `.quotInfo` as a request
to replay Eq and add `.quotDecl`. `Quot.lean:Environment.addQuot` regenerates the
canonical quotient declarations, and does not compare every supplied export
header. Consequently, the suite does **not** claim upstream replay rejects all
forged header payloads.

The 27 canonical-header negatives test the explicit local exported-claim
integrity contract: a supplied quotient header must equal the declaration it
claims to represent. Their manifest basis is `claim-integrity`. One unknown
kind discriminator is separately `malformed`. Other negatives target an
actual prerequisite or typed-term/reduction mismatch. These bases are retained
in runtime result records; none is silently conflated with the others.

## Provenance

Review manifest: `tests/hol_quotient_audit/snapshot/manifest.json`, SHA256
`eb4dfadc04f3b5dfa79ddad8f6a218cb5aacd22a3a349a9756d113a4ae607964`.
It preserves 53 files, including the project loader closure, bridge bytecode
and interfaces, explicit frontend sources, relevant upstream sources, test
helpers, and six actual exports. The capture compares source bytes and the
project closure before writing. It pins the full Arena manifest hash but
retains only selected seed identities, paths, sizes, and hashes, not outcomes.

Upstream revision: `8223d223ed98661882e95d9d6a7126df7097cd76`.
The primary sources are captured copies of `Quot.lean`, `Replay.lean`, and
`TypeChecker.lean`.

Assigned READY provenance: `runtime-provenance.json`, SHA256
`9edacc5e005ad863c595eedfeb947b38fdf3debb7db05afdffaa2b6e71517c67`.
Its complete project loader input hashes and bootstrap match this review's
capture: **no runtime/source mismatch override was needed**. This is the new
quotient/structure/primitive snapshot, not the old 1384 projection runtime.
The parent's focused native and transport counts are contextual reports, not
tests independently rerun by this sidecar. Later test-only changes do not
change this loaded checker identity.

These hashes do not attest execution, semantics, external HOL/OCaml/dynamic
libraries, operating-system state, or transient edits restored between
observations. Bytecode hashes do not establish correspondence to ML sources.

Fixture manifest SHA256:
`832ba237840d394bafa40cf05d44d7910cd95bf6d7f281775fff63cbda106e23`
in `fixtures-final/manifest.json`. The initial manifest and all its input bytes
remain separately preserved in `fixtures/`; see the control correction below.

## Source Review

No concrete false-acceptance premise was identified in this bounded review.
The following are observations about the captured rules, not a formal proof
of equivalence to upstream.

- `Quot.lean:checkEqType` requires the inductive named Eq, one universe,
  one listed constructor, the canonical Prop-valued equality type, and the
  canonical reflexivity constructor type. It follows that constructor's name
  rather than demanding the spelling `Eq.refl`. The matching local
  `l4_quot_eq_meta` also requires generated inductive/constructor roles and
  connects the constructor parent to Eq.
- `l4_quot_header` checks kind, structural reserved name, universe arity,
  distinct formal universe names, absence of an implementation body, and the
  anonymous-binder canonical signature. The input/output roles in lift's
  two universes remain ordered. Merely swapping the formal list without
  consistently changing the signature is not alpha-renaming.
- Quotient admission requires an already valid environment, fresh name,
  membership of the Eq entries, the exact header and prerequisite predicates,
  parameter closure, and a sort certificate for the declaration type.
  Candidate ML computations must produce closed HOL proofs of those premises.
- The new iota clause checks canonical eliminator and constructor headers,
  restricts the eliminator to lift or ind, checks universe/application arities,
  and requires both the full redex and selected branch application to have
  the same certified type. The ML candidate chooses arguments; it cannot
  bypass those typed premises. Tests vary the major's relation, constructor,
  universe, representative, arity, and claimed result.
- Upstream supports reduction with extra arguments following the eliminator.
  The local primitive step recognizes a saturated eliminator, with ordinary
  application reduction handling larger terms. This audit does not attempt a
  complete overapplication/congruence correspondence proof.

## Cases

| Group | Cases | Purpose |
| --- | ---: | --- |
| Six unchanged/binder/order control triplets | 18 | Exact exports; anonymous binders; reversed declarations with implicit Eq dependency |
| Kind-specific headers | 24 | Each kind: name, tag, missing/extra universe, whole signature, first binder domain |
| Additional header paths | 4 | Structural versus dotted-single name; duplicate/swapped lift universes; unknown discriminator |
| Equality prerequisites and controls | 6 | Missing/renamed Eq; renamed constructor; universe alpha-renaming; two coherent incorrect Eq shapes |
| Lift reduction | 8 | Canonical and beta controls; six independently justified typing/result failures |
| Induction reduction | 8 | Canonical/beta/proof-irrelevance controls; five typing/result failures |

The two altered Eq families are constructed coherently, including recursor
types, rule right-hand sides, field counts, and K metadata:

1. A Prop-valued Eq-shaped family with a constructor for every index. Its
   constructor has an additional field, so it is not reflexivity.
2. A reflexivity-shaped family whose result is `Sort 1`, not Prop. Its K flag
   is false and its ordinary large recursor is generated consistently.

Each altered family must first accept in isolation. Its negative appends the
actual canonical quotient declarations and tests the prerequisite guard.
Failure to admit the dependency would mark the case `not_covered`, not count
as a successful rejection.

## Proof Irrelevance and Assumptions

The neutral-major induction control intentionally accepts without a
constructor reduction: given `q : Quot A r` and `hq : B q`, the induction
result and `hq` are proofs of the same proposition. Proof irrelevance can
justify their equality. Treating every nonconstructor major as an invalid
equality would be a false expectation.

In contrast, the wrong induction result uses `f other : B (Quot.mk r other)`
where `B (Quot.mk r x)` is required. Arbitrary different propositions are not
made definitionally equal by proof irrelevance.

Authentic export 129 includes the explicit object axiom `Quot.sound`.
Acceptance of that baseline and its transport controls is relative to that
input assumption policy. The suite neither proves quotient soundness from
scratch nor presents 129 as axiom-free. No fixture adds a new object axiom;
the other five source exports and both altered Eq gates contain none.

## Verification and Reproduction

```sh
PYTHONDONTWRITEBYTECODE=1 python3 tests/hol_quotient_audit/quotient_audit.py --verify
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/hol_quotient_audit -p 'test_*.py'
```

All 12 initial offline tests passed before any runtime request. All 13 final
tests passed before replaying the corrected universe control. They independently
decode the generated wire DAGs, check scope/references, compare the named
reconstructions of Eq and both genuine reduction theorems, verify coherent
dependency gates, preserve explicit assumptions, test multi-gate accounting,
and enforce the case bound and hashes. They are construction tests, not an
alternative logical checker.

The runner accepts arbitrary checker argv after `--checker`, appending the
filename as data. Runtime use requires `--run --report NEW_PATH
--runtime-provenance PATH --runtime-sha256 SHA`. A distinct loaded snapshot
requires explicit acknowledgement. Requests are serial; each diagnostic is
bounded to 4096 bytes. Reports are private, atomic, size-bounded, and never
overwrite an existing path. Fixture and client/provenance hashes are checked
around replay. No expected outcome is passed to the checker.

Code 0 is acceptance, 1 rejection/malformed input, 2 a coverage gap, and 3 a
fault. Failed gates skip dependent cases. In particular, a negative decline
is not a refutation and does not count as a successful rejection.

## Runtime Results

| Final suite | Result |
| --- | --- |
| Positive gates | 8/8 accepted |
| Expected-positive cases | 25 accepted |
| Expected-negative cases | 1 malformed-input rejection, 42 declines |
| Wrong verdicts / faults / integrity failures | 0 / 0 / 0 |
| Worker or outer timeouts / truncated diagnostics | 0 / 0 |

Requests used 30-second worker limits and 40-second outer deadlines. The sole
code-1 result is the unknown quotient-kind discriminator, not a logical
refutation. All 42 remaining negatives are coverage gaps. No source, client,
or bridge changed during either replay; both runs matched the READY snapshot.

The two coherent Eq-family gates accepted in 1.15 and 1.09 seconds. Their
quotient-appended cases then declined after `checked=1`, with `CONJ_TAC`
proof-construction diagnostics. This isolates the prerequisite stage from
failure to admit the altered dependency, but still does not prove invalidity
inside HOL. The renamed Eq-constructor control accepted. Both beta-major
controls and the neutral-major proof-irrelevance control accepted.

Final report: `tests/hol_quotient_audit/final-report.json`, SHA256
`6eb42bc198332177136454fc1f73bdd80dac98972e85ce34d2b8d1489c93193c`.
It is an explicitly labeled aggregation of actual measured observations,
joined by exact case ID and input SHA256. It does not invoke a checker or
serve as an oracle. `assemble_report.py` pins the two measurement reports,
requires matching runtime identity and unchanged checker observations, and
retains each result's source-report hash.

Raw evidence remains unchanged:

- `quotient-report.json`, SHA256
  `3f5da567c17897233b470fbc97f81f481eccff774016c73a66a1b619d0819399`.
- `universe-control-report.json`, SHA256
  `1ff4cae85420df286c64f186bd7a131b2dd7948fead5b4ac076a80fddb094e7e`.
- `completion.json` records process cleanup and all report hashes.

## Corrected Control

The initial whole-export universe-renaming control was withdrawn, not reported
as a checker bug. It also renamed Eq.rec's generated elimination universe.
Upstream `Inductive/Add.lean:280-287` selects the fresh universe starting at
`u`; `getRecLevelParams` prepends it, and `Replay.lean:247-249` compares the
resulting recursor metadata exactly. Arbitrarily renaming this generated name
without regenerating the claim is therefore not a valid positive transport
control. Its observed decline was at the Eq declaration, line 60, checked 0.

The corrected control renames only quotient-specific universe parameters,
leaving the generated Eq block identical. It accepted in 3.25 seconds after
its genuine 126 gate accepted again. The final test suite still has 68 cases;
including the withdrawn initial candidate, **69 distinct non-gate inputs**
were tried, below the requested 70 bound. The initial runner, fixtures,
manifest, report, and withdrawn observation remain available for inspection.
No raw report was rewritten to hide the corrected expectation.

At `2026-09-29T22:09:51Z`, warm parent 34103 had no remaining worker children
and `/private/tmp/hol-run-_63lkxxh/s` had no active clients. Supervisor 34032
and the warm parent were left alive, and the socket was released to the parent.
