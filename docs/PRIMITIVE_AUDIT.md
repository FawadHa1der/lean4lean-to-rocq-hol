# Bounded Primitive Audit

Date: 2026-09-29. Scope: `rocq/PrimitiveAdversarial.v` and this report only.
No implementation, build-script, frontend, shared `.vo`, or binary changes.
Source line references below refer to the frozen, hashed audit snapshot.

## Current Source Note (2026-10-13)

The report below remains the historical September29 audit, not a fresh build
of today's files. In the current source, the earlier example
`pa_same_proposition_accepts_expanded_reflexivity` has been replaced by
`pa_alias_proposition_rejects_expanded_reflexivity`, which expects
`Reject TypeMismatch`. The old paragraph claiming expanded-reflexivity
acceptance must not be applied to the current alias fixture.

A bounded source review found no new demonstrated Nat admission/acceleration
defect and confirmed that the noninjective text limitation remains documented.
It did not compile these examples, prove overall soundness, or establish an
end-to-end counterexample from an empty environment. Exact inspected source
hashes and boundaries are retained in
[the current source audit](../build/workers/parent-arena-reconciliation-20261013-01/lean-ports-primitive-audit332/AUDIT-02.txt).

## Result

**No Nat acceleration/body mismatch was demonstrated through checked safe
admission in this bounded audit.** There is one confirmed, inherited text
conversion limitation and two important API trust boundaries. These must not
be conflated with a primitive-admission exploit or a whole-kernel soundness proof.

The new file contains **40 executable examples and one general theorem**.
Every adversarial family has a positive control; well-founded mutations also
check body/helper typing before testing the symbolic authentication failure.

## Findings

### Inherited Text Incompleteness

Locations: `rocq/Checker.v:1076` (`core_quick`) and
`rocq/Checker.v:1051` (`compare_after_whnf`). Both can compare two literals by
their encoded values without expanding distinct strings.

Reproducer, entirely through safe primitive admission over the shared fixtures:

1. Set `Char := Nat`, with `Char.ofNat := fun _ => 0`, and
   `String := List Char`, with `String.ofList := fun xs => xs`.
2. Both primitive definitions pass header checking, body typing, and the
   faithful interface classifier.
3. Explicit expansions of `"A"` and `"B"` compare equal: both are singleton
   lists containing the declared character value zero.
4. Comparing the two literals directly yields `Reject NotDefinitionallyEqual`.

The alternate fixture with identity characters and constant-empty `String.ofList`
has the same behavior for `"A"` and `""`. The normal identity representation
distinguishes the expansions of `"A"` and `"B"`, providing a negative control.

The distinction reaches theorem admission: direct literal reflexivity for
`Eq String "A" "B"` rejects with `TypeMismatch`, while reflexivity at the explicit
expansion proves that same proposition and is admitted. See examples
`pa_collapsed_text_literal_reflexivity_is_rejected_at_admission` and
`pa_same_proposition_accepts_expanded_reflexivity` at
`rocq/PrimitiveAdversarial.v:73` and `:79`.

**Impact:** incompleteness/false rejection for deliberately noninjective but
interface-valid representations, not false acceptance. The behavior is also
present in pinned upstream `Lean4Lean/TypeChecker.lean:591` (`quickIsDefEq`;
literal comparison at line 603). This is not a newly introduced Rocq-only bug.
No Lean executable was queried to establish this comparison; the source was read.

**Disposition:** retain faithful Char/String interface authentication. Do not
invent injectivity or defining-equation obligations to hide this behavior.
Any future decision to expand unequal string literals before rejecting is a
separate core completeness/policy change requiring parent coordination and an
explicit account of the difference from upstream.

### Trusted Metadata Boundary

Locations: `rocq/Primitives.v:84` (`primitive_authenticated`),
`rocq/Checker.v:313` (`core_reduce_nat`), and `rocq/Declarations.v:54`
(`checked_constant`). Dependency authentication checks the exact tag, signature,
parameters, and retained body presence; it does not re-prove that body's equations.

The audit deliberately constructs a raw record for `Nat.add` with tag
`DPrimitive PNatAdd` but body `fun x _ => x`. The guard accepts this forged record;
the accelerated call on `(1,2)` gives `3`, while applying its body gives `1`.
The generic internal `checked_constant` helper can also construct that record
if a caller explicitly supplies the primitive kind. See
`pa_forged_record_demonstrates_the_trusted_metadata_boundary` and
`pa_internal_checked_constant_is_not_a_primitive_admission_api` at
`rocq/PrimitiveAdversarial.v:119` and `:125`.

**This is a contract-violation witness, not an input-admission bypass.** The
same body is well typed but is rejected by `Declarations.admit` with
`NotDefinitionallyEqual`. A valid addition is admitted with its original body
and tag, and a subsequent replacement attempt rejects as a duplicate. An
ordinary alias receives `DDefinition` and evaluates according to its body.

Inspection of production `checked_constant` call sites finds only assumption,
theorem, and opaque kinds. The safe-definition path at `Declarations.v:76`
classifies first and stores that exact body at lines 80-83. The frontend's
definition conversion at `frontend/rocq_adapter.ml:91` supplies `InputDefinition`,
not a caller-selected `DPrimitive`. Its declaration dispatch calls checked
admission. Restricted admission also rejects all 18 reserved definition names;
the audit checks this over the complete primitive-kind list.

**Disposition:** keep raw environment records and `checked_constant` outside
untrusted admission APIs. Future environment import/cache/replay paths must
preserve checked provenance; a tag and type alone are not a certificate that
can be deserialized from untrusted input. Rechecking all equations inside every
arithmetic reduction is not proposed by this audit.

### Body-Typing Precondition

Location: `rocq/Primitives.v:755` (`classify_primitive`). With a valid Char
interface, calling the classifier directly with the canonical arrow type but
the non-function body `Nat.zero` returns `Some PCharOfNat`. Calling safe
declaration admission with those same arguments rejects `TypeMismatch`.

This is intentional interface factoring, documented in `PRIMITIVES.md`, not an
in-contract false acceptance. The classifier does not accept a body-typing
proof as an argument, so ordinary Gallina callers can misuse it. Tests at
`PrimitiveAdversarial.v:86` and `:90` preserve this distinction explicitly.

## General Admission Assurance

`pa_admission_retains_exactly_the_classified_body` proves, for arbitrary fuel,
environment, name, parameters, type, and body, that successful safe admission
returning a `DPrimitive k` head record:

- keeps the original environment as the tail;
- retains the exact submitted name, parameters, type, and body;
- has `classify_primitive ... body = Accept (Some k)` for that same body.

This theorem rules out swapping the classified body for another body within
`Declarations.admit`. It is closed under the global Rocq context. It does not
prove that arbitrary raw environment records are valid, nor that every accepted
conversion or accelerated arithmetic implementation is semantically sound.

## Symbolic Probe Audit

The source comparison used the pinned Apache-2.0 Lean4Lean commit
`8223d223ed98661882e95d9d6a7126df7097cd76`, including `Primitive.lean`'s
`unfoldNatWellFounded`, `Probe.probe`, and Char/String clauses. Existing
attribution remains in `Primitives.v`; no upstream assumptions were imported.

| Case | Positive Gate | Observed Result |
| --- | --- | --- |
| Canonical gcd / bitwise | Actual safe admission | Both accepted |
| Measure changed from first to second coordinate | Mutated unary helper typechecks | `Reject NotDefinitionallyEqual` |
| Eager gadget changed to successor | Gadget and fix definition typecheck | `Reject NotDefinitionallyEqual` |
| Gcd functional captures an opened argument | Unary helper typechecks | `Reject UnknownFreeVariable` |
| Gcd functional ignores `ih` | Unary helper typechecks; existing base probe passes | `Reject NotDefinitionallyEqual` |
| Nat supplied as decrease proof | Probe extracted from canonical gcd | `Reject TypeMismatch` |
| Bitwise hardcodes AND | Helper/body typecheck; entire AND specialization equals the correct one | `Reject NotDefinitionallyEqual` |
| Recursive second tuple coordinate changed to zero | Helper/body typecheck; first-coordinate decrease still valid | `Reject NotDefinitionallyEqual` |
| Output digit changed from one to two | Helper typechecks | `Reject NotDefinitionallyEqual` |
| Opaque unary wrapper | Canonical interface retained | `Decline UnsupportedDeclaration` |
| Exhausted classifier fuel | Reserved canonical interface | `Decline OutOfFuel` |

These results exercise the important generality boundaries: the functional is
retyped without the opened recursion variables (`Primitives.v:595`); probes use
a fresh, arbitrary `ih` and typecheck the whole right-hand side (`:622`); and
bitwise quantifies over the boolean operator (`:650`). The AND impostor matches
an entire specialization, not merely a finite set of samples, yet cannot obtain
the general bitwise certificate. The wrong recursive tuple is well typed and
decreases, so its rejection demonstrates the equation check beyond termination.

## Reproduction

Private build directory: `/private/tmp/leanport-primitive-audit.smkQZs`.
Unmodified copies of `Syntax`, `Universes`, `Checker`, `InductiveUtils`,
`Primitives`, `Declarations`, `Safety`, and `PrimitiveRegression` were compiled
there, followed by the new audit file. The shared parent build is not modified.

From that private directory:

```sh
sh '/Users/fawadhaider/code/lean4 in rocq:hol light/scripts/toolchain-exec.sh' rocq compile -Q rocq LeanPort rocq/PrimitiveAdversarial.v
sh '/Users/fawadhaider/code/lean4 in rocq:hol light/scripts/toolchain-exec.sh' rocq check -silent -Q rocq LeanPort LeanPort.PrimitiveAdversarial
```

Compilation of all 40 examples and the preservation theorem passed. Sampled
`Print Assumptions` checks report `Closed under the global context`.
The independent `rocq check` of the final frozen module and its dependency
closure completed successfully (exit status 0).

While this check ran, the core owner changed beta reduction and added batched
substitution to Syntax. A separate compile-only recheck in
`/private/tmp/leanport-primitive-audit.smkQZs/latest` rebuilt those dependencies,
the original 119 regressions, and all 40 new examples plus the preservation
theorem successfully. Its Syntax hash is
`e8ae6fe46f8ab2581f97e9f7f505e59e26796f41091700ec91936fdd5a352be9` and Checker
hash is `7b69bb52074755ccc6fe1fe9a446373d152d12536497c9b76718948b8fc38324`.
Sampled assumption checks, including the preservation theorem, also remained
closed on that snapshot. The independent full-library check above applies to
the frozen snapshot, not to later moving parent sources.

Audited source SHA-256 identifiers:

```text
Syntax.v               91ce24710c244d27e60cdb2a87473b6fd7c22bdd332fdc721abec5ec724d2679
Universes.v            02ff6fd5992c02834b60945f4ac9d932ac8d718014a71b37699a53e8bce680ba
InductiveUtils.v       d2fc8ff2134dc9cbc977e22669445d2cb150cdbfb35c5896fa5e41d95b46cfbb
Primitives.v           8e7d66e507f7851fe8a32f07927abcaa419fc6c76159bd5cc32a00d4653e1aee
Checker.v              e9065703dae5bf068d9069424b20aaa8640586280e819c785bc1e8d4bcf9aeb8
Declarations.v         ad855de6517f42d2da8efa0189e9942ff1eb25af7eadd875c17ccbdc0605e548
Safety.v               8d8e5ca69eef0ead4f617fd8d2bddff25976a1480146b32d2677b5bd815f7f0b
PrimitiveRegression.v  8482b74f9c6a59841853191881c355fd201fec1c05298c53edd146b7fc9f7973
PrimitiveAdversarial.v e6f380de240ad18a7220d50a94893a65086831e13df7ded2c7dd03d2257fa45a
```

## Limits

The suite reuses explicit unit fixtures from `PrimitiveRegression`: inductive
and recursor metadata, and object-language constants standing for ordinary true
arithmetic propositions. These are AST data, not Rocq axioms. Positive controls
exercise real safe-definition admission over those fixtures, not a complete
empty-environment import of Init. Mutated environments isolate individual
validator obligations; they are not claimed reachable via duplicate-safe
admission. The forged-record cases intentionally violate the trusted-environment
precondition and are labeled accordingly.

This is bounded adversarial assurance, not exhaustive semantic verification of
the kernel, every possible compiler shape, or the exported Arena corpus. No
corpus expected answers, input recognizers, external Lean verdicts, new axioms,
proof admissions, or trust-expanding extraction/checker flags were used.
