# Primitive Definition Validation

`rocq/Primitives.v` is a changed Gallina adaptation of
`vendor/lean4lean/Lean4Lean/Primitive.lean`, pinned at
`8223d223ed98661882e95d9d6a7126df7097cd76` (Mario Carneiro and Lean4Lean
contributors, Apache-2.0). Attribution is preserved in the source; the license
is `rocq/LICENSE`. Upstream verification assumptions are not imported.

## Integration Contract

```coq
classify_primitive : nat -> environment -> name -> list name ->
                    expr -> expr -> result (option primitive_kind)
```

The final arguments are the declared type and body. The caller must first
check the header, scope, type, and body of a **safe definition**, in the empty
context against the previously validated environment. The candidate must not
already be installed. Safety is a caller obligation because the interface has
no safety argument. Inductive, recursor, and primitive metadata must come from
checked admission, never unvalidated input records.

- `Accept None`: a nonreserved hierarchical name; ordinary admission may proceed.
- `Accept (Some k)`: canonical signature and dependencies passed, followed by
  either Nat equation validation or upstream text interface validation.
  The caller may install `DPrimitive k`, retaining the checked type and body.
- `Reject`: a definite signature, equation, dependency, typing, or duplicate error.
- `Decline`: unsupported compiled form or exhausted
  fuel. Never issue metadata or fall back to ordinary reserved-name admission.

The six primitive inductive/constructor names are rejected as definitions.
Imports are `Syntax`, `Universes`, `Checker`, and `InductiveUtils`, not
`Declarations`. This module does not change admission, extraction, or frontend code.

## Canonical Equations

Variables below are arbitrary variables in checked contexts, not numeric
samples. `f` denotes the candidate **body**, not a preinstalled constant.
`check_defeq` checks both sides and their common type before conversion.

| Primitive | Equations | Certified dependency |
| --- | --- | --- |
| `Nat.add` | `f x 0 = x`; `f x (succ y) = succ (f x y)` | canonical Nat |
| `Nat.pred` | `f 0 = 0`; `f (succ x) = x` | canonical Nat |
| `Nat.sub` | `f x 0 = x`; `f x (succ y) = pred (f x y)` | pred |
| `Nat.mul` | `f x 0 = 0`; `f x (succ y) = add (f x y) x` | add |
| `Nat.pow` | `f x 0 = 1`; `f x (succ y) = mul (f x y) x` | mul |
| `Nat.beq` | true at `(0,0)`; false at `(0,succ x)` and `(succ x,0)`; `f (succ x) (succ y) = f x y` | canonical Nat/Bool |
| `Nat.ble` | same four cases, but true at `(0,succ x)` | canonical Nat/Bool |
| `Nat.shiftLeft` | `f x 0 = x`; `f x (succ y) = f (mul 2 x) y` | mul |
| `Nat.shiftRight` | `f x 0 = x`; `f x (succ y) = div (f x y) 2` | div |

Signatures are exactly the canonical arrows, with no universe parameters.
Binder names/info and `EMData` wrappers are transparent; arbitrary signature
aliases are not accepted. Each dependency needs its correct `DPrimitive` tag,
nonempty body, and canonical signature. Name/type presence alone is insufficient.
Beta, zeta, delta, iota, and other checked conversions may establish equations.
Closedness is checked before introducing probe binders, and the candidate is
never preinstalled, preventing circular self-authentication by acceleration.

### Reflection And Conditions

Both upstream continuation-style `Reflection` encodings are represented:
false evidence is either `Not (b = true)` or `b = false`. The relation's type,
conditional interfaces, and both true/false branch equations are checked.
Dependent Nat conditionals also check their proof-producing branches.

`Nat.decLe` is compared with the first reflection instantiated at certified
`Nat.ble`; `Nat.decEq` uses the second at certified `Nat.beq`. A typed lambda
gadget simultaneously checks the proposition, boolean, and reflection proof.
Proof helper names are not trusted: their types and applications are checked.
Boolean `ite` checks both general branches. Boolean `dite` explicitly declines,
matching upstream; no primitive clause needs it.

### Division And Modulo

`primitive_check_fuel_rec` implements the shared upstream validation:

1. Authenticate subtraction, Nat/Bool, the `Nat.le` interface, reflected decision
   procedure, and required conditional equations.
2. Check `go : forall y, 1 <= y -> forall fuel x, succ x <= fuel -> Nat`.
3. Check the top equation and general helper equation below.

Division uses `Nat.div.go`:

```text
div x y = if h : 1 <= y then go y h (succ x) x proof else 0
go y hy (succ t) x h =
  if hle : y <= x then succ (go y hy t (sub x y) decrease) else 0
```

Modulo uses `Nat.modCore.go`:

```text
mod 0 y = 0
mod (succ x) y =
  if y <= succ x then
    (if h : 1 <= y then go y h (succ (succ x)) (succ x) proof else succ x)
  else succ x
go y hy (succ t) x h =
  if hle : y <= x then go y hy t (sub x y) decrease else x
```

Applications of `Nat.lt_succ_self` and `Nat.div_rec_fuel_lemma` are typechecked.
No zero-fuel helper equation is needed: its bound premise is impossible in the
validated environment. Checking only the top equation is insufficient; typed
fixtures replacing the helper by zero or the wrong recurrence are rejected.

### Gcd And Bitwise Recursion

`primitive_unfold_nat_well_founded` follows upstream's compiled unary-wrapper,
`WellFounded.Nat.fix`, `go`, and `Nat.eager` boundaries, using non-delta
`whnf_core_method` and explicit unfolding. It checks the packed measure equals
the first Nat argument, fix/go arguments and initial fuel agree, the eager
gadget's general equation, and the helper's symbolic successor-fuel step.
Recursion-variable capture by the functional is rejected by retyping it in
the original outer scope.

The result is a packing function, an induction-hypothesis domain, and a
functional `F`. Every probe introduces a fresh, arbitrary, typed `ih`; it does
**not** replace recursive calls by the candidate. Probes constrain all fuel
levels, not merely the outermost unfolding.

Gcd checks `F (pack 0 n) ih = n` and
`F (pack (succ m) n) ih = ih (pack (mod n (succ m)) (succ m)) decrease`.
Bitwise checks arbitrary `f : Bool -> Bool -> Bool`, `n`, and `m`: both zero
branches and the recursive branch with `div n 2`, `div m 2`, parity from
`mod _ 2 = 1`, and output `2*r` or `2*r+1`.

Public `Nat.mod_lt`/`Nat.zero_lt_succ` and `Nat.bitwise_rec_lemma` proof
applications replace compiler-generated private proof names. Each must
typecheck against the induction hypothesis's actual decrease domain. Proof
irrelevance permits this replacement; theorem names alone authorize nothing.

`primitive_check_boolean_operator` implements land/or's two general Bool cases
and xor's four constructor cases. `primitive_check_bitwise_instance` additionally
requires the literal `Nat.bitwise operator` form and certified bitwise metadata.

### Complete Metadata Table

All 18 primitive definition names in upstream `checkDef` now have classifier
branches. `PNatBitwise` has the distinct canonical signature
`(Bool -> Bool -> Bool) -> Nat -> Nat -> Nat`; its metadata is issued only after
the complete symbolic well-founded and functional equations pass. Land/or/xor
consume that certificate, check the canonical application, and authenticate
their own boolean operator equations before issuing binary-operation metadata.
The primitive dependency guard compares exact kinds with `primitive_kind_eqb`.

No native reduction of the higher-order bitwise function is requested: the
parent core keeps it on the ordinary definition-unfolding path. Positive tests
check body typing and classification at every step of the bitwise/land/or/xor
chain, then exercise the existing binary Nat reductions. Adversarial tests
reject ordinary name/type-only definitions, wrong tags/signatures, missing
bodies, wrong boolean operators, noncanonical heads, and circular installation.
Unknown wrapper shapes still decline instead of receiving partial certificates.

## Text Is Interface-Only

Upstream deliberately has **no defining-equation probes** for `Char.ofNat` or
`String.ofList`. The verification clauses in
`Verify/Environment/Primitive/Clauses.lean` record interface/translation facts,
not host arithmetic semantics. This port preserves that design, with the
caller's checked-body-typing precondition:

- Char: canonical `Nat -> Char`, canonical Nat, and `Char` is a type.
- String: canonical `List.{0} Char -> String`; `Char` and `List.{0} Char` are
  types; instantiated `List.nil` and `List.cons` have their canonical types.

Successful interfaces issue metadata. Different well-typed representations,
even constant implementations, are not rejected by invented equations. Core
`core_expand_string` builds
`String.ofList (List.cons (Char.ofNat codepoint) ... List.nil)`; no arbitrary
accelerated text arithmetic is authorized. A regression compares an actual
literal with this expansion after checked interface admission.

## Fuel, Proofs, And Trust

All new recursive traversals decrease explicit fuel: signature matching,
closedness, equation lists, lambda telescopes, and free-variable inspection.
Checker fuel bounds each check's depth, not a global instruction budget.
Unsupported compiler shapes and exhaustion yield `Decline`, never certificates.

`classify_primitive_metadata_requires_certificate` proves a returned kind has
either successful Nat equation validation or successful text interface
validation, according to its disjoint operation class.
`primitive_check_equations_accepts` proves every check in a simple equation
list succeeded. `primitive_lookup_complete` covers every enum constructor;
`classify_bitwise_requires_full_equations` establishes the bitwise equation gate;
`primitive_bitwise_instances_require_certificate` establishes the dependency
gate for its instances. These are operational gate theorems, **not a semantic soundness
proof of the whole kernel or host arithmetic**. They retain the validated
environment and pretyping obligations.

No Gallina axioms, admissions, unchecked extraction, external Lean verdicts,
Arena expected answers, or corpus-specific recognizers are used.

## Local Verification

From `/Users/fawadhaider/code/lean4 in rocq:hol light`:

```sh
sh scripts/toolchain-exec.sh rocq compile -Q rocq LeanPort rocq/Primitives.v
sh scripts/toolchain-exec.sh rocq compile -Q rocq LeanPort rocq/PrimitiveRegression.v
sh scripts/toolchain-exec.sh rocq check -silent -Q rocq LeanPort LeanPort.Primitives LeanPort.PrimitiveRegression
```

`Syntax.vo`, `Universes.vo`, `Checker.vo`, and `InductiveUtils.vo` must match
current sources; coordinate parent rebuilds instead of using stale artifacts.

`PrimitiveRegression.v` contains 119 examples, retaining the original 56
scenarios (with corrected, faithful text and now-supported bitwise expectations). Coverage includes
typed arithmetic chains, both reflection encodings, reflected comparisons,
complete div/mod validation, classified right shift, compiled gcd/bitwise
probes, boolean operators, forged dependencies, wrong equations, sample-only
impostors, recursion capture, fuel/unsupported propagation, text interfaces,
complete bitwise certificate chains, and accelerated binary bitwise operations.
Explicit object-language theorem assumptions and kernel metadata are unit
fixtures, not claims of parsed declaration admission or new Rocq axioms.
Tests are independent of extraction and the frontend.

The final metadata-tag integration was compiled in the isolated directory
`/private/tmp/leanport-bitwise.SQ5L7g`: copied `Syntax`, `Universes`, `Checker`,
and `InductiveUtils` sources were compiled unchanged, followed by both owned
modules. No shared `.vo` files were written for this integration. Run the same
commands above inside that directory, using the absolute path to the project's
`scripts/toolchain-exec.sh`. Parent must rebuild the integrated dependency graph
from source; copying isolated `.vo` files into an older build is not supported.

The prior Arena report `build/reports/rocq-arena-nested-primitives.json` only
prioritized remaining names. Corpus compatibility and performance are separate
parent integration runs; no report result is used by this checker.
