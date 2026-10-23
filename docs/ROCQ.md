# Rocq Core Interface

This is a standalone Gallina port, not an invocation of Lean. Executable reference:
`digama0/lean4lean` at `8223d223ed98661882e95d9d6a7126df7097cd76`.
The implementation includes the dependent-function core and metadata-gated
inductive, literal, primitive and quotient reduction. Declaration/inductive/
quotient admission and the strict NDJSON adapter are separate parent-owned work;
canonical primitive admission is owned by the primitive worker.

## Stable Data Contract

Gallina constructor names below become OCaml constructors with the same spelling.
Numeric name segments and natural literals use binary `N` (with binary positive
constructors), retaining arbitrary precision with logarithmic representation.
Binder indices, offsets and fuel use structural `nat = O | S of nat`, NEVER
OCaml `int`. The adapter must convert nonnegative numerals exactly, or decline
on a resource limit; it must not truncate, wrap, or saturate them.
Strings use default structural extraction (`EmptyString | String` of ASCII
and string); no custom or machine-integer extraction substitutions are used.
Wire names must retain their anonymous/string/numeric segment structure.

```text
name = NameAnon | NameStr name string | NameNum name N
level = LZero | LSucc level | LMax level level | LIMax level level
      | LParam name | LMVar name
binder_info = BDefault | BImplicit | BStrictImplicit | BInstImplicit
literal = LitNat N | LitString string
expr = EBVar nat | EFVar name | EMVar name | ESort level
     | EConst name (list level) | EApp expr expr
     | ELam name binder_info expr expr
     | EPi name binder_info expr expr
     | ELet name expr expr expr bool
     | ELit literal | EProj name nat expr | EMData expr
```

Lambda/Pi arguments are name, binder-info, domain, body. Let arguments are
name, type, value, body, nondependent hint. The hint and binder annotations do
not alter logical equality. Metadata is erased by `EMData`; the adapter must
not erase the attached expression. Names are not flattened dotted strings.

```text
binding = { binding_type : expr; binding_value : option expr }
context = { bound_context : list binding;
            free_context : list (name * binding) }
decl_kind = DAssumption | DDefinition | DTheorem | DOpaque | DUnsupported
          | DInductive inductive_data | DConstructor constructor_data
          | DRecursor recursor_data | DPrimitive primitive_kind
          | DQuotient quotient_kind
          | DUnsafe decl_kind | DPartial
declaration = { decl_name : name; decl_params : list name;
                decl_type : expr; decl_value : option expr;
                decl_kind_of : decl_kind }
environment = list declaration
```

Inductive extension contract (all count/index fields are `nat`; all metadata
must be independently derived or verified by parent-owned `Inductive.v`):

```text
inductive_data = { ind_num_params : nat; ind_num_indices : nat;
  ind_all : list name; ind_ctors : list name; ind_num_nested : nat;
  ind_is_rec : bool; ind_is_reflexive : bool; ind_is_unsafe : bool }
constructor_data = { ctor_induct : name; ctor_index : nat;
  ctor_num_params : nat; ctor_num_fields : nat; ctor_is_unsafe : bool }
recursor_rule = { rule_ctor : name; rule_nfields : nat; rule_rhs : expr }
recursor_data = { rec_all : list name; rec_num_params : nat;
  rec_num_indices : nat; rec_num_motives : nat; rec_num_minors : nat;
  rec_rules : list recursor_rule; rec_k : bool; rec_is_unsafe : bool }
```

The common declaration header retains universe parameters/type/name; rule
right-hand sides use the recursor declaration's universe parameters.
`rec_num_params + rec_num_motives + rec_num_minors` is the first index position;
adding `rec_num_indices` gives the major-premise position. Constructor fields
are the final `rule_nfields` arguments of a saturated major constructor.

`primitive_kind` is `PNatAdd | PNatPred | PNatSub | PNatMul | PNatPow |
PNatGcd | PNatMod | PNatDiv | PNatBEq | PNatBLE | PNatLAnd | PNatLOr |
PNatXor | PNatBitwise | PNatShiftLeft | PNatShiftRight | PCharOfNat | PStringOfList`.
`PNatBitwise` names structured `Nat.bitwise` (`core_bitwise_name`), with
`primitive_kind_eqb` and its proved equality specification available in Syntax.
It has no accelerated computation: native dispatch returns `Accept None`
without evaluating partial arguments, allowing ordinary certified-body delta
reduction. Canonical classification and signature/name tables remain owned by
the primitive worker.
`DPrimitive` is an authenticated admission result, not a wire flag. The parent
may install it only after validating the upstream required equations/signature.
Ordinary named definitions never gain arithmetic semantics just from their name.

`quotient_kind = QType | QCtor | QLift | QInd`; `DQuotient` is installed only
by parent-validated canonical quotient admission. Lift's major premise is
argument 5 and ind's is argument 4 (zero-based); both functions are argument 3.
Reduction requires a validated `QCtor` head with exactly three arguments.

Bound context and environment are newest-first. Bound entry `n` is stored in
the context *before* that entry was pushed; lookup lifts its type/value by
`n+1`. Free-context entries are closed with respect to bound variables and
may reference earlier free entries. `empty_context` is the external closed
term context. `DAssumption` is an object-language assumption, not a Rocq axiom.
Definitions and theorem bodies delta-reduce, matching `Declaration.deltaValue?`
at the pinned upstream commit; opaque bodies are not unfolded.

`DUnsafe role` preserves the underlying declaration role; `DPartial` marks a
partial definition. The default safe `get_constant` rejects both with
`MalformedDeclaration` before reading their type or unfolding their value.
Parent-owned `Safety.v` may construct checking-only environment views that
strip `DUnsafe` for unsafe checking, and map `DPartial` to `DDefinition` for
partial/unsafe checking. The stored logical environment retains the markers;
the core does not globally unwrap them or introduce a new checker mode.

## Result And Entry Points

```text
result A = Accept A | Reject reject_reason | Decline decline_reason
reject_reason = UnknownConstant | UnknownFreeVariable | LooseBoundVariable
              | UnknownUniverse | UniverseArity | ExpectedSort | ExpectedPi
              | TypeMismatch | NotDefinitionallyEqual | DuplicateDeclaration
              | DuplicateUniverse | MalformedDeclaration | MetaVariable
decline_reason = OutOfFuel | UnsupportedExpression | UnsupportedDeclaration

infer : nat -> environment -> list name -> context -> expr -> result expr
whnf : nat -> environment -> list name -> context -> expr -> result expr
defeq : nat -> environment -> list name -> context -> expr -> expr -> result bool
check : nat -> environment -> list name -> context -> expr -> expr -> result unit
check_defeq : nat -> environment -> list name -> context -> expr -> expr -> result unit
level_equiv : nat -> level -> level -> result bool
level_le : nat -> level -> level -> result bool
lift : nat -> nat -> expr -> expr
subst : nat -> expr -> expr -> expr
instantiate : expr -> expr -> expr
subst_many : nat -> list expr -> expr -> expr
instantiate_many : expr -> list expr -> expr
subst_levels : list name -> list level -> expr -> expr
```

`check ... term expected_type` validates the expected type, infers the term,
and compares the types without cumulativity. `instantiate body value` removes
bound variable zero capture-avoidantly. `lift amount cutoff term` and
`subst index value term` use de Bruijn indices. `defeq` is the internal
conversion interface on already well-typed inputs: `Accept false` means a
completed negative equality decision, not acceptance of a declaration.
`check_defeq` checks both inputs and their types before deciding conversion.
`whnf` is also an internal reduction interface, not a typing verdict.

`subst_many index values body` removes a contiguous block of binders starting
at `index`. Values are ordered innermost binder first and live outside the
removed block; substitution lifts them beneath residual binders and lowers
variables above the block. `instantiate_many body values` uses cutoff zero
and returns `body` unchanged for an empty list. These are syntax operations,
not typing or admission judgments.

All entry points require a previously validated environment and context.
Raw declaration records are NOT certificates. In particular the adapter must
not admit arbitrary declaration types or bodies merely by constructing these
records. The parent-owned `Declarations.v` checker owns that precondition;
its `admit` and `check_declarations` functions are included in extraction.
Unsupported declarations must use `DUnsupported`, never `DAssumption`.
An empty environment/context requires no external validation.

Fuel bounds semantic recursive depth and the local lazy-delta loop, following
upstream `Methods.withFuel`, rather than promising a global allocation or
wall-clock bound. Checked inference traverses input syntax by structural
recursion without spending semantic fuel merely for syntax depth. Fuel exhaustion
propagates as `Decline OutOfFuel`. Runtime stack/allocation exceptions also
must be reported as declines by the frontend, never accept/reject.
Arithmetic uses standard binary `N` operations. Power and left shift also
bound their iteration count by the available fuel; exceeding it declines.
Right shift first uses a proved `log2` zero shortcut, otherwise bounds the
iteration count. No large shift operand is converted into unary `nat`.

## Modules And Provenance

Compile with the working directory `rocq/` and `-Q . LeanPort`, using
`From LeanPort Require Import Syntax Universes Checker.`.
`Declarations.v`, `DeclarationRegression.v`, `InductiveUtils.v`, `Inductive.v`,
`InductiveRegression.v`, `Quotient.v`, `Safety.v`, `InductiveSafety.v`, the nested
admission modules and `ArenaExtract.v` are parent-owned.
`Primitives.v` and `PrimitiveRegression.v` belong to the primitive worker.

`Syntax.v`: syntax, structural name equality, capture-avoiding substitution,
universe substitution, local/environment lookup.
`Universes.v`: the guarded sublevels of upstream `Level.Normalize.normalizeAux`
and its Theorem-39 domination comparison, represented as lists instead of
balanced maps. Essential `imax` is not approximated by `max`.
`Checker.v`: checked inference; conservative and full beta/zeta/delta/iota/quotient WHNF;
proof irrelevance, function/structure eta and unit-like conversion;
dependent projection typing with Prop restrictions; binary Nat primitives;
and UTF-8 string expansion through validated `Char.ofNat`/`String.ofList`.
`Regression.v`: executable Gallina positive, negative, and decline examples.
`ExtensionRegression.v`: metadata-gated literal, arithmetic, projection,
recursor, structure-eta, quotient-layout and safe-lookup regressions.
`PerformanceRegression.v`: low-fuel argument congruence and proof irrelevance,
structural inference depth, erased unequal arguments, full projection retry,
rigid-head negative congruence without repeated speculation, and batched-beta
argument ordering/capture avoidance under residual binders.
`Extract.v`: ordinary OCaml extraction without custom extraction substitutions.

### Lazy Conversion

Conversion first tries bounded alpha comparison and the upstream quick cases.
It checks proof irrelevance by inference-only type lookup before evaluating
proof bodies, and tries matching delta-head application arguments before unfolding.
Rigid applications are compared only after lazy reduction stalls: trying their
arguments at each preliminary stage repeats failed subproblems exponentially.
Definitions whose first lambda binder is syntactically unused unfold before
speculation. This last optimization selects ordinary delta/beta reduction; it
never directly produces an equality verdict or treats a fuel decline as rejection.
Conservative WHNF preserves definition heads and uses cheap projections;
the decreasing lazy-delta loop performs native reduction and head unfolding.
Failed argument congruence is never treated as a definitive mismatch, since
unfolding can erase unequal arguments. Stuck projections, including projections
in application heads, retry full projection reduction before final conversion.

The alpha fast path shares a 256-node budget between branches. Running out
returns an inconclusive false fast-path result, not a negative conversion
verdict. `core_alpha_sound` proves that a successful fast path implies
`expr_eqb = true`. There is no pointer equality, unchecked extraction hook,
or cache keyed without a context. Support scans remain at the public reduction
boundary, not every recursive reduction/inference call. Identity substitutions
preserve their input value; the no-universe-parameters shortcut has a proved
agreement lemma with ordinary universe substitution.

The internal `methods` record now also exposes:

```text
infer_type_method : context -> expr -> result expr
whnf_core_method : bool -> context -> expr -> result expr
```

The boolean means cheap projections. Inference-only is for known well-typed
conversion operands, never admission; public `infer` and `check` still check
every argument and annotation. `infer_step` takes an explicit checking boolean;
`defeq_step` now also receives the universe-parameter list. Public entry-point
signatures above are unchanged.

### Batched Beta

`core_beta_collect` consumes the syntactically visible lambda prefix before
performing one simultaneous substitution and reapplying remaining arguments.
This follows the `instantiateRange` loop in pinned
`TypeChecker.whnfCore'`. Lambdas exposed by substitution are handled on the
next WHNF iteration, so fuel accounting can differ from repeated single-beta
steps. This avoids copying an argument beneath binders that are immediately
eliminated. It does not introduce a cache, pointer identity, syntax metadata,
or an extraction override; singleton substitution is unchanged.

The new checked lemmas establish empty substitution identity, singleton
agreement with existing `subst`/`instantiate`, scope preservation for lifting,
and general scope preservation for simultaneous substitution. Specifically,
an expression scoped at `index + length values + depth`, with every
replacement scoped at `depth`, remains scoped at `index + depth`.
These are syntax invariants, not a typing-preservation theorem. A general
equivalence theorem between batched beta and repeated beta, and overall
checker semantic soundness, remain unproved.

This is a changed reimplementation of executable upstream algorithms, under
Apache-2.0; see `rocq/NOTICE` and `rocq/LICENSE`. It does not port upstream
verification axioms, pointer tricks, or proof holes. Small checked invariants
are not a proof of overall checker soundness.

## Builds And Verification

Standard commands using parent-installed Rocq 9.2 and OCaml 4.14.2:

```sh
cd rocq
make check
make audit
```

`make check` compiles the Gallina core, the parent declaration modules, all
121 core Gallina examples (54 original, 44 extension and 23 strategy examples), and ordinary
structural extraction to `lean_core.ml`
and `lean_core.mli`. It compiles a native `core_regression` executable and runs:

- 40 extracted core acceptance/rejection/decline checks.
- 19,200 valuation checks comparing universe normalization to `level_eval`.
- 1,536 deterministically generated universe identities, each also checked at
  25 valuations. These finite samples are tests, not completeness proofs.
- 4,096 deterministic generated simultaneous-substitution comparisons against
  repeated single substitution, checking exact syntax equality and output scope.
  Cases include open arguments, nonzero cutoffs, empty/multiple replacement
  lists, and residual binders.

The 2026-09-29 lazy-conversion checkpoint was compiled, extracted and tested
from identical copies of the six core/regression modules under
`/private/tmp/rocq-strategy-20260929`, to avoid concurrent writes to the parent's
shared `.vo` build. All 113 examples and the then-current 38 native checks,
universe valuations and identities passed there;
`rocq check` rechecked those six modules and dependencies. Full parent admission
integration and a fresh Arena benchmark remain separate from this checkpoint.

The subsequent batched-beta checkpoint was compiled, extracted and tested in
`/private/tmp/rocq-depth-profile-20260929/rocq`. All 121 examples, 40 native
checks and generated checks listed above passed; `rocq check` rechecked all six
core/test modules and dependencies. Only the reviewed four source diffs were
then applied to shared `Syntax.v`, `Checker.v`, `PerformanceRegression.v` and
`core_regression.ml`. No compiled objects or native binaries were copied.
A fresh shared build and parent integration run are separate from these private
results.

### Strategy Regression Profile

The initial lazy strategy compared failed rigid arguments before conservative
WHNF, again in the lazy loop, and again at final congruence. A private native
harness that counts calls to the unchanged extracted `defeq_step` measured
118,097 calls for a depth-10 constructor mismatch. Restricting speculation to
delta heads and removing its duplicate entry-stage invocation reduced that to
21 calls, with the same negative result. Regression examples forbid recursive
speculation on rigid heads and ensure an unused argument can be erased even
when evaluating it would exceed the available fuel.

A preceding strategy checkpoint's private integration executable was tested without replacing
`build/rocq-check`. All 141 tutorials retained correct verdicts. The selected
147-case run recorded 98 correct accepts, 48 correct rejects, one fuel decline
(`perf/church-numerals`), zero wrong verdicts/timeouts/integrity failures, and
73 explicitly unselected cases. Its report is
`/private/tmp/rocq-profile-20260929/arena-strategy-regression.json`; the runner
verified the executable hash before and after the run. This is a selected
regression run, not a whole-corpus result.

Standalone private timings at unchanged fuel 512 were approximately 0.26s for
`discarded-argument`, 0.008s for `discarded-argument-match`, and 0.007s for the
correct rejection of `refute-cheap-first`. `church-numerals` reached its genuine
fuel decline in 0.006s instead of timing out. These are single-run timings,
not statistically controlled benchmarks. Other deep conversion/fuel cases
and shared-DAG costs remain unresolved.

### Method Allocation

Profiling confirmed that eager predecessor construction allocated a complete
method-record chain before even inferring one sort. At fuel 512, 10,000 such
calls allocated 27,152 minor-heap words per call and took about 0.094s; fuel
2048 increased that to 108,560 words and 0.81s. Delaying predecessor construction
inside the five method lambdas reduced this to 102 words per call at every
tested fuel (8, 32, 128, 512, 2048, 4096, 8192), with about 0.0002s for 10,000 calls.
These numbers measure the extracted core, excluding parser/scheduler work.
An extended constant-sort profile at fuel 512, 4096 and 8192 also stayed flat
for WHNF (125 words/call), defeq (113), checking (420), and checked equality
(467). The fuel numeral is constructed once before the measured calls, as in
the frontend. Larger fuel can still permit more real reduction and allocation;
this result only removes the cost of constructing unused predecessor methods.
The default remains 512. The parent's bounded 4096-fuel Arena experiment is
separate and was not duplicated by this worker.

`checker_delayed_equivalent` proves exact record equality with the retained
eager reference for every fuel, environment and universe-parameter list, by
`reflexivity`. This introduces no cache, effects, extraction override, or fuel
increase. The unused eager reference is absent from the extracted executable.
Both implementations produced identical verdicts in a private A/B comparison.
Three-run medians were nearly unchanged for shift-cascade (0.021s) and
beta-ladder (1.51s), while refute-cheap-last was somewhat slower (2.36s versus
2.54s). The allocation win is not a claim that every reduction-heavy case speeds
up, nor does it resolve deep-fuel or DAG-sharing limitations.

### Batched-Beta Profile

The private integration candidate passed 187 selected Arena cases: 100 correct
accepts, 69 correct rejects, 18 acceptable-either results, and 33 explicitly
unselected cases, with no wrong verdicts, declines, timeouts or integrity
failures. All 141 tutorials were included. The immutable report is
`/private/tmp/rocq-depth-profile-20260929/batch-regression.json`; this is not a
whole-corpus run.

At fuel 4096, shared-subterm accepted privately in 1.21s. Its baseline run
was still running at 40s when the private timeout stopped it; a CPU sample at
about 12s showed a 10.7GB footprint, dominated by `lift` copying intermediates
and garbage collection. At unchanged default fuel 512 the candidate instead
declined in 0.012s. Church numerals still decline at 4096 but accept at 16384
in 0.034s; their normal form has 14,520 nested applications. These are single-run
observations. The baseline executable hash was
`22eb979996c6332400f107217ad95d64d182a11a7d8eb808f6d604ed823bf1f4`.
The candidate also includes delayed methods, so these timings do not isolate
beta batching from that earlier optimization. Default fuel remains 512.

The private app-lam profile reaches the last definition and stalls in the
`scoped 0` precheck before inference. Fueled-chain spends its sample under
repeated checked inference, with name/string equality and list-environment
lookup dominating the leaves. Both remain unresolved. A synthetic shared-DAG
profile using unchanged extracted functions confirms exponential revisitation
in scope checking and inference: inference allocations rise from 2,719,270
words at depth 12 to 43,515,430 at depth 16 and 174,063,142 at depth 18.
No shared memoization change is included in this checkpoint.

`make audit` rechecks the compiled modules and their dependencies through
`rocq check`, with no admitted modules and no weakened checking flags.
The actual context summary reported no axioms, no type-in-type dependencies,
no unsafe fixpoints and no inductives with assumed positivity.

Proved invariants include structural name-equality correctness, zero lifting,
variable-zero instantiation, decline propagation, zero-fuel decline for all
core operations, guarded-sublevel domination soundness, list-of-sublevels
comparison soundness, the fuel-bounded binary right-shift shortcut's agreement
with standard `N.shiftr`, rejection of unsafe/partial constant lookup,
bounded-alpha success correctness, the universe-substitution identity shortcut,
primitive-tag equality, bitwise native-fallback/delta invariants, delayed/eager
method-record equivalence, empty/singleton simultaneous-substitution identities,
lifting and simultaneous-substitution scope preservation, and
decomposition of successful checking into successful inference and conversion.
`check_accepts_conversion` is an implementation
invariant, NOT a semantic typing soundness theorem.

The extracted `.mli` is the authoritative OCaml adapter interface. Default
extraction retains explicit `True/False`, `Nil/Cons`, `Some/None`, `Pair`,
`Tt`, structural ASCII/string and binary `N0/Npos` constructors. There are no
custom extraction replacements, native integer casts, `Obj.magic`, or calls
to Lean or an external logical checker in the extracted core. Regression
checks are a function, not an automatically executed module initializer.

The parent-owned `ArenaExtract.v` separately emits `lean_arena.ml/.mli` with
inductive and quotient admission for the NDJSON adapter. `lean_core.ml` remains
the standalone core/regression extraction. This worker rebuilt the parent
integration harness without editing its source and ran the pinned full Arena
corpus at the pre-quotient-integration checkpoint recorded in
`rocq/arena-core-check.json`: 213 executed, 95 correct accepts, 62 correct
rejects, 8 acceptable-either results, 48 declines, 7 missing downloads, zero
wrong verdicts/faults/timeouts. The report pins the corpus/inputs and records
the checker command, but does not hash the executable. It is a timestamped
runtime checkpoint, not a preserved binary snapshot; later parent integration
results must not be conflated with it.

## Missing Coverage And Trust Boundary

Implemented core reductions require admitted metadata, not supplied wire flags.
Nat literals require the exact Nat/zero/succ shapes; arithmetic requires
`DPrimitive`; string literal support additionally requires authenticated
`PCharOfNat` and `PStringOfList`; quotient reduction requires `DQuotient`.
Unsupported dependencies decline even in a subtree a reduction could erase.
Recursor RHS terms are independently generated by parent admission. This core
worker does not claim to have implemented or audited the parent-owned admission
modules or the primitive worker's canonical equation recognizers. Nested
inductive admission, primitive coverage, safety policy, and reserved-name
policy remain integration responsibilities of those workers.

The core uses de Bruijn local binders instead of upstream fresh free variables
and list environments instead of hash maps. Lazy conversion preserves folded
heads, but declaration records currently omit upstream reducibility hints:
when both sides are delta-reducible this port unfolds both, without the
height/abbreviation priority rule. It does not reproduce upstream memoization,
hash-consing, or cache/fuel/performance behavior. Shared expression DAGs are
still traversed structurally by typing and by parent admission's `scoped`
precheck; the bounded alpha shortcut alone does not solve that cost. Deep
semantic conversion can still decline. These are genuine remaining performance
limitations, not reasons to classify resource exhaustion as rejection.

Outstanding proofs: correctness/completeness of the complete guarded-level
normalizer, capture-avoiding substitution and context invariants beyond the
small lemmas above, preservation of reduction, and soundness of inference and
conversion against an independent Lean typing relation. Overall semantic
soundness and compatibility with all Lean4Lean features are NOT established.
Standard extraction, OCaml compilation/runtime, and the separately developed
NDJSON parser/adapter remain explicit trust boundaries. The finite Arena
checkpoint above is an end-to-end runtime result, not a soundness proof or a
claim of whole-corpus support; all declines and missing cases remain visible.
