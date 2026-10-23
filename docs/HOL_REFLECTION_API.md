# Additive Reflection and Condition Library

Integrated locally as an optional library against the **28 native / 10 admission**
main snapshot. It is not loaded by the default checker and does not claim
transfer to the still-private indexed/raw 29/11 composition.

## Main Integration Evidence

The source-only integration adds 23 files, including nine production modules.
Its independent audit holds all 484 pre-existing source files and verifies all
65 borrowed dependency pins. The actual-main fixture-free smoke passes 25
certificate-boundary assertions in 54.522 seconds, including unchanged rule
counts, theorem closedness, structured errors and no new HOL axioms. Its owned
process group is absent after cleanup. The actual-main synthetic runner suite
passes 17 tests and checks cleanup of all 13 test process groups.

Evidence is in `build/reports/hol-reflection-main-integration-audit.json` and
`build/reflection-evidence/20260930T141329-smoke-0ce3e6df/report.json`.
The 274 full-capability assertions below remain historical private evidence,
not a fresh main matrix. Neither the smoke nor this optional integration adds
an Arena pass or completes downstream primitive admission. Documentation was
updated after the source-copy audit; the nine production files remain identical
to its reviewed payload.

## Source Boundary

Load `needs "hol/reflection.ml";;` from the project root. The production
dependency closure contains no fixture, test, generated environment, policy
grant, or declaration-admission call added by this payload.

New library files:

- `condition_contracts.ml`, `condition_validation.ml` (Boolean capability).
- `reflection_syntax.ml`, `reflection_contracts.ml`,
  `reflection_validation.ml`, `reflected_condition.ml` (reviewed capabilities).
- `reflection_terms.ml` (candidate AST builders only), `nat_instantiation.ml`
  (checked proof composition), `reflection.ml` (fixture-free entry point).

The six reviewed capability libraries retain their exact source and contracts
from the sealed Nat successor. This runner/boundary-repair successor additionally
guards the public Nat `cast`, `pi`, and `sort` entry points and preserves
structured error kinds in `reflection_terms.get`. These are OCaml boundary
changes, not changes to theorem statements, logical rules, or contracts.
The existing main `instantiation_certificates.ml` is
imported unchanged, SHA-256
`299b427c05c0a552f93da0c3d02f9b4f48ceb6c0419b1ba2b0dec45f7544fb11`.
The two optional Nat recurrence proof modules are not required or loaded.
No checker, model, environment, validator, native rule, admission rule, or
frontend file is changed.

Fixtures and original control suites are visible under
`tests/hol_reflection/`, not installed by the production entry point. Only
their `needs` paths and exact expected 28/10 counters change. Candidate terms,
typing obligations, negative assertions, and fuel settings are preserved.
Pinned fixture hashes and source transformations are audited separately.

## Public API

All result-returning APIs use `(value, Lean4hol.error) result`. Resource
exhaustion remains an explicit Resource error, not a logical rejection.
Certificates are abstract. Supplied theorems must have no hypotheses or free
variables and match an entire required checked judgment, including environment,
policy, context, expressions, and type. No proof is reused across environments.

```ocaml
type reflection = { typ:expr; of_true:expr; of_false:expr; to_dec:expr }
type nat_condition = {
  prop:expr; as_bool:expr; proof:expr; dec:expr; reflect:reflection
}
type condition = Boolean of expr * expr | Reflected_nat of nat_condition

Lean4hol_reflection_syntax.reflection : bool -> reflection
(* false = Reflection.defn1, true = Reflection.defn2 *)
Lean4hol_reflection_syntax.bool_condition : unit -> expr * expr
Lean4hol_reflection_syntax.nat_condition : bool -> nat_condition
(* false = Condition.natLE, true = Condition.natEq *)

Lean4hol_condition.check_bool_ite :
  ?fuel:int -> environment -> expr -> expr -> (bool_ite_certificate,error) result
Lean4hol_condition.bool_ite_theorem : bool_ite_certificate -> thm
Lean4hol_condition.bool_ite_raw_theorem : bool_ite_certificate -> thm
Lean4hol_condition.bool_ite_inputs : bool_ite_certificate -> expr * expr * expr
(* exact prop, decision, and inferred decision type *)

Lean4hol_reflection.check_type :
  ?fuel:int -> environment -> reflection -> (certificate,error) result
Lean4hol_reflection.check_ite :
  ?fuel:int -> environment -> reflection -> (certificate,error) result
Lean4hol_reflection.check_nat_dite :
  ?fuel:int -> environment -> reflection -> (certificate,error) result
Lean4hol_reflection.check_ite_using :
  ?fuel:int -> thm list -> environment -> reflection -> (certificate,error) result
Lean4hol_reflection.check_nat_dite_using :
  ?fuel:int -> thm list -> environment -> reflection -> (certificate,error) result
Lean4hol_reflection.check_nat_condition_using :
  ?fuel:int -> thm list -> environment -> nat_condition ->
  dec_type:expr -> gadget_type:expr -> (certificate,error) result
Lean4hol_reflection.check_nat_condition :
  ?fuel:int -> environment -> nat_condition -> (certificate,error) result
Lean4hol_reflection.theorem : certificate -> thm
Lean4hol_reflection.raw_theorem : certificate -> thm

Lean4hol_reflected_condition.check :
  ?fuel:int -> ?ite:bool -> ?dite:bool -> environment -> condition ->
  (certificate,error) result
Lean4hol_reflected_condition.check_prepared :
  ?fuel:int -> ?ite:bool -> ?dite:bool -> ?ite_proof:thm -> ?dite_proof:thm ->
  environment -> condition -> thm -> (certificate,error) result
Lean4hol_reflected_condition.theorems : certificate -> thm list
Lean4hol_reflected_condition.raw_theorems : certificate -> thm list
```

The existing `check` and no-proof APIs still perform their original search.
Prepared proofs are an explicit alternative interface, not a hidden cache.
The additive `check_prepared` consumes a whole checked base contract and optional
whole capability contracts. Supported supplied proofs are guarded even when their
flags are false. Bool DITE remains Unsupported, including when supplied a proof.
See [prepared conditions](HOL_PREPARED_INTEGRATION.md) for its separate evidence
and the distinction between current focused tests and historical full-matrix runs.
The candidate type parameters in `check_nat_condition_using` are checked
obligations, never trusted type annotations. The canonical tests obtain them
with genuine `Env.infer`. Optional Bool DITE remains explicitly unsupported.

The main typed-instantiation theorems are `l4_defeq_instantiation`,
`l4_edef_instantiation`, and `l4_checked_instantiation`. The checked theorem
has the exact premise/conclusion:

```
J g A A (Sort u) /\ J (A::g) e f T /\ J g v v A
  ==> J g (inst v e) (inst v f) (inst v T)
where J = l4_checked policy env
```

`Lean4hol_nat_instantiation` exposes checked `judgment` records and operations
`infer`, `check`, `convert`, `close`, `app`, `beta`, `sym`, `trans`, `cast`,
`instantiated_typing`, `apply_symbolic`, and `apply_wrapper`. Every operation
that returns a checked judgment guards the actual theorem against its record;
the identity `cast` and already-Pi `pi` branches are guarded as well. `sort`
also validates before interpreting the type. The record itself remains public
and forgeable: possession of a record alone is never a certificate. Internal
syntax construction and direct field access are not validation operations.
`seed env second` regenerates the generic equation in that exact
environment, with the two Nat variables in its context. `arguments second`
constructs the four canonical arguments. These proof-construction operations
can raise a checked error/exception; structured `Stop` kinds, including Resource,
are preserved with a diagnostic label. They are not a new admission or verdict
API. They do not create an environment or admit dependencies. Proofs certify
actual substitutions through the existing HOL definitions and typed rules,
not unproved syntax-identity shortcuts.

```ocaml
type judgment = {
  env:environment; g:expr list; left:expr; right:expr; ty:expr; h:thm
}
Lean4hol_nat_instantiation.seed : environment -> bool -> judgment
Lean4hol_nat_instantiation.arguments : bool -> expr list
Lean4hol_nat_instantiation.instantiated_typing : judgment -> judgment -> judgment -> judgment
Lean4hol_nat_instantiation.apply_symbolic : judgment -> expr -> judgment
Lean4hol_nat_instantiation.apply_wrapper : judgment -> judgment -> judgment
```

The fixture-free algebra supplies actual proof-building operations; the
staged tests illustrate full composition into `check_nat_condition_using`.
No fixture-dependent automatic Nat checker is installed. The generic theorem
and the concrete arithmetic instance must be produced in the consumer's exact
final environment and policy. Body instantiation uses the main checked helper;
application congruence and beta carry the non-reflexive symbolic equality.

## Five Capability Groups

The portable bounded runner is `scripts/test-hol-reflection.py`. Groups are
`bool`, `ite`, `dite`, `nat-eq`, and `nat-le`. The first three can share one
process and one exact environment; each Nat group uses its own fresh admitted
environment. Setup-library, setup-fixture, and every subsequent real proof stage
have an independent 180-second cap. The same deadline includes both the group's
marker and a fresh completion token printed after the command returns. An early
marker cannot reset an unfinished query's deadline. All preparation and total
process lifetimes are recorded. A branch proof is not a whole capability.

Historical pre-repair native runs on the pinned private 28/10 snapshot completed all five
whole checked and raw capability groups. All 81 real stages passed, with 274
test assertions and no failure/timeout attempts in those three historical runs.
The longest stage was 133.964256 seconds. These 274 assertions were NOT rerun
for this boundary/runner repair and are NOT new main integration evidence. Their
complete logs and copied inventories were independently audited clean. The
sealed 27/9 evidence is provenance only, not substituted for these runs.

| Run | Whole Groups | Assertions | Full Process Lifetime |
| --- | ---: | ---: | ---: |
| Canonical Bool, defn1 ITE, defn1 NatDITE | 3 | 76 | 712.642288 s |
| Canonical NatEq | 1 | 83 | 496.428791 s |
| Canonical NatLE | 1 | 115 | 1041.667640 s |

All three processes exited successfully and were reaped. These are **not**
claims of whole capabilities completing within 180 seconds: the three full
lifetimes sum to 2250.738719 seconds, including setup, admitted dependencies,
symbolic proof preparation, full contracts, and negative controls. Assertions
include preparation and invariant checks, not 274 distinct capabilities.
Logs and source inventories are generated under `build/reflection-evidence/`.

```sh
python3 scripts/test-hol-reflection.py bool ite dite
python3 scripts/test-hol-reflection.py nat-eq
python3 scripts/test-hol-reflection.py nat-le
```

The runner needs the project's already installed HOL toolchain and standard
Python 3; it performs no installation. Fixture pins are enforced at launch.
It copies and individually verifies all library/ML-test/runner/bootstrap bytes,
makes the copied project sources read-only, and starts HOL with that copy as
its working directory. The external shared `toolchain` symlink target is recorded
explicitly; its binaries, dynamic libraries and runtime semantics are not attested.
Both original and copied inventories are rechecked after the process ends. This
is local reproducibility checking, not protection against a hostile account owner.

Continuous error scanning, unique ordered markers and completion tokens, and a
full final-log scan all participate in success. An operational exception, capture
limit, timeout, nonzero exit, source mismatch, or failed cleanup makes the run
fail. Capture is limited to 16 MiB; overflow is an explicit fault, not a clean
truncated log. The owned process group is cleaned even after the direct parent
exits, and parent reaping and group absence are reported separately. Processes
that deliberately escape that session are outside this containment guarantee.
The exact 28/10 rule guards fail on drift rather than ignoring it.

`python3 scripts/test-hol-reflection.py --smoke --stage-cap 180` loads only the
fixture-free library smoke and focused public-record/error-boundary controls.
It does not run any of the five capability groups or admit canonical fixtures.
`python3 tests/hol_reflection/test_runner.py` exercises synthetic process and
source faults, not HOL/Arena verdicts. Proof-search fuel is per delegated query,
not an end-to-end work bound; the runner's wall deadlines are separate.

## Boundary Repair Validation

The corrected private successor completed one authorized fresh fixture-free
smoke in 62.931080 seconds, with a 180-second cap and 25 boundary assertions.
It covers genuine inference/identity cast/Pi/sort, forged theorem/context/
hypothesis/endpoint rejection, and preservation of Resource, Unsupported,
Invalid_input and Proof_failure both directly and through `Lean4hol.run`.
Existing no-new-axiom, theorem-closedness and exact 28/10 rule guards also ran.
The source inventories match, both markers occur exactly once, the complete
log is error-free, the parent exited zero and was reaped, and its group is absent.

The prior smoke's test-only `module NI` parse error is retained, not counted as
a pass; the corrected spelling is `Ni`. No unfinished proof was resumed. The
17 synthetic runner regressions passed with process-group permissions. A
separate sandbox-limited attempt that encountered signal/probe permission errors
is retained as failed; every tested group was ultimately absent. These are
runner controls, not logical verdicts. Neither this smoke nor the synthetic
tests reruns the historical 274 capability assertions or establishes new main
runtime coverage. The integration owner must label any later main smoke separately.

## Remaining Primitive Bridge

This library proves capabilities, not downstream arithmetic admission. The
existing `Lean4hol_primitive.check_definition`, primitive contracts, native
reduction, and declaration admission are untouched. To consume these helpers,
a future separately reviewed primitive validator must obtain capabilities in
its actual candidate environment, check the candidate primitive's own body
and required equations, and derive the exact existing/new primitive contract
from the checked capability premises. It must then use the existing admitted
contract boundary. Merely matching a canonical name, having a test fixture,
or observing a successful capability marker must never install a primitive.
Div/mod/gcd/bitwise/well-founded unfolding and frontend integration are not
implemented by this payload. No source oracle or precomputed verdict is used.
The Bool/ITE/DITE tests and each Nat test have separately admitted environments.
Their certificates cannot be combined across those environments. A consumer
requiring NatLE plus ITE/DITE must check all needed capabilities in its own
single final environment. Defn2 ITE/DITE and every combination of dispatcher
flags are not added to these five focused groups.

## Provenance

Lean4Lean `Primitive.lean`, first 177 lines, pinned at
`8223d223ed98661882e95d9d6a7126df7097cd76`; Apache-2.0 attribution is retained
in each adapted library and `hol/NOTICE`. The test payload carries the original
upstream license. Canonical fixture bodies are genuinely admitted typed
implementations, not a claim of byte-identical Lean elaborator output. The
encoded HOL specification is not thereby proved equivalent to the Lean kernel.
