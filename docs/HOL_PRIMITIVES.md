# HOL Primitive Contracts

## Current Integration Status

The current local checker supports guarded definition admission for add, pred,
sub, mul, beq, ble, pow and shiftLeft. Typed Char/String interfaces, literals and
the quotient dispatch fix are also integrated. The latest combined source
snapshot passes 18 native suites with 1,181,728 assertions in 490.161s, chiefly
UTF-8 boundary checks. Its retained evidence is
`build/reports/hol-extensions-native.json` and `.log`; the rebuilt frontend
passes 67 transport checks. The separate full Arena run now records 86 accepts,
six rejects, two allowed-either outcomes, 122 declines and four missing inputs,
with no wrong verdict or integrity failure on all 216 available files. This is
not complete Arena coverage; internal ten-second timeouts count as declines.

ShiftLeft's contract includes the complete mul/add dependency contracts and
both symbolic equations: `shl x 0 = x` and
`shl x (succ y) = shl (mul 2 x) y`. It preserves the actual admitted body;
no host arithmetic or name-only accelerated reduction is enabled.
Focused factory checks and equation phases pass 47 and 33 assertions, with
repeated positive setup not counted as distinct behavior coverage. The original
unsplit factory attempt timed out at 180s; that failure is retained, not passed.
The independent original shiftLeft checkpoint also records 384 assertions across
eleven bounded phases in `/private/tmp/leanport-hol-shiftleft.NN5w7N/SHIFT_LEFT_HANDOFF.md`.

Three generated general-frontend fixtures pass: a four-declaration admission
gate, a dependent conversion requiring `shiftLeft 1 1 = 2`, and a wrong-result
control that declines without timeout. These are not three extra Arena cases.
Evidence: `build/reports/hol-shift-left-exports.json`, paired with
`hol-extensions-pre-raw-runtime.json`. Permanent commands and phase accounting
are in `tests/hol_primitives/README.md`.

Pow's separate pre-integration checkpoint passes 236 focused assertions across
eight bounded phases plus 63 legacy admission assertions. Its contract carries
the complete mul/add dependency certificates and proves both recurrence
equations in arbitrary symbolic contexts. It preserves the original Definition
body and ordinary delta reduction; it adds no accelerated arithmetic rule.
Source pins, the one incomplete combined phase and all successful split phases
are retained in `/private/tmp/leanport-hol-pow.3mOQ6l/POW_HANDOFF.md`.

Remaining arithmetic primitives and accelerated literal arithmetic are still
under development. The following sections preserve earlier checkpoint evidence;
their historical integration boundaries are not the current status above.

## Boolean Comparison Checkpoint

The first post-projection extension is limited to `Nat.beq` and `Nat.ble`.
Their contracts, body constructors, and additive declaration-factory branches
passed all eight focused phases: 95 assertions per operation, including repeated
setup and exact-statement gates. The original four branches and
public declaration-contract type are unchanged. No parent-owned native module,
frontend, loaded production server, or accelerated reduction rule was changed.

The current private source directory is
`/private/tmp/leanport-hol-natbool.G9UMae/hol/`, captured after the projection and
primitive server reached READY. The initial combined beq test run timed out at
175.011 seconds: 21 assertions completed, including the closed symbolic body
contract and all four equation projections, but the factory did not finish.
`beq-tests.log` is therefore **not a suite pass**. Separate `body`, `factory`,
`bases`, and `diagonal` phases then passed under the same 180-second per-run
limit. A passed negative phase alone does not establish successful admission;
both positive phases on the same source hashes are also required and passed.

| Operation | Phase | Assertions | Elapsed | Log basename |
| --- | --- | ---: | ---: | --- |
| beq | body | 23 | 98.115 s | `beq-body-tests.log` |
| ble | body | 23 | 97.902 s | `ble-body-tests.log` |
| beq | factory | 33 | 127.392 s | `beq-factory-tests.log` |
| ble | factory | 33 | 116.661 s | `ble-factory-tests.log` |
| beq | bases | 19 | 111.031 s | `beq-bases-tests.log` |
| ble | bases | 19 | 110.048 s | `ble-bases-tests.log` |
| beq | diagonal | 20 | 152.555 s | `beq-diagonal-tests.log` |
| ble | diagonal | 20 | 148.584 s | `ble-diagonal-tests.log` |

All logs are under `/private/tmp/leanport-hol-natbool.G9UMae/`. Each final run
exited zero, emitted its operation-and-phase success marker, and was reaped.
Scans of those eight logs found no `Error:`, `Exception:`, `Parse error`,
`Error in included file`, or `RUN_TIMEOUT`. Their unchanged-axioms assertions
also passed. The `all` mode was not rerun after splitting; these are separate
phase results, not a claim that a combined run completed within the deadline.

The unchanged `hol/primitive_admission_tests.ml` also passed all 63 assertions
on this same extended, projection-capable snapshot in 113.925 seconds. Its log
is `/private/tmp/leanport-hol-natbool.G9UMae/original-four-admission-tests.log`.
The final success marker is present, the process exited zero and was reaped,
and the same error scan found no matches. Add/pred/sub/mul factory and consumer
positives, canonical dependencies, replay/hypothesis/forgery guards, exact source
body retention, and symbolic equations are therefore freshly revalidated.
The old 105-body and 64-factory suites were preserved but not rerun in this batch;
neither were the full native suites or Arena. The completed checkpoint is
190 comparison-phase assertions plus 63 original-four admission assertions,
not 253 distinct scenarios. No test processes remain active.

This is the bounded first batch only. Other reserved primitive names still
decline in the HOL declaration factory. Integration into a new parent production
server, including its pending quotient changes, remains parent-owned.

Source identities for the successful comparison phases:

| File | SHA-256 |
| --- | --- |
| primitive_contracts.ml | `0c6be8cb520b2782f6a1fdc603eee59d79ca7b3176185a894a88c86856f2b027` |
| primitive_validation.ml | `c38b22ed18b106145dd1b95dc90d9eb7af2993f9ee36fb836b332566013bcb39` |
| primitive_contract_tests.ml | `1bc8bbb9ae74fd31b3932a861e2495f9e6038275e2777cd5856ec60a84ae4b9d` |
| primitive_admission_tests.ml | `3e2f584d23d74c8939fef0d07d5af85bffda1634b2bb250b43f0a8da39c1ee47` |
| core.ml | `acd440b00fd104ac2d9cb6d6ce9cd14e38c3a6f299b99baa191c960472fd9c0a` |
| environment.ml | `f87ad8b7ebdbf20a6b5e05de6b1814fd5c590fe07162efa125b2fd031a0ed7f0` |
| environment_rules.ml | `f409066bc852c510509ecc8755ba4138cf3f6bfd6372f1a2afee46499fb02cad` |
| syntax.ml | `e2b470d6fe10fbd519cf32069bbcd60b9857d96d692d8e6a7e131ae828148a70` |

The parent subsequently announced a quotient kind and appended native rules.
Those changes are not in this verified snapshot. A source audit found no
primitive helper that exhaustively matches the old declaration-kind datatype:
`check_definition` accepts Definition and returns Unsupported for every other
kind. These files do not index native EValid/edef rules. Canonical protection of
Nat/Bool names remains a native admission obligation. This is a static
compatibility assessment, not a quotient-enabled compilation result.

## Four-Operation Checkpoint

The focused declaration-factory suite passed **64 assertions** in 95.939 seconds;
the guarded-consumer suite passed **63 assertions** in 117.609 seconds. These
runs use the captured native 727/pre-projection sources, with the consumer added
in the second snapshot. All four factory/consumer positives, canonical admitted
dependencies for sub/mul, exact closed certificates, symbolic equations, and
the listed rejection guards passed. Both final success markers are present,
both logs are free of HOL errors, and both processes were reaped. Neither run
reran the old native suites or the 105 body-contract assertions.

Two owned-source corrections were needed, without changing the intended API or
contract formula: annotate `ps : l4_name list` in `l4_prim_definition_header`,
and instantiate `l4_prim_definition_contract` using `REWR_CONV` on the exact
application instead of assuming the inferred theorem binder order with `SPECL`.
The exact-type gates and complete focused suites now pass. Parent-owned native
files were not edited. Later projection datatype changes and full current-tree
integration are **not** covered by these frozen-source results. There is no
arithmetic acceleration in this checkpoint.

## Scope and Source

`hol/primitive_contracts.ml` defines HOL object predicates for the canonical
Nat.add, Nat.pred, Nat.sub, Nat.mul, Nat.beq, and Nat.ble signatures and symbolic defining
equations. `hol/primitive_validation.ml` constructs closed certificates using
only the existing `Lean4hol_env.check` and `Lean4hol_env.convert` proof sources.
The constructor module does not itself admit a declaration, install metadata,
or accelerate evaluation. The parent-owned native consumer now accepts a raw
declaration-contract theorem and retains the original source Definition body.
The tests described below do not modify native environment, rules, or frontend
sources. No primitive acceleration is implemented by this work.

The source is `vendor/lean4lean/Lean4Lean/Primitive.lean`, pinned commit
`8223d223ed98661882e95d9d6a7126df7097cd76`, Apache-2.0, specifically
`checkNatAdd`, `checkNatPred`, `checkNatSub`, and `checkNatMul` (lines 315-354),
plus `checkNatBoolCases`, `checkNatBEq`, and `checkNatBLE` (lines 386-401).
The shared provenance and license record remains `hol/NOTICE`.
The local upstream file SHA-256 is
`0bafbbd0fffd0e56034b205bfacb9985c908d56d3d4cee4379059777d5f83c2e`.

| Contract | Canonical type | Zero equation | Successor equation |
| --- | --- | --- | --- |
| add, body `b` | Nat -> Nat -> Nat | b x 0 = x | b x (succ y) = succ (b x y) |
| pred, body `b` | Nat -> Nat | b 0 = 0 | b (succ x) = x |
| sub, dependency `p` | Nat -> Nat -> Nat | b x 0 = x | b x (succ y) = p (b x y) |
| mul, dependency `a` | Nat -> Nat -> Nat | b x 0 = 0 | b x (succ y) = a (b x y) x |

Here `=` denotes the selected object's typed conversion judgment, not OCaml
equality or a check of finite arithmetic examples. Zero and successor are the
canonical Nat constructors. Sub's contract also contains the entire pred
contract for `p`; mul's contains the entire add contract for `a`.

The comparisons have canonical type `Nat -> Nat -> Bool` and share four
constructor equations:

| Pattern | Nat.beq | Nat.ble |
| --- | --- | --- |
| f 0 0 | true | true |
| f 0 (succ x) | false | true |
| f (succ x) 0 | false | false |
| f (succ x) (succ y) | f x y | f x y |

The shared HOL predicate is `l4_prim_bool_cases_contract J b0s b`. Its beq and
ble specializations fix `b0s` to false and true respectively; each also includes
the candidate's canonical body typing. The dependencies are the native-certified
canonical Nat and Bool blocks, not arithmetic definitions. The tests construct
both through `Env.admit_inductive`; no unchecked environment is supplied.

## Certificate Boundary

The predicates take a judgment parameter
`J : l4_expr list -> l4_expr -> l4_expr -> l4_expr -> bool`, so the contracts
do not depend on declaration admission. The constructor specializes it to
`l4_checked policy entries`, binding both to the exact certified environment.
An add result has conclusion:

```text
|- l4_prim_add_contract (l4_checked policy entries) quoted_body
```

The theorem has no HOL hypotheses and no free HOL variables. Its equations
use symbolic object contexts: `[Nat]` for `x`, and `[Nat;Nat]` for `x,y`,
represented by `BVar 1 = x`, `BVar 0 = y` in the latter context. Consequently
the successor equation is checked at an arbitrary variable, not at several
chosen literals. This is the de Bruijn counterpart of upstream's fresh local
variables. It is not a new theorem identifying the object Nat with HOL `num`,
nor a port of the full Lean4Lean metatheoretic soundness proof.

Every contract includes a body-typing judgment in the empty object context
at the canonical type. Every conversion source is checked for its exact
expected conclusion and empty hypothesis list. Kernel conjunction and
definitional equality rules assemble the result; there are no new axioms,
unchecked theorem constructors, external verdicts, or expected-input cases.

The generic predicates do not assert that an arbitrary supplied `J` has sound
typing rules. That obligation is met by the constructor's fixed native
`l4_checked` specialization and certified environment, not by accepting a
caller-provided relation or theorem. Existing environment axiom policies
remain explicit in the theorem; they are not erased.

## API

`Lean4hol_primitive` exposes distinct abstract certificate types:

```ocaml
check_add : ?fuel:int -> environment -> expr -> (add_certificate, error) result
check_pred : ?fuel:int -> environment -> expr -> (pred_certificate, error) result
check_sub : ?fuel:int -> environment -> pred_certificate -> expr ->
            (sub_certificate, error) result
check_mul : ?fuel:int -> environment -> add_certificate -> expr ->
            (mul_certificate, error) result
check_beq : ?fuel:int -> environment -> expr -> (beq_certificate, error) result
check_ble : ?fuel:int -> environment -> expr -> (ble_certificate, error) result
```

Each kind has `*_body` and `*_theorem` read-only accessors. Candidates are raw
source bodies, not declarations named Nat.add or another protected name.
Native ordinary admission continues to forbid those names, even after a
contract certificate has been constructed. The raw-body API does not take or
authenticate declaration fields; its body-typing certificate alone does not
authorize adding a declaration. The field-based declaration factory below is
intended to authenticate the reserved name, empty universe parameters, closed
universe use, and the exact canonical declared signature required by upstream.
Admission must bind the exact certified body and judgment (or supply a checked
transport theorem). A contract for a substituted candidate must not silently
authorize a different original source body.

For sub/mul, embed the certified dependency body (or use an already admitted
ordinary source definition with its own contract). The checker does not
rewrite source references or inject any declaration into the environment.
Bodies are reused in symbolic contexts only after native typing in the empty
context; dangling object variables cannot become captured dependency parameters.
Dependency certificates must have exactly the same environment and policy.
Replaying across a changed environment, even a valid extension, declines until
an explicit weakening/revalidation path is implemented. Convertible but
syntactically different dependency bodies are allowed when native conversion
proves the exact requested recurrence.

Fuel defaults to 100000 for input validation and each native proof-source call
independently. The original body constructors make three direct calls; beq/ble
make five. Dependency revalidation and the declaration factory add their own
calls. This is bounded proof search, not one shared
aggregate budget or a wall-clock bound on HOL kernel computation. Native error
classes propagate; unsuccessful proof search yields no certificate and is not
proof that a body is mathematically invalid. Environment/policy mismatch is
`Unsupported`. Zero fuel is `Resource`; malformed syntax is `Invalid_input`.

## Declaration Factory and Consumer

The declaration-factory API is:

```ocaml
check_definition : ?fuel:int -> environment -> declaration ->
                   (definition_certificate, error) result
definition_declaration : definition_certificate -> declaration
definition_theorem : definition_certificate -> thm
definition_raw_theorem : definition_certificate -> thm
```

The generic `l4_prim_definition_contract J n ps a b` combines the header,
typing of the exact declared type and body, and the selected operation's
symbolic body contract. Sub and mul use the canonical `Nat.pred` and `Nat.add`
constants respectively, recertified in the current environment. This does not
inject a dependency or substitute a different body for the declaration.
Beq and ble add only their corresponding canonical names/signatures and symbolic
contracts. For an exactly canonical comparison signature, the factory derives
the body-typing obligation from the already checked contract, with an exact
statement guard; other binder spellings use native checking. It does not replace
body typing with a name/type test.

The intended raw certificate is exactly:

```text
|- l4_prim_definition_contract (l4_edef entries) name params type source_body
```

`l4_prim_definition_checked_raw` derives this from the checked judgment using
the native checked-to-raw implication and generic contract monotonicity. The
raw statement deliberately omits the checked policy: the consumer uses the
current environment's existing validity proof, including its policy. This is
not an assertion that the raw judgment alone certifies environment validity.

Parent-owned `Lean4hol_env.admit_primitive ?fuel env d theorem` requires this
exact raw statement with no HOL hypotheses, a Definition with a source body,
and a fresh name. EValid rule clause 6 appends that Definition. The source
continues to delta-reduce normally; the consumer adds no arithmetic reduction
rule. These consumer gates have been inspected and exercised in the captured
source; the focused results and hashes below delimit that verification claim.

## Tests and Integration

`hol/primitive_contract_tests.ml` runs independently of the normal test driver.
It now defaults to the focused declaration-factory tests, without running the
old 105 body assertions first. `HOL_PRIMITIVE_SUITE=body` selects those existing
assertions; `body-projections` additionally selects eight monotonicity checks.
The body suite's positive controls check exact closed statements and extract the
arbitrary-variable equations. Adversarial bodies must first pass native body
typing. Tests cover wrong bases, wrong successor branches, ignored recursive
results, capture/wrong-variable mistakes, poisoned dependency bodies, and
functions that pass zero/one examples but fail the symbolic contract. Additional
tests cover beta/zeta-equivalent bodies, certified ordinary source dependencies,
environment/policy replay, malformed/open bodies, resource exhaustion, protected
name admission, unchanged environments, and unchanged HOL kernel axioms.

The focused factory suite puts add/pred positives first, then name, parameter,
signature, kind and body negatives, missing-environment/dependency checks,
exact statement mismatch checks, resource exhaustion, and benign syntax
variants. The statement mismatch checks are not consumer rejection tests.

`HOL_PRIMITIVE_SUITE=beq` or `ble` selects the new comparison tests, and
`HOL_PRIMITIVE_BOOL_PHASE=body|factory|bases|diagonal` selects a bounded phase.
The default comparison phase `all` remains available but exceeded the current
wall-clock limit in the initial beq run. Phase success markers include both the
operation and phase. The positive phases check closed exact body/factory
contracts, all symbolic conjuncts, guarded admission preserving the original
Definition, and a symbolic diagonal equation after admission. Mutant bodies
must pass native typing before rejection. The diagonal phase also tests a
decoy that passes the finite `0,0` and `1,1` cases but not the symbolic recurrence.
The factory phase includes a separately typed bad-body attack, canonical header
checks, missing dependencies, and certificate replay/mismatch checks.

New `hol/primitive_admission_tests.ml` exercises factory and consumer together:
add/pred first; wrong body/name/params/signature/kind/env, replay, a freshly
recertified duplicate-name attempt, nonempty hypotheses, forged `TRUTH`, checked
instead of raw judgment, and fuel zero; then sub/mul using already admitted
canonical dependencies. Final checks request arbitrary symbolic successor
equations of all four admitted constants and unchanged kernel axioms. Wrong-body
tests first prove the mutant body is well typed. Exact constant-type checks run
before all of these. The 64 factory and 63 admission assertions passed on the
frozen pre-projection checkpoints, not on the subsequently changed shared native
datatype.

The existing driver and native modules are parent-owned and unchanged. For a
private run, copy `hol/` into a temporary working directory and run the original
repository's toolchain wrapper there:

```sh
env HOL_PRIMITIVE_SUITE=factory LINE_EDITOR=env \
  sh '/absolute/repository/scripts/toolchain-exec.sh' hol.sh \
  < hol/primitive_contract_tests.ml > primitive-tests.log 2>&1

env LINE_EDITOR=env sh '/absolute/repository/scripts/toolchain-exec.sh' hol.sh \
  < hol/primitive_admission_tests.ml > primitive-admission-tests.log 2>&1
```

These commands require an external wall-clock supervisor when run under the
current 180-second task bound. Each recorded focused run used a private process group,
a 175-second execution deadline, SIGTERM then at most two seconds before SIGKILL,
and process reaping. A timeout is not a pass; no active parent server is touched.

Require the selected suite's final `HOL_PRIMITIVE_FACTORY_TESTS_PASSED`,
`HOL_PRIMITIVE_ADMISSION_TESTS_PASSED`, or `HOL_PRIMITIVE_CONTRACT_TESTS_PASSED`
marker, respectively, and absence of `Error:`,
`Exception:`, `Parse error`, or `Error in included file`; a zero REPL exit alone
does not establish success.

## Earlier Four-Operation Results

Final successful runs, on 2026-09-29:

| Suite | Assertions | Elapsed | Log |
| --- | ---: | ---: | --- |
| Factory | 64 | 95.939 s | `/private/tmp/leanport-hol-factory-727.DWEIYk/factory-matched-tests.log` |
| Admission | 63 | 117.609 s | `/private/tmp/leanport-hol-primitive-admission.yLIyNU/admission-matched-tests.log` |

Both processes exited zero, were reaped, and emitted their final success marker.
Scans for `Error:`, `Exception:`, `Parse error`, `Error in included file`, and
`RUN_TIMEOUT` found no matches. The admission log also contains all three
intermediate markers: add/pred admitted, guards passed, and all four admitted.

Earlier failed runs are retained for diagnosis, not counted as passes:

| Snapshot | Elapsed | Result |
| --- | ---: | --- |
| `/private/tmp/leanport-hol-factory-727.DWEIYk/` | 52.220 s | Two Nat-environment assertions, then first add factory failed with `mk_comb: types do not agree` |
| `/private/tmp/leanport-hol-primitive-admission.yLIyNU/` | 52.773 s | First exact-HOL-type assertion failed; no factory/admission positives reached |
| `/private/tmp/leanport-hol-factory-727.DWEIYk/` | 66.104 s | With only the type annotation, four assertions passed, then add factory failed at `SPECL` |

Logs are respectively `factory-tests.log`, `admission-tests.log`, and
`factory-monotype-tests.log` in those directories. These REPLs also exited zero
despite exceptions; none timed out, and all were reaped. The first consumer run
printed the actual header type as
`l4_name -> (?146803)list -> l4_expr -> l4_expr -> bool`; the schematic type
variable's numeric identifier is incidental. The current source test requires
`l4_name -> l4_name list -> l4_expr -> l4_expr -> bool` for the existing
monomorphic construction API. With that annotation applied, HOL exposed the
second issue: the definition theorem quantified `ps a n J b`, not the `J n ps
a b` order assumed by the factory. Exact-application rewriting removes that
assumption. These were compatibility failures, not unsound accepted certificates.

SHA-256 identities in that earlier successful consumer snapshot (also matching
the shared owned primitive sources at that earlier handoff):

| File | SHA-256 |
| --- | --- |
| primitive_contracts.ml | `22ad8c57225ab81d7c368a26dc6dcaba9949648a7d8e363dcb69b05505de938d` |
| primitive_validation.ml | `7d36541c8d03aea8062de066cce1115f4022ed89d6851fe7b86c122f8d3218bb` |
| primitive_contract_tests.ml | `9bb121e704793bb9539f4e26743247674bed097645edb53c62f4e44d436e3cd1` |
| primitive_admission_tests.ml | `3e2f584d23d74c8939fef0d07d5af85bffda1634b2bb250b43f0a8da39c1ee47` |
| core.ml | `ebdb5717da301b2d7623790abee40e57aa07274abb5bd361b531b87a059bb1df` |
| environment.ml | `f649b5f59f5c72337750e38eee962d718052515bf604779c5be4f35d8976cde7` |
| environment_rules.ml | `51c283aa8db2f688639f5aed5009b3940b9639f2b40009be0277de8c1b4e697d` |
| syntax.ml | `ee6eba129b3eaeb91a41d56f640589a774f3f95402df7f7cf4c99f2ce86b0849` |

The factory-only snapshot uses the same primitive, core, and syntax sources,
but predates consumer integration: `environment.ml` is
`844e8243da7a9d9d38bdbb60f8b59042e2095f569bb68e34533aa7c8b7b2dd40` and
`environment_rules.ml` is
`bc91e7a6067ba40d08c88b50057d69a6c389559c2e1240cb5322ee7a942fe497`.

## Earlier Body Verification

The refreshed indexed-native private run at
`/private/tmp/leanport-hol-primitive-ready.Rkr4Tq/primitive-tests.log` contains
`HOL_PRIMITIVE_CONTRACT_TESTS_PASSED 105`. It predates the declaration factory and
consumer work and does not validate either. An earlier interrupted extension
run reached 42 existing body assertions but did not reach factory tests; it is
not a pass and is no longer running.

## Historical Combined Snapshot

On 2026-09-29 the combined private run passed all 715 assertions:

| Suite | Assertions |
| --- | ---: |
| Core | 71 |
| Admission | 38 |
| Environment | 95 |
| Inductive | 194 |
| Nat literals | 63 |
| Families | 149 |
| New primitive contracts | 105 |

All seven success markers were present, the process exited zero, and the log
contained no HOL errors. The new tests additionally require both empty theorem
hypotheses and no free HOL variables. The ordinary-source pred and add dependency
paths, all four exact symbolic equations, all typed mutants, policy/environment
replay negatives, and unchanged-axioms checks passed. An earlier standalone
99-assertion pilot also passed; it is superseded by the expanded suite above.

Frozen source directory:
`/private/tmp/leanport-hol-primitives.b5UCju/latest/hol/`.
Combined log:
`/private/tmp/leanport-hol-primitives.b5UCju/latest/full-tests.log`.
Pilot log: `/private/tmp/leanport-hol-primitives.b5UCju/primitive-tests.log`.

The combined run fed `hol/tests.ml`, `hol/nat_literal_tests.ml`,
`hol/family_tests.ml`, and `hol/primitive_contract_tests.ml`, in that order,
to the normal initialized HOL interpreter using the original repository's
`scripts/toolchain-exec.sh`. No shared compiled artifacts were written and no
parent-owned source or build scripts were edited.

SHA-256 identities of the tested sources:

| File | SHA-256 |
| --- | --- |
| primitive_contracts.ml | `f39a1a419ff128e426063a8dd0fd0dea11ce8dedca97c1987edfe7489281c7df` |
| primitive_validation.ml | `c8f335ef87239df0947dfde461ac87beb446769fbdb76950665126def7fb32f3` |
| primitive_contract_tests.ml | `14580eadf3c311dfec9ec16a842865640c6bee369444163a0400c57eb2824b26` |
| core.ml | `e26fdddde4b3f641f7d004e1325d461702fa605c4b4613acdbe238029ab6fd8a` |
| environment.ml | `a8de549af063867d977c2eacd39215a2a33a38d7a93c48aefa5256936549acd0` |
| environment_rules.ml | `3615bbb88c1e991a8050a7be4a2d29f1d50c34dc4bfcae2d5ef430fb076cb340` |
| inductive_model.ml | `80d00ffbf41c27bc570a121b8dc0b7923d19f17d25cd17ef19ebf7610132a04d` |

The parent added indexed-inductive types and changed native recursor handling
after this snapshot. Those changes are not covered by these counts. At the final
hash check, the public `check`/`convert` signatures and native core were unchanged,
but `environment.ml` was
`dd8f7af1f49db1959b2a44c66b3640eece48585c50e755373ceefd63b8505094` and
`environment_rules.ml` was
`bc91e7a6067ba40d08c88b50057d69a6c389559c2e1240cb5322ee7a942fe497`.
These historical counts certify only the bounded contracts and frozen tests
stated here, not the current declaration factory, guarded native primitive
admission, accelerated arithmetic, or full Lean compatibility. Current focused
successes and the remaining current-tree integration boundary are recorded above.
