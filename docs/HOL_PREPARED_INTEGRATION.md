# Repaired-Main Prepared Conditions

## Fresh 29/11 Replay

After indexed-mutual/raw-function/HAdd integration, actual main passes the
focused prepared API replay again, now at 29 native / 11 admission clauses.
All 65 focused assertions and 25 library boundary assertions pass across 13
stages in 438.934556 seconds. The longest stage is 115.678569 seconds; every
stage keeps the existing 180-second limit. The process exits zero, is reaped,
and its process group is absent. Full-log and source-integrity checks pass.

Evidence: `build/reflection-evidence/20260930T212738-focused-965974cc/report.json`,
SHA-256 `4f4b12e6a8d6945437b4c9cbde8c98bbc61729040a9911438e0642d30d012afe`.
This is not a full unified matrix, an Arena outcome, or a default dispatch hook.
The cleanup repair separately passes 23 existing/new synthetic runner controls;
the unified runner passes 15 controls. Their persistent copies are under
`build/reports/continuation-20260930/runner-controls`.

## Earlier 28/10 Integration

The reviewed nine-file payload was initially integrated in main at 28 native /
10 admission clauses. Only `reflected_condition.ml` changes in the production
library; the original `check`, all logical contracts and default dispatch remain
unchanged. The integration verifies all payload before/after hashes and holds
1,808 source/artifact paths, including unrelated Rocq and frontend files.

Fresh main validation passes 17 existing and 15 new synthetic runner tests,
25 fixture-free boundary assertions, and 65 focused canonical Bool assertions
plus the repeated 25 boundary assertions. The focused run completes all 13 stages
in 442.578570 seconds; its longest stage is 117.497002 seconds, below the unchanged
180-second stage cap. The separate smoke takes 51.479315 seconds. Both runs hold
97 exact sources, retain clean complete logs, and reap their process groups.
The independent audit also confirms all 24 synthetic test groups are absent.

Evidence: `build/reports/hol-prepared-main-audit.json` and the reports under
`build/reflection-evidence/20260930T160601-smoke-829bd8c7` and
`build/reflection-evidence/20260930T160740-focused-b115f8fb`.
Main source holds are released after this audit. No new Arena pass, full unified
matrix, default primitive hook or indexed-mutual integration is claimed here.
The fresh actual-main 29/11 replay above supersedes the need to rely on the
separate historical private candidate for these particular focused assertions.

## Reviewed Payload

The candidate started from actual repaired main28/10, including optional
pred proof sources. Only the prepared API and unified payload are imported
from the older successor. Repaired `nat_instantiation.ml`,
`reflection_terms.ml`, core, and logical contracts are not overwritten.
No native/admission rules, axioms, default frontend hooks or Primitive bridge
are added. The original `check` body is unchanged.

## API

```ocaml
val check_prepared :
  ?fuel:int -> ?ite:bool -> ?dite:bool ->
  ?ite_proof:thm -> ?dite_proof:thm ->
  environment -> condition -> thm -> (certificate, error) result
```

The final theorem is a whole checked base contract. Optional arguments are
whole checked capability contracts. Supported supplied proofs must be closed,
hypothesis-free and match the exact source, environment, policy and contract,
even if their flag is false. Raw contracts are derived by the existing
checked-to-raw theorems. The return order is base, requested ITE, requested
DITE. Boolean DITE is always Unsupported, including when supplied a proof:
no claim is made that an unsupported DITE proof passes a supported-contract
guard. A valid Boolean base and supported ITE proof are checked before that
Unsupported branch. Fuel exhaustion remains Resource.

This is an explicit proof consumer, not a changed default dispatcher or an
assertion of identical resource behavior to search. It still validates the
input expression syntax and checks exact closed theorem conclusions. It does
not authorize an environment, grant a policy, or install a primitive.

## Runner

`python3 scripts/test-hol-unified.py` defaults to `focused`.
`python3 scripts/test-hol-unified.py --smoke` runs the fixture-free 25 guard
assertions. The historical full matrix remains explicit `unified` opt-in,
and was NOT run in this task.

The repaired driver keeps its original transcript parser, random completion
nonce, final full-log scan, capture ceiling, process-group cleanup, read-only
execution snapshot and final source-inventory equality. Only UNIFIED marker/
failure recognition and an explicit fixture-load-stage hook are added.
The wrapper's inventory hashes its wrapper and synthetic controls relative
to the supplied root, including when the root is the execution snapshot.

For `unified`, the hook first loads `nat_instantiation_tests.ml` and requires
its readiness marker, then separately loads `unified_tests.ml` and requires
UNIFIED readiness. HOL `needs` caches the dependency; no readiness marker is
ignored to hide the old nesting mismatch. The native full-matrix load path is
not freshly executed here; a focused synthetic three-stage process validates
the exact two generated setup stages plus a UNIFIED work stage.

## Fresh Coverage Boundary

Fresh focused tests use canonical `Syn.bool_condition()` in a genuinely
admitted environment, not a generic substitute. Base and ITE are checked
independently, compared as whole checked/raw contracts, and reused only in
the identical environment and empty policy. All four flag pairs for default
and prepared dispatch are exercised. Successful result bundles are compared
exactly; DITE outcomes must be Unsupported rather than Resource.

Malformed theorem/kind/raw/hypothesis controls, typed changed source,
unbound/malformed syntax, stale empty and newly extended environments,
different-policy environments, missing optional proof, wrong optional proof
with false flag and zero fuel exercise the proof consumer. A policy-only
changed conclusion comparison additionally confirms policy binding without
claiming it is a separately constructible admitted environment. Negative
policy grants are not used for positive capabilities.

The 189 assertions / 82 stages described in `HOL_REFLECTION_UNIFIED.md` remain
historical pre-repair evidence. No new canonical NatEq/NatLE/defn1/defn2
matrix, generic Nat surrogate, full native suite, Arena, Init or Std result
is claimed by this focused validation. The fresh 29/11 result is limited to
the focused replay documented above. Prior private HANDOFF paths may no longer
exist after temporary-directory cleanup; project-local evidence is retained.

Fresh candidate result: existing17 and new15 synthetic tests passed; the
fixture-free25 guard smoke passed in51.750502 seconds. The focused process
passed65 API/fixture/invariant assertions plus a repeated25 guard assertions,
13 stages,390.850515 seconds total. Two distinct canonical positive gates
(Bool base and ITE) and all8 default/prepared flag routes passed their exact
expected outcomes. Maximum stage101.716899 seconds; cap180 unchanged.
Both native processes exited0, were reaped with their groups absent, retained
complete clean logs, and passed before/after/execution-snapshot equality.

Pinned provenance: Lean4Lean `Primitive.lean` commit
`8223d223ed98661882e95d9d6a7126df7097cd76`, Apache-2.0. Existing fixture pins
are unchanged; no hidden test fixture enters the production library closure.
