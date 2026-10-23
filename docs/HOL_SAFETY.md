# Opt-In Safety-Marked Declarations

The integrated `hol/safety_syntax.ml`, `hol/safety_admission.ml`,
`frontend/hol_safety_input.ml` and `frontend/hol_safety_check.ml` implement a
restricted safety-marked definition layer. This is an opt-in API, not a new
default CLI/server path. Existing native/admission rule lists remain 29/11.

## Certificate Scope

Three claims are deliberately separate:

- Raw-fragment typing, exposed by the narrow `fragment_check` helper in
  `hol/environment.ml`. It checks syntax, context, target formation and a typed
  reflexive judgment; it does not authenticate or admit that fragment.
- Validity of the ordinary safe environment, excluding restricted definitions.
- `l4_safety_full` validity of the full marked history, including retained unsafe
  and partial entries, their original bodies, and the explicit object-axiom policy.

The restricted slice distinguishes unsafe single definitions, partial single
definitions and homogeneous mutual blocks. Headers are checked before the
permitted body placeholders are introduced. Safe continuation cannot reference
restricted entries, including through otherwise unused syntax. Freshness checks
cover both the complete raw registry and the canonical safe environment.
The full marked history is not replaced by its safe projection.

Certificates concern decoded syntax with the existing transport erasures, not
the original byte stream. No parser/compiler correctness or Lean-correspondence
theorem is supplied. This slice is not general unsafe-inductive support.

A `Forbidden` result supplies a closed theorem about the exact local forbidden
reference predicate plus an authenticated accepted prefix. It is **not** a
negation of complete-file certificate existence. Other procedural error paths
do not uniformly produce negative certificates. Consequently this API is not
connected to the certificate-only rejection dispatcher under development.

## Actual-Main Validation

Evidence directory:
`build/reports/hol-safety-main-integration-20261001T083152Z`.

- Only the approved eighteen integration targets changed; all target hashes
  and explicit historical preservation checks passed before and after application.
- Twenty-four offline routine/maintenance tests, frontend build and preparation
  passed. Tests allow unrelated maintenance while retaining strict safety guards.
- One native group (`general`) passed twenty assertions in 61.701 seconds,
  within its unchanged 180-second cap.
- The next normal-pressure/free-memory gate declined launch. `single`, `mutual`,
  `references`, `authentication`, `shape`, `atomicity`, `wrappers` and `arena`
  were unattempted in that original execution. Its stop and seal are retained.
- All 1,876 source pins, 96 Rocq source files, runtime and frozen snapshot inputs
  held. Integrity failures were empty; owned processes were reaped and absence
  was checked again at handoff.
- Core `4d22b942...`, the shared 138-job registry and Rocq executable `5f9d5e34...`
  are unchanged. No new full-Arena or public-CLI coverage is claimed.

The prior private loading-repair candidate passed nine native groups and 204
assertions, but that remains separately identified historical evidence. The
eight outstanding actual-main gates are now covered by the separate continuation
below; the original nine-group private run is not relabelled as main evidence.

### Reviewed Continuation

`build/reports/hol-safety-harness-addendum-20261001T101100Z/continuation/replay`
records eight passing groups and 184 assertions: single (28), mutual (32),
references (26), authentication (20), shape (22), atomicity (17), wrappers (22),
and arena (17). Each group completes within the unchanged 180-second HOL limit
including startup; observed times range from 56.526 to 74.332 seconds. All eight
direct children are reaped and read-only PID/group absence checks pass.

The reviewed harness addendum pins a cleanup-only runner overlay; it does not
edit the historical frozen runner or refresh arbitrary source pins. The
eighteen Safety targets, original snapshot, runtime pins and registry remain
unchanged. The earlier general group's twenty assertions are explicitly reused
for the staged gate: this is not a fresh nine-group matrix. No retry occurred
within the continuation, and no group remains unattempted in it.

This completes the staged API integration validation. Default CLI/server
dispatch remains unchanged. The Arena-named focused group is not a complete
221-case Arena replay, and the negative-certificate limitations above remain.

## Test Maintenance

`tests/hol_safety/test_offline.py` and `test_maintenance.py` check the nine safety
jobs, exact limits, loading, authentication, history and fragment-helper contract.
`integration_preservation.py` is a separate explicit one-time audit against the
original whole-file/138-job baseline. Future independently reviewed integrations
may intentionally fail that historical gate; its pins must not be refreshed to
conceal the difference. Fresh native runs still pin their actual sources/runtime.
