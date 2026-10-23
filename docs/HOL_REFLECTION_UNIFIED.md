# Historical Unified Reflection Capability Evidence

The 189/82 results below belong only to the sealed, pre-repair
`/private/tmp/hol-reflection-unified-20260930` checkpoint. This document is
retained for provenance, not a fresh pass of this repaired-main candidate.
For the present focused integration scope see `HOL_PREPARED_INTEGRATION.md`.

Private successor of the sealed portable 28/10 payload. No main, default
dispatch, native/admission rule, logical contract, or frontend hook changed.
This run predates the separate `NI.cast/pi/sort` and error-preservation repairs.
It is not fresh evidence for the repaired main or the moving 29/11 model.

## Additive Interface

`Lean4hol_reflected_condition.check` remains byte-identical. New explicit API:

```ocaml
val check_prepared :
  ?fuel:int -> ?ite:bool -> ?dite:bool ->
  ?ite_proof:thm -> ?dite_proof:thm ->
  environment -> condition -> thm -> (certificate, error) result
```

The last argument is a whole checked base contract. Optional arguments are
whole checked ITE/DITE contracts, not host verdicts or unguarded judgment
records. Every supplied theorem for a supported capability must be closed,
hypothesis-free, and exactly match the requested contract, condition source,
environment, and policy. Even an unused supplied optional ITE proof is
validated. For reflected Nat this also applies to optional DITE proofs.
Boolean DITE is always Unsupported, including when a DITE proof is supplied;
it does not pass that proof through a supported-contract guard. Missing requested
capabilities fail closed. Type witnesses are read from the guarded proved
base contract, not trusted native annotations. Raw results are derived through
the unchanged checked-to-raw lemmas. The returned order is base, requested
ITE, requested DITE. Boolean DITE remains Unsupported.

The prepared entry validates the reflected helper syntax as well as its
required contract proofs. It is an explicit proof-consumer interface, not a
claim of identical acceptance/resource behavior to default search. It does
not invoke the Nat composition algebra or add primitive admission hooks.

## One Exact Environment

All original NatLE dependencies were genuinely admitted first, with no policy
grants. The resulting environment and empty policy were frozen before proof
preparation. NatLE, defn1 ITE/NatDITE, defn2 ITE/NatDITE, and Boolean dispatch
were then proved/tested in that same environment in one HOL process. Every
later capability operation verifies the frozen quote still matches. Different
environments/policies are created only for negative controls, never to supply
positive capabilities.

Canonical defn2 satisfied the original branch-selection laws. No law was
weakened or replaced. Branch proofs open syntactically matching binders, use
genuine checked conversion under the exact typed context, then close via the
existing derived lambda rule and require the complete original closed target.
The branches remain symbolic, with arbitrary Type-valued selectors or
Nat-valued proof-dependent functions; no finite numeral surrogate is used.

## Completed Coverage

All five whole checked **and** raw contracts passed:

- Canonical NatLE.
- Canonical defn1 ITE and NatDITE in the NatLE environment.
- Canonical defn2 ITE and NatDITE in the NatLE environment.

Twelve flag routes passed their exact expected outcomes:

| Entry | Flag Pairs `(ite,dite)` | Outcomes |
| --- | --- | --- |
| Prepared NatLE | 00, 10, 01, 11 | All four succeed; exact checked/raw lists compared |
| Default Boolean | 00, 10, 01, 11 | Two successes; both DITE requests Unsupported |
| Prepared Boolean | 00, 10, 01, 11 | Same outcomes; successful lists match default results |

Four poisoned defn2 branch expressions were independently type-checked and
rejected by conversion for non-resource reasons. Further controls cover
typed swapped true/false helpers, typed changed source, missing requested
capability, wrong optional reflection/kind (including flag-false inputs),
hypothesis-bearing and unrelated proofs, stale environment, changed policy,
an isolated different-policy target, and zero fuel. Resource-only failures
cannot count as successful logical negative controls.

## Timing And Scope

One native run, 82 completed stages, 189 counted assertions (75 Nat
preparation/invariant assertions plus 114 unified assertions). No failed or
timed-out attempts. Full process lifetime: **2174.559266 seconds** (36.24
minutes). Longest stage: **164.348955 seconds**, defn1 NatDITE false body.
Each stage had a 180-second cap. These are not <=180-second whole-run claims;
all setup, admission, proof preparation, dispatch, and controls are included.

PID 74270 exited 0 and was reaped. Source inventories match before/after;
the complete log has no HOL error and its stage markers are unique and
ordered. This used the original driver, not the later hardened runner's
nonce, immutable-execution-snapshot, or process-group attestation protocol.

Production changes: only the additive prepared API in
`hol/reflected_condition.ml`. New tests are
`tests/hol_reflection/unified_tests.ml`; the new wrapper is
`scripts/test-hol-unified.py`. All logical contracts, main instantiation
helper, original fixtures, and borrowed algebra remain byte-identical.
Pinned upstream: Lean4Lean `Primitive.lean` at
`8223d223ed98661882e95d9d6a7126df7097cd76`, Apache-2.0.

No default reflected-Nat full-search flag matrix, NatEq base contract in this
unified environment, Primitive integration, full native suite, Arena, Init,
or Std run is claimed. NatEq's earlier separate-environment evidence is not
stitched into this bundle. Repaired-main adoption needs the separate focused
integration checks described in `INTEGRATION_NOTES.md` in the private handoff.
