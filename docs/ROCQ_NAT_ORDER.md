# Nat-Probe Scheduling

The ordinary and indexed-lookup lazy-delta loops now follow the pinned
Lean4Lean ordering for this slice of `TypeChecker.lazyDeltaReduction`:

1. Preserve the existing quick and Nat-offset comparisons.
2. Attempt the left Nat reduction. A result, rejection or decline is decisive;
   do not evaluate the right probe after left success.
3. Attempt the right probe only when the left returns no reduction.
4. Attempt speculative congruence only when neither side reduces, then retain
   the existing opposite-projection retry and reducibility-hint fallback.

Primitive authentication and fuel limits are unchanged. This deliberately
changes evaluation order, so old/new equality at the same fuel or identical
error ordering is not claimed. The lookup/refinement proofs establish complete
result equality against the **new** ordinary strategy, including rejection and
decline reasons.

`rocq/NatProbeRegression.v` proves the local scheduling laws. The extracted
callback regression exercises nine groups with 1,199 assertions: left/right
priority, errors, ordinary/accessor behavior, authenticated environments,
contexts, collisions and fuel boundaries. A retained old-extraction control
fails the intended ordering-sensitive test.

## Main Validation

The actual main build passes sixteen native suites / 69 bounded steps and an
independent 76-module Rocq kernel audit. Its generated checker source is
byte-identical to the reviewed candidate; the main linked executable has its
own recorded digest. All 216 available Arena inputs are attempted at fuel
16,384 and a 30-second exploratory cap:

- 117 correct accepts, 71 correct rejects and 18 allowed-either outcomes.
- Ten timeouts and four missing exports; no incorrect verdicts.
- All 141 tutorials correctly decided; no changed classifications against the
  preceding main executable.

See `build/reports/rocq-main-nat-order-integration-20261001/validation.json`.
This is not a full Arena pass, a performance-ratio claim, or an overall proof
that acceptance implies Lean typing. A separate full Init attempt at its
published 500-second budget is recorded independently.

## Full Init Regression

The full 347 MB Init input times out at 500.019579 seconds on the actual-main
`efd4d266...` executable, still at fuel 16,384. It completes 3,902 Wire admission
records, down from 7,842 on the preceding projection build and 9,546 on the
earlier hints build. The last started declaration is
`String.utf8EncodeChar_eq_utf8EncodeCharFast`, at input line 325661. It was not
accepted. All 3,903 progress events were retained without truncation.

Input and main/frozen executable digests are unchanged. The progress timestamp
60.969 is process CPU time, not received wall time; it cannot be subtracted
from the timeout to infer an exclusive wall-time stall. This single attempt
does not establish a causal speed ratio, and it collected no continuous RSS
or per-case process journal. The other 219 manifest cases were not attempted
in this separate run. The complete input is not a passing test.

See `build/reports/rocq-main-nat-order-init500-20261001/progress-summary.json`
for the sealed report, original logs and their digests. The next policy slice
must investigate this regression rather than treating unchanged short-budget
Arena verdict counts as evidence of unchanged performance.

The exact 16,868,205-byte ordered prefix through the same theorem reproduces
the problem: the frozen projection build accepts all 3,903 records in 18.509592
seconds, but the Nat-ordering build times out at 180.010640 seconds with 3,902
records completed. Both use fuel 16384 and a 180-second cap. This removes the
full export's suffix heap from that diagnostic; it still does not establish a
controlled causal timing ratio. See
`build/reports/rocq-string-prefix-pair-20261001/CHECKPOINT.md` and its pinned logs.

Upstream free-variable/eager-mode gating, its separate WHNF-loop fuel budget,
and the failed-congruence cache are not implemented by this change. The next
private mode-policy work must preserve these explicit distinctions rather than
silently broadening this checkpoint's claims.
