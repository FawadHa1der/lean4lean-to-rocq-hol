# Main Reducibility-Hint Integration

Completed 2026-09-30. This is actual-main build and validation evidence, not a private candidate binary substituted into main.

This is a documentation copy of the sealed integration checkpoint. Historical
evidence remains in `/private/tmp/rocq-hints-main-integration-20260930`;
subsequent full-Init work has a separate evidence directory.

## Integration

All 55 main source paths matched the exact sealed before-hashes. All 1,056 sealed predecessor artifacts verified before integration and again after validation; none was modified, including the predecessor's failed audit attempt.

The approved 55-path patch was applied with narrowly escalated `apply_patch`. All 55 sealed after-hashes matched immediately afterward. The only subsequent change within those paths was the approved permanent test-fixture default in `scripts/test-hints.sh`.

Two additional approved paths make the tests permanent:

- `scripts/test_rocq_native.py`: registers the two hint suites and includes their fixture in source holds.
- `tests/rocq/hint-policy-controls.json`: exact sealed review fixture bytes; test-only, never passed to the checker. Its prose records the historical review requirements; current executed coverage is given below.

No HOL source, parent-owned documentation, manifest, checker fuel default, hash/cache policy, or Solidity file was edited by this worker. No commit or push occurred. Standard build-generated artifacts were regenerated normally. `HintsRegression.v` needs no explicit build-list edit because the build dependency-sorts every local `.v` file.

Full paths and before/after hashes: [integrated-paths.json](/private/tmp/rocq-hints-main-integration-20260930/integrated-paths.json). Reviewable 57-path source delta: [integrated-source.diff](/private/tmp/rocq-hints-main-integration-20260930/integrated-source.diff). Original conditional preflight: [before-hash-preflight.json](/private/tmp/rocq-hints-main-integration-20260930/before-hash-preflight.json).

## Actual Main Build

`sh scripts/build-rocq.sh` completed successfully in 170.029 seconds under a 900-second bound. No private executable was copied over `build/rocq-check`.

- Wire parser: 31 checks, zero failures.
- Replay transport: 279 checks, zero failures; 2,006 differential assertions in the native driver.
- All 13 existing plus two new native suites passed: 15 suites, 66 bounded steps, stable source hashes, every recorded child reaped.
- New hint suite: 3,217 assertions.
- New callback suite: 14 priority vectors, 22 supported guard requirements, one extra equivalent-universe control. Projection retry and failed-congruence caching are explicitly documented as unimplemented, not passes.

Main native report: `build/reports/rocq-native-20260930T172139Z-23668/report.json`; immutable copy: [main-native-report/report.json](/private/tmp/rocq-hints-main-integration-20260930/main-native-report/report.json).

Actual freshly built runtime, 2,577,296 bytes:

```text
acd3d008970f48ba0fd866dd8977267bedeb19ac057e10761094894d2a60a1db
```

Fresh `rocq/lean_arena.ml`, 631,755 bytes, byte-identical to the approved candidate extraction:

```text
2268a0cd28204f55b9732a5ba45cc866c6e5b1a97e79af0be0d369b84bf5d175
```

## Independent Audit

The audit was deliberately held until the parent confirmed the three HOL modules, four drivers, and registry changes had landed. Then `bash scripts/audit-build.sh` passed in 248.061 seconds under a 600-second bound.

All 75 Rocq modules were independently kernel-rechecked. Sources, objects, and inventories remained unchanged during the audit. All three source/generated-extraction scan reports are empty. The kernel reported no axioms, type-in-type dependencies, unsafe (co)fixpoints, or assumed positivity. No unsafe extraction casts or custom extraction directives were introduced.

Main audit: `toolchain/logs/audit-20260930T172345Z-29601`; immutable copy: [main-audit-report](/private/tmp/rocq-hints-main-integration-20260930/main-audit-report). The frozen Rocq/OCaml sources and objects were also matched to the audit's input hashes.

This is not an overall proof that every checker acceptance is well-typed in Lean. Exact-result refinements target the **new ordinary hint strategy**, not old853 at equal fuel. Existing projection-retry, failure-cache, erasing-heuristic, Nat-order, argument-count-order, and fuel discrepancies remain disclosed in the preserved [implementation handoff](/private/tmp/rocq-hints-main-integration-20260930/validation/hint-candidate-IMPLEMENTATION.md). Regular heights remain exact arbitrary-precision N, an explicit extension beyond upstream UInt32-compatible values.

## One Full Inventory Run

Exactly one full inventory run used an immutable copy of this actual main runtime, fuel 16,384, `--progress 100`, and a 30-second whole-process cap per available case. No selections, skips, reruns, published-budget library attempts, or test outcomes were supplied to the checker. The generic shared runner/classifier was copied unchanged; its process launcher used the unchanged, previously used resource guard.

Manifest: 220 records, SHA-256 `d0ef9bd650fa4256cca4e4256ef45eda096e8ad3505945dad9c41a3f3d063b19`. All 216 available inputs were copied and byte/hash checked: 3,425,364,332 bytes, comprising 193 published-tarball inputs, 20 locally generated exports, and three upstream-static inputs. All four missing-download records were retained.

| Result | Exact Shipped 853 | Integrated Main |
| --- | ---: | ---: |
| Correct accept | 116 | 117 |
| Correct reject | 71 | 71 |
| Acceptable either | 18 | 18 |
| Wall timeout | 11 | 10 |
| Missing download | 4 | 4 |

There were zero wrong verdicts, true native faults, declines, resource stops, skips, missing-generated cases, input/execution errors, integrity failures, or monitor errors. All 141 tutorial cases decided correctly: 94 accepts and 47 rejects. The runner's `complete: false` and exit 1 correctly retain the ten timeouts and four missing cases; they do not mean the inventory loop was unfinished.

The **only** changed classification, raw result, or non-progress diagnostic was `perf/grind-ring-5`: prior wall timeout at 30.005683 seconds, now actual native exit 0 / accept at 28.582600 seconds. No regression was observed. This single-run observation is not a causal timing improvement claim. The prior raw killed-process `verdict: fault` field belongs to a correctly classified `status: timeout`, not a prior logical/native fault.

Ten timeouts remain: `cslib`, `init`, `std`, `perf/fueled-chain`, `perf/magma-list-deep-n21`, `perf/magma-list-deep-n36`, `perf/magma-list-pair-n21`, `perf/magma-list-pair-n7`, `perf/magma-string-n4`, and `perf/magma-string-pair-n9`.

Four missing downloads remain: `cedar`, `con-leche`, `mathlib`, and `navier-stokes-euler`. No downloads were attempted here. Init, Std, and CSLib were full byte-exact inputs, but their **attempts timed out at 30 seconds**; no full-library success or use of the published 500/590/1800-second budgets is claimed.

Full per-case results: [arena report](../build/reports/rocq-shipped-hints-arena-30s.json). Every changed classification and full non-progress diagnostic: [comparison.json](/private/tmp/rocq-hints-main-integration-20260930/validation/comparison.json). Raw-result differences, all changed paths, and aggregate evidence: [summary.json](../build/reports/rocq-shipped-hints-arena-summary.json).

## Holds and Cleanup

The sampled guard applied an 8 GiB aggregate process-group RSS threshold and 64 GiB disk reserve, sampling approximately every 0.25 seconds. This is not an OS-enforced hard memory cap. Maximum observed RSS was 3,248,672 KiB; minimum free disk was 863,234,658,304 bytes. Ten groups were killed at their wall deadline; 206 exited natively. All 216 checker children were reaped; no resource-monitor errors or survivors remained.

The copied GMP dependency was hash-pinned and confirmed in the actual dyld loader output. Host system-library/version evidence is retained separately; system libraries were not copied. All 465 frozen closure files held before/after, including runtime, source/objects, manifest, inputs, runner/guard, and baseline report. The final process audit also covered all 66 native-suite process groups plus build/audit groups.

Evidence: [origins.json](/private/tmp/rocq-hints-main-integration-20260930/validation/origins.json), [holds-after.json](/private/tmp/rocq-hints-main-integration-20260930/validation/holds-after.json), [process-audit.json](/private/tmp/rocq-hints-main-integration-20260930/validation/process-audit.json), and [all-processes-audit.json](/private/tmp/rocq-hints-main-integration-20260930/all-processes-audit.json).

**Main source and runtime holds are released.** No future main hold is required; retained evidence is independently frozen. Parent-owned main changes after these historical holds do not invalidate them. No further checker, full-Arena, Init500, Std, or CSLib run was launched.

## Subsequent Init Attempt

After this integration was sealed, a separate actual-runtime Init500 attempt
completed 9,546 Wire admission records before timing out. It passed the old
shift-left target and last started `Int64.toBitVec_div`; the last batch and
full Init remain unfinished. See [large-input results](ROCQ_LARGE_RUNS.md) and
the separate [sealed attempt](/private/tmp/rocq-hints-init500-20260930/CHECKPOINT.md).
