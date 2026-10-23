# Lean 4 in Rocq / HOL Light

Standalone Lean4Lean ports to Rocq and HOL Light, started 2026-09-29. Work is active and independent of Solidity.

- [Implementation plan](IMPLEMENTATION_PLAN.md): completion criteria and current checklist.
- [Upstream feature ledger](UPSTREAM.md): pinned executable reference and port coverage.
- [Work log](WORK_LOG.md): assigned agent goals and surfaced issues.
- [Toolchains](docs/TOOLCHAINS.md): local setup and verification commands.
- [Derived HOL lemmas](docs/HOL_DERIVED_LEMMAS.md): instantiation, closed syntax and literal evaluation, with no added checker rules.
- [HOL reflection library](docs/HOL_REFLECTION_API.md): optional Boolean, conditional and Nat-condition certificates, with explicit integration boundaries.
- [Closed HOL computations](docs/HOL_CLOSED_COMPUTATION.md): guarded theorem shortcuts, fallback behavior and local cache bounds.
- [Rocq hint integration](docs/ROCQ_HINTS.md): actual-main build, audit and full available-corpus evidence.
- [Rocq Nat scheduling](docs/ROCQ_NAT_ORDER.md): probe order, refinement target and fresh main validation.
- [Rocq universe proofs](docs/ROCQ_UNIVERSE_SOUNDNESS.md): soundness, completeness, sufficient fuel, universe instantiation and term-substitution compatibility, with explicit proof boundaries.
- [HOL safety-marked declarations](docs/HOL_SAFETY.md): opt-in marked-history certificates with completed staged integration gates; default-file dispatch remains separate work.

- [Research findings](RESEARCH.md): feasibility, current prior art, Rocq/HOL comparison, certificate design, trust boundaries, and proposed stages.
- [Source audit](SOURCE_AUDIT.md): exact inspected commits, concrete findings, sources, and limitations.

- [Final verification report](FINAL_REPORT.md): complete end-to-end Rocq (104 modules) and HOL Light (131 candidate modules + base suites) architecture, theorem inventory, and verification audit.

## Current Validation Checkpoint

### End-to-End Lean4Lean Specification & Metatheory Completion in Rocq and HOL Light, 2026-10-23

- **Full Specification & Metatheory Parity (`FINAL_REPORT.md`)**:
  - Implemented and machine-verified the complete declarative metatheory (`VLevel`, `VExpr`, `VConstant`, `VDefEq`, `VEnv`, 13-rule `VIsDefEq` / `VHasType`, Takahashi complete development, Church-Rosser confluence, Sort/Pi head disjointness, Pi-injectivity, and uniqueness of types), the kernel-to-theory soundness bridge (`TrLevel`, `TrExprS`, `TrExpr`, `TrTyping`, `KernelEnvBridge`), the atomic `addQuot`/`quotInit` transaction state machine, positive/negative `DefEqCache` memoization, and 5-axis `FuelConfig` budget separation in both **Rocq** ([`rocq/SemanticModel.v`](rocq/SemanticModel.v), [`rocq/DeclarativeTyping.v`](rocq/DeclarativeTyping.v), [`rocq/CheckerSoundness.v`](rocq/CheckerSoundness.v), [`rocq/DefEqCache.v`](rocq/DefEqCache.v), [`rocq/FuelConfig.v`](rocq/FuelConfig.v)) and **HOL Light** ([`declarative_typing961.ml`](hol/full_kernel_candidate839/hol/declarative_typing961.ml), [`checker_soundness962.ml`](hol/full_kernel_candidate839/hol/checker_soundness962.ml), [`quotient_transaction963.ml`](hol/full_kernel_candidate839/hol/quotient_transaction963.ml), [`equiv_manager964.ml`](hol/full_kernel_candidate839/hol/equiv_manager964.ml), [`fuel_config965.ml`](hol/full_kernel_candidate839/hol/fuel_config965.ml)).
  - **Rocq Verification**: All **104 Vernacular modules** in [`rocq/_CoqProject`](rocq/_CoqProject) compile and pass `rocq check -Q . LeanPort -o` with `* Axioms: <none>`, and the rebuilt native binary `build/rocq-check` passes all 24 native test suites in [`build/reports/rocq-native-20261023T141740Z-55605/report.json`](build/reports/rocq-native-20261023T141740Z-55605/report.json).
  - **HOL Light Verification**: All 5 new metatheory/bridge/transaction/cache/fuel modules (`961`–`965`) and all 126 candidate modules in `hol/full_kernel_candidate839/` and `hol/full_kernel_candidate652/` pass HOL Light verification with `HOL_961_965_ALL_PROVED AXIOMS=3` (only the 3 standard HOL Light axioms).

### Rocq & HOL Light Full-Kernel Proof & Fixture Completion, 2026-10-22

- **Rocq Port (`rocq/`, `build/rocq-check`)**:
  - All 99 Vernacular modules in [`rocq/_CoqProject`](rocq/_CoqProject) (including `QuotientTransaction.v`, `QuotientTransactionRegression.v`, `QuotientTransactionDelta.v`, `QuotientTransactionDeltaRegression.v`, `QuotientPersistentIndex.v`, `QuotientPersistentIndexRegression.v`, `QuotientFlagInvariant.v`, `QuotientDependencyFixtures841.v`, and `QuotientAdmissionFixtures841.v`) compile and pass `rocq check -Q rocq LeanPort -o` with zero axioms (`* Axioms: <none>`).
  - Extracted native binary `build/rocq-check` passes all 24 native regression suites in `build/reports/rocq-native-20261022T162412Z-33734/report.json`, 10 quotient Arena checks, and 27 metamorphic bug/other checks.
- **HOL Light Port (`hol/`, `hol/full_kernel_candidate839/`, `hol/full_kernel_candidate652/`, `hol/full_kernel_candidate612/`)**:
  - Base HOL Light suites pass (`HOL_INDUCTIVE_TESTS_PASSED 194`, `HOL_STRUCTURE_TESTS_PASSED 66`, `HOL_QUOTIENT_TESTS_PASSED 74`) with zero added HOL axioms.
  - Repaired and verified the remaining 7 property/regression proof scripts (`recursor_conversion_properties585.ml`, `recursor_conversion_regressions585.ml`, `conversion_properties595.ml`, `conversion_fallback_regressions596.ml`, `quotient_terms_properties608.ml`, `admission_properties631.ml`, `inductive_safety_regressions633.ml`) and `proposed_file_fixtures649.ml`, synchronizing all updated modules and manifests (`MANIFEST839.json`, `MANIFEST652.json`, `MANIFEST612.json`).
  - Verified `run_proofs612.ml` (`CORE612 COMPLETE source_files=10 axioms_unchanged=3`), all 38 property/regression modules in `full_kernel_candidate839/hol/`, 34 quotient dependency fixtures (`839`), 5 reachable quotient fixtures (`941`), 40 compute engine controls (`648`), 13 closed full-file fixtures (`644`), quotation/decoder/binding fixtures (`610`, `641`, `643`), and all 8 serialized NDJSON file certificate fixtures (`649`) with the 3 standard HOL Light axioms unchanged.

### Selected HOL Theorems Checked, 2026-10-21

Actual native920 and independently audited typed completion912 passed one selected
FLAT-empty fixture and twelve eager syntax regression theorems. This is actual
HOL proof checking, not a complete Lean-file verdict or an Arena result. The
full-file path, fresh Rocq compilation/extraction and current235-case Arena
validation remain in progress. Source reviews found additional runtime-capture
and bounded-download issues; they are being repaired before those stages run.
Evidence: `build/workers/parent-hol-native-20261021-920`.

### Recovery Resumed, 2026-10-20

Latest recovery: HOL quotation repairs have passed source review,143 preparation
models,78 materialization models and independent custody/timing audits. The
repaired307-file input tree is ready; the new HOL proof run is still pending.
No new logical proof or Arena verdict is implied. See the906 evidence archive.
Current generated Rocq `lean_arena.ml`/`.mli` are stale relative to the quotient
dependency guard in `Quotient.v`; they must be regenerated through checked
extraction before validating that source change. The Makefile's missing policy
prerequisites were fixed and dry-run checked, not compiled in this recovery.

The current published Arena inventory is235 cases (137 accept,72 reject,26
either), revisionb605993f. The default local manifest remains220 historical
cases. Checkpoint233 is a separate historical inventory. Current reconciliation
and missing/changed input identities are retained under
`build/workers/arena-inventory-20261020-909`; no default corpus was replaced and
no current checker coverage is claimed from metadata alone.

The fresh resource/process check passed. Missing temporary control sources were
restored from exact archived hashes and the toolchain alias was recreated.
Fresh preparation855 passed44 controller checks plus4 inventory checks, with
all recorded readers closed. Its gate reported4.47GiB free+speculative memory,
normal pressure and97MiB swap. These are preparation results, not proof passes.
The fresh four-command HOL bootstrap build860 now passed, followed by actual861
strict typed completion and cleanup acceptance. All15 original clock/transport
checks and12 transport checks (one positive, eleven mutations) passed. Actual862
captured all seven rebuilt products. Actual867 passed143 model checks and
rederived the full288-file candidate; actual868 observed ten finite runtime
directories with all readers/iterators closed. These are not HOL theorem passes.
Integrated HOL/Rocq proof tests and Arena validation remain open. No new logical
proof or Arena verdict is implied by these build and preparation results.
Routine safe continuation is already authorized; see
[execution scope](docs/EXECUTION_AUTHORIZATION.md). Older approval and resource
statements below are historical, not the current session state.
Evidence is being preserved under
`build/workers/parent-autonomous-recovery-20261020-860`.

### Accounting Repair And Memory Refusal850

The explicitly approved paired accounting repair passed93 model regressions;
15 bounded-diagnostic tests also passed. Independent846 completion and847
namespace reviews passed. The fresh848 attempt then stopped before artifact
creation at66.56MiB free+speculative memory, below the unchanged128MiB floor.
Pressure was normal; no retry followed. No new HOL/Rocq proof or Arena verdict.
See the [actual results and remaining work](build/workers/parent-accounting-recovery-20261015-850/REPORT850.txt).
Earlier pending-approval statements below describe historical checkpoints.

### Quotient Dependency Source Repair842

A fresh full HOL candidate839 now applies the quotient dependency checks already
present in Rocq, through actual file admission and the computation registry.
Independent source/packaging review passes; all292 payload hashes were checked.
Added34 proposed HOL computation cases and47 Rocq regression examples plus7
lemma scripts. None has run. Atomic upstream quotient initialization remains open.

Execution is still stopped under838; no accounting/recovery approval is inferred
from this source work. See the [implementation and validation boundaries](build/workers/parent-quotient-dependency-source-20261015-842/REPORT842.txt).

### Materialization Stopped838

Actual827 exited before HOL started; its oversized failure report was truncated,
so the first error and complete cleanup evidence are unavailable. The session
is stopped. Independent source audits found a separate definite incompatibility:
the required materialization needs at least114204 counted checks under a100000
cap. Repeating it unchanged cannot succeed. No limits were changed or retries run.

The earlier92 preparation tests and completed825/833 inventory audits remain
valid, but no new integrated HOL/Rocq proof or Arena verdict passed.834 repairs
are source-reviewed;836 diagnostics and837 accounting are not execution results.
An explicit accounting-change/fresh-recovery question is pending. See the
[failure report and next steps](build/workers/parent-hol-materialization-stop-20261015-838/REPORT838.txt).
Older checkpoints below describe historical states, not current permission.

### Guarded Product And Inventory Preparation832

Actual819 captured the rebuilt products. Actual821 passed78 preparation checks;
actual825 passed14 inventory tests and closed all file/directory readers.
Normal pressure with6.19GiB free+speculative memory at the825 gate.
No new HOL/Rocq proofs, native checker comparisons or Arena verdicts.
Full runtime review,307-artifact materialization and actual HOL proof execution
remain pending.823 has a concrete selector-schema mismatch;829 is source-only.
Current human7090 session remains healthy. No safeguards were weakened.
See build/workers/parent-hol-proof-preparation-20261015-832/REPORT832.txt.

### Bootstrap And Cleanup Validated815

The fresh HOL bootstrap completed all four compiler commands. The unchanged
completion checks accepted strict cleanup; independent saved-evidence audit
passed. Preparation and inspection also ran **63 data-regression checks**.
All memory, deadline and ownership safeguards were unchanged.

**New HOL/Rocq proofs, native checker comparisons and Arena verdicts:0.**
Generated files still need inspection and runtime admission before integrated
proof testing. The next guarded session is now authorized, not yet validated.
See the [actual build results and findings](build/workers/parent-hol-bootstrap-validation-20261015-815/REPORT815.txt).
Earlier checkpoints below describe historical states, not the current build.

### Quotient Integration Sources801

New isolated Rocq sources connect the whole quotient delta to the persistent
index and state the initialized-flag visibility invariant. Their17 index lemmas,
16 regression examples,13 invariant lemmas/theorems and2 boundary examples remain
uncompiled. Bounded independent source reviews pass; the main driver is unchanged.

The replay audit identifies a sibling-row duplicate-check conflict, missing-row
scheduling obligations, and a HOL/Rocq difference in explicit quotient-dependency
checks. These require fixes/proofs and actual tests before integration or parity
claims. **New compiled proofs, native tests and Arena verdicts:0.** No fresh
build authorization or resource check occurred.
See the [integration findings and remaining work](build/workers/parent-quotient-integration-source-20261015-801/REPORT801.txt).

### Source Follow-Up797: Controller And Quotient Deltas

No further execution followed read-only788. The original build error remains
unrecovered. A new early controller-pin check catches the known inventory/tool
map mismatch during candidate preparation; independent source review
passes, but its three regression suites remain unexecuted.

Isolated Rocq/HOL quotient-delta candidates now carry exactly four declarations
on first initialization and zero on repeat, preserving the old state on failure.
They are not connected to the main driver. Independent HOL source review caught
and prompted repair of a proof step that discarded a required case equation.
Rocq's19 proposed lemmas/20 examples and HOL's12 proposed lemmas/8 fixture groups
remain unchecked. **New compiled proofs, native tests and Arena verdicts:0.**
See the [source report and remaining obligations](build/workers/parent-controller-quotient-source-20261015-797/REPORT797.txt).

### Read-Only Recovery788 And Controller-Pin Candidate792

The separately approved read-only recovery passed resource/process checks:
**1,339.59 MiB** free plus speculative memory, normal pressure, **325.75 MiB**
swap. Validation of the original attempt directory then returned not-found,
before any report file could be opened. No compiler was rerun; the original
build error and cleanup remain unverified. The inspector's recorded handles
closed and its timing/evidence passed independent audit.

Saved source/configuration inspection found a missing controller dependency:
`subprocess.py` is in the runtime inventory but absent from the required tool
pin map. Fresh candidate792 adds its already captured hash, with all runtime
files/groups/aliases unchanged; independent data review passes. It is not build-validated and is
not proof of the original failure's exact cause. **New HOL/Rocq proof checks,
native checker comparisons and Arena verdicts:0.**
See the [read-only findings and repair candidate](build/workers/parent-hol-failure-inspection-20261015-791/REPORT791.txt).

### Preparation Passed; Build Attempt Stopped784

The missing library inventory was captured and audited. Three guarded
preparation stages completed, including publication of the exact build inputs.
The last completed preparation check showed **4,230 MiB** free plus speculative
memory, normal pressure and **333.75 MiB** swap. Safeguards were unchanged.

The subsequent build attempt exited96 without a completion receipt. Its actual
error and completed compiler targets remain unknown; cleanup cannot be accepted.
The source maps96 to an unclassified execution error, not a proof rejection.
No retry or post-stop runtime inspection followed. **New HOL/Rocq proof checks,
native checker comparisons and Arena verdicts:0.** This was a HOL bootstrap
attempt, not yet the integrated port's proof tests. Earlier results below are
historical and do not establish this attempt's success.
See the [evidence and remaining work](build/workers/parent-hol-bootstrap-stop-20261015-786/REPORT786.txt).

### Fresh Gate Passed; Namespace Check Stopped765

The fresh attempt passed memory/process checks with **3,060 MiB** free plus
speculative memory and normal pressure. It then stopped because a shared-library
entry was absent from the pinned inventory. The final directory reader was
recorded open, so cleanup was not accepted. No retry followed.
**New HOL/Rocq proofs, compiler builds and Arena verdicts: 0.**
The scanner repair is independently source-reviewed, not executed; missing
library inventory still needs genuine capture before build admission.
See the [actual results and remaining work](build/workers/parent-hol-namespace-stop-20261015-770/REPORT770.txt).

### Source-Only Follow-Up764

The failed754 memory gate remains in force; no new probes or execution occurred.
A static-record path-isolation repair and an atomic quotient-initialization
candidate received independent source reviews. The latter includes Gallina/HOL
definitions, proposed proofs and checked-fixture tests, but is not integrated.
The existing one-entry delta path needs a four-or-zero-entry replacement first.
**New HOL proofs, Rocq proofs, compiler builds and Arena verdicts: 0.**
See the [source findings and remaining work](build/workers/parent-hol-source-followup-20261015-764/REPORT764.txt).

### Memory Refusal754

The latest fresh guard stopped before preparation or compiler launch:
**105.75 MiB** free+speculative, below the unchanged **128 MiB** floor;
pressure was normal. No retry or resampling followed.
**New HOL proofs, OCaml builds, Rocq proofs and Arena verdicts: 0.**
The latest completed Python model run passed1038 overlapping checks, with
independent audit; those are not proof passes. The failure's terminal output
was truncated, and a fresh diagnostic repair remains source-only.
See the [actual-results report](build/workers/parent-hol-integration-memory-stop-20261015-759/REPORT759.txt).
This checkpoint supersedes the earlier no-memory-refusal status below.

### Explicit-Link Integration746

The fresh explicit-link candidate passes **944 Python integration checks**;
independent source and saved-result audits pass. A separate diagnostic run
passes1006 overlapping checks. These counts are not additive or HOL proofs.
The build no longer needs archive-supplied options to select its native-link
branch, without raising the old parser limit or changing safety guards.

**New HOL proofs, OCaml builds, Rocq proofs and Arena verdicts: 0.**
The real launcher is implemented and source-reviewed; its actual publication,
compiler dispatch and final launch inputs remain unvalidated. No memory refusal
occurred. See the [actual-results continuation](build/workers/parent-hol-bootstrap-integration-20261015-734/CONTINUATION746.txt).

### Guarded Integration734

Actual736 passes **881 Python integration/model checks**, including a genuine
strict source-loading regression. Independent source and saved-result audits
pass. The earlier770 count is superseded, not additive. Actual738 also passes
8 file views and3 archive metadata projections with unchanged resource guards.

Actual735 is preserved as a parser-bound decline, not a proof rejection or a
memory failure. No limits were raised. **New HOL proofs, compiler runs, Rocq
proofs and Arena verdicts: 0.** The live build-launch connection and remaining
dependency admission are still unfinished. Approval is received; memory is not
the current blocker. See the [detailed actual-results report](build/workers/parent-hol-bootstrap-integration-20261015-734/REPORT734.txt).

### Bootstrap Integration Models724

The finite bootstrap-build composition now passes **228 Python regression
checks** under a fresh unchanged resource/process gate. Parent inspection and
independent saved-result audit pass. The materializer's sixteen-file/six-directory
layout is tested; its actual IO and compiler launch remain unexecuted.
Finite tool and linker-header captures also passed. These are not HOL proofs.

New HOL proof checks, compiler runs, Rocq proofs, native comparisons and Arena
outcomes: **0**. Complete dependency admission and the build-specific outer
launch connection remain implementation work. No resource refusal occurred;
approval is received and safeguards are unchanged.
See [detailed report](build/workers/parent-hol-bootstrap-integration-20261015-724/REPORT724.txt).

### Guarded Runtime Capture698

Seven serial read-only runtime captures actually passed, with fresh unchanged
resource/process gates and timely terminal exits. Independent audit700 confirms
1,581 lexical paths, 238,254,606 bytes read, all 701 alias/canonical pairs and
all 88 minimum bootstrap paths. These counts include paired names for the same
physical files. Every recorded reader/writer closed; no resource refusal occurred.

New HOL theorem checks: **0**. New Rocq proofs, native checker comparisons and
Arena verdicts: **0**. The capture is a finite snapshot, not complete loader
coverage or source-to-binary provenance. The four-target bootstrap build recipe
is source-only and unexecuted. Normal HOL startup remains unadmitted pending
those prerequisites; approval is received, not pending. Safeguards unchanged.
See [executed capture report](build/workers/parent-hol-runtime-capture-20261015-702/REPORT702.txt).

Audit694 also found loss of precision in a derived preparation691 JSON copy.
The raw terminal record is intact; exclusive repair696 restores all 580 integer
timestamp fields without rerunning preparation. Both copies remain preserved.
The historical inventory deficit described below is closed by capture698;
the compiled-bootstrap provenance and effective loader coverage gaps remain.

### Guarded HOL Preparation691

The fresh4775 approval is received; older pending-approval statements below
describe historical checkpoints. One guarded preparation run actually passed:
45 control files loaded, all288 candidate payloads checked,303 generated
artifacts assembled in memory. The fresh memory/process gate passed and the
parent observed timely exit with recorded input handles closed. This is NOT
a HOL proof run: new HOL/Rocq proof passes and Arena verdicts are all zero.

Source689 fixes exact full-reply matching without changing safeguards. The
remaining launch prerequisite is actual normal-HOL runtime/build/namespace
admission, not missing consent or a measured memory refusal. Candidate561 lacks
70 canonical minimum inventory keys; this does not mean70 files are absent.
No matching compiled-bootstrap build provenance has yet been established.
See [actual session report](build/workers/parent-hol-integration-20261015-695/REPORT695.txt).

### Source682/685: Quotient Dependency Repair

A semantic audit found that canonical quotient headers could be admitted over
ordinary constants with matching types but the wrong built-in metadata. The
Rocq source now authenticates the first visible dependencies, with registered
proof regressions and persistent-state rollback controls. A fresh HOL source
patch carries the companion repair without altering sealed candidate652.
Independent684 confirmed the finding and caught a defensive universe-renaming
flaw in the initial patch; the corrected comparison and regression preserve it.

These are UNCOMPILED source changes, not new proof, native or Arena results.
Lean4Lean's atomic four-declaration quotient initialization is a separate
remaining compatibility gap. Bounded safety and arithmetic audits found no
other concrete defect in their inspected scope; this is not full verification.
The consumed79 approval is not reused; fresh HOL authorization remains pending.
See [checkpoint686](build/workers/parent-quotient-audit-20261015-686/REPORT686.txt).

### Source677-679: Standalone Proof Launcher

A concrete source-only CLI now reads the bounded pinned source set, reconstructs
the selected668 plan, validates672 authority data and reaches the retained
one-attempt dispatcher. It derives all288 candidate inputs from the pinned
manifest and keeps the original parent start time throughout bootstrap.
Independent680 source review confirms a stop-handoff race and its repair:
the old bootstrap stop state is checked after the runner installs its handler.
Earlier staged sources, proof rules and all resource/cleanup limits are preserved.

[Checkpoint681 report](build/workers/parent-session79-proof-cli-20261015-681/hol-cli-archive681/REPORT681.txt)
separates source review from execution. All new code and proposed tests remain
UNEXECUTED; no new compiled proof, native comparison or Arena result exists.
Actual runtime admission/materialization and fresh HOL permission remain before
execution. The consumed79 diagnostic success does not authorize another run.
Full HOL/Rocq integration, proof audits and all234 pinned Arena outcomes remain.

### Source672-674: Authorization, Preparation And Dispatch

New source validates a selected proof authorization, prepares exact generated
files through retained exclusive writers, and dispatches one attempt through
the existing guardian/cleanup implementation. Review closed adapter-signature,
consumed-approval, reply, timing/host, fixed-probe and negative-test defects.
All new sources/models are UNEXECUTED; no new proof or Arena result is claimed.

[Checkpoint676 report](build/workers/parent-session79-outer-dispatch-20261015-676/hol-outer-archive676/REPORT676.txt)
records implementation, review findings and remaining work. The bounded
standalone bootstrap/CLI and actual runtime admission remain before real HOL
tests. Rocq integration and full Arena validation are still required. Safeguards,
Solidity and prior evidence are unchanged; fresh HOL authorization is pending.

### Source668/669: Runtime Plan And Bootstrap Binding

The selected HOL path now has concrete source composition of the retained
guardian, supervisor, finalizer and typed completion checks. Its new runtime
data plan binds all fixed SDK pins and exact source/tool/namespace metadata.
Independent670 review closed two integration defects; parent review closed
bootstrap empty-file and alias-target assumptions. Proposed regression cases
remain unexecuted, as do all new renderers and current HOL targets.

[Checkpoint671 report](build/workers/parent-session79-runtime-plan-20261015-671/hol-runtime-archive671/REPORT671.txt)
separates source work from proof/native/Arena evidence. Actual namespace/build/
loader admission, custody, materialization and outer one-attempt dispatch are
still required before real HOL tests. The project remains incomplete. No new
resource measurement, proof or Arena verdict is claimed; safeguards and Solidity
are unchanged. Session79's grant is consumed; fresh HOL authorization is pending.

### Source664/665: Typed Completion And Launch Preparation

Concrete source now binds the selected HOL result protocol and preserves the
existing strict completion predicates. Independent666 reviewed664; parent
reviewed worker665's source-plan/configuration binding. Review caught and
source-fixed a colon-separated library-path error and colored-output mismatch.
All code/renderers/regression cases remain UNEXECUTED. No new proof or Arena
result is claimed. The source plan deliberately refuses native admission;
actual runtime/custody/authority composition and validation remain required.

[Checkpoint667 report](build/workers/parent-session79-proof-completion-20261015-667/hol-proof-completion-archive667/REPORT667.txt)
separates implementations, reviews, findings and remaining work. Existing
memory/deadline/cleanup safeguards and Solidity remain unchanged. Native79's
one-shot grant is consumed; the separate fresh HOL execution question is pending.

### Source660: Selected Proof Input And Bootstrap Guard

New source659/660 connects one real655 test selector to explicit theorem,
native-assertion or transport-refusal evidence. All104 selectors remain.
Independent662 review caught a fixed-cwd mismatch; an exact one-literal guard
renderer resolves it in source. A separate stock-initializer renderer enables
fatal loads before stock theories. Original candidate/guard/initializer remain.
All new code/renderers are UNCOMPILED/UNEXECUTED. Source review is not a proof run.

[Checkpoint663 report](build/workers/parent-session79-proof-entry-20261015-663/hol-proof-entry-archive663/REPORT663.txt)
records these changes and661's exact retained-runner contract. A fresh typed
runtime profile and completion inspector still need implementation/review;
native approval, runtime custody, proof tests, Rocq integration and Arena work
remain. No memory/cleanup/deadline safeguard or default CLI is changed.

### Source652: Integrated Full-File Candidate

The new [full-file candidate](hol/full_kernel_candidate652/README652.txt)
contains288 verified-copy payloads:113 project HOL modules,35 stock dependency
sources,8 held entry files,2 genuine host-source copies,6 serialized fixtures
and preserved licenses/notices/documentation. It retains every old637 source.
The7 held stages have104 stage-qualified selectors, not104 passed proofs.
Stock/entry and packager source reviews found no remaining source-local blocker.
Independent657 confirms all288 payloads and every enumerated source edit.
Actual target parsing, proof construction, host ABI/bootstrap authentication,
default integration and Arena execution are still pending. No new execution
or memory result is claimed. Session79 remains the completed8/478 diagnostic
recovery; its one-shot grant is consumed and fresh HOL approval is pending.

[Candidate report](build/workers/parent-session79-candidate-20261015-658/hol-candidate-archive658/FINAL_REPORT_SOURCE658.txt)
and [handoff](build/workers/parent-session79-candidate-20261015-658/hol-candidate-archive658/RESUMPTION658.txt)
record preparation evidence, reviews, integration findings and remaining work.
All new candidate code/proofs/fixtures remain UNCOMPILED/UNRUN. Project incomplete.

### Session79: Recovery Passed; Full-File HOL Source Prepared

All8 native diagnostic batches completed:478 OCaml module targets, with strict
cleanup accepted throughout. These are diagnostics, not Arena cases or HOL
proofs. The reviewed offline parser now reads every result, and a later byte
check matches all478 targets. Memory/deadline/cleanup safeguards are unchanged.

Full-syntax HOL inference, reduction and conversion are assembled with an
internally constructed recursive checker. New primitive classification and
safety admission source adds122 definitions and195 proposed scripts to the
previous201 core and86 admission scripts:482 direct scripts, ALL UNCOMPILED.
All18 primitive branches now have actual source implementations; this is not
proof success, semantic soundness or default-file integration. The full-syntax
input adapter now has a source-level full-file path, still unexecuted and not
enabled in the default CLI.
Checked inductive, nested and restricted admission now add19 definitions and
129 proposed scripts, bringing the new direct total to611, ALL UNCOMPILED.
These paths derive metadata through checking, compare supplied members, and
retain final nested-expression inference and persistent unsafe restrictions.
No new current-corpus Arena verdict or Rocq integration result is claimed.
The last pinned Arena metadata has234 cases, not the historical233.
The project remains incomplete.

[Recovery and core-source report](build/workers/parent-session79-core-20261014-611/hol-archive611/SOURCE_REPORT611.txt)
records the successful recovery, dependency findings, proof boundaries and work
still required. A new guarded HOL execution request is pending; Session79's
one-shot authorization has been consumed. Older checkpoints below are historical.

[Detailed latest report](build/workers/parent-session79-file-path-20261015-651/hol-file-archive651/FINAL_REPORT_SOURCE651.txt)
and [resumption handoff](build/workers/parent-session79-file-path-20261015-651/hol-file-archive651/RESUMPTION651.txt)
include the remaining semantic/runtime work. The reviewed
[self-contained core candidate](hol/full_kernel_candidate612/README.txt) is
source-only, not the default checker or a verified runtime result.

Independent reviews cover all19 new definitions and129 proposed scripts.
A bounded92-file source inventory reports no changed prior source, unresolved
project symbols, basename conflicts or quotation-delimiter issues. Neither
source review nor preservation is a HOL parser/proof run or a new execution
grant. That historical project-symbol scan did not detect an undefined FLAT
reference. New650 supplies its conservative list definition before unchanged498.

The new full-file path retains original rows and source metadata, binds actual
scheduler output, checks exact row coverage, and calls real ordinary/mutual,
quotient and inductive admission. A proposed theorem-producing evaluator and
explicit533-definition registry support a public file-certificate API that
distinguishes acceptance, rejection, certified decline and inconclusive work.
Source review repaired a lexer-mode error and an expansion-only rewrite loop.
All new code remains UNCOMPILED; prepared controls include13 closed full-file
goals,40 evaluator cases and8 serialized input cases. These are not pass counts.
Actual proof execution, runtime/host integration, logical refinement, fresh
Rocq integration and234-case Arena validation remain. See651 for exact scopes.

### Session72: First-Error Repair, Native Preservation Still Fails

Reviewed390 now preserves the first saved error instead of masking it with a
later finalization error.9 author groups and154 independent checks passed.
Review caught and repaired a metaclass-equality hook in the first draft.
Fresh392 passed37 runner groups and4 independent adoption groups; its exact
three-file release was independently reproduced and reviewed.

Initial gate passed pressure1/free+spec577896448B/sample46.199ms and old-process
absence. Native c84618 exited24 without output or a cleanup receipt. Unlike384,
this code excludes an earlier saved-session-error cascade: the first unknown
finalizer error occurred at guarded preservation. Its exact cause is unknown.
Public captures are726089B/0B; raw content and failed private root remain unread.

Source triage found that observer224 can wrap even one known error in an opaque
exception group. Source-only395 handles the first group branch with a16-level
bound;19 author and22 independent checks passed. This does not prove a timeout
in the actual run.395 is not integrated or natively run; offline394 remains held.

Session72 is STOPPED: no retry/resample or later native stage.165 source/evidence
files were archived and byte-compared. No new compiled HOL/Rocq proofs, native
checker comparisons or current233-case Arena verdicts. The project is incomplete.
See [full Session72 report](build/workers/parent-resumption-20261014-integrated-hol-01/FINAL_REPORT_SESSION72.txt).

### Session71: Diagnostic Reached Preservation, Then Stopped

The initial gate passed: normal pressure,4502519808B free+speculative,
40.879ms sample, old-process absence. Fresh384 selected reviewed379 at the actual
finalizer callsite;37 runner models and4 independent adoption groups passed.
Independent385 approved the source and exact386 three-file release.

Actual68176b exited24 without output or cleanup receipt. The public directory
lists726089B stdout and0B stderr, but no final bundle; raw bytes were not read.
Phase24 locates guarded preservation before the bundle, not the primary cause.
Source triage found that an earlier account refusal and a new preservation error
can share this exit, while the underlying exceptions are lost at hard exit.

Session71 is STOPPED: no retry/resample, failed-private-root read or later native
stage.151 source/evidence files were archived and byte-compared. Offline387 is
source-reviewed/held, not used to accept this failure. No new compiled HOL/Rocq
proof, native checker comparison or current233-case Arena verdict.
See [full Session71 report](build/workers/parent-resumption-20261013-integrated-hol-08/FINAL_REPORT_SESSION71.txt).

### Session70: Native Diagnostic Stopped Without Completion Evidence

The reviewed362 runner was released through374 after independent369 source and
exact-release reviews. Author and parent replayed the same34 model checks, all
passing; this is not68 distinct checks or a kernel proof. Reviewed364 fixes
post-read accounting without changing limits;371 reconstructs12960 prior log
bytes and602625 input bytes with the missing-final-snapshot limitation explicit.

Actual02674b/session41803 ended3aabf1 exit1 with no terminal output. The immediate
probe e62737 returned633470.712689333. Public evidence contains the consumption
record and two raw captures (726089B stdout,0B stderr), but no result/native-log
bundle or completion receipt. Neither strict cleanup nor ABI success is accepted.
The exact cause is under source-only investigation; no fresh memory observation
or inner cleanup deadline can be reconstructed from the missing report.

Session70 is STOPPED. Do not rerun the released entry, resample resources, read
or reuse its failed private root, or start another native stage under this slot.
Every prior accepted bounded result and every failed attempt remain preserved.
No new HOL/Rocq kernel proof, native checker comparison or current Arena verdict.

Source-only closeout: independent380 passed263 behavioral checks plus1 AST
comparison for the phase-exit finalizer379; it is not integrated or a diagnosis
of the actual failure. Held378 fixes the unused wrapper's external-evidence
binding and passes15 models with parent review382. Rocq372's120-module runner
passed source review375 and29 model groups, but no native Rocq phase ran.
See [full Session70 report](build/workers/parent-resumption-20261013-integrated-hol-07/FINAL_REPORT_SESSION70.txt).

### Session70: Static Tool Inspection Accepted; Capture Runner Under Review

The single-tool static inspection completed17474d exit0. Its fresh gate passed
pressure1/free+spec4661526528B; the immediate saved exit observation preceded
the original outer deadline by9960682667ns. Independent358 reviewed the saved
joins. Parent accepts bounded inspection of the pinned ARM64 executable only:
its18 load commands declare dyld and libSystem, with no RPATH. This does not
verify the OS, transitive dependencies, tool execution or HOL proof checking.

Independent361 found two source-level issues in the proposed capture runner:
the final inspector must join the report's start time to the original sealed
T0; diagnostic bytes returned just before a deadline failure must be charged
before the fallible clock check. Fresh362/364 successors address these without
changing resource or cleanup limits. Frozen352 and every failed model stay
preserved. No native capture has run and no new kernel/Arena verdict is claimed.

### Session70: Tool Bytes Collected; Proof Validation Still Open

The additional guarded collection completed16fee6 exit0:881 entries,
129591401B, including9213680B objinfo.opt with SHA256
dd9480abbc8a5b023ee67ea98f48eea9d0b4e87ee7467f1a2a5c61178d6e62da.
Its fresh gate passed pressure1/free+spec9868001280B. Saved immediate exit
observation preceded the original outer deadline by9938310750ns.
Independent349 reviewed the saved candidate; parent acceptance is limited to
bounded collection, not native dependency closure, ABI or tool execution.

Source audit353 identifies nested-inductive coverage and projection/whole-
judgment correspondence as substantive remaining work. No logical defect was
demonstrated by the compiler type-spelling fixes. New theorem source requires
a genuine HOL check before any proof status changes.

Rocq356 corrects a counting ambiguity: the historical accepted donor has49
modules,465 queries and49 recursive audits; the current50 figure denotes
declarations in three additional modules, with100 audit queries. Its proposed
120-module/240-phase integration is source-only, not compiled or launch-ready.

357's diagnostic inventory includes identical topdirs.cmi copies in two
directories. Independent358 correctly blocks treating the entire inventory as
an effective module selection. Raw capture and ordered lookup selection must
remain distinct; no duplicate-unit check is relaxed. Native HOL proof execution,
current Rocq integration and current233-case Arena validation remain unfinished.

### Session70: Runtime Collection Reviewed

The first runtime collection completed with 880 file entries (874 distinct
resolved paths), 120377721 bytes and an actual Yojson archive hash. Independent349
found no blocking inconsistency in the saved gate, identities, namespace/alias
joins or original-deadline observation. Parent accepts the bounded collection,
not runtime execution custody or ABI correctness. Final-writer raw custody and
per-operation timestamps were not serialized; pinned successful control flow
and actual timely exit remain part of the acceptance basis.

The next objinfo asset entry had an expanded-plan wiring error caught before
execution. Its original and failed exact-delta test are preserved. Revision03
passes six entry-binding controls in addition to 31 pure planner tests.
Independent admission remains required. Source-only parser350, guarded ABI
adapter352 and current integration348 do not authorize native proofs. No new
HOL/Rocq proof, native checker comparison or current Arena verdict is claimed.

### Session70: Compiler Transport Build Accepted

The fresh call_fab906 approval was consumed by one guarded recovery. Initial
pressure1/free+spec1740029952B passed; native342 then completed all11 stages
and produced17 outputs (110916B), including five interfaces and the original
compiled API witness. Actual af4e28 exit0 was observed1054330375ns before the
original outer deadline. No retries or guard changes occurred.

Independent343 reviewed the saved stage chain, cleanup, actual outputs and
five interfaces. Parent acceptance is limited to this compiler transport build.
Final accounting/observer raw snapshots were not serialized; their successful
checks are supported by pinned control flow and aggregate saved claims, not
independent replay of missing snapshots. Existing failed sessions stay failed.

Offline347 checks the actual17 files through the selected Results API and
refuses17 changed-output cases. Its first serialization error is preserved;
revision02 changes only dataclass encoding and its own snapshot name.
Runtime345 has39 passing source models. The new asset entry346 is under separate
review; runtime bytes, CMI imports/ABI, external String resolution and integrated
HOL proof execution remain pending. The compiler witness is not a Lean proof.
No new Rocq proof, native checker comparison or Arena verdict is claimed.

Read [compiler acceptance](build/workers/parent-resumption-20261013-integrated-hol-07/compiler-native-01/COMPILER_ACCEPTANCE.json)
and the archived [independent result review](build/workers/parent-resumption-20261013-integrated-hol-07/source-checkpoint-02/hol-recovery-review343/RESULT70_REVIEW.txt).
The full ports remain unfinished. Entries below are historical checkpoints.

### Session69: Later String-Type Interface Mismatch

Fresh call_5061 approval was consumed by one guarded attempt. Initial memory
pressure was1 with2441592832B free+speculative; controller and active-stage
observations also passed. Native92dffc/session69345 ended2c65e1 exit1 after
nine reported candidate records. The first diagnostic is now
`hol_hint_input203.regular_decimal`: emitted `String.t -> (String.t, string) result`
versus required `string -> (string, string) result`.

Failed outer completion was observed6.914092416s before its original endpoint.
Child cleanup is reported, but whole-controller/lock/root cleanup remains
unaccepted. No full11-stage build, HOL/Rocq proof or new Arena verdict is accepted.
69 is stopped; do not retry, resample or inspect/reuse its failed private root.

Prospective339 supports only four complete regular_decimal type shapes, with
local String/Stdlib shadow rejection and unchanged external resolution/ABI holds.
264 distinct cases pass (376 invocations including112 baseline replays).
Fresh340 passes20 composition-model groups. Its first run's negative test
expected rejection too late; the corrected model checks the exact earlier
refusal without changing production predicates. Every failed attempt is retained.
The separate proposed regular_decimal witness is uncompiled and not integrated.

Runtime337's current331 source plan passes39 models; parent341 checks the bounded
source delta. Its stopped-session entry is deliberately nonlaunchable. None of
these source/model results is a native runtime/ABI/proof result. A worker339
wrong-directory instruction read and attribution error are disclosed in its
preserved correction; all worker writes stayed in its assigned temporary scope.

The233-case Arena inventory remains unchanged and unvalidated by current ports.
A fresh recovery question is pending. Keep all resource, cleanup and proof/trust
requirements unchanged. Read the [Session69 report](build/workers/parent-resumption-20261013-integrated-hol-06/FINAL_REPORT.txt)
and [resumption handoff](build/workers/parent-resumption-20261013-integrated-hol-06/RESUMPTION.txt).
Full ports and end-to-end validation remain unfinished; entries below are history.

### Current Arena Snapshot: 233 Cases

Published revision `c6d13acb518e8afe7695678779f57bf9e029a4aa` adds ten cases
to the previous223-case inventory and changes Cedar's input hash. The fresh
snapshot has135 accept,72 reject and26 either cases.216 small inputs are
hash/header verified;8 new corner exports and9 large inputs remain unvalidated
here. Five of the large inputs have preserved historical candidates.

57 preparation controls pass; independent review verifies the input snapshot
and39 published timeout mappings. Ten new definitions and five shared Lean
generator sources are pinned, but not executed. These are input/source results:
no new compiled proof, native checker comparison or Arena verdict. No historical
verdict is promoted. The default corpus and all earlier attempts remain unchanged.
Native68 remains stopped with fresh recovery approval pending and unchanged guards.
Read the [reconciliation report](build/workers/parent-arena-reconciliation-20261013-01/REPORT.txt)
and [resumption handoff](build/workers/parent-arena-reconciliation-20261013-01/RESUMPTION.txt).

### Session68: Failing Interface Declaration Identified

Fresh human approval authorized one recovery with unchanged limits. Diagnostic319
was integrated through Inputs320/Bridge320 and sealed323. Final assembly13/13 and
exact preparation3248/8 pass; independent322 reviewed source, authority and seals.
These are source/model checks, not proof tests.

Initial68 passed pressure1,4482629632B free+speculative,43.090708ms; controller
passed5027250176B and active stage1574879232B. These are separate observations.
Native50c58c/session9843 ended d0fa56 exit1 with nine reported candidate records.
The new diagnostic identifies required value type drift: hol_input.expr.
Exact actual type spelling was not captured. Exprs.key/Wire.expr remains a
source-grounded explanation, not a directly observed native type comparison.

Outer completion was observed at T0+91.306433584s,6.848100833s before its original
endpoint. Child cleanup is reported; lock/root whole-controller cleanup remains
unaccepted. No complete11-stage build, HOL/Rocq proof or new Arena verdict.
68 is stopped: no retry, resample or failed-private-root inspection. Its failed
attempt and consumed approval cannot be reused. Prospective329 checks the scoped
transparent key equation and exact optional table injectivity marker;112 synthetic
cases pass. Actual native spelling remains unknown, so this is not a confirmed
native fix. Memory, cleanup, deadlines and proof/trust limits remain unchanged.

Independent review caught malformed saved JSON in328/330 despite passing in-memory
models. Those artifacts remain held. Fresh331 strictly validates saved JSON and
reconstructs the204-entry source mapping with exact hashes; cached source snapshots
may be reused, not204 fresh disk reads.17 model groups pass, including six malformed
JSON negatives. Final331 review finds no remaining issue in its bounded source/model
scope. These are not compiled proofs, native checker comparisons or Arena verdicts.
A new recovery question is pending; no fresh native authority has been received.
Read the [Session68 report](build/workers/parent-resumption-20261013-integrated-hol-05/FINAL_REPORT.txt)
and [handoff](build/workers/parent-resumption-20261013-integrated-hol-05/RESUMPTION.txt).
The independent ports and current Arena validation remain unfinished.

### Session67: Bootstrap Fixed; Native Interface Review Refused

The compiler bootstrap is now one original30s setup phase; later stage preparation
uses the same original180s execution budget. Memory, freshness, ownership, cleanup
and proof/trust limits remain unchanged.13 deadline models,13 report/terminal
models,13 assembly checks and6 exact-selection preparation groups pass, with
independent source review. These are source/model checks, not Lean proof tests.

Fresh67 passed its initial/controller/active-stage memory checks and reached
zero-based stage9, reporting nine prior candidate records. It then refused
actual214 interface-contract review. Outer exit was observed at T0+95.703407792s,
6.784979958s before its original deadline; this was not a bootstrap timeout.
Child cleanup is reported, but terminal lock/root cleanup acceptance is incomplete.
No complete11-stage compiler build, HOL/Rocq proof or new Arena verdict is accepted.

The generic interface error lost the underlying declaration/reason. Source-only319
preserves bounded detail without relaxing acceptance;8 models and independent
review pass. It is not integrated into a new native selection and cannot recover
67's lost detail. Do not guess the actual mismatch or normalize types to bypass it.
67 is stopped, with no retry, resample or failed-private-root inspection.
Read the [Session67 report](build/workers/parent-resumption-20261013-integrated-hol-04/FINAL_REPORT.txt)
and [handoff](build/workers/parent-resumption-20261013-integrated-hol-04/RESUMPTION.txt).
Full ports and current Arena validation remain unfinished; earlier entries are historical.

### Session66: Four Candidate Stages; Batch Deadline Failure

The fresh initial gate passed normal pressure and398MiB free+speculative memory;
later controller and active-stage gates also passed. The new reviewed selection
reported four candidate compiler-stage records and active-child cleanup. A normal
diagnostic receipt arrived and outer completion was observed before its deadline.
The batch nevertheless failed an internal absolute-deadline check. No full build,
new HOL/Rocq proof or Arena verdict is accepted; this attempt is stopped.

A source-level finding: every stage still faces the same original30s bootstrap
endpoint despite the separate180s execution budget. Expiry approaching stage4 is
plausible, but the old receipt does not identify its exact failing call. Limits
remain unchanged. Bounded failure-location diagnostics now pass8 source models
and independent review; they are unsealed/source-only, not a timeout fix.
The executed selection passed13 assembly and6 preparation groups.

See the [Session66 report](build/workers/parent-resumption-20261013-integrated-hol-03/FINAL_REPORT.txt)
and [handoff](build/workers/parent-resumption-20261013-integrated-hol-03/RESUMPTION.txt).
No retry or post-failure resource/process resample was made. Prior evidence is
preserved. The complete independent ports and current Arena validation remain
unfinished. Earlier checkpoints below are historical.


### Session65: Native Finalization Failed; Repair Source-Reviewed

The fresh recovery passed all memory checks; the inner stage recorded normal
pressure and1314996224B free+speculative memory. The guardian ran and was reaped,
but finalization exceeded the original cleanup deadline and the controller's
outer deadline check failed. No compiler stage or new proof/Arena verdict is
accepted. The failed attempt remains stopped and uninspected, without a retry.

A source-reviewed successor reduces redundant capture scans during fixed
terminal evidence writes/readbacks while retaining original file, hash, custody,
deadline and cleanup checks.17 source-model groups and6 preparation checks pass.
The full finalizer model reduces capture-provider operations310750->11550 while
retaining276 evidence-file operations. This is not a native timing result.
Review found and resolved an exact-type regression and a fallback-after-refusal
gap; all historical failures and reviews remain preserved.

See the [Session65 report](build/workers/parent-resumption-20261013-integrated-hol-02/FINAL_REPORT.txt)
and [handoff](build/workers/parent-resumption-20261013-integrated-hol-02/RESUMPTION.txt).
Fresh recovery permission and a new sealed selection are required before the
next native attempt. The ports and current Arena validation remain incomplete.


### Session64: Past The Memory Gate, Terminal Deadline Failure

The approved recovery passed normal-pressure checks, including252.796875MiB
free+speculative memory at the inner stage gate. The guardian was created and
reaped, but terminal preservation exceeded cleanup10 and the controller's
outer deadline check failed. No compiler stage, HOL/Rocq proof or Arena verdict
is newly accepted. Native work stopped; no resampling or retry followed.

A reviewed source repair reduces redundant capture rescans around clean,
read-only terminal inspection.23 source-model tests pass; the ten-file model
uses1100 capture-provider operations instead of298650, with matching acquired
file evidence. This is not a native timing result or completion claim. Failed
inspection diagnostics remain retained, and all guards stay unchanged.
See the [Session64 report](build/workers/parent-resumption-20261013-integrated-hol-01/FINAL_REPORT.txt)
and [handoff](build/workers/parent-resumption-20261013-integrated-hol-01/RESUMPTION.txt).
The repair still needs a fresh sealed selection and authorized guarded run.

### Session63: Captured Inner Resource Refusal

The approved fresh recovery passed its initial gate with normal pressure and
6.46GiB free+speculative memory. The later compiler-controller gate passed with
135.03125MiB, but the inner first-stage gate measured118.453125MiB, below the
unchanged128MiB floor. No guardian/compiler child was created. These are separate
saved observations, not current measurements or a diagnosis of the memory change.

The reviewed diagnostic repair now retains that inner sample. Actual controller
exit1 was observed before its outer deadline; strict cleanup remains unaccepted.
No compiler stage, HOL/Rocq proof or Arena verdict is newly accepted. No native
retry or resource/process resampling followed the refusal.

Five source-only finalizer models pass, including a parent replay. They exercise
report writing/readback and modeled terminal closes, but do not validate complete
native/batch cleanup or clear the held pre-spawn repair. See the
[Session63 report](build/workers/parent-resumption-20261012-integrated-hol-14/FINAL_REPORT.txt)
and [handoff](build/workers/parent-resumption-20261012-integrated-hol-14/RESUMPTION.txt).
All earlier evidence remains intact; the complete ports remain unfinished.

### Session62: Inner Gate Refusal Before Compiler Spawn

The approved fresh recovery started. Its initial check passed with normal
pressure and about12.3GiB free+speculative memory; the controller's later check
passed with148.671875MiB. The inner first-stage gate then refused its128MiB
floor before creating a compiler child. These are saved observations, not live
measurements. The exact inner value was not retained in the terminal report.

The controller exited within its outer deadline, but terminal preservation also
failed and strict cleanup was not accepted. No compiler stage, HOL/Rocq proof
or Arena result is newly accepted. Native work is stopped without resampling.
Source-only repairs address missing runtime archive evidence and diagnostics;
they do not establish executable validation or completion of the ports.
See the [Session62 report](build/workers/parent-resumption-20261012-integrated-hol-13/FINAL_REPORT.txt)
and [handoff](build/workers/parent-resumption-20261012-integrated-hol-13/RESUMPTION.txt).
All earlier attempts are preserved. A fresh recovery session requires actual
human approval and passing unchanged resource/ownership guards.

### Session59: Resource Refusal Before Compiler Execution

The latest approved recovery session's initial check passed, but its required
pre-execution check recorded warning pressure2 and81.046875MiB free+speculative
memory, below the unchanged128MiB floor. The controller stopped before any OCaml
command, returned a matching failure receipt and exited before its outer deadline.
No post-refusal resource sample or retry occurred. These are saved observations,
not measurements of the host at the time this document is read.

The repaired runtime/artifact-bridge selection, cleanup logic and bounded error
diagnostic have source/model review. Actual full preparation and bridge binding
were exercised with modeled native effects, not proof-assistant execution.
There are zero newly accepted compiler stages, HOL/Rocq proofs or Arena verdicts.
The latest sources, exact evidence and remaining milestones are in the
[Session59 report](build/workers/parent-resumption-20261012-integrated-hol-12/FINAL_REPORT.txt)
and [recovery handoff](build/workers/parent-resumption-20261012-integrated-hol-12/RESUMPTION.txt).
A fresh actual recovery approval and passing guards are required before native
work resumes. The full ports remain incomplete; all failed attempts are retained.

Historical223-case accounting is complete as an accounting exercise, not as a
full-suite pass. It does not cover the233-case public category-count observation
recorded in Session57. Current corpus reconciliation and validation of both
current ports remain unchecked in the plan.

### Session57: Native Compiler Attempt Stopped; No Accepted Build

On2026-10-12 the user approved validation of the integrated HOL path. This
supersedes the pending-authorization statements in historical continuations.
The single initial read-only check passed: pressure1,592986112 free+speculative
bytes,1349.50MiB swap used,20.391416ms sample, and all listed old PID/groups
absent. Evidence is in `build/workers/parent-resumption-20261012-integrated-hol-11`.
The separately gated asset-preflight-01 completed with exit0:879 runtime files,
118909579 bytes read, and an immediate actual clock probe before its anchored
outer-completion deadline. Its fresh gate recorded pressure1 and6109937664
free+speculative bytes (about5.69GiB). This is a candidate runtime inventory,
not complete runtime/ABI authentication, a compiler/HOL pass, or an Arena result.
The reviewed native compiler attempt subsequently passed its fresh resource
gate: pressure1,605093888 free+speculative bytes,1341.50MiB swap used and a
19.698541ms sample. The first command produced wire.cmi/wire.cmo, but the
controller failed its original cleanup-completion check before an outer receipt.
No compiler stage is accepted; no new HOL proof or Arena verdict is credited.
The primary inner failure is unavailable, not diagnosed as memory or bad proof.
The actual tool chain and separate parent STOP are preserved in that session.
A later command-name process snapshot found only the diagnostic observers;
this is not authenticated cleanup. No heavy retry or memory resample followed.
Keep the consumed native and asset attempts intact. Source diagnosis continues;
the complete ports, Rocq integration and Arena validation remain unfinished.
Independent source review now passes the269 preservation-scan optimization
with the272 finalizer refusal guard.267 repairs exact-stock validation ordering;
264/271 check the cache-audit source/query mapping without compiling Rocq proofs.
These repairs and all their failed model attempts are in source-checkpoint-03.
Fresh recovery permission is pending; no new native acceptance is implied.
The child/finalizer/supervisor source integration also passes independent models;
see [Session57 report](build/workers/parent-resumption-20261012-integrated-hol-11/FINAL_REPORT.txt)
and its integration closeout. Those checks do not establish full compiler
preparation, native runtime custody, HOL parsing or proof acceptance.
A separate2026-10-12 [Arena website](https://arena.lean-lang.org/) observation
shows135 valid,72 invalid and26 either-outcome cases:233 total. The retained
223-case run is historical. A new manifest/input-hash comparison and campaign
are required; the public count is not a freshly pinned corpus or test result.

### Continuation56: Genuine Division Prefixes; Native Validation Blocked

244 supplies two exact original Arena-derived Nat/div prefixes:540292 bytes/265
declaration rows and458356 bytes/209 rows. Both retain full structural dependencies
and intervening declarations, with zero axiom rows. Ten static tests and parent
byte/provenance readback pass. They are not certified HOL environments or Arena
verdicts; the shift-right fixtures still require actual execution.

Fresh native-session authorization remains pending after repeated source-only
continuations. No new memory diagnosis is available and no native run occurred.
The [Continuation56 report](build/workers/parent-source-continuation-20261011-56/FINAL_REPORT.txt)
and completion audit record the blocker and unchanged end-to-end requirements.
The full ports remain incomplete. No defaults, limits, Solidity or prior evidence
changed; native validation cannot be replaced by additional model-test counts.

### Continuation55: Shift-Right Composition And Output Custody

240 incorporates the four reviewed237 replacements into an actual139-file HOL
source package and paired compiler profiles. All eleven profiles agree in source
models; no compiler or HOL process ran. Parent14 and independent14 source checks
pass, with overlapping coverage. New237 fixtures remain dormant without a genuine
Nat/div prefix. The profile helper requires caller-recomputed pairing; it is not
an independent authenticator for arbitrary source objects.

241 adds caller-retained private-root/output ownership, per-operation budget
checks, exact236 readback and sticky refusal with uncertain descriptor custody.
Its21 author model methods and10 independent methods/263 targeted scenarios pass,
with overlapping coverage; see the [Continuation55 report](build/workers/parent-source-continuation-20261011-55/FINAL_REPORT.txt).
Native provider/namespace/outer teardown and updated guardian bindings remain
unfinished. No new compiled proof, native comparison or Arena verdict is added.
The full ports remain incomplete; limits, defaults, old evidence and Solidity
are unchanged. Fresh native-session authority is still pending.

### Continuation54: Read Custody And Shift-Right Source

236 repairs the read half of PinIO: per-operation budget checks, explicit held
or uncertain descriptor custody, sticky refusal and hash-before-baseline commit.
20 parent model methods and29 independent methods pass, with overlap. This is
not yet the selected runtime reader; private-directory/output cleanup is separate.

237 proposes the missing `Nat.shiftRight` selection through the generic HOL
primitive contract and opt-in frontend. An older standalone implementation
already existed but was not selected in210.29 static checks pass; dormant HOL
fixtures and genuine Nat/div prefix provisioning remain unexecuted. No division
semantics, numeric acceleration or new axiom is assumed. Fresh logical rebuild
and actual210/211 composition are required before execution.

New compiled proofs, native comparisons and Arena verdicts remain zero. The
full ports are incomplete; the unanswered fresh-session question is not replaced
by earlier consumed consent. Limits, defaults and Solidity remain unchanged.
Read the [Continuation54 report](build/workers/parent-source-continuation-20261011-54/FINAL_REPORT.txt)
for exact implementation/review scope, preserved failures and next steps.

### Continuation53: Serial Compiler Source Integration

231 joins all11 compiler stages under one original clock and live accountant,
using actual inspected predecessor hashes, a non-exiting finalizer and concrete
output inspection. Selected233/234/235 successors repair real OwnershipTrace
serialization, explicit unresolved terminal custody and acquisition-IO refusal.
Failed batches retain original owners and available diagnostics; unavailable
evidence is never success. No forced late close or deadline renewal was added.

20 parent model methods and35 independent controller/custody methods pass.
Finalizer62 and bridge17 source suites overlap other checks; do not add counts.
Models substitute native effects and compiler outputs, so this adds zero compiled
proofs, native controls/comparisons or Arena verdicts. Full port completion,
native provider/runtime/namespace custody, inherited PinIO issues, outer teardown
and fresh execution authority remain open. Limits/defaults/Solidity are unchanged.
Read the [Continuation53 report](build/workers/parent-source-continuation-20261011-53/FINAL_REPORT.txt)
and its review closeout for exact selected hashes, preserved failures and limits.

### Continuation52: Capture And Compiler Report Integration

223 supplies concrete immutable compiler plans and a separate provisional report
contract.224 observes captures through anchored directory handles and records
returned sizes before later failures.226 connects the same live accountant and
current original budget to the retained session. Predecessor outputs now require
explicit supplied pins. Independent review reproduces and closes two deadline
boundary defects, preserving old sources and failures.

Parent/source checks pass40 contract,74 capture/accounting,25 session and5 cross
integration methods. The cross test includes eleven synthetic finalizations;
these are not native compiler runs or proof/Arena results. A provisional receipt
can precede a late output failure, so hash linkage explicitly returns passed=false.
Borrowed root ownership and actual outer terminal evidence remain external.

Full batch execution, original-scope authority/runtime custody, actual generated
interfaces and native validation remain open.220 finalizer exits its process;
it cannot simply be looped while retaining one live accountant. No new compiled
proof, HOL control, native comparison or Arena verdict is added. Full port goal
is incomplete; limits/defaults/old evidence/Solidity are unchanged. Read the
[Continuation52 report](build/workers/parent-source-continuation-20261011-52/FINAL_REPORT.txt)
for exact source/review scope, preserved failures and next required work.

### Continuation51: Guardian And Cumulative Log Integration

220 now binds the original108 spawn code and actual54/110 session classes to
clock-free sealed compiler inputs and an original-start runtime header.221
provides one cumulative16MiB retained/capture log budget across all11 commands,
with conservative two-file reservation and sticky failure accounting. These
are source integrations, not a runnable or native-validated compiler controller.

Parent replays pass13 guardian/binding,18 session and53 accounting source/mock
tests. Independent review found source mutation, lost attribution, terminal-order
and inspector-arity defects; repairs and original failures are preserved. The
session tests exercise the actual110 finalizer body with synthetic IO/report
data. Neither those tests nor a pre-exec marker establish native/proof acceptance.
A further reviewed failure path motivated finalizer220: it records the final
exit-check failure that110 omitted. Old/new synthetic regressions preserve the
failure and require the repaired path to block a successor. Its factory refuses
the old proof-fixture report contract; genuine compiler reporting remains external.

Compiler plan/authority, real capture custody, complete batch finalization,
runtime/ABI/interface checks, fresh session authority and actual execution remain.
No new Rocq compilation, HOL control, native comparison or Arena verdict; no
limit/default/feature promotion or Solidity change. Full goal remains incomplete.
[Continuation51 report](build/workers/parent-source-continuation-20261011-51/FINAL_REPORT.txt)
records exact review disposition, findings, evidence and next integration steps.

### Continuation50: Compiler Payload And Result Integration

215 supplies exact eleven-command profiles;217 implements owned-child separate
captures and fixed exec;218 consumes typed output inventories and actual215
profiles;219 adds bounded EOF input, original-clock handoff and an uninvoked
embedded-source entry. Old216 and all failed/pre-review evidence are preserved.
Parent source/model checks pass34+13+63+14 methods,26 renderer assertions and235
cross-component assertions. Reviews overlap these counts; none is a proof or
Arena pass. Independent review found/repaired mutable-source hash/reuse gaps;
parent integration found/repaired symbolic-versus-absolute command mismatches.

Guardian configuration/parent integration and cumulative guardian-plus-capture
log enforcement are still required. Actual runtime/ABI custody, generated-object
validation and fresh session authority remain prerequisites to native work.
The source-only entry is not a ready guarded runner. No new compiled proofs,
native controls/comparisons or Arena verdicts; no limits/defaults/Solidity changes.
[Continuation50 report](build/workers/parent-source-continuation-20261011-50/FINAL_REPORT.txt)
records exact boundaries, tests, findings and remaining work. Full goal is open.

### Continuation49: Combined Source Package

The private HOL path now has a concrete phased loader211, five-unit transport
build/interface component212, and six-group fixture entry213. Their combined
139-file source mapping plus metadata is preserved as a fresh source snapshot.
It includes no compiled objects and grants no execution authority. Parent checks
pass:19 loader methods,37 transport methods,19 join methods,32 entry source/model
groups,6 interface-shadow regressions and5 materializer methods. These are not
HOL proof checks or Arena tests. The37 transport regressions also pass on214.

Review found and repaired three source-loader integrity gaps: posthoc-only include
checking, reopening a hashed scanner, and an unpinned guard template. The loader
now enforces parent scope/parser order before loading and retains nested failures.
A separate214 successor repairs interface helpers shadowing required type names;
the original212 and its review remain preserved.
Actual OCaml interfaces/objects, a reviewed guarded build/native adapter, runtime
custody and native validation remain required. Existing208 profiles cannot run
this new plan unchanged. Recovery10's approval is consumed; the new-session
question is unanswered. Defaults, limits, Rocq and Solidity remain unchanged.
[Continuation49 report](build/workers/parent-source-continuation-20261011-49/FINAL_REPORT.txt)
distinguishes source reviews/models from compiled proofs and native evidence.

### Continuation48 History

Source continuation48 adds a private hint-aware marked-history file adapter209
and a complete118-source inventory210. It connects the safe-hint API to existing
ordinary/generated and opt-in extended primitive admission, preserving failure
classification and publishing one authenticated successor. Independent review
found an axiom metadata-prepass bug; its source repair and regression are saved.
Parent also corrected a fixture parser hazard and a negative hook that could
have counted resource declines as passes.10 adapter source checks,28 graph/model
checks and fixture-data checks pass. All new ML/HOL fixtures remain unparsed
and unexecuted; no default code or validated feature status is promoted.
A phased loader, compiled interfaces and guarded native validation are still
required. No new proof/native/Arena result was added in48. The new-session
question is unanswered; recovery10's old approval is not reused.
[Continuation48 report](build/workers/parent-source-continuation-20261011-48/FINAL_REPORT.txt)
records exact source pins, preserved failures, tradeoffs and remaining work.

### Latest Actual Native Validation

Recovery10 completed the newly authorized guarded HOL Environment run.
Initial and per-stage resource gates passed with unchanged limits; all775
runtime assets were verified. Fresh208 preparation and exact independent207
coverage passed. Actual terminal8f92d7, immediate probe553d47 and strict
inspectiona8fbbb validate all11 selected Environment controls and cleanup.
The stock axiom inventory remains3. These are real HOL checks, not Arena cases.
Earlier Core180's64 focused checks remain separate historical evidence.

This validates the selected182 loading-order and186 alias repairs. It does not
validate newest163/203, compile Rocq202, prove Lean equivalence, or complete the
ports. New Arena verdicts and new Rocq compilations are zero. Source review
caught another stale human-schema kind in205 and an unbound prepared-review
basis in the grant helper;208 and reviewed206 repair both before execution.
47 Python source/model methods and3 JS cases/17 assertions pass in the final
launcher packages. Frozen205/191 and all prior failures remain unchanged.
[Recovery10 report](build/workers/parent-resumption-20261011-recovery-10/FINAL_REPORT.txt)
records exact evidence and remaining work. The bbf approval is consumed; do not
repeat this attempt or reuse its resource samples. No commits or pushes.
Earlier pending-question/STOP wording below describes its historical session.

### Source Continuation47 History

Source continuation47 adds actual checker/admission source. Rocq202 carries the
existing failed-congruence cache through the local lazy-delta body and loop,
with complete-result refinement scripts and16 dormant Gallina fixtures.14
source/model methods pass; independent204 source review found a weak fixture,
now strengthened to distinguish stale expression-state forwarding. No Gallina
script or fixture was parsed/compiled. Recursive/default integration is pending.

HOL203 adds hint-preserving safe transport and certified post-admission metadata
binding before history append. Existing private07/163 hint policy remains
unchanged. Parent review corrected a forbidden-reference error from Unsupported
to the existing Invalid_input classification;20 source/model groups pass.
Its two ML/HOL fixtures and complete loader/default integration remain unrun.
No new compiled proof, native checker result or Arena verdict. STOP09 and the
pending new-session question remain; no guard, default or old attempt changed.
[Continuation47 report](build/workers/parent-source-continuation-20261011-47/FINAL_REPORT.txt)
records code, findings, corrected regressions and remaining integration work.

### Source Continuation46 History

Source continuation46 implements framed typed-entry audits198, a strict
recursive-summary classifier199 and a finite source/content composition200.
83 distinct source/model test methods pass, including actual renderers and
parsers fed synthetic transcripts. The proposed110-module/220-stage schedule
covers722 framed query occurrences,712 distinct names and110 recursive roots.
It has not been applied to the native runner or compiled;185 still returns HOLD.

Primary-source inspection confirms that rocqchk honors stored checking flags:
exit zero alone does not establish safe checking. Its summary has no global UIP
category and covers final-environment maps, not all transient checking contexts.
The selected Darwin runner also OS-merges stdout/stderr;200 requires explicit
capture mode and never invents an empty secondary stream. New outputs remain
content matches only, not authenticated native evidence or stage acceptance.
No new compiled proof, native checker comparison or Arena verdict is claimed.
[Continuation46 report](build/workers/parent-source-continuation-20261011-46/FINAL_REPORT.txt)
records exact sources, model results, findings and remaining obligations.
STOP09 and its pending fresh-session question remain; no probe or retry followed.

### Recovery09 History

Recovery09 consumed the fresh ead7 approval. Both read-only resource gates
passed: normal pressure,1043.14 MiB then1118.83 MiB free+speculative memory,
1373.50 MiB swap used.775 runtime assets were verified. Actual Environment191
preparation then failed before HOL or grant creation: the191 entry still
required an183 seal kind. This packaging defect, not memory, stopped09.
The prior source tests and194 review missed the outer-reader contract.

Fresh196 changes one literal and adds eight passing source/model regressions
through the actual authenticator. It reproduces the old failure in both modes
and rejects altered sources/pins/kinds/deadlines. It is not a runnable successor
or native proof validation. Failed191 and STOP09 remain unchanged.

Rocq192 supplies31 typed signature witnesses and62 direct/witness queries in
five uncompiled audit modules.20 source/model methods pass;21 direct targets
extend the660-name inventory. Independent195 approves source only. Labelled
output integration, guarded compilation, recursive audits and185 HOLD remain.
No new compiled proof, native comparison or Arena verdict; full ports incomplete.
[Recovery09 report](build/workers/parent-resumption-20261011-recovery-09/FINAL_REPORT.txt)
records the failure, regression, evidence and remaining work. A fresh session
requires new authority; the consumed ead7 approval cannot be retried.

### Historical Source Continuation44

Source continuation44 advances the next validation inputs without reopening
stopped recovery08. HOL188 composes both loader182 and alias186 repairs:
80 sources, all11 Environment controls, 40 passing source/model checks and
independent189 source approval. Candidate190 fixes the old consumer's shared
fixture-review assumption with per-profile review binding; 16 pure-helper checks
and narrow independent review pass. It is not a complete sealed runtime package.

Rocq187 implements exact target-labelled assumption-query generation and strict
output-content checking for660 targets in42 proposed batches. Parent replay
passes21 source/synthetic tests. Supplied matching bytes are explicitly not
native evidence or accepted stages; runner185 still returns HOLD. The new query
jobs have not been compiled or added to the guarded plan. No new proof, native
comparison or Arena result. The fresh-session question remains pending.

### Recovery08 Execution

Recovery08 consumed the fresh e0pQ approval. The initial, runtime-asset and
native-stage guards passed with unchanged limits. The repaired include order
got past the old entry-fragment failure and loaded the Environment module, but
the final fixture failed to parse its single-letter module alias E. Work exit3
and controller exit1 stopped08 without strict cleanup acceptance; none of its11
controls ran. No memory refusal, timeout, resample or post-STOP native job.

Fresh alias-only repair186 renames E/F to Env/Fixture under HOL Light's JRH
lexer, preserving all11 controls and proof/axiom checks. Six source tests pass;
actual parser/HOL validation remains pending. Rocq185 implements native hooks
and bootstrap source and passes34 distinct source/model/mocked tests, including
parent replay. Its semantic completion remains HOLD, so no accepted stage2 or
real Rocq build/audit follows. Core180's64 strict controls remain historical.
No new Arena verdict, Rocq compiled proof or Environment control pass.
[Recovery08 report](build/workers/parent-resumption-20261011-recovery-08/FINAL_REPORT.txt).
The full independent ports remain incomplete; older checkpoints below are history.

### Historical Recovery07

Recovery07 now has a genuine focused HOL Core pass: all64 selected controls,
actual terminal exit0, unchanged axiom inventory and strict completion/cleanup.
The repaired loader binder and exact1000ms polling metadata are validated for
this run. Initial and fresh asset gates passed, with775 runtime files checked.

The separate Environment run exited3 before its11 controls, reporting ABS in
inductive_entries.ml. Its flat loader prematurely loaded nine parent-scoped
fragments before environment_rules.ml defined their prerequisites. Strict
inspection stopped07; cleanup remains provisional for that failed attempt.
Fresh loader-only repair182 retains all80 sources, passes19 negative source
models and independent source review, but needs new native validation. Rocq181
has18 passing model tests; its real native hooks/bootstrap remain incomplete.
No new Rocq compile or Arena verdict follows. Full ports remain incomplete.
[Detailed Recovery07 report](build/workers/parent-resumption-20261011-recovery-07/FINAL_REPORT.txt).

### Historical Recovery06

Recovery06 passed fresh memory and775-asset checks, then reached actual HOL
source loading. Core failed on an unused parameter identifier; a separate
parent polling-metadata error also prevented strict completion. The session
is stopped, not memory-blocked. Two minimal HOL source repairs and a six-test
polling metadata repair are preserved but not native-validated. Rocq170 still
needs finite safe-runner adaptation before its batch build/audit. No new proof
controls or Arena verdicts passed. The full ports remain unfinished.
[Recovery06 report](build/workers/parent-resumption-20261010-recovery-06/FINAL_REPORT.txt)
separates actual execution, independent reviews, model tests and unvalidated
source; a fresh-session question is pending. Old failures and limits remain.

### Prior Source Checkpoint

Continuation43 stages a complete63-file local Rocq source composition and a
consolidated audit for the new cache work. Bounded source checks and independent
review pass; two scanner false positives are preserved and repaired. The660
audit-target names are unexecuted and not exhaustive declaration coverage.
[Detailed report](build/workers/parent-source-continuation-20261010-43/FINAL_REPORT.txt)
and [review closeout](build/workers/parent-source-continuation-20261010-43/REVIEW_CLOSEOUT.txt)
separate source evidence from proof/runtime claims. No new compiled proof or
Arena result. Safe preparation is complete; required guarded compilation is
blocked on the pending fresh-session approval. The full ports remain unfinished.

Continuation42 adds Rocq exact structural keys and an actual-congruence-observer
cache adapter.18 source/hash assertions pass; independent review finds no
blocking source defect and an isolated context-value coverage gap is addressed
with four additive fixtures. All new proof scripts and71 combined dormant
Examples across167/168 remain uncompiled/unexecuted, not Arena passes.
[Detailed findings](build/workers/parent-source-continuation-20261010-42/FINAL_REPORT.txt)
explain alpha-key collisions, erased ownership and outstanding state integration.
No new native proof/Arena result; recovery05 remains stopped pending the existing
fresh-session question. Full completion and default integration remain open.

Continuation41 advances recursive HOL certificate reuse and the Rocq failure-
cache algebra.17 HOL source/model methods pass; source review164 supplies11
unexecuted genuine HOL groups. Rocq162's24 proof scripts and40 Examples remain
uncompiled. Audit165/166 checks coverage for35 new assumption-query targets,
not the resulting proofs. [Detailed findings](build/workers/parent-source-continuation-20261010-41/FINAL_REPORT.txt)
record scope, extraction and stateful-integration limits. No new native proof
or Arena verdict; full completion remains open and recovery05 stays stopped
pending a fresh-session answer. No default/runtime selection was changed.

Continuation40 adds HOL158 alpha-certificate source and Rocq161 direct
observation-refinement scripts.16 source/model methods pass; independent source
reviews find no blocking issue. Nine genuine HOL fixture groups, two new Rocq
lemmas and five new Rocq fixtures remain unexecuted/uncompiled.
[Detailed report](build/workers/parent-source-continuation-20261010-40/FINAL_REPORT.txt)
records the exact scope and findings. No new native proof or Arena verdict;
default/runtime selections and recovery05 STOP remain unchanged. The pending
fresh-session answer, native validation and full project completion remain open.

Continuation39 advances checker source: HOL154 adds reviewed, typed certificate
reuse with19 passing source/model methods; Rocq157 distinguishes failed
congruence from unattempted cases with uncompiled preservation scripts.
[Detailed report](build/workers/parent-source-continuation-20261010-39/FINAL_REPORT.txt)
records seven dormant genuine HOL groups and22 dormant Rocq fixtures, not
executed proof results. Default/native selections and recovery05 STOP remain
unchanged. Full compatibility, native validation and proof audits remain open.

Continuation38 packages and independently reviews the repaired fresh proof
runner, with separate historical stock evidence and fresh operational authority.
[Detailed report](build/workers/parent-source-continuation-20261010-38/FINAL_REPORT.txt)
records23 profile,22 authority/join,12 reader,8 package and9 actual-Python
composition methods passing. These are source/model tests, not HOL proofs.
The entry remains inert; recovery05 is still stopped pending a fresh-session
answer and new unchanged gates. All75 selected HOL controls remain unvalidated.
No new compiled proof or Arena verdict; the complete two-port goal remains open.

Continuation37 adds a reviewed private whole-file conversion entry, not a new
validated runtime: [candidate and boundaries](build/workers/hol-whole-file-source-20261010-146/README.md).
It exposes enabled conversion, retains explicit Legacy mode and authenticates
the returned closed environment/policy/raw-history certificates. Ten source/model
methods pass; actual ML/HOL and full-file validation are still outstanding.
Recovery05 remains stopped; no new port proof or Arena result is inferred.

Latest, 2026-10-10 recovery05: actual guardian plus stock HOL startup now passes
strict native completion and independent saved-evidence review. The subsequent
Core proof controller failed before saving an attempt report; Environment was
not launched and all75 selected controls remain unvalidated. The session is
stopped, with no retry or resampling. An independently identified runtime-file
classification bug has a source-only repair with15+8 passing model regressions;
it is not installed or natively validated. No new port proof or Arena verdict.
See [session report](build/workers/parent-resumption-20261010-recovery-05/SESSION_REPORT.txt)
and the current Implementation Plan. Older numbered checkpoints below are history,
not current pending approvals or evidence that the full project is complete.

Final continuation23 review deliveries: runtime54 review68 3803a91b and quick
loader69 review70 1b36b455 both approve source only with no blockers. They report
28+19 and12+9 source/mock methods respectively. Genuine runtime assets, platform
validation, current recovery authority and actual HOL execution remain open.
Separate proof-only runtime75 and genuine eager fixture74 are now assigned;
neither exists as validated execution evidence. The sealed checkpoint has an
additive ADDENDUM-REVIEWS68-70.txt rather than overwritten prior reporting.

Later continuation23 delivery: eager-true source67 230a3008 now has independent
source review72 075c09b1 (17 author + 8 independent methods). It matches the
resolved Bool.true name, uses full typed WHNF and guarded original-endpoint
joins, and preserves enabled-only scheduling. Extra scanner ticks can cause
earlier finite-fuel declines; no runtime-cost parity is claimed. No genuine67
fixture has run or replaced the existing selection. Fuel61 final binding737d66b6
adds six conditional theorem-source constructions, including numeric induction,
not executable full division/remainder. Independent review71 and genuine raw
go-producer work73 are underway. Every new HOL construction remains unvalidated.

Continuation23 supersedes the pending-review statements below. Reflected proof
repair64 now has independent source approval65 b5c3c209; the original source52
remains blocked and preserved. Six author and five independent source methods
pass, not actual HOL theorem construction. Fuel-composition61 received the
exact approved dependency without inheriting a proof or runtime approval.

Execution59 has independent source review63 eee71048 (15 author + 14 reviewer
methods). Runtime54's fresh review63-bound successor15b67757 consumes that exact
review and passes28 effects-denied methods; independent runtime source review68
is underway. Its bridge builds, immutable runtime/platform evidence, current
authority and actual execution remain separate unresolved gates.

Genuine quick fixture62 has parent review66 2f868728 (14 author + 8 independent
source methods). It uses actual enabled-Native and public Env APIs, not a fake
positive proof producer. Its65 HOL controls remain unrun. New separate loader69
handoff8e07112b captures stock axioms before all project loads, loads66 source
files without transport bridges, and invokes the fixture exactly once after
its module is defined. Twelve source/protocol tests pass, including installed
replay2b23db; independent review70 is underway. The prior self-invoking driver
is preserved but excluded from loading. Suite53/runtime54 are not retargeted.

No new compiled proofs, native comparisons or Arena verdicts are claimed.
Native STOP and resource/trust requirements are unchanged. Eager-true shortcut67
and numeric-fuel work61 remain active. The whole two-port goal is incomplete.
Older numbered paragraphs below are historical, including their pending states.

Late continuation22 finding: independent review60 1fac340f BLOCKS source52.
It quotes the HOL function l4_prim_succ where an object Nat.succ expression is
required. Parent fresh repair64 handoff07b8cadf changes only that quotation;
six source regressions pass87a02f and installed1889b4. Independent re-review65
is underway. No actual HOL load or proof success follows. Source52 and its
passing-but-insufficient model receipts are preserved, not relabelled as valid.

Continuation22: common suite53 now has independent source review58 0ef7e933,
with12 author plus8 independent methods. Parent execution59 handoff54f7ffed
explicitly binds that exact suite to new three-phase loaders, invocation files
and full event protocols. Its15 effects-denied source/fake-operation methods
pass fb5594 and installed1e15ff. Independent review63 is underway; runtime54
binding, fresh bridge artifacts, platform evidence and genuine current authority
remain prerequisites. The347 arithmetic,136 mode and71 K actual-path controls,
plus10 separate K metadata controls, have NOT executed in HOL.

Quick-comparison56 now has source review57 b0680eab (13+14 methods), covering
initial/repeated quick scheduling and normalized proof-irrelevance placement.
It is not selected by suite53/execution59; a genuine fixture62 is being built.
Div/mod groundwork44 has source review55 16200ad0 (14+9 methods), not checked
proofs. Reflected-condition52 handoff0656bf36 adds four theorem constructions
and15 source/model tests; review60 and fuel-composition61 are underway. General
div/mod evaluation and full inductive/conversion parity remain incomplete.

No compiler, HOL proof execution, native comparison or Arena verdict was added.
Native STOP and all limits remain unchanged. Older numbered paragraphs below
are retained historical checkpoints, not additional current approvals.

Late continuation21 delivery: independent integration review51 now approves
selection48 source only, with8 author+10 independent methods and14 mutation
controls. The347 HOL controls remain unrun. Unified same-production suite53 is
being composed; exact K41 review49 is still required. See the checkpoint's
ADDENDUM-REVIEW51.txt for the updated scopes and interface terminology.

Continuation21 binds genuine arithmetic fixtures to the newer normalized-major
K and seven-operation candidate. Production45 has independent source review46
(18 source methods). Original seven37 fixture now has parent review47: 20 author
methods, seven binding methods and eight independent source-audit methods pass.
Its 347 main controls and optional separate raw106 remain unexecuted HOL tests.
Selection48 replaces both Core and production Env while preserving the complete
original fixture bodies, runner, all other rows and transport sources. Its
97+5 graph totals 869912 bytes; eight source-composition methods pass, with
independent selection review51 underway. This is not a core-only interface swap.

Normalized-major K34 has independent source review42. Genuine fixture41 now
tests major-TYPE aliases and type-derived constructor syntax, with 71 planned
public/private controls plus ten separately labeled copied-metadata controls;
all remain unexecuted and independent review49 is underway. Dormant suite
execution adapter43 adds exact invocation/event checking and retained lifecycle
API wiring; 14 effects-denied methods pass, review50 underway. It still targets
the older suite32, not selection48. Runtime closure, fresh bridge builds,
platform/ownership evidence and current authority remain separate prerequisites.
No compiled proof, native comparison or Arena verdict is added. STOP remains.

Source continuation20 adds an actual seventh arithmetic backend route:
Nat.shiftLeft now delegates to the reviewed same-budget HOL proof producer,
preserving six24's previous routes byte-for-byte. Handoff676f3109 selects
combined28 core and93 HOL/five transport sources,809816 bytes. Twelve effects-
denied source/adapter methods pass; independent review39 and a genuine admitted
fixture37 are underway. This is uncompiled source, not validated default support.

The common three-fixture suite32 has independent reviewe5bfd2c8 (6+8 methods).
Loader31 now has parent review73366cbd (26+8 methods), with four bridge builds and
three explicit lexer phases. Parent loader38 handoffd61b1849 adds K29 while
retaining both original arithmetic/mode plans as unchanged references; seven
source methods pass, independent extension review40 pending. All193/136/45
planned controls remain unrun. Normalized-major-type K selection is assigned34.

Rocq recovery composition30 has review86a4e107 (21+12 methods), not a complete
current recovery session or a native test. STOP, limits and prior Arena results
remain unchanged. No compiler/proof/native verdict or execution authority is
added. See the plan and work log for remaining source and runtime boundaries.

Source continuation19: combined28 has independent review92922026 (6 author+15
independent methods). Sixfixture25 review0b5f3fa9 has21+12 methods. Parent reviewed
qualified-modefixture28 with26 author+10 independent methods, reviewc2acdf00.
Its136 planned controls remain unexecuted and genuine public Lean.reduce*
admission remains absent; root-name definitions are unrelated nonmarkers.

New selection30 handofff265192d explicitly binds the arithmetic and mode fixtures
to the same combined28 core, changing only their core graph rows. Separate test
environments, runners, dependencies and transport are unchanged. Seven source
tests pass; exact selection review is pending. Kfixture29 handoffba849cb1 has45
planned controls and15 source methods, with independent review underway.

Loader audit found the main bootstrap only loads three transport bridges; this
candidate also needs Hol_safety_input and deliberate HOL/frontend lexer phases.
Bridge .cmi/.cmo generation is distinct from HOL-loaded Core/Env signature checks.
No new native/proof/Arena result is claimed. STOP and guards remain unchanged;
source-only loader and Rocq recovery-harness composition are now assigned.

Source continuation18 consolidates two concrete repairs into one candidate:
K selection is attempted before explicit major WHNF, and native refusal matches
the genuine Lean.reduceNat/Lean.reduceBool namespace. Older root-name tests
missed the latter defect; their historical evidence is retained, not relabelled.
K26 review74ccbdc9 has26 source/model methods; qualified27 review492d2ff3 has20.
Combined28 handoffe051e1b7/cored4d5218b passes six composition methods and an
installed replay. Its91 loadable plus five transport sources total794926 bytes;
only the core row changes. Exact independent composition review is pending.

Combined23 and six24 now also have their exact source reviews. Genuine six25
provides193 prospective arithmetic checks, while raw shiftLeft25 review8ffc00bd
has35 source/model methods and106 prospective parameterized controls. None of
these actual HOL checks has run. ShiftLeft is not bound into the six-route backend.
Qualified-mode28 and genuine K29 fixtures are being prepared with explicit pins.
K candidate construction still differs from upstream normalized-major-type
selection. No compiler, native comparison or Arena verdict is added; STOP and
limits remain unchanged. See the current plan and work log for exact boundaries.

Source continuation17: a fresh six-route backend now connects add/sub/mul/pow/
beq/ble to the combined default/nested and ordinary reduction core. Handoff
4f264a63 selects91 HOL-loaded and five transport sources (794977 bytes);13
effects-denied source/adapter methods pass, including installed replay. The
power addition preserves the five old routes byte-for-byte and original source
universes. Exact combined review and all actual HOL execution remain pending.

Default18 and ordinary19 now have source reviews; combined23 selects the active
eager mode and same whnf service, with six composition checks. Five-backend21
review14f0c0aa and raw-power19 review883152c4 approve source only. Parent reviewed
the81-control default fixture22 after19 author plus8 independent methods;
reviewbdc9f954 selects only its final runner/binding. All81 actual controls,
the100 subtraction controls and110 parameterized power assertions remain unrun.
The scheduled50-control fixture20 has source review1deb9d02 (9+8 methods), not
a runtime pass. Positive String coverage still needs genuine prerequisites.

No compiled proof, native comparison or Arena verdict was added. The power cap
is not a time/memory bound; numeral conversion still requires external guards.
Native STOP94d47aff and old attempts remain untouched. Pending fresh recovery
authorization has not been replaced by automatic goal continuation. Arithmetic
and combined-mode fixture successors and raw shiftLeft implementation continue
in separate agent scopes. End-to-end coverage and proof/trust audit remain open.

Source continuation16: ordinary lazy conversion now has a source successor
that probes Nat left-first, then refuses exact native markers before lazy
unfolding. Typed casts/symmetry/transitivity retain the original endpoints.
A binder-aware scan distinguishes surrounding-context variables from variables
bound inside the expression. Fifteen source/model and four graph methods pass;
handoffac801f80 selects86 HOL/five transport sources,763989 bytes. This wiring
is normal-mode only, pending review and composition with default/eager work.

Four-backend17 now has independent source approval4fca91ec (25 methods), and
rawsub17 has approval99c10b61 (16 author plus12 reviewer methods). Subtraction
is not yet bound into that backend. The genuine four-operation fixture17 is
sealed with192 planned HOL checks and19 passing source/model methods; review
is pending and every actual HOL check is unrun. No native/proof/Arena results
or default-integration claims follow. Native STOP and restart authorization
remain unchanged.

Source continuation15: the new four-operation backend binds Nat.add/mul/beq/ble
to their typed raw certificate producers. Exact composition b9ecdd5f selects
86 HOL sources and five transport inputs (761432 bytes); eight adapter methods
and seven graph methods pass. Independent backend review is pending. This is
not compiled/default support: ten binary producers and nested scheduling remain.

Opaque-add16 has independent source approval be4589d0 (10 author plus four
reviewer methods); comparison15 has approval dafc0956 (30 methods). The actual
comparison fixture's 158 checks remain unrun. The separate real-add/full-WHNF
fixture has approval 19fc3cb9 (22 author plus six reviewer methods), with 41
planned HOL checks, all unrun. It retains the historical canonical raw-add12
composition, not the four-operation backend. No new compiled proof, native
comparison or Arena verdict is added. The native STOP and pending restart
authorization remain unchanged. Default/nested integration is now an explicit
delegated implementation task, not claimed as completed by source composition.

Source continuation14: the exact addition backend and extended marked frontend
now have a combined graph of82 HOL sources plus5 transport inputs (729856 bytes).
Parent independently approved the binding/graph source after22 author methods
and6 independent checks. Handoff1f30aacd records the composition. The backend
supplies actual raw addition certificates to the internal reducer; default WHNF
still does not call it. Its51 planned HOL controls remain unexecuted.

A separate full-WHNF14 outer scheduler implements independent normal/eager loop
limits, explicit recursive operand normalization and guarded success-only caching.
Review56cbf07c passes23 author plus10 independent source methods. A fresh graph15
now selects this core with the addition backend (82 HOL/5 transport,733269 bytes);
four source-composition checks pass. Default dispatch and nested eager parity
remain unfinished. Raw multiplication also has source approval774fb175 (14+6
methods). Raw Beq/Ble packaging and opaque-environment preparation repairs are
underway. No new compiled proof or Arena result follows.

Source continuation13: the new typed binary Nat dispatcher preserves original
operands through guarded congruence, evaluates left before right, retains binary
head universes and enforces the upstream power bound. Its18 source/model methods
pass, including installed replay; independent review30f7196b adds six passing
source controls and approves this exact source delta. It dispatches
14 names but supplies no evaluation producer itself. A separate backend worker
is connecting the raw addition producer; full WHNF scheduling is also underway.
The new paths are not default checker integration or native-validated support.

Addition helper11 was source-rejected: whole-theorem arithmetic rewriting could
alter its retained environment and trigger a spurious certificate fault.
Repair12 confines rewriting to the result numeral. Independent review4a930e6e
passes12 author and6 reviewer methods without narrowing the API or weakening
guards. Native-refusal12 also has source approvalb462cf02 (257 author assertions
and12 reviewer methods); its58 actual HOL checks remain unrun.
The string-literal dependency gap in the two selected complete inputs is now
resolved at source level: all modeled implicit dependencies precede use. These
inputs still cover only five primitive routes; lor/xor remain compressed leads.
None of this adds an Arena verdict, compiled proof or native execution authority.

Source continuation10 (2026-10-09): the optional marked frontend now routes
Nat.div/mod/gcd/bitwise/land/lor/xor through the existing full certificate
producers. Independent source review2dcd8b19 passes21 source/model methods.
Its111 actual transport checks, generated interfaces and HOL admission remain
unrun. A separate full-file HOL fixture is implemented as unexecuted source;
it checks original metadata in certified history, not the canonical registry.
Typed Nat offset source has independent review532f9456 (693 author assertions
and208 independent controls); actual proof execution remains pending.
Loop08, telemetry08 and projection-runtime08 source reviews also passed.
Payload-only25ms pacing has source review3d9522b1; cleanup remains10ms and all
caps/deadlines are unchanged. It is not an executed cure for the prior STOP.
No native/compiler/proof/Arena result is added by these changes. The current
native STOP and unanswered fresh-session authorization request remain unchanged.
Neither default integration nor full executable feature coverage is complete.
See the [frontend candidate](build/workers/hol-extended-frontend-source-20261009-09/README.md)
and [full-file fixture](build/workers/hol-extended-frontend-fixture-source-20261009-10/README.md).

Historical execution checkpoint:

2026-10-09: fresh recovery03 passed. The separately authorized quiet typed-timeout
control then ran natively and passed the unchanged strict retained inspector.
The child was killed and reaped; PID/group absence, closed handles/lock, complete
empty log and both original/cleanup deadline bounds were verified. This is
runtime-safety evidence, not a checker acceptance, compiled proof or Arena pass.
Exact evidence is in `build/workers/parent-typed-timeout-validation-20261009-07`.
Independent native eligibility review then passed. All twelve untouched Arena
files were attempted: three accepts, seven strict time declines, one fuel decline
and a final supervisor STOP on2.42GB cslib. Cumulative pinned223-case accounting
is120accept/82reject/15decline/4missing/2stopped-uninspected, with no available
input unattempted. Independent result reviewb95e3047 reproduced all11 new strict
inspections and the aggregate.202 decided outcomes are expectation-compatible;
this is not full-suite success. No native work or resampling followed the STOP.

The remaining12 preparer passes54 replayed and8 additional independent
effects-denied methods. HOL projection06 review found a certificate-fault
classification defect, not demonstrated logical unsoundness. The fresh07 repair
passed independent source review and five-file composition review; actual HOL
validation is still required. A planned fixture was source-rejected for enabling
delta before binding hints. Its fresh08 repair is now independently source-approved
(review6b3d0a9e); all52 planned actual HOL checks remain unrun. A separate ordinary
lazy-loop1000 allowance repair and fixed-size supervisor counter telemetry have
been implemented and submitted for independent source review. Their447 and45
source/model checks respectively are not compiled proofs or Arena passes.
Both complete executable ports and whole-Lean adequacy remain
unfinished. Historical recovery01/02 failures and old206 remain unchanged.
Detailed checkpoint: [execution report](build/workers/parent-full-execution-20261009-07/FINAL_REPORT.txt).

## Run Locally

Earlier source work (2026-10-08): marked-source binding reached the fixed
gcd contract, with16 pure checks and independent source review. A separate
unvalidated gcd-specific29/13 model implements the proposed admission/state
extension path and passes15 source checks plus independent source review.
No model has been loaded or promoted
to default, and no new HOL or Arena pass is claimed. See the
[marked composition](build/workers/hol-marked-gcd-contract-20261008/CLOSEOUT.txt)
and [admission closeout](build/workers/hol-gcd-admission-source-20261008/CLOSEOUT.txt).
These source results do not release the native execution hold below.

Source-only continuation (2026-10-08): the new automatic gcd bridge recovers
recursor witnesses from the original wrapper and invokes the fixed logical
contract, including arbitrary-functional recursion obligations. Fifteen bounded
source/model checks and independent source review pass. No native proof or
Arena result is added; primitive
admission and default integration remain incomplete. See
[the source report](build/workers/hol-gcd-automatic-contract-20261008/REPORT.txt)
and [reviewed closeout](build/workers/hol-gcd-automatic-contract-20261008/CLOSEOUT.txt).
The native STOP below is
unchanged and does not prevent bounded source implementation work.

Earlier resumption (2026-10-08): a fresh reviewed HOL diagnostic attempt was
refused before child creation. Its single gate measured2,430,500,864 available
bytes (2.26GiB), but pressure code2 instead of required normal1. Lowering the
128MiB floor would not address this refusal. No proof or Arena result was
produced, and no retry/resample follows in this session. See
[the refusal report](build/workers/parent-resumption-20261008-02/REPORT.txt).

Earlier resumption (2026-10-08): after explicit human restart,154 complete Rocq
Arena files ran. The campaign stopped on checker fuel exhaustion,not memory
pressure or wall-clock timeout.65available inputs remain unrun;continuation
policy clarification is pending. Source-only work and retained audits continue.
The earlier first-seven HOL180s timeout remains preserved. The retained HOL
first-four-phase fixture passes actual strict validation and independent audit.
The repaired Rocq runner passes both actual fixed cleanup controls and their
independent retained audit. A separately reviewed, exact Syntax profile now
also passes actual compilation. Neither releases the ordinary checker commands
below or a general launcher. Each new native stage still
requires its own fresh pre-spawn gate and exact scoped authorization.

Validation-runner notice (2026-10-07): the historical October1 cleanup repairs
passed their focused suites, but subsequent review reproduces ownership and
absolute-deadline defects in the inherited HOL supervisor and finds the same
early-reaping pattern in the default Arena runner and inherited Rocq helper.
New runs through all three old helpers are held pending complete validation
of a supported replacement. The original warm backend requires a Python spawn
capability absent on this Mac. The Darwin-specific successor has now passed
reviewed native clean/descendant, compiler/FD and self-SIGTERM controls;
the October7 full-timeout control was refused before spawn at its memory gate.
The corrected-ABI full180s control subsequently passed on October8. Earlier
proof results remain scoped observations, not validation of these failure paths.
No accidental unrelated signal has been established. See the findings log.

The latest2026-10-07 user authorization permitted serial validation with private
HOL128MiB and Rocq64MiB available-memory floors. Normal pressure, deadlines,
cleanup and proof/trust checks remain required. These floors are not RSS caps.
That earlier resumption stopped at resource refusal2f68c8. The new October8
human authorization starts a separate guarded session; the old STOP remains
historical evidence. Source-only work never authorizes resampling or retry.
Historical resource refusals and failed attempts remain preserved. The
commands below document normal usage; they are not approval to bypass the
reviewed, serial, resource-controlled validation stages.
The ordinary Arena runner does not itself impose a hard memory cap. Neither
port is complete, and neither is claimed to have a whole-kernel soundness proof.
See [the current plan](IMPLEMENTATION_PLAN.md) for the exact remaining gates.

```sh
sh scripts/build-rocq.sh
build/rocq-check arena/corpus/tutorial/001_basicDef.ndjson
python3 scripts/test_arena.py --checker 'build/rocq-check --fuel 16384' --timeout 30 \
  --report build/reports/rocq-current.json
```

For HOL Light, see [the warm runner](docs/HOL_RUNNER.md). Every case runs in an
isolated, bounded child of a loaded HOL process. The HOL checker constructs
theorems of its object-language judgment; it does not call the Rocq or Lean
checker to obtain verdicts.

Exit codes are `0` acceptance, `1` rejection, `2` unsupported/resource decline,
and `3` operational fault. A decline is never counted as a passing test.

## Current Checkpoint

Fresh recovery03 passed on 2026-10-09 after a new direct human request. The
single sample measured normal pressure1, 1,190,871,040 free bytes and
3,500,064,768 speculative bytes (4,690,935,808 combined), with 2,889.12MiB
swap used. Actual outer62b778 exited0 with its exact receipt. Recovery02's
earlier pressure2 refusal remains immutable. Independent completion review
and the repaired timeout/cleanup control are the next gates before further
Arena execution; passing recovery is not itself a native execution grant.
See [the capture report](build/workers/parent-resumption-20261009-recovery-03/FINAL_REPORT.txt).

The opt-in HOL decoded-hint integration now has an independent source review:
29 author methods plus9 reviewer methods pass. Projection-pair logic is a
separate source successor under review. These are not new ML/HOL proof runs
or Arena verdicts; both complete ports remain unfinished.

The2026-10-09 continuation05 remaining-test preparer is independently source-
approved after47 author and9 additional review tests. It now requires successful
actual recovery completion, not just a positive saved observation. All prior
results and unchanged limits are preserved. No new native or Arena run follows
from this source approval; a fresh human check approval is still pending. See
[the preparer report](build/workers/rocq-arena-remaining12-recovery-source-20261009-05/README.txt)
and [independent review](build/workers/rocq-arena-remaining12-recovery-review-20261009-05/REVIEW.json).

The same continuation adds an opt-in HOL lazy-delta core candidate with266
source/model assertions including independent review. It is not loaded in HOL
or enabled in the default checker; remaining transport and scheduling gaps are
explicit. The codec validates semantic UInt32 values but cannot reconstruct raw
numeric spelling after decoding. See
[the continuation report](build/workers/parent-source-continuation-20261009-05/FINAL_REPORT.txt).

Source-only continuation on 2026-10-09 completed the separate recovery wrapper,
typed-timeout validation outer and a focused HOL arity fixture with dormant
guarded runtime composition. Source/model tests pass; reviews are recorded in
[the current plan](IMPLEMENTATION_PLAN.md). No fresh host check, native proof,
HOL parse or Arena result followed the pressure refusal. These candidates do
not promote the default checker or establish a complete port.

On 2026-10-09, an explicitly authorized fresh recovery check failed macOS pressure
level 2 versus required normal level 1. Free plus speculative memory was 251.75 MiB;
swap used 6.42 GiB. The byte floor passed, but the pressure guard did not. No new
native proof/checker run, retry or resampling followed. Exact raw measurements
and independent retained audit are preserved. Both ports remain incomplete.
See [the recovery evidence](build/workers/parent-resumption-20261009-recovery-01/RECOVERY_OBSERVATION.json)
and [independent failure review](build/workers/rocq-arena-domain-continuation-review-20261009-02/recovery-result-review/REVIEW.json).

The pinned 223-case Rocq ledger currently has 117 accepts, 82 rejects, 7 fuel declines,
12 untouched inputs, 4 missing files and 1 stopped/uninspected attempt. All 199 decided
results match required or permitted-either outcomes; this is not a passing full
suite. Timeout continuation has reviewed source but still needs a positive native
validation. The genuine HOL gcd dependency-subset assembly is source-approved,
not executed. The subsequent paragraphs retain older checkpoints as history;
in particular, fuel-decline continuation was later authorized and tested.

The new marked-input binding source ties gcd/bitwise certificates to declaration
metadata and exact prior history. Eleven source/model checks and independent
reviews pass, including a repair to isolate history-only replay testing.
No native proof, admission, default dispatch or Arena coverage is added.
See [the marked-input report](build/workers/hol-wf-marked-binding-20261008/CLOSEOUT.txt).

The private generic bitwise consumer now has independently reviewed source
for the original compiled wrapper and full conditional equation. A real-export
inspection revealed an ordinary-wrapper exposure defect; that and a universe
pattern restriction are repaired. Fifteen source/model checks pass, including
an independent rerun. No new HOL execution, primitive admission or Arena result.
See [the bitwise source report](build/workers/hol-bitwise-decoder-consumer-20261008/CLOSEOUT.txt).

The private gcd source now consumes the automatic compiled-wrapper decoder,
without caller-supplied decoding witnesses. It requires typed dependency,
base and recursive-step evidence; eleven source/model checks pass after a
header-rewrite repair. Independent source review approves the exact code and
reproduces all eleven checks. This candidate has not
run in HOL and does not yet provide primitive admission or default integration.
See [the gcd source report](build/workers/hol-gcd-decoder-consumer-20261008/CLOSEOUT.txt).

Source implementation progressed after the pressure refusal: the private HOL
well-founded decoder now handles constructor-field projection candidates,
requiring the existing typed conversion proof before using each result.
Nine source/model tests and independent source review pass. No HOL compilation,
proof execution or Arena outcome is claimed for this unintegrated change.
See [the decoder change](build/workers/hol-nat-wf-decoder-20261007/source-03/REPORT.txt).

A separate explicit --fuel16384 Arena profile now passes48 pure/mock tests and
independent exact-source review. It has not run a checker; the actual154-case results
below remain512-fuel results. Memory/time/cleanup limits and stop policy are
unchanged;no higher-fuel acceptance is claimed.
See [the held explicit-fuel profile](build/workers/rocq-arena-fuel16384-source-20261008/REPORT.txt).
See [the independent source review](build/workers/rocq-arena-fuel16384-review-20261008/REVIEW.json).
The source approval does not authorize a native run. The pending decisions are
whether to select this higher-fuel profile and whether fuel/time declines may
be recorded while independent tests continue. Host memory, ownership, and
cleanup failures must still stop execution. No such policy change is assumed.

Fresh human-authorized session (2026-10-08):154 complete Arena files ran through
the audited Rocq CLI:90 accepts,63 rejects and one fuel-exhaustion decline.
There are65 available inputs still unrun and four missing. All154 result and
cleanup inspections and independent retained audits pass; this is not
whole-suite success. The campaign used
default fuel512,not the16384 used by earlier broad validation. Its stopping
case,church-numerals,has the same input hash as that earlier accepted case;
the binaries/configurations differ,so this does not establish a regression.
HOL diagnostic activation is prepared but unrun in this session.
See [the fresh execution report](build/workers/parent-arena-session-20261008-01/REPORT.txt).

The following paragraphs are earlier checkpoints, retained as history.

Source progress after the timeout: the finite 223-case Rocq Arena runner has
independent source approval and 47 passing pure/mock tests; it remains unrun.
A separately reviewed HOL diagnostic source adds ten progress markers while
preserving all 123 first-seven assertions and the original proof operations.
Its fresh runtime/parent source composition now passes exact pure checks and
four negative controls plus independent composition review. No diagnostic
ML parsing, proof execution or performance measurement has occurred.
No native retry or resource sample has followed the timeout.
See [the prepared diagnostic composition](build/workers/prefix-seven-diagnostic-generation-20261008/REPORT.txt).
See [diagnostic scope and limits](build/workers/hol-prefix-seven-diagnostic-source-20261008/REPORT.txt)
and [Arena source review](build/workers/rocq-arena-campaign-review-20261008/REVIEW.json).

Latest execution (2026-10-08): the existing extracted Rocq checker accepted the
complete Arena basicDef file, checking one declaration. Independent retained
review confirms the exact run, including a documented tool-poll parameter
deviation; the original report-verifier refusal remains preserved.
See [the Rocq result](build/workers/rocq-cli-owned-basicdef-20261008-r2/NATIVE_RESULTS.json).

The expanded seven-phase HOL run timed out at the unchanged 180s limit during
Nat.eq_of_beq_eq_true, its fifth declaration. Memory passed the gate; owned
cleanup was reported verified. This is not a seven-phase proof success, and no
further heavy run or resource resample follows in this resumption.
See [the HOL attempt](build/workers/parent-prefix-seven-profile-20261008/NATIVE_RESULTS.json).
The earlier completed four-phase result below remains valid. Neither port is
complete, and broad Arena validation through the new runner is still pending.

New actual results (2026-10-08): ordinary-certificate HOL r5 passes strict
completion checking: 66 assertions, 295 events, four of thirty prefix phases,
15 admissions and 29 declarations. Runtime is 130.79s; cleanup through the
immediate observation is 3.71s of the unchanged 10s. Original ordinary
certificates are inspected, with one certified universe conversion to retain
the exact Sort Zero obligation; full type/body replay is not repeated.
See [HOL r5 result](build/workers/parent-ordinary-retained-phase4-profile-20261008-r5/NATIVE_RESULTS.json).

Rocq compiled the exact Syntax.v into a fresh 171072-byte object, including its
14 existing closed lemmas. The genuine terminal, immediate observation and
strict structural inspection pass; parent acceptance is recorded separately
without changing legacy held flags. Startup through observation took 3.49s.
See [Rocq result](build/workers/parent-rocq-syntax-execution-20261008-r3/NATIVE_RESULTS.json).
The log contains only a deprecated From Coq import warning. These are actual
proof executions, not new checker features or new Arena verdicts. Narrow
independent retained outcome reviews also pass for both completed runs.
Neither port is complete. The next useful target is real Arena checking through
the repaired ownership implementation, not a blanket rebuild of old proofs.

The following first-four-phase paragraphs describe the earlier r4 checkpoint.

The latest successful HOL fixture checks four of thirty prefix phases from
empty policy, through `Nat.beq_refl_checked`: 15 admissions, 29 declarations,
66 assertions and all 295 expected events. The 56-source closure, 22 prechecks
and 143 postchecks pass. Execution took 148.64 seconds; cleanup through the
genuine post-exit observation took 3.71 seconds within the original 10-second
allowance. Independent retained audit found no blocking issue in this scope.
See [the result](build/workers/parent-nat-retained-phase4-profile-20261008-r4/NATIVE_RESULTS.json)
and [the independent audit](build/workers/hol-retained-phase4-actual-review-20261008-r4/REPORT.txt).
This inspects the original primitive certificate, not a duplicate producer run.
It is not full-prefix, positive division/modulo, Arena-file or whole-Lean
semantic validation. Ordinary-certificate retention is a separate source-only
successor until it is actually checked by HOL Light.

The corrected Rocq environment wrapper now passes its fixed interruption and
timeout controls with genuine expected exits 65 and 66, fresh memory gates,
owned cleanup and immediate postterminal observations. The records preserve
`passed:false`: these intentional negative cases are not proof successes.
The independent retained audit and exact Syntax proof-profile activation are
separate pending steps. All earlier failed attempts remain preserved.

The following paragraphs record earlier checkpoints, not the current stop state.

Latest attempt (2026-10-08): the four-phase HOL fixture timed out during the
fourth admission at the unchanged180s cap. Its memory gate passed (normal,
216.17MiB). Partial events are not a proof verdict. Owned cleanup is reported
clean, and the actual outer process exits1; no successful completion receipt
or postterminal bound exists. No retry or new native work follows this stop.
The earlier independently audited three-phase success below remains valid.
See [the session report](build/workers/parent-low-memory-20261007/SESSION_REPORT-20261008.txt)
and [failed-attempt evidence](build/workers/parent-nat-phase4-profile-20261008/NATIVE_RESULTS.json).

The new HOL run passes strict actual validation for the first three natural-
number prefix phases, including Nat.beq:14admissions28declarations and49
fixture assertions, from an empty permission policy with unchanged HOL axioms.
All56source/22pre143post checks and277expected transcript events pass.
Execution took167.28s; cleanup, preservation and the genuine post-exit check
took4.63s within the original10s allowance. Exact evidence is in
[the proof result](build/workers/parent-nat56-cleanup-origin-repair-20261008/NATIVE_RESULTS.json).
The corrected native stop and full180s timeout controls also passed.
At that checkpoint there was no resource refusal. This is3of30prefix phases,
not full division/modulo, Arena coverage or a Lean-adequacy theorem.
Independent retained audit41aa577d confirms the result and rejects15 mutated
evidence controls. A separate child-free Rocq raw-gate observation78325f passes
normal pressure with487424000bytes; it is not a proof or full runtime release.
The cumulative fourth HOL phase retains all earlier checks and adds17
assertions; its later attempted execution times out as described above.

Independent review also found and repaired a HOL late-timeout cleanup-origin
bug. Rocq outer-entry review found two separate failure-path/invocation issues;
a fresh repair is being reviewed before native proof execution. Prior evidence
is preserved. The checkpoint paragraphs below describe earlier states.

The held HOL stop-control setup and a Rocq record-validation chronology repair
are now independently source-approved. HOL has12pure setup tests plusfive
independent checks; Rocq has11pure tests plusfive independent methods. Review
reproduced and repaired six inconsistent event sequences, without any false
proof PASS. The Rocq outer launcher/final-record binding remains incomplete.
No new native validation, compiled proof or Arena verdict follows from this
source work. See [the latest findings report](build/workers/parent-low-memory-20261007/REPORT-held-parent-boundaries-20261008.txt).

The repaired ABI is now wired into fresh source-only HOL stop-control,
Nat56 proof-profile/parent-helper and Rocq Syntax candidates. Rocq's exact
integration and all three HOL packages are independently source-approved.
No default checker, native stage or execution authority is changed.
The latest source suites pass20 HOL control methods,8 Nat56 profile methods,
40 parent-helper methods and9 Rocq wiring methods. These are not proof or
Arena results. See the plan and work log for exact immutable handoffs, and
[the detailed integration findings](build/workers/parent-low-memory-20261007/REPORT-abi-consumer-integration-20261007.txt).

A subsequent SDK/source audit also finds a page-size ABI mismatch in the
shared Darwin gate: a32-bit output object for pointer-sized vm_size_t. Fresh
source-only repairs pass11author+9reviewer mock tests and are source-approved;
fresh consumer wiring is source-only; native validation is pending. Existing byte arithmetic
already avoids speculative-page double counting. Old native observations stay
preserved but do not validate that ABI; no further use of the old gate is approved.

The latest native attempt was refused before spawning a child: normal pressure
but69,517,312free-plus-speculative bytes (66.3MiB), below the approved128MiB HOL
floor. No resample/retry or further native validation followed. The controlled
self-SIGTERM test immediately before it has strict expected-failure evidence
and verified owned cleanup; that is not a proof PASS. Both attempts are
preserved in parent-native-stop-controls-validation-20261007. Full180timeout
coverage and proof-profile release remain pending. Rocq final-lock P01/P02
repairs are independently source-approved (14author+6reviewer pure methods),
not natively validated. No new proof or Arena verdict comes from these controls.

Earlier platform checkpoint:

The repaired Darwin supervisor now passes two actual non-HOL platform cases:
clean exit and exit with a surviving descendant, both with verified cleanup
and genuine same-deadline outer-exit evidence. The original failed clean case
remains preserved. Broader FD/signal controls and proof-profile integration
are still required; old-helper HOL/Rocq/Arena execution remains held. Rocq
runner source repairs are independently approved but not natively integrated.
The WF decoder remains source-only. Prior successful proofs are preserved.

The latest Rocq composition is validated:49module compiles465closed-context
queries49recursiveaudits, independently retained-audited with198cleanchildren,
50sealedobjects and648preservedinputs. Its theorem composes actual projection
checking with indexed admission under explicit premises; it is not Lean soundness.
The exact combined HOL file candidate passes nine distinct Arena files:
four accepts and five proved rejects, plus a separate deliberate zero-fuel
decline. A custom whole-file fixture also passes the extended MH2true route.
Neither is a default-server or full-corpus result. Current work integrates the
validated lineage, repairs process supervision and extends remaining features.

Earlier checkpoints:

The fresh Base-plus-Boolean prefix run now passes:13admissions27declarations,
29assertions and all56source/22pre/143post checks, with clean90.7s execution.
Only2of30prefix phases are complete; positive division/modulo proofs remain
unvalidated. Warm-server integration separately awaits a confirmed package-load
failure-propagation repair and its native failure tests.

The newest combined-file batch passes49assertions: four actual Arena negative
files receive theorem-backed rejection, BasicDef accepts, and forced zero fuel
declines without falling through to rejection. The84.8s run passes64pre64post
proof checks, preservation and cleanup. This is focused file-API validation,
not a default server or full Arena campaign. Detailed findings and exact evidence
are maintained in build/workers/parent-low-memory-20261007/PROGRESS_REPORT.txt
and FINDINGS.txt; new source-only successors are not counted as proof results.

### Lower-Floor Validation Resumed, 2026-10-07

Actual execution now passes all45 original MH2 controls acrossfive bounded HOL
batches, plus11 environment-binding additions and32 separate decoded-input
smoke assertions. Fresh Rocq validation passes18 module compiles,176 closed
global-context queries and18 recursive audits. A proof-script placeholder error
and a HOL lexer-mode mismatch are repaired in fresh successors; failed evidence
is retained. These are focused results, not full Lean adequacy or Arena verdicts.

All85 original decoded controls now pass across21 reviewed partitions, with110
occurrences and unchanged proof postchecks. Retained aggregate895055 verifies
897 source/evidence files. The32 smoke assertions are not an exact subset and
cannot be subtracted from85. Allfour fresh fuel regressions now pass after a
harness repair that hides binary OCaml digests without weakening log checks.
The positive-fuel forwarding fix is validated on one real inductive row;
allfive dispatch branches and production integration remain separate work.
Four distinct authentic Arena whole files pass through the private adapter:
basicDef, sparse-name-index, level-index-out-of-order and complete Empty.
Explicit input axiom policies remain visible; this is not a full campaign.
The private Nat.div/mod model and producer load also pass fresh HOL validation
(47sources,22pre/143post). Positive arithmetic certificates and native routing
remain unvalidated; this is separate from the MH2 candidate, not a combined build.
The opt-in file adapter now passes17 focused predicates and a real basicDef
file, with full inherited proof checks. No server/default integration yet.
The first constructive-Nat stage failed on fixture module-alias parsing; its
child exit0 was correctly rejected by full-log checks. A fresh alias-only
repair passes all11 controls and admits one canonical Nat declaration.
The next Base-phase run passes16 controls and completes ten real admissions
from empty in71.5seconds, producing24declarations. This is phase1 of30,
not a complete arithmetic prefix or positive div/mod certificate.
Warm-server initialization and whole-session deadline handling remain explicit
source-review gaps. The combined negative-dispatch successor now passes11
checks on a complete real orphan-ctor file, including exact certificate replay
and altered-export refusals. This is a narrow owner-condition rejection route,
not a complete invalidity checker or server/default integration.
See the [detailed progress report](build/workers/parent-low-memory-20261007/PROGRESS_REPORT.txt).
See the [current resumption handoff](build/workers/parent-low-memory-20261007/RESUMPTION.txt)
and [findings log](build/workers/parent-low-memory-20261007/FINDINGS.txt).

### Source Implementation Continues, 2026-10-07

Under the unchanged resource hold, a private HOL successor now implements the
missing division/modulo recognizer contracts, certificate producer, guarded
admission and input/frontend routing. Adversarial, scoping and native-routing
fixtures are authored but unrun; independent source review catches and prompts
a modulo-fixture repair. This intentionally extends the private admission model,
so fresh kernel/schema and interface validation are mandatory. It is not part
of the shipped checker and adds no validated Arena result. See the
[source implementation report](build/workers/hol-nat-fuel-rec-source-20261007/REPORT.txt).

### Guarded Resume, 2026-10-07

The runner's terminal stop/deadline repairs pass17 runtime mock tests and
129 independent terminal scenarios under each of two Python versions. Actual
Rocq validation then compiles nine dependencies but finds an unvalidated new
projection proof-script error. A fresh one-line repair is preserved. Its next
attempt stops before any compiler because free+speculative memory falls to
63.16MiB, below the4GiB guard, despite normal pressure. Both failed attempts
have actual exit1, matching STOPPED terminal records and verified cleanup;
21 owned children in total. No new closure/audit result, HOL validation, native
comparison or Arena verdict is claimed. The repair remains uncompiled.
See the [resumption report](build/workers/parent-projection-resume-20261007/REPORT.txt).
Older chronological checkpoints below retain their original validation limits.

### Source-Only Continuation, 2026-10-05

The resource hold below remains active; no new memory check or heavy validation
has occurred. Private source now includes a reviewed Rocq literal-telescope
proof bridge (16 lemmas/eight examples), a 13-line HOL typed-head-congruence
search candidate, and 11 proposed HOL certificate environment-binding controls.
All new Rocq proof scripts and HOL fixtures remain uncompiled/unrun. No root
checker promotion or new Arena verdict is claimed. See the
[source continuation report](build/workers/parent-kernel-source-20261005/continuation-01/REPORT.txt).

### Resource Stop, 2026-10-05 12:03 UTC

The refreshed upstream snapshot at `b1d6e91d` has 223 cases, 219 available and
4 missing, including new `perf/proj-cheap-struct` and `perf/proj-lazy-struct` inputs. This is
a data inventory, not a new checker pass. The first new projection-stage sample
had normal pressure but only 1.804916 GiB free including speculative pages,
1.577118 GiB raw free and 1.373657 GiB swap. No checker started; all 223 rows remain
accounted for with 2 unattempted and 221 unselected, zero raw verdicts.

An inherited preflight bug kept sampling instead of stopping on that first
failure. The parent interrupted only its owned launcher; exit 130 and all failed
evidence are preserved, with verified owned cleanup. A fresh source04 repair
latches the first refusal and has 30 pure tests plus scoped parent review; it has
not run natively. No further heavy job or memory probe is allowed in this same
follow-up. Missing-row exit and terminal-deadline fixes also remain preserved.

Safe source work adds the HOL MH1 mutual-header transport definitions/producer,
a separately gated materializer, a DAG validation adapter repair, and an
operational projection-selection lemma. None has new compiled/HOL/native/Arena
validation. Root checker promotion and whole-kernel soundness remain unfinished.
See the [new resource-stop handoff](build/workers/parent-projection-validation/RESUMPTION-20261005-1110.txt)
and [detailed continuation report](build/workers/parent-projection-validation/FINAL_REPORT-20261005-1110.txt)
for exact source/review boundaries. The [work log](WORK_LOG.md) retains chronology.

### Earlier Validated State, 2026-10-05

The 2026-10-05 follow-up validates a fresh private Rocq composition: 113 module
compiles, 1,340 closed-assumption queries, 113 recursive audit roots and
extraction. Generated-interface review precedes 25 native suites / 114 commands,
with 228 verified owned-child cleanups. The private CLI build and all 19 boundary
controls also pass. Independent native and CLI evidence reviews are complete.
These are component-proof and executable-test results, not a whole-kernel
soundness theorem or Arena proof-file counts. The shipped checker is unchanged.

The exact private candidate attempts 27 distinct inputs from the pinned
221-case snapshot: 18 correct accepts, 2 correct rejects and 7 timeouts.
The 347 MB Init input times out at its published 500-second limit after 9,546
completed wire records, with peak sampled owned RSS of 1.54 GiB and no memory
refusal. A partial prefix is not file acceptance. The other 194 records remain
unattempted for this candidate, including four unavailable exports. Both actual
Arena selections pass independent evidence review, not whole-corpus validation.

The private HOL negative-only file API and opt-in public dispatcher now validate
three full decoded negative fixtures and a later-owner decline control. An
ordinary valid Arena fixture also passes normal, disabled and enabled public
routes with closed positive certificates bound to the full raw history and
axiom policy. The same 64 schemas are checked before/after each public stage;
repeated checks are not distinct new theorem counts. All failed loader,
lexer-guard and bytecode-expectation attempts remain preserved. There is no
default dispatcher integration or proof of full Lean equivalence.

The old native runner's final-stop limitation remains disclosed. Its fresh
three-defect repair and a stack-safe DAG candidate are source/mock-only, not
new native validation. Production promotion and major semantic proofs remain
unfinished. At that earlier checkpoint closing pressure was normal and no
resource refusal had occurred; the later refusal above supersedes that status.
See the [detailed checkpoint report](build/workers/parent-projection-validation/FINAL_REPORT-20261005-0314.txt)
and [chronological handoff](build/workers/parent-projection-validation/RESUMPTION-20261005-0314.txt).

The preserved original Arena snapshot has **220 cases**, of which216 are available,
including exact reproductions of the 347 MB Init, 597 MB Std and 2.42 GB CSLib exports.
The four missing exports are tracked individually with unresolved acquisition
blockers. There is no 128 KB input limit.

Refresh note (2026-10-01): the live Arena publication at `4c30c4ac` has **221
cases**. A separate source-pinned snapshot has 217 available inputs, including
the new 51,334-byte `perf/proj-stuck-struct` test (50-second limit). Existing
case outcomes and limits are unchanged; only the unavailable Cedar export's
bytes changed. The default 220-case snapshot and the completed runs below are
preserved, not relabeled. A protected historical-binary run on the221-case
snapshot now records18 correct accepts,2 correct rejects and6 published-limit
timeouts in its26 selected performance cases;195 cases are unselected. It does
not test the new private composition and is not a complete221-case run. Snapshot:
`build/workers/parent-arena-refresh-20261001/snapshot-report.json`; retained run:
`build/workers/rocq-arena221-resume-source-20261004/resource-launcher/real-perf26-resume-01`.

| Port / completed full run | Correct accepts | Correct rejects | Allowed either | Declines | Timeouts | Wrong verdicts | Missing |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Rocq, complete primitive validators | 108 | 69 | 18 | 12 | 8 | 0 | 5 |
| Rocq, positivity repair + explicit fuel 4096 | 113 | 71 | 18 | 1 | 12 | 0 | 5 |
| Rocq, proved Nat dispatch + explicit fuel 16384 | 115 | 71 | 18 | 0 | 11 | 0 | 5 |
| Rocq, shipped String repair + DAG/depth/index + fuel 16384 | 116 | 71 | 18 | 0 | 11 | 0 | 4 |
| Rocq, shipped persistent admission + fuel 16384 | 117 | 71 | 18 | 0 | 10 | 0 | 4 |
| Rocq, shipped scheduler + persistent admission + fuel 16384 | 116 | 71 | 18 | 0 | 11 | 0 | 4 |
| Rocq, shipped reducibility hints + fuel 16384 | 117 | 71 | 18 | 0 | 10 | 0 | 4 |
| Rocq, shipped opposite-projection retry + fuel 16384 | 117 | 71 | 18 | 0 | 10 | 0 | 4 |
| Rocq, shipped Nat-probe ordering + fuel 16384 | 117 | 71 | 18 | 0 | 10 | 0 | 4 |
| Rocq, shipped eager policy + guarded probes + fuel 16384 | 116 | 71 | 18 | 0 | 11 | 0 | 4 |
| Rocq, shipped independent WHNF limits + application orientation + fuel 16384 | 117 | 71 | 18 | 0 | 10 | 0 | 4 |
| HOL Light, canonical guards + native Nat literals | 39 | 6 | 1 | 169 | 0 | 0 | 5 |
| HOL Light, parameterized families + metadata order repair | 52 | 6 | 1 | 156 | 0 | 0 | 5 |
| HOL Light, indexed families + symbolic environment specialization | 65 | 6 | 1 | 143 | 0 | 0 | 5 |
| HOL Light, neutral K + theorem specialization caches | 67 | 6 | 1 | 141 | 0 | 0 | 5 |
| HOL Light, projections + guarded primitive admission | 72 | 6 | 1 | 137 | 0 | 0 | 4 |
| HOL Light, quotient + structure eta + six primitive contracts | 83 | 6 | 2 | 125 | 0 | 0 | 4 |
| HOL Light, syntax-sharing caches + seven primitive contracts | 85 | 6 | 2 | 123 | 0 | 0 | 4 |
| HOL Light, text literals + eight contracts + structure-major | 86 | 6 | 2 | 122 | 0 | 0 | 4 |
| HOL Light, higher-order recursive fields | 88 | 6 | 2 | 120 | 0 | 0 | 4 |
| HOL Light, iterative validation + nonindexed mutual + raw history | 87 | 6 | 2 | 121 | 0 | 0 | 4 |
| HOL Light, indexed mutual + raw function + polymorphic HAdd | 86 | 6 | 2 | 122 | 0 | 0 | 4 |
| HOL Light, closed computations + checked add-body reuse | 87 | 6 | 2 | 121 | 0 | 0 | 4 |
| HOL Light, guarded early proof irrelevance | 87 | 6 | 2 | 121 | 0 | 0 | 4 |

The Rocq full runs use a 30-second exploratory cap, at fuel 512
(`build/reports/rocq-arena-primitive-complete.json`) and 4096
(`build/reports/rocq-arena-fuel4096.json`) and 16384
(`build/reports/rocq-arena-dispatch-fuel16384.json`). The HOL runs use a
10-second case limit. These are not the full upstream performance budgets.
HOL's worker wall timeouts return exit 2 and are included in the Declines
column, not the outer-harness Timeouts column. The preceding closed-computation HOL attempt
has 61 such worker timeouts and 60 other declines. It attempted all 216 available
inputs, including Init, Std and CSLib, without a wrong verdict or integrity
failure. Only `tutorial/091_projProp3` changes classification from the preceding
run: its 10-second decline becomes an 8.98-second acceptance. The preceding
`tutorial/112_structEta` timeout remains. This is an observed deadline change,
not a causal performance claim.
Tutorial 055 passes a longer focused proof test but still times out at 10 seconds.
See `build/reports/hol-full-main-arena-retry-20261001T041046Z/arena.json` and
`attempt-audit.json`. All 179 frozen source/bytecode files, 56 startup-closure
inputs and 4,119 scoped runtime files held; 250 audit checks pass, and all 216
clients and the owned server are reaped. The initial zero-case attempt's
report-only PATH/observer fault remains preserved separately. None of these
results claim that the optional Bool/shiftLeft APIs accelerate default checking.

The latest guarded early-irrelevance integration has the same classifications,
decline categories and diagnostics for all 220 records. Its fresh 14-group replay
passes 219 assertions: ten candidate groups / 158 assertions and four explicitly
historical control groups / 61 assertions. The preserved twenty-suite regression
also passes under its unchanged 900-second cap. All 124 older job definitions
are retained exactly, with fourteen additions giving 138 registered jobs; this
is not a complete fresh 138-group replay. The full irrelevance fixture accepts
in 15.161s under its published 50-second cap, but remains a timeout in the
separate ten-second inventory run. Source/runtime checks and owned-process
cleanup pass; the full Arena tree's sampled peak RSS is 951,877,632 bytes.
See `build/workers/hol-early-irrelevance/guard-repair-01/main-integration-02/final-audit.json`
and its `seal.json`. No new logical rule, axiom or causal speedup is claimed.

The newly integrated indexed-mutual/raw-function/HAdd model has 29 native and
11 admission clauses. Fresh main replay passes eight selected groups, including
all twenty existing native suites, old rule prefixes, mixed original-history
certificates and 106 power assertions. Prepared conditions separately pass
65 focused and 25 boundary assertions. See `build/reports/hol-indexed-main-audit.json`.
The fresh frozen-main matrix now passes all 94 selected existing groups, with
zero failed or unrun jobs and 278 source identities held. This excludes the
three separately tested closed-computation groups and the newer Bool/shiftLeft
groups. The unchanged caps are 180s per ordinary group and 900s for preserved-full;
the latter completes in 684.219s. See
`build/reports/hol-main-matrix-20261001T022118Z/summary.json`.
The full inventory attempt above is not a passing Arena suite: declines and
missing files remain gaps.
The latest Rocq main executable integrates separate normal/eager WHNF limits
and upstream application-domain comparison order. Fresh actual-main build,
twenty native suites and an 88-module audit pass, and all 216 available Arena
cases are attempted: 117 accepts, 71 rejects, 18 either outcomes, ten timeouts
and four missing inputs. The sole classification change from preceding main is
grind-ring-5 returning to acceptance; no causal speedup is claimed. Evidence:
`build/workers/rocq-whnf-orientation/evidence/actual-main-integration/closure-20261001T062440Z/summary.json`.
The additive universe/substitution proofs now pass a fresh 24-suite / 109-step
main build and 96-module audit while leaving the checker binary byte-identical.
The 33 public component theorems cover normalization soundness, completeness,
sufficient fuel, universe instantiation, and commutation with term lifting and
capture-avoiding substitution. The two newest native suites pass 3,366,071 and
7,264,342 assertions. These syntactic and universe-semantic results do not prove
term typing preservation or whole-kernel soundness. Evidence and exact scope:
`docs/ROCQ_UNIVERSE_SOUNDNESS.md`.

The separately audited `rocq/ProjectionPreservation.v` adds four closed
projection-control theorems and sixteen small regression proofs. It protects
retention of the original major when a projection gets stuck, callback selection,
field offsets, and error/decline propagation. The runtime binary is unchanged;
this is not a result for the new Arena projection file.

At the unchanged CLI default fuel of 512, that same binary correctly decides
all 141 tutorials (94 accepts, 47 rejects). A separate frozen-binary full run
records 110 accepts, 71 rejects, 18 either, eight fuel declines, nine timeouts
and four missing files. Seven high-fuel accepts become default-fuel declines.
Use the explicit profile above to reproduce the high-fuel setting; these remain
30-second exploratory limits, not Arena's longer published performance budgets.
See `build/workers/parent-default-tutorial/README.md` for both default-fuel runs.

Rocq correctly decides all 141 tutorial cases. The newer run includes the
positivity repair and correctly rejects all 71 expected-invalid cases.
The preceding main eager-policy/guard-order build passes eighteen native suites
(79 steps) and an independent 84-module kernel audit. Its exact 3,903-record
String prefix accepts in 18.285s and shared-subterm in 1.189s. Its full 216-input
Arena run has one observed deadline regression: grind-ring-5 times out at 30s,
having accepted in the preceding run and private candidate. This is retained
without a causal timing claim. No wrong verdict or operational fault occurs.
See `build/workers/rocq-eager-policy/evidence/main-guard-integration/final-seal/summary.json`.
The higher fuel also turns several quick declines into timeouts; the default
remains 512 while performance work proceeds. The first full-budget Init/Std
runs timed out at 500/590 seconds after at least 1,700/2,000 records were checked;
see [large-input results](docs/ROCQ_LARGE_RUNS.md). These are kernel attempts,
not just transport scans.

The Arena infrastructure suite separately passes all 52 tests against the full
3.2 GB local corpus, including streaming metamorphic generation and comparison.
The run takes 502.473s; peak observed process-tree RSS is 2,754,912 KiB. Streaming
avoids whole-file record lists but memory can depend on the largest record.
This is pipeline validation, not additional kernel acceptance. Evidence:
`build/reports/arena-streaming-main-20261001T044828Z/report.json`.

The preceding hint-enabled executable `acd3d008...` passes fifteen native suites
(66 bounded steps) and an independent 75-module audit. Its single full inventory
run has 206 decided outcomes and ten timeouts; `grind-ring-5` is the only changed
classification, accepting in 28.58 seconds after the preceding run's 30-second
timeout. This is not a repeatable speedup claim. All 216 available inputs were
attempted, no wrong verdict was observed, and all process/source holds passed.
See `build/reports/rocq-shipped-hints-arena-30s.json` and
[the integration report](docs/ROCQ_HINTS.md). The separate full-Init attempt
still times out at 500 seconds after 9,546 completed Wire admission records.
It passes the old target and reaches `Int64.toBitVec_div`; that last started
theorem is not counted as accepted. See [the large-input record](docs/ROCQ_LARGE_RUNS.md).

The preceding shipped Rocq executable was tested on all 216 available
inputs at fuel 16384 and a 30-second exploratory cap. It records 205 decided
outcomes (116 correct accepts, 71 correct rejects, 18 allowed-either), 11
timeouts and four missing inputs, with no wrong verdict or integrity failure.
This is direct evidence for executable `2daf6e33...`, not an inference from
a separately built binary. Its outcomes match the two frozen composition
baselines; all child processes were reaped. The report is
`build/reports/rocq-shipped-dag-arena-30s.json`. Neither the timeouts nor the
missing files pass. The native regression counts below are separate evidence.
The newer persistent-admission executable `cd06e5a0...` passes its 74-module
kernel/source audit and twelve native suites. Its separate all-216-available
run records 117 correct accepts, 71 correct rejects, 18 either outcomes and ten
timeouts, with four inputs still missing. `grind-ring-5` accepts after 2,273
declarations in 28.1 seconds in this run. This single deadline crossing is not
a causal or repeatable speedup claim. There are no other classification changes,
wrong verdicts, checker faults or integrity failures. Evidence is
`build/reports/rocq-shipped-persistent-arena-30s.json` and the matching summary.

The subsequent scheduler integration produces executable `853e4eae...`, with
unchanged Gallina extraction. All thirteen native suites (60 bounded steps)
and a fresh independent 74-module audit pass. Its exact-binary full Arena
attempt records 116 correct accepts, 71 correct rejects, 18 either outcomes,
11 timeouts and four missing inputs. `grind-ring-5` newly times out against both
preceding references. This is an observed deadline regression, not a wrong
logical verdict or evidence of a repeatable slowdown. Init remains in scheduling
at the short cap, unlike the private composition. See
[scheduler evidence](docs/REPLAY_SCHEDULER.md).
A full 500-second Init attempt on frozen `cd06e5a0...` times out after at least
3,200 admitted records. The last progress anchor is not an exact stall location;
neither the longer attempt nor the improved scheduler establishes an Init pass.
The subsequent current-853 Init attempt, with progress on every batch, admits
3,224 records and starts `Int64.toBitVec_shiftLeft` before its 500-second timeout.
The stack sample was truncated despite exit zero; its reported percentages are
withdrawn. Exact progress and later direct callback diagnostics are separate
evidence. See [core profiling](docs/ROCQ_CORE_PROFILING.md).

After batched substitution, a separate **213-case nonlarge run** at fuel 16384
and a 30-second cap records 115 accepts, 71 rejects, 18 either outcomes and nine
timeouts, with no declines or wrong verdicts. Seven cases are explicitly
unselected. `shared-subterm` accepts in 1.09 seconds and `church-numerals` in
0.04 seconds in that run. This selected run does not replace the full-run table.
All nine remaining performance cases also time out in a separate local run
at their published 50--390-second budgets, with unchanged input/executable
hashes. See `build/reports/rocq-batched-performance-upstream-limits.json`.
A proved Nat-dispatch optimization has since been built and tested on all 215
then-available inputs. Its full run has the same 204 correct verdicts and nine
performance timeouts, plus Init and Std timeouts. It does not solve those stalls.

An earlier wrong Init rejection came from overly strict safe declaration-group
metadata handling. That is fixed, with all 1,824 Init.Prelude declarations
accepted in a selected rerun. Init and Std reached the 60-second exploratory
cap, not an input-size limit.

Additional Rocq validation: 237 baseline-gated metadata mutations/controls,
12 authentic unsafe/mutual declaration export tests, and 148 selected
filename-neutral tutorial/semantic cases pass. These are separate local suites,
not additional Arena cases or a claim that the full Arena suite passes.
The HOL transport also uses dependency ordering, with 40 focused bridge checks;
unsupported nested, unsafe or broader raw mutual admission remains an explicit decline.
HOL's neutral-K integrated checkpoint passes 727 assertions. Its earlier
97-case export mutation rerun accepts all seven baselines, then records 45
accepted controls, six malformed-input rejections and 46 declines. A separate
family audit accepts all ten baselines; its 41 cases produce ten accepts, two
transport rejections and 29 declines. No wrong verdict was observed within
those bounded suites. Declines are gaps, not passes; see the
[family review and runtime records](docs/HOL_FAMILY_REVIEW.md).
The family Arena run is recorded in
`build/reports/hol-arena-family.json`, with its loaded project snapshot in
`build/reports/hol-family-runtime.json`. Internal worker timeouts are included
in code-2 declines, not the harness's outer-timeout column.
The indexed run and startup identity are `build/reports/hol-arena-indexed.json`
and `build/reports/hol-indexed-runtime.json`. Of its 143 declines, 61 are valid
cases, 65 are expected-invalid cases, and 17 allow either verdict. The new
indexed audit accepts all seven baseline gates; 67 cases produce 15 accepts,
four transport rejections and 48 declines, including two valid Prop-only
controls needing a proof-search repair. See `docs/HOL_INDEXED_REVIEW.md`.
The K run and startup identity are `build/reports/hol-arena-k.json` and
`build/reports/hol-k-runtime.json`. Neither declines nor missing inputs pass.
The newer projection checkpoint passes 1,384 native assertions. Its 216-input
run and loaded identity are `build/reports/hol-arena-projection-primitive.json`
and `build/reports/hol-projection-primitive-runtime.json`. Structure eta,
quotient integration and subsequent proof-search edits are not covered by that
loaded checkpoint. The other table rows used the earlier 215-input inventory.
Quotient support now passes 59 signature/model checks and 74 focused native
checks. All six exact Arena quotient tutorials accept in a separate 30-second
selected run; its other 214 cases are explicitly unselected. This does not
replace the full-run table. The newer quotient/structure full run is
`build/reports/hol-arena-quotient-structure-10s.json`, paired with
`build/reports/hol-quotient-structure-runtime.json`; all 216 available inputs
were attempted, with no wrong verdicts or integrity failures. Its native
regression checkpoint passes 1,450 assertions, separately from the 74 focused
quotient checks. The quotient mutation audit accepts eight baseline gates and
25 controls; one malformed input is rejected and 42 negatives decline. These
declines are not refutations. See [quotient checking](docs/HOL_QUOTIENTS.md) and
[the quotient audit](docs/HOL_QUOTIENT_REVIEW.md).

Immutable syntax-sharing caches and guarded Nat.pow contracts have since been
integrated locally; the combined native checkpoint passes 1,570 assertions.
The fresh 216-input Arena attempt records 85 accepts, six rejects, two allowed
either outcomes, 123 declines and four missing inputs, with no wrong verdicts
or integrity failures. Its report is `build/reports/hol-arena-cache-pow-10s.json`
and loaded-source identity is recorded in `build/reports/hol-cache-pow-runtime.json`.
The permanent syntax suites separately reproduce 27,051 quotation checks and
13,523 bridge checks against the integrated sources.
Typed text interfaces and string literal checking are now integrated too,
including the reviewed quotient-major dispatch repair. The exact private
sources subsequently integrated pass a 16-marker native run with 1,181,651
assertions, chiefly exhaustive UTF-8 boundary tests; 22 export fixtures meet
expectations and all six selected Arena quotient tutorials accept. The rebuilt
integrated frontend passes 61 checks. These results do not replace the historical
full-run table or make its 123 declines into passes. See
[string checking and evidence](docs/HOL_STRINGS.md).
Guarded Nat.shiftLeft admission and nonrecursive structure-major expansion are
now integrated too. Their exact combined source snapshot passes all 18 native
suite markers and 1,181,728 assertions, chiefly the same UTF-8 boundary checks.
Three shift-left export controls meet expectations, authentic Arena 075 accepts
in a selected run, and the rebuilt frontend passes 67 checks. The subsequent
full Arena run attempts all 216 available files: 86 accepts, six rejects,
two allowed-either outcomes, 122 declines and four missing inputs. The only
classification change from the earlier cache/pow run is Arena 075 accepting.
Of the declines, 39 are internal ten-second timeouts; the other 83 are checker
declines. No wrong verdict, operational fault or integrity failure was observed.
Reports are `build/reports/hol-extensions-full-arena-10s.json` and
`hol-extensions-full-runtime.json`. The worker is stopped and reaped.
See [recursor-major checking](docs/HOL_RECURSOR_MAJOR.md) and
[primitive contracts](docs/HOL_PRIMITIVES.md).
The subsequent single-family higher-order recursive-field extension is also
integrated locally. Its exact combined sources pass all 19 native suites
(1,181,788 assertions, mostly the same UTF-8 sweep), preserve all three shiftLeft
export controls and accept authentic Arena 121-124 in a selected run. The two
reducible-constructor cases 119/120 still decline. Its fresh full-Arena run
attempts all 216 available inputs: 88 accepts, six rejects, two allowed-either
outcomes, 120 declines and four missing inputs. Cases 121 and 123 are the two
newly accepted files at the ten-second cap; 122 and 124 need longer, as shown
by the separate selected run. The declines include 47 internal timeouts and
73 other checker declines, not passing tests. No wrong verdict, operational
fault or integrity failure was observed; the server is stopped and reaped. See
[higher-order fields and evidence](docs/HOL_REFLEXIVE_FIELDS.md).
An iterative syntax validator has since replaced the fixed 512-level guard.
Its exact integrated source passes 20 native suites and 4,170 new focused checks;
the six formerly depth-limited Arena inputs now reach the 30-second wall cap,
not acceptance. See [syntax validation](docs/HOL_SYNTAX_VALIDATION.md). This
selected attempt does not replace the historical full-run table.
Before integration, the cache-only candidate passed 1,524 native assertions,
27,051 quotation checks, 13,523 translation checks, and a separate full Arena
attempt with 85 accepts, six rejects, two either outcomes, 123 declines and
four missing inputs. No verdict or proof fuel is cached. The 4,096-entry limits
are not byte-memory bounds; the current runner releases each child after its
case. Reproduce syntax comparisons with
`python3 tests/hol_syntax_cache/run.py quotation` and the `bridge` phase.

Rocq's implementation is executable Gallina with kernel-checked helper lemmas
and computational regressions, **not yet a proof of overall typing soundness**.
HOL acceptance certificates prove the currently encoded rules, not equivalence
of those rules with Lean. See [the trust audit](docs/TRUST_AUDIT.md).
The general [batched-substitution refinement](rocq/SubstitutionProof.v) is proved
for arbitrary expressions, cutoffs and replacement lists; it is not an overall
checker soundness proof. The [primitive audit](docs/PRIMITIVE_AUDIT.md) documents
an inherited text-conversion incompleteness and trusted-environment boundaries.
The separate [environment-index refinement](rocq/EnvironmentIndex.v) preserves
list lookup for every hash function, including collisions and duplicate-name
shadowing. It is now used by the default checker together with DAG admission,
depth-keyed caches and an early-header guard; their combined theorem preserves
the complete result of the corrected ordinary checker. See
[the runtime and its proof boundaries](docs/ROCQ_DAG_RUNTIME.md).
An earlier private hybrid-index candidate additionally proved full-result refinement
and gives 115 accepts, 71 rejects, 18 either outcomes, 12 timeouts and four
missing inputs on the 216-file inventory. All 237 metadata and 47 coherent-name
checks passed. That standalone candidate was not adopted at that checkpoint;
see `WORK_LOG.md` for the separate candidate identities. The later combined
runtime is now integrated, as described above.
The newer combined DAG/depth/index candidate records 116 accepts, 71 rejects,
18 allowed-either outcomes, 11 timeouts and four missing inputs on all 216
available files at a 30-second exploratory cap. App-lam is the sole newly
decided comparable case; there are no newly wrong or undecided comparable cases.
That full run remains evidence for its historical private candidate. Evidence is
`build/reports/rocq-private-combined-arena.json`. All 216 native children were
reaped; the sampled peak process-group RSS was 3.098 GiB. Full published library
budgets and the later String-ordering repair are not covered by this run.

The newer String-corrected DAG/index/depth/cheap-header sources are now integrated
and rebuilt locally. Their completed private verification covers 68 Gallina
modules, nine native regression matrices and independently linked old/new
String observations. The project rebuild passes all nine suites with stable
hashes and reaped children; its separate 68-module kernel/source audit passes.
The frozen candidate and exact rebuilt default binary have now both completed
their full available-corpus attempts with matching outcomes. The 11 timeouts
and four missing files still prevent a passing complete Arena suite.

Persistent environment/index admission has subsequently been integrated and
rebuilt. Its Gallina proofs preserve complete results for declaration streams
and establish rollback on rejection or decline. Twelve native suites pass,
including collision/shadowing, full-result, stream, metadata, String-ordering
and true nested-inductive restoration checks. The independent 74-module audit
also passes. This does not establish whole-checker soundness, eliminate the
remaining performance bottlenecks, or make the ten new-binary Arena timeouts
and four missing inputs pass. See [persistent admission](docs/ROCQ_PERSISTENT.md).

The earlier scheduler-plus-persistent build passes thirteen native suites and
the same 74-module independent audit. These include 2,006 old/new scheduling
comparisons in addition to the logical checker suites; transport equivalence
is not a logical soundness proof.

The preceding opposite-projection retry build `b7812ef8...` separately passes
fifteen native suites (66 bounded steps), the independent 75-module audit and
sixteen closed-assumption queries. Its fresh 216-input Arena run has the same
classifications as the hints predecessor. A separate full Init run still times
out at 500.039666 seconds, confirming 7,842 admission records and last starting
`Array.toList_reverse.go._unary`. The hints predecessor confirmed 9,546 records.
This observed loss of progress is not hidden or treated as a controlled causal
benchmark. The ordinary strategy changed; old same-fuel/error equivalence is
not claimed. See [the complete validation record](build/reports/rocq-shipped-projection-validation.md).

The latest Nat-ordering build `efd4d266...` also times out on full Init at
500.019579 seconds, with 3,902 completed Wire admission records. The last
started, not accepted, declaration is
`String.utf8EncodeChar_eq_utf8EncodeCharFast`. This further loss of progress
against 7,842 records is retained as a regression observation, not a controlled
causal timing comparison. The full input and binary hashes remain unchanged.
See [the bounded-run record](docs/ROCQ_NAT_ORDER.md).

The opt-in HOL theorem API for `Nat.beq` and `Nat.ble` is now integrated with
27 registered test groups. Its fresh frozen-main replay passes all 27 groups
and 1,185 assertions at unchanged 180-second caps, with 282 source pins stable
and all child processes reaped. The sealed audit is
`build/workers/hol-bool-derived/evidence/fresh-main-native-audit.json`.
It does not enable default proof-file
dispatch. The composition registry now contains 124 groups, preserving every
previous job and limit; registration is not a claim that all 124 have passed
on the current sources.

The opt-in contextual `Nat.shiftLeft` theorem/API and separate ten-group runner
are also integrated. The fresh frozen-main matrix passes all ten groups and
357 assertions; ten main offline tests and 64,233 separate pure budget
assertions pass. The native audit is
`build/reports/shift-left-main-audit-20261001T032945Z-8917/main-matrix-audit.json`.
Its output-size
preflight is only a resource guard, never evidence of a logical judgment.
Run it with `python3 -B tests/hol_shift_left/run.py`; it does not change the
shared registry or default proof-file dispatch.

The private Rocq eager-policy candidate passes the full build, seventeen native
suites and independent kernel audit, and accepts the exact 3,903-record String
prefix. Its first all-216 Arena run has 116 accepts, 71 rejects, 18 either
outcomes and eleven timeouts, with four missing inputs. `perf/shared-subterm`
newly times out against main's acceptance. This regression blocks integration;
the candidate's prefix success is not a full Init pass. Main remains `efd4d266...`.

The HOL implementation now also includes safe nonindexed mutual inductives and
bounded raw constructor-type checking. Every frontend acceptance carries a closed
certificate for the exact decoded input history, its explicit axiom policy and
the canonical environment. Integration caught and repaired a declaration-table
ordering mismatch without discarding raw claims or relaxing semantic metadata.
Sixteen private proof/composition groups and the 20-suite preserved native matrix
(1,185,958 assertions plus three invariants) pass on the composed sources.
The current shared transport passes 67 checks; fourteen portable-runner tests
also pass. Focused project-directory runs and a fresh full Arena comparison are
separate from those results. Safe nonnested indexed mutual blocks are now
integrated; nested/unsafe blocks and general raw telescopes remain incomplete.
See [input-history and mutual checking](docs/HOL_INPUT_HISTORY.md)
and [the reproducible tests](tests/hol_composition/README.md).

Implementation is in progress; neither port is complete. Consult the build/test
records and feature ledger. No Solidity code has been changed, and nothing has
been committed, pushed, or published.
