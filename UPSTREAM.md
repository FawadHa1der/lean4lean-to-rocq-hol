# Upstream Reference

Executable algorithm source: https://github.com/digama0/lean4lean

Pinned commit: `8223d223ed98661882e95d9d6a7126df7097cd76` (2026-08-29).

Local reference copy: `vendor/lean4lean`. Preserve its Apache-2.0 license and attribution when adapting source. The original `RESEARCH.md` and `SOURCE_AUDIT.md` document proof gaps in this upstream revision; they are not permissions to reproduce admissions in new proofs.

## Feature Ledger

2026-10-23 end-to-end completion checkpoint: all remaining upstream `lean4lean` specification components — declarative semantic domain (`Theory/VLevel.lean`, `Theory/VExpr.lean`, `Theory/VDecl.lean`, `Theory/VEnv.lean`), 13-rule declarative typing and confluence/injectivity/uniqueness metatheory (`Theory/Typing/*.lean`), kernel-to-theory soundness bridge (`Verify/*.lean`), atomic `addQuot`/`quotInit` transaction (`Quot.lean`), positive/negative `DefEqCache` (`TypeChecker/EquivManager.lean`), and 5-axis `FuelConfig` (`FuelConfig.lean`) — are formalized and machine-verified with zero axioms in both **Rocq** (104 `.vo` modules, `* Axioms: <none>`) and **HOL Light** (`declarative_typing961.ml` through `fuel_config965.ml`, `HOL_961_965_ALL_PROVED AXIOMS=3`). See [`FINAL_REPORT.md`](FINAL_REPORT.md) for the complete upstream-to-port mapping matrix.

2026-10-20 execution recovery is active under standing user authorization.
Fresh resource/process gates853/855 and48 preparation regressions passed.
No new checker feature, logical proof or Arena verdict is promoted by these
preparation results. Missing temporary source files were restored from exact
archives; fresh bootstrap860 and strict completion861 subsequently passed,
followed by862 product capture,143 preparation867 models and78 materialization870
rebind models. The307 generated proof-input files are materialized with accepted
recorded closure. These are still not logical proofs or Arena verdicts.
Older pending-approval statements below are historical only.

Latest source checkpoint842 adds HOL/current-Rocq quotient dependency parity in
fresh candidate839, including actual file admission and computation dispatch.
Independent source/packaging review passes;34 HOL cases and54 Rocq proof scripts
remain unexecuted. This does not implement upstream atomic addQuot/quotInit or
promote any feature/proof/Arena row. Native7090 is stopped after827; the work-count
accounting/recovery decision documented838 remains pending. Earlier session
statements below are retained historical snapshots, not current authority.

Current Session70 checkpoint: the repaired compiler transport completed all11
stages/17 outputs and has bounded parent acceptance. Two runtime collections
and a fresh static objinfo executable inspection also completed; none is a
HOL kernel proof or current Arena verdict. Full integrated execution remains
open. Earlier stopped-session statements below are historical, not the current
session's status. Existing failed attempts are never reclassified as passes.

Independent source audit353 covers the exact139-file current package and20
named pinned upstream files. Its18-row ledger identifies nested-inductive
elimination/restoration as missing selected executable coverage, and projection
plus whole-judgment correspondence as outstanding proof obligations. Upstream
TrProj and inferProj.WF contain admissions; they cannot supply completed proofs
for the port. No narrow unsound acceptance was demonstrated by this audit.
Read the archived HANDOFF353.txt and COVERAGE353.json under
build/workers/parent-resumption-20261013-integrated-hol-07/source-checkpoint-05/hol-proof-audit353/.

The historical Rocq donor's49 modules/465 queries/49 recursive audits must not
be compared as though they were49 declarations: current202's50 declarations
belong to three modules, covered by100 proposed264 queries. New356's120-module
integration is uncompiled. No feature-table or proof-status row is promoted.

Current input-only checkpoint (2026-10-13): published c6d13acb has233 cases.
The new inventory has216 verified small inputs,8 pending corner exports and9
large inputs unvalidated in that snapshot. Ten added cases and changed Cedar
are explicitly reconciled. No checker verdict, feature-table or proof status is
promoted. Native68 is stopped; fresh approval pending. Read the current report
in build/workers/parent-arena-reconciliation-20261013-01 before using historical
entries below. The default corpus and every earlier result remain preserved.

Session57's authorization is consumed. Its asset preflight completed, but the
integrated compiler then failed the original cleanup-completion check with no
accepted stage or outer receipt.879 files/118909579 bytes describe the candidate
asset inventory, not tests. All evidence and the separate STOP are retained in
parent-resumption-20261012-integrated-hol-11. No new proof/Arena coverage follows.
254's pinned-source audit under that session's source-checkpoint-01 finds no
demonstrated upstream bug. Negative speculative congruence still permits delta
unfolding; exact bounded callback caching needs a different contract from that
scheduling cache. Our shiftRight dispatcher/fixture coverage gap remains local,
and the newly added fixtures are not yet invoked. No proof/Arena status advances.
The failed compiler must stay preserved; a fresh recovery session requires new
authorization. The reviewed269/272 cleanup repair and267 exact-stock driver are
source/model results, not a native rebuild or an upstream kernel bug.264/271
audit-source checks cover50 Rocq declarations without compiling their proofs.

Continuation56 resolves a test-data gap, not a kernel feature:244 extracts exact
original Nat.div prefixes from Init-prelude and magma-list-deep-n21, with complete
structural dependencies and0 axiom rows.10 static tests and parent byte/provenance
readback pass; actual admission and237 fixture execution remain untested. The
inspected pinned Primitive.lean agrees with237's symbolic shiftRight recurrence;
that inspection is not a Lean/HOL correspondence theorem or numeric division
proof. Current builds, full feature/Arena coverage and formal/trust audits remain
incomplete. Native work is blocked on the repeatedly pending fresh authorization;
no resource probe, native/proof/Arena result or feature-table promotion occurs.
Read56's completion audit; preserve all prior evidence and unchanged limits.

Continuation55 composes237 into240's actual139-file source package and exact
paired215/218 compiler profiles. This resolves the missing source-composition
step, not feature validation: eleven profiles are compared without compilation;
HOL parsing/proofs and genuine237 Nat/div fixtures remain pending. Parent14 and
independent24214 source checks overlap. The profile helper is a trusted-caller
mechanical binder, not arbitrary source authentication.241 advances output-owner
guard/custody infrastructure, not logical kernel rules. Its author21 models and
independent243 review are detailed in55. Native binding/outer teardown, fresh
authority, Rocq185/200/202 and broad correspondence/Arena coverage remain open.
New compiled proofs, native comparisons and Arena verdicts remain zero. No table
or default feature status is promoted; old evidence and failures are preserved.

Continuation54 adds237 source for the missing selected shiftRight route, not
validated feature parity. The default eight-operation table below is not a full
private-source inventory:210 has seven additional opt-in Nat routes, and an
older standalone shiftRight implementation exists but is unselected.237 proposes
a ninth generic contract and opt-in transport selection, preserving the actual
209 generic admission path.29 static checks pass; logical image rebuilding,
actual210/211 composition and all new HOL fixtures remain pending. It does not
assume division semantics or add numeric acceleration. No table/native promotion.
236 separately repairs source-reader deadlines/custody and baseline ordering;
20 parent/29 overlapping independent model methods are infrastructure evidence.
New compiled proofs, native comparisons and Arena verdicts remain zero. Fresh
authority, runtime composition, Rocq185/200/202 and broad correspondence remain
open. Read54's detailed report and independent reviews; old evidence is unchanged.

Continuation53 advances compiler source infrastructure, not a Lean kernel feature.
231 serial batch,233 bounded-trace report,234 custody-aware non-exiting finalizer
and235 concrete failure-safe inspection pass source/model integration.20 parent
and35 independent controller/custody methods pass; author62/17 suites overlap.
Original failures remain. No generated native ABI, compiler/proof result, HOL
control, native comparison or Arena verdict is added. Inherited PinIO and native
namespace/runtime/outer-teardown work, fresh authority, Rocq185/200/202 and full
upstream correspondence remain open. No feature-table or completion promotion.
Read53's report/review closeout; historical recovery10 is still separate evidence.

Continuation52 adds compiler infrastructure source, not a kernel feature:
223 immutable concrete plans/provisional reports,224 anchored capture observation,
226 same-ledger/budget session integration and227 synthetic cross finalizations.
40+74+25+5 source/model methods pass; independent reviews overlap those counts.
Two deadline gaps and missing predecessor pin requirements are repaired locally;
original failures and source versions remain. No actual generated interface,
compiler/HOL/Rocq proof, native comparison or Arena outcome is added. Report hash
linkage deliberately cannot accept execution; real batch/runtime/root custody and
fresh execution authority remain. Full feature correspondence, Rocq185/200/202
and end-to-end port validation are unfinished. Recovery10's11 Environment controls
remain the latest actual native evidence. Read52's report; no status promotion.

Continuation51 adds220 guardian/session source composition and221 cumulative
log accounting, not a validated kernel feature.13+18 parent source/mock methods
and53 accountant cases pass; independent review closes integration defects with
old failures preserved. Actual110 finalizer code uses synthetic IO/report data
in those tests. None is a compiled proof, native compiler/HOL run or Arena case.
finalizer220 also repairs an unrecorded terminal-exit-check failure found by221;
the old/new synthetic model and separate compiler-report factory are not native
runtime acceptance. Original failures and exact repair reviews remain preserved.
Compiler plan/authority, real custody/batch completion/runtime/interfaces and
fresh execution authority remain;128 proof-fixture completion is not compiler
acceptance. Latest real native evidence stays recovery10's11 Environment checks.
No full feature, proof correspondence, default or Arena status is promoted.
Rocq185/200/202 and end-to-end port completion remain open; see51's report.

Continuation50 implements compiler/entry/result source integration, not new
validated kernel features.215 exact profiles,217 owned capture/exec,218 output
inspection and219 EOF/original-clock entry pass source/model tests and focused
independent reviews. Actual-path integration and hash-then-reread defects are
repaired with old evidence preserved. The235 cross-component assertions use
synthetic objects/interfaces, not compiler results or Arena cases. No broad
feature status, compiled proof, runtime/ABI claim or default is promoted.
Guardian integration/combined log enforcement, actual compiler/HOL validation,
Rocq185/200/202 work and full feature/Arena coverage remain. Full goal is open;
latest real native evidence is still recovery10's11 Environment controls.
See50's report for all counts, boundaries, findings and outstanding work.

Continuation49 supplies the concrete211 phased source loader,212 transport
build/interface and source-package composition, and213 six-group fixture entry.
The139-file combined source mapping has no compiled artifacts. Parent source/
model methods pass19+37+19+32, plus6 interface-shadow and5 materializer checks,
not new logical
coverage. Independent review closes preload-policy, scanner-reopen and template
pin findings;214 separately repairs unreviewed interface type-name rebinding.
Compiler/runtime interfaces and native validation remain unproven;
existing208 execution profiles are incompatible with the new plan. No broad
feature status, default dispatch, Rocq proof or Arena result is promoted.
Recovery10's11 actual Environment controls remain distinct historical evidence.
The full ports, upstream correspondence and extensive current validation remain
incomplete. See49's detailed report for exact source/native boundaries.

Continuation48 joins the existing safe hint API and marked-history file path
in private209, including existing generated bridges and opt-in extended Nat
validators.210 adds a complete118-source inventory and private-server selection.
These are unparsed source candidates, not verified feature parity or changed
defaults.10 source contracts and28 graph/model checks plus fixture-data checks
pass; genuine HOL fixture/Arena verdict counts added here remain zero.
The existing07/163 hint policy is reused, not a new feature credited to209.
Restricted-body scheduling, whole Lean/HOL adequacy, byte provenance and common
fuel equivalence are not established. Extended-history projection repeats some
proof computation. A phased loader, generated interfaces and native validation
remain open; no broad feature-table row is promoted. Details are in48's report.

Recovery10 adds11 genuinely checked focused HOL Environment controls with
strict accepted cleanup and the same three stock axioms. Selected182/186
loading and alias repairs now have native validation. Cases cover generated
inductive admission, structure/unit conversion, directional retry and expected
declines for unequal fields/nonunit neutrals. This is neither full Lean parity
nor11 Arena cases. Earlier64 Core controls remain a separate historical pass.
No feature-table broad status, newest163/203 default integration, Rocq202 proof
compilation or whole-kernel soundness claim follows.208/206 also repair two
launcher evidence contracts caught before execution;47 Python models and3 JS
cases are infrastructure tests, not proof/Arena verdicts. Full goal remains open.
The bbf session succeeded without weakening limits. Earlier STOP09/pending
wording below is historical; its failed evidence remains preserved.

Continuation47 adds uncompiled opt-in implementations, not validated feature
parity.202 connects scoped failed-congruence reuse to the local lazy-delta loop
while preserving170's result/control structure;14 models and204 source review
are not checked refinement proofs or full recursive-cache integration.203 binds
safe hint metadata after certified admission and before history append, with20
source/model groups. Private07/163 already implements priority scheduling;
that existing policy is not credited as a new203 feature or replaced by main.
Source review corrected a forbidden-reference classification regression and a
nondiscriminating Rocq state fixture. Neither candidate changes defaults,
compiled feature coverage, Arena totals or STOP09. Full integration is pending.

Continuation46 adds audit-source/content machinery, not a kernel feature or
native verdict:198 frames reviewed typed entries,199 validates exact recursive
summary content, and200 composes a prospective110-module/220-stage schedule.
83 distinct source/model methods pass using synthetic transcripts, not proof
execution. The722 framed queries cover681 original entries plus31 typed
witnesses, with10 repeated original queries. None proves full Lean parity.
Primary-source inspection finds rocqchk restores stored safety flags and its
summary omits global UIP and transient checking environments. Exact summary
matches cannot authenticate roots, commands, compiled objects, captures or exit.
The selected Darwin merged-log contract is explicit.185 remains HOLD and no
runtime/default/feature-table claim is promoted. STOP09 is still in force.

Recovery09/continuation45 promotes no kernel feature or Arena/proof pass.
Fresh resource/775-asset checks pass, but actual191 preparation fails because
its entry consumes183 seal kinds while its producer emits191.196 is a one-literal
source repair with eight actual-authenticator source/model regressions, not a
runtime successor.194's missed reader contract is preserved and documented.
Rocq192 adds31 source-derived typed witnesses/62 assumption queries, including
21 direct targets outside660;20 models and195 source review are not compilation,
unsafe-flag clearance, extraction fidelity or a correspondence theorem.185 HOLD
and all full-port obligations remain. Current STOP09 consumes ead7; earlier
pending-question or session-clearance wording below is historical.

Continuation44 promotes no kernel feature or native verdict.188 composes the
two HOL source repairs with independent review and40 source/model checks;
190 fixes per-mode fixture-review binding with16 pure-helper checks and narrow
review.187 adds target-labelled Rocq audit-source generation and output-content
checking for660 targets, with21 parent-replayed synthetic tests. All generated
query jobs are uncompiled and185 remains HOLD. Source/audit plumbing is not a
Lean correspondence theorem, native runtime validation or full compatibility.
Recovery08 STOP and its pending successor question remain unchanged.

Recovery08 promotes no feature or Arena/proof pass. The actual repaired loader
reaches the Environment module but fails parsing fixture aliases E/F before11
controls. New186 is an alias-only source repair with six passing source checks;
HOL execution remains unvalidated. Rocq185's new hooks/bootstrap have34 passing
mocked/source tests, not compilation or audit acceptance. Its completion still
holds stage2. STOP08 and prior Core180's64-control pass remain distinct.
See parent-resumption-20261011-recovery-08/FINAL_REPORT.txt. Entries below are
historical checkpoints, not current execution clearance or unanswered questions.

Recovery07 adds64 genuinely validated focused HOL Core controls with strict
cleanup and unchanged axioms. It validates repaired selected118, not the latest
163 cache source or full upstream correspondence. The separate Environment
attempt fails before its11 controls: flat loading puts nine in-file fragments
before environment_rules defines their prerequisites.182's loader-only repair
retains80 sources and11 controls;19 negative source models are not native tests.
07 is now stopped and old failures remain preserved. No feature-table broad
status, Rocq proof count, full-graph claim or Arena verdict is promoted. Current
evidence: parent-resumption-20261011-recovery-07. Earlier checkpoints are history.

Recovery06 promotes no feature, proof or Arena verdict. Fresh resource/asset
checks passed and Core149 actually reached HOL, but selected118 failed to load
at _level_certificates. Latest163 contains the same unused binder;176 preserves
two minimal source-only repairs without retargeting old graphs or seals.
Parent polling metadata also drifted from the strict chain contract;177's six
RAM tests and173 review validate metadata only, not native execution or cleanup.
The safe Rocq170 batch/audit runner adaptation remains pending (175 handoff).
Current STOP is06; its fresh successor question is unanswered. See
parent-resumption-20261010-recovery-06/FINAL_REPORT.txt. Earlier entries below
describe historical checkpoints, not clearance to reuse their attempts.

Continuation43 promotes no kernel feature or validated runtime.170 composes
63 local source files from the existing157/161/162/167/168 lineage and inherited
regression closure.171 consolidates160 query names;172 independently reviews
selection/order/linkage/extraction boundaries.660 combined names are not checked
proofs or exhaustive per-declaration coverage. Source-only checks and reviews
cannot establish upstream equivalence, stateful cache integration or soundness.
Native successor validation remains blocked by recovery05 and pending fresh
authorization; no default/runtime or Arena count changes. Detailed evidence:
parent-source-continuation-20261010-43/FINAL_REPORT.txt and REVIEW_CLOSEOUT.txt.

Continuation42 supplies167 exact represented-syntax keys and168 an adapter from
the162 failure-cache algebra to actual157 ordinary/accessor observers. Explicit
scope values and161 full-observation refinement avoid alpha-key and Boolean-
erasure assumptions.18 source assertions and independent169 review are not
compiled proofs or upstream parity. All scripts and71 Examples remain dormant.

Full-loop state threading, positive-update/effect preservation and extracted
ownership remain open. No feature-table row, runtime/default selection, Arena
total or soundness claim is promoted. HOL163 and recovery05 STOP are unchanged.
See parent-source-continuation-20261010-42/FINAL_REPORT.txt for scope and findings.

Continuation41 adds source163 recursive typed equivalence reuse: child forest
lookup is interleaved with congruence, and proved children can survive later
sibling failure.17 source/model methods and independent164 review do not
establish native behavior;11 genuine HOL fixture groups are unexecuted. Exact
typed context/type strata still differ from upstream's untyped open terms.
No full EquivManager, fuel/cost or Lean/HOL adequacy claim is made.

Rocq162 now has a pure-observer bounded ordered failure-cache algebra, with24
uncompiled lemma scripts and40 dormant Examples. Stateful callback/positive-
update preservation and checker integration remain absent.165/166 covers35
new157/161 audit query names over52 sources, not actual assumptions or proofs.
No feature-table validation row, default selection or Arena total is promoted.
See parent-source-continuation-20261010-41/FINAL_REPORT.txt for exact limits.

Continuation40 adds HOL158 structural-alpha selection and typed certificate
construction, not full upstream EquivManager parity. Existing typed congruence
and one-step zeta rules justify results; a Boolean hint cannot accept.16 passing
source/model methods and independent160 review do not promote native coverage.
Nine genuine HOL fixture groups remain unexecuted; runtime149 still selects118.

Rocq159/161 separate erased-result preservation from observation-tag equality.
Two direct refinement scripts and five fixtures are uncompiled; immediate and
composed source inverses preserve inherited text. Stateful failed-congruence
caching and compiled proofs remain outstanding. No feature-table row, Arena
result or overall soundness claim is promoted. See
parent-source-continuation-20261010-40/FINAL_REPORT.txt for exact boundaries.

Continuation39 adds source154 proof-valued positive equality reuse to the HOL
candidate, not full EquivManager parity: exact type/context strata, bounded
retention and guarded symmetry/transitivity, but no generic alpha discovery or
cross-type transport.19 source/model methods and independent156 static review
do not promote a native feature-table row. Seven HOL fixture groups remain
unexecuted. Default/runtime selections are unchanged.

Audit155/observation157 address the Rocq failure-cache prerequisite in the latest
validated source lineage. Explicit attempted/unattempted outcomes now have
full-result preservation scripts and22 dormant fixtures; none is compiled.
Stateful failed-congruence caching, symmetric-key justification and shared
positive-state parity remain unfinished. No new soundness or Arena claim.
See parent-source-continuation-20261010-39/FINAL_REPORT.txt for exact scope.

Continuation38 changes no kernel feature-table validation status. Fresh runner
source149 incorporates144r2 and separately binds historical stock evidence and
new operational authorization, with profile150/reader151 and independent152
review. Source/model tests and9 actual-Python RAM composition methods153 pass;
the sealed export is inert, not canonical installation or native validation.
All75 selected HOL controls remain unvalidated. Recovery05 STOP is unchanged,
the fresh-session question remains unanswered, and no new proof/Arena outcome
or full upstream equivalence claim follows. See continuation38/FINAL_REPORT.txt.

Continuation37 adds source-only whole-file integration146: explicit enabled
Core118/Env119 conversion through the retained frontend09 declaration loop,
with exact closed environment/policy/history packet gates and a Legacy API.
Independent148 approves this narrow source composition, not native behavior or
full upstream parity. No feature-table validation status or Arena outcome is
promoted. The separate145 fresh-run transition remains design/prototype only;
recovery05 STOP and all prior evidence are unchanged.

Recovery05 adds one strictly validated stock/guardian native startup, not a
kernel feature. The actual selected Core controller failed before a saved proof
report; Environment was not launched. All75 controls remain unvalidated. The
runtime pin-classification repair144/revision02 passes15+8 source/RAM regressions
but is not installed in a fresh sealed runner. No compiled/native feature-table
row, logical soundness claim or Arena outcome is promoted. Session05 STOP and
all historic evidence remain. See recovery05/SESSION_REPORT.txt for the actual
resource checks, stock success, Core failure and remaining integration work.

Continuation33 promotes no kernel feature or native result. Focused loader122r2
selects exact118/119 with repaired fixture125, all64+11 HOL controls unexecuted.
Independent123 exposed/closed a fixture false-positive scope defect: unrelated
theorem setup now occurs outside expected Certificate_fault handling. Review124r2
approves the exact source selection only. Typed guardian integration, actual
HOL loading/proof construction and the full feature/trust audit remain pending.

Continuation32: source118/Env119 now implement the pinned final enabled late
conversion schedule: application, function eta, structure eta in both directions,
decisive exact String.ofList expansion, then left-type-led unit equality. The old
No_delta callbacks are byte-preserved. Independent121 reviewb07dac96 approves
the exact108HOL+5transport source composition, not ML/HOL execution:77 source/model
methods include25 independent controls. All75 new genuine HOL fixture controls
remain unexecuted. No native feature-table row, soundness claim or Arena total is
promoted. Alpha/equivalence-manager and broader primitive/inductive parity remain.
Recovery04 STOP still binds; reviewed guardian113 awaits fresh authorized native
validation. See118 REVIEW_ADDENDUM.json and continuation32 report for exact scope.

Continuation29 supersedes the active-session note below: source93 has exact
independent97 source approval, but no executed port theorem. A real stock-only
HOL startup emitted all required stock/axiom markers; strict EPERM cleanup failed,
so it is not a validated startup or proof release. Recovery04 is stopped for
heavy work. No feature-table row or Arena total is promoted by that attempt.

Continuation28: source93 now connects actual same-budget Core inference/check/
conversion services to both raw zero88 and positive89 Nat.div/mod producers using
the exact Env definition body. The explicit Core90/Env45/codec86 composition has
108 HOL+5 transport source files,963752B,21 passing source/model methods and no
actual HOL validation. Component91/92/94 reviews do not approve the whole new
composition; independent97 is underway. No executable feature-table row is
promoted solely by this integration. Fresh human-authorized recovery04 passed
normal-pressure/memory/process-absence gates; actual runtime inventory checks
uncovered and recorded missing ocamlrun/GMP/controller dependencies. These are
runtime preparation findings, not Lean compatibility or logical soundness results.

Late continuation27 source89 de3821ec implements positive top-level div/mod source,
not a validated backend. Six conditional constructions plus a same-budget producer
preserve original initial proof witnesses and typed constructor/literal transports;
35 source/model methods,0HOL. Independent92 reviews exact89 and codec86 dependency.
Genuine prefix/services, checked environment/policy binding and execution remain.

Continuation27 source90 cb75a292 aligns the enabled final application comparison
with upstream TypeChecker.lean661-673: full-spine arity, bare heads, then arguments
left-to-right. Existing typed congruence uses the original left dependent domain;
all other Core76 code is inverse-preserved. Twelve source/model methods and16
dormant genuine Pure-backend controls are not executed HOL coverage. Independent91
review is underway; no default runner or old validation selection is retargeted.

Independent zero-theorem review87 9a810906 approves80 source with16+9 methods,
not six constructed HOL theorem values. Raw zero88 and positive top-level89 remain
in progress. Alpha/equivalence-manager parity and late eta/structure/string/unit
ordering remain unfinished alongside full primitive/inductive integration. No
compiled/native feature-table entry or historical Arena accounting is promoted.

Continuation26 corrects, rather than fixes, the prior Unicode-name claim:
quote_name/Char.chr roundtrip BYTES; Strlit uses Unicode scalars. No native-name
restriction follows from the decoder. Source85/additive errata and independent84
record the correction. Closed proof syntax and genuine-prefix restrictions do
remain. Historical25/73 prose below is superseded on this specific point.

Producer73 review84 e2ccbc26 is source-only (30+6+10 methods). Parent86
handoffcc5b6ef1 removes an actual future backend dependency cycle by extracting
the byte-identical syntax module and changing only two import boundaries. Its
10 source methods and51-file environment-checker-free raw closure establish
source structure, not HOL parsing/proof validity or backend activation. The
full graph preserves Core28/Envseven35 and all other ancestor source rows.

Eager fixture74/review83 13a593f1 has15+8 source methods, not76 executed HOL
controls. Zero-divisor source80 8e80a4d3 supplies six conditional constructions
with16 model methods; genuine body links and branch typing remain premises.
Independent87 review, raw zero88 and positive top89 are in progress. None of
these changes promote compiled/native coverage or alter Arena accounting.

Continuation25/24 add source evidence only. Full projection retry76/review77
now covers arbitrary unknown operand shapes after the existing fast cases;
genuine fixture78/review79 tests source-planned one-sided and application-head
cases with original typed certificates. No dependent/nested parity or actual
HOL run is claimed. Eager fixture74 is source-complete under independent83
review. It targets Core67, while78 targets Core76; no implicit pairing is made.

Fuel61/review71 remains conditional theorem source. Raw producer73 finalbinding
de51e82e resolves per-step premises and carries actual hrec instead of assuming
the uniform induction prerequisite; independent84 is underway. Top-level zero
divisor work80 is separate. Closed proof syntax, decoder-compatible names,
genuine full prefix and actual HOL construction remain unmet conditions.

Exact quick runtime75/review81 c77752a6 and dormant stock-launcher82 ce116b2f
prepare execution without promoting native eligibility. Stock82 avoids alias
repair/discovery during fixture startup, but its source tests do not establish
complete runtime assets or a real startup. No compiled/native table, logical
soundness claim or historical Arena outcome is changed by these source steps.

Final continuation23 reviews68 3803a91b (runtime54) and70 1b36b455 (quick69 loader)
approve source only, without blockers. No compiler/proof/native/feature-table
count changes. Real runtime/source/platform binding, authority and execution
remain open. Genuine eager fixture74 and proof-only runtime75 are now assigned;
existing full-suite and transport obligations remain unchanged.

Later continuation23: source67/review72 075c09b1 supplies source-approved
enabled eager-true scheduling with exact resolved Bool.true and actual typed
proof joins.17+8 source methods are not HOL passes; no genuine67 fixture is
selected. Source61 final737d66b6 supplies six conditional step/induction scripts,
with20 source/model+6 binding methods. Genuine uniform prerequisites, raw
producer and top-level div/mod are not thereby proved or implemented;71 review
and73 producer work continue. All compiled/native feature counts stay unchanged.

Continuation23 promotes no executable or proof coverage. Review65 b5c3c209
approves the exact successor quotation repair64 only; source52 remains blocked.
Execution59 review63 eee71048 and quick fixture62 review66 2f868728 are source
approvals. Runtime54 now binds review63 explicitly; independent review68 is
underway. New quick loader69 8e07112b uses a pre-project stock-axiom baseline,
66 source loads and one late-parsed invocation, without transport dependencies.
Its12 source/protocol methods are not65 HOL passes; independent review70 is
pending. Full suite53 stays unchanged and all actual execution gates remain.
Eager-true shortcut67 and substantive numeric-fuel61 are active source work.
The compiled/native table and all prior Arena outcome counts are unchanged.

Late continuation22: review60 1fac340f BLOCKS source52 for the bare successor
helper's HOL type mismatch. Fresh repair64 handoff07b8cadf changes only that
quotation, retaining all proof obligations; six source regressions pass and
independent review65 is pending. Source52/model passes are not proof coverage.
Neither candidate has run in HOL or is selected by the current common suite.

Continuation22 adds no native table coverage. Quick-comparison56 has independent
source review57 b0680eab (27 total methods) for initial/repeated quick routing
and normalized proof-irrelevance placement; full alpha/union-find/eager parity
and inherited Unsupported behavior remain explicit. Genuine fixture62 is under
construction. Existing suite53/execution59 still select Core34, not quick56.

Suite53 review58 0ef7e933 approves exact common-production source integration,
not its347/136/71+10 planned actual HOL controls. New loader/invocation59 binds
that exact suite, handoff54f7ffed, with15 effects-denied methods and independent
review63 pending. Runtime54 and every actual execution gate remain separate.
Source44 review55 16200ad0 approves13 partial theorem scripts at source level;
source52 adds four conditional reflected-branch constructions with15 model
methods, under review60. No new binary route, div/mod evaluator, checked proof
or complete induction is established; numeric-fuel composition61 is underway.
Earlier numbered entries below are historical, not current approval transfers.

Late continuation21 review51 approves arithmetic selection48 source only with
18 methods/14 mutation controls; no HOL/native feature status changes. Paired
suite53 composition is underway and K41 review49 remains pending.

Continuation21 supplies reviewed source for normalized-major K selection34 and
its composition45 with seven Nat routes. Reviews42 c953b1da and46 64134b7f do
not establish actual proof execution or general mutual/indexed K completeness.
Constructor levels/parameters now come from the normalized inferred major type;
exact guarded type comparison and original expression proof joins are retained.

Genuine seven37 review47 344091f8 checks real primitive admission and the
changed-input shiftLeft recurrence.347 main controls and optional separate106
are not HOL passes. Selection48 b96599f7 binds the unchanged fixture to BOTH
new Core and Env, with8 source methods; independent review51 remains pending.
Normalized-type K fixture41 has71 planned public/private controls plus10
explicit copied-metadata controls. Its19 source/model methods are not native
coverage; independent review49 is pending. Execution43 has14 source/fakeoperation
methods and review50 pending. It still targets the old suite, with runtime
bindings, interfaces and authority unresolved. No feature table compiled/native
status or Arena count is promoted. Div/mod groundwork44 supplies13 unvalidated
theorem constructions, not general literal evaluation. Fourteen source/model
methods pass; reflected branch composition52 and fuel induction remain work.

Continuation20 adds a source-only seventh raw Nat backend route: shiftLeft.
Seven35 handoff676f3109/Env63d0dc7c selects combined28 core, preserves all six
old routes and adds only the reviewed contextual theorem/producer dependencies.
Twelve source/adapter methods pass, exact independent review39 and genuine
admitted fixture37 pending. The remaining raw binary routes here are gcd, mod,
div, land, lor, xor and shiftRight. No compiled/native table status is promoted.
There is no upstream generic shift-count cutoff; external resource supervision
remains necessary even for zero-base multiplication by an expensive power.

Suite32 reviewe5bfd2c8 approves three same-core source selections, not proof
results. Loader31 review73366cbd approves four-bridge/three-lexer-phase planning
and strict failure boundaries, not a working native loader. Loader38 adds K29
with unchanged old arithmetic/mode plan refs; seven methods pass, review40
pending. Counts193/136/45 remain unexecuted. Normalized-major-type K selector34
is under implementation; metadata-only selection is not yet superseded. Rocq
supervisor composition review86a4e107 is source/fake-operation evidence only.
No Arena verdict, compiled proof, runtime approval or default integration follows.

Continuation19 adds explicit validation selection, not new compiled semantics.
Combined28 review92922026, sixfixture25 review0b5f3fa9 and qualifiedfixture28
reviewc2acdf00 are source-only. Selection30 handofff265192d binds arithmetic and
mode fixtures to one combined core while preserving their separate environments;
seven source-selection methods pass. All193/136 planned fixture controls remain
unrun. Their ancestor reviews do not prove the changed binding at runtime.

Genuine Kfixture29 targets the same core with45 planned controls and15 source
methods, under independent review. It tests order only, not normalized-major-type
candidate selection or full indexed-inductive parity. The main bootstrap lacks
the selected Hol_safety_input bridge and requires explicit lexer-phase handling
for appended HOL fixtures. Complete loader/interface review and actual guarded
proof execution are still prerequisites. No table status or Arena count is promoted.

Continuation18 corrects a discovered namespace mismatch: pinned Init/Core puts
reduceNat/reduceBool inside Lean, while earlier private hooks/fixtures used root
names. Qualified27 review492d2ff3 approves the one-pattern repair (8+12 source
methods). Historical root-name evidence is not upgraded to genuine coverage.
Both full and ordinary paths still share the same exact whole-term hook.

K26 review74ccbdc9 (14+12 methods) approves K-before-major-WHNF order only. K
candidate construction from recursor metadata, rather than normalized inferred
major type, remains an explicit gap. Combined28 handoffe051e1b7/core d4d5218b
selects both repairs with unchanged six24 backend; six composition methods pass,
exact independent review pending. No feature-table compiled status is promoted.

RawshiftLeft25 review8ffc00bd approves21+14 source/model methods and its changed-
input recurrence producer, not a bound seventh route. Unlike pow, upstream
generic shiftLeft has no exponent cutoff; no new cap was invented. The106 raw
assertions and193 genuine six-arithmetic assertions remain prospective, not
executed proof checks. Current full-K, general inductive, structure, primitive
and quick-comparison gaps, generated-interface and Arena validation remain open.

Continuation17 selects a combined default/nested and ordinary core (dc01f635)
whose Nat/native phase receives the active eager mode and same whnf service.
Default18 reviewa3243147 and ordinary19 review142eef30 approve components only;
combined23's six source methods do not prove full scheduling parity. Six-backend24
handoff4f264a63 binds add/sub/mul/pow/beq/ble,91 HOL-loaded+5 transport sources,
794977 bytes, with13 passing source/adapter methods. Original power universes,
fixed add[]/mul[] dependencies, ownership and core None-above-cap are preserved.
Five21 review14f0c0aa and power19 review883152c4 are independent source evidence;
exact six24 composition and all actual HOL/native validation remain pending.

Defaultfixture22 reviewbdc9f954 (19+8 methods) covers81 planned controls, not
executions. Its genuine eagerReduce/projection/quotient admissions are fixture
source, not entire-Lean adequacy. Positive String still lacks its genuine prefix.
Scheduledfixture20 review1deb9d02 covers50 unrun controls and synthetic hints,
not actual Arena metadata. No feature-table native status or Arena count below
is promoted. Other binary operations, K/structure/quick-comparison and general
inductive completeness remain open. Uninterruptible numeral conversion still
needs external guards; pow's2^24 cutoff is not a resource feasibility theorem.

Continuation16 adds normal-mode ordinary-loop Nat/native scheduling, source
handoffac801f80/coreb4bbf38f. It uses binder-aware surrounding-variable detection,
left-first committed arithmetic comparison and exact original-endpoint proof
joins before native refusal and lazy unfolding. Fifteen source/model plus four
graph methods pass; review and default/eager composition are pending. The scan
charges structural proof fuel, unlike upstream's cached hasFVar; identical fuel
behavior is not claimed. Four-backend17 review4fca91ec and sub17 review99c10b61
approve source only. Fixture17's192 actual checks are unrun. No table status,
compiled proof, native result or Arena count is promoted.

Continuation15 composes four raw producer routes (add/mul/beq/ble) with full14
and the marked frontend,86 HOL/five transport inputs,761432 bytes. Handoff
b9ecdd5f/graph4eae6a8d passes eight adapter plus seven graph methods; independent
binding review is pending. This is neither fourteen binary producers nor actual
HOL/runtime validation. Opaque-add16 reviewbe4589d0 and Bool15 reviewdafc0956
approve their exact source only. Real full-WHNF/add fixture review19fc3cb9 approves
41 planned checks, not executions; its raw-add12 canonical composition is
distinct from backend17. Sub17 review and default/nested WHNF implementation are
underway. No feature-table status, compiled proof or Arena result is promoted.

Continuation14 connects the same-budget raw addition producer to its environment
backend and composes82 HOL sources with5 transport inputs. Parent review passes
22 author and6 independent methods; no ML/HOL/default coverage is promoted.
The separate full-WHNF14 outer scheduler uses pinned100000/1000000 allowances,
explicit operand recursion and successful certificate caching;23 source/model
methods pass, plus10 independent controls56cbf07c. Fresh graph15 composes that
core with the addition backend;4 graph methods pass, with no native claim.
It does not fix inherited nested eager routes or public default dispatch.
Multiplication source has14+6 method approval774fb175; Beq/Ble and opaque-env
preparation repairs remain underway. Compiled proofs and Arena results unchanged.

Continuation13 adds source-only binary Nat dispatch matching all14 pinned names,
retaining original binary-head universe arguments, left-before-right operand
normalization and the strict pow exponent bound. It requires exact typed
certificates from a backend and constructs original-operand congruence;18
source/model methods pass, plus six independent review controls30f7196b. This is
neither fourteen implemented producers nor
complete full-WHNF integration. The addition backend and outer WHNF successor
are separate active tasks. No native feature-table status is promoted.
Raw-add12's result-only rewrite repair has independent source approval4a930e6e;
the rejected11 is preserved. Native-refusal12 reviewb462cf02 approves only the
isolated whole-term hook, not whole-program scheduling. Input selection11 now
accounts for strVal implicit dependencies, but only five of seven marked routes
have selected unchanged whole-file inputs and none has a new HOL verdict.

Continuation11 source additions: a shared-budget raw addition theorem service
and a separate typed successor/partial operand service. Neither is integrated
into complete reduceNat or full WHNF. Ten source/model methods for addition
and507 assertions for successor are not ML/HOL proof executions. The full-file
fixture is independently source-reviewed, but genuine selected inputs currently
cover only five of seven new primitive routes and actual acceptance is untested.
No feature-table row or native/Arena count below is promoted by this source work.

Latest source-only continuation10: normal-loop08 and typed offset09 are
independently source-approved, not natively validated. Offset does not establish
the remaining whole-term Nat/native pipeline. A separately reviewed optional
marked frontend connects seven existing full Nat certificate producers, with
21 source/model methods and111 unrun transport checks. Source graph and generated
interfaces must be composed/rebuilt before execution. The full-file fixture is
unexecuted; original input marks belong to certified history, while the live
safe registry intentionally uses canonical marks. No table status is promoted.
Pinned reduceNative is only an exact-shape unsupported-operation check; placing
it on recursive application prefixes would not match upstream whole-term order.
No new Arena or native proof evidence follows the historical STOP below.

Latest October9 execution checkpoint: all219 available inputs in the pinned223
inventory have been attempted.217 strict completions yield120accept,82reject
and15declines (8fuel/7time);4inputs are missing and2attempts remain uninspected.
184 required matches plus18 allowed-either results give202 expectation-compatible
decisions. Actual new11 completions and aggregate were independently reproduced
by reviewb95e3047. The final2.42GB cslib run hit the fixed supervisor operation
bound, not a launch-memory refusal, and remains STOP with old206. No native job
or resampling followed. This is not full-suite success or a soundness theorem.
HOL projection07 repair and five-file composition are source-approved only.
The fixture08 hint-order successor is now independently source-approved; its52
actual HOL checks are still unrun. A separate normal-loop candidate implements
an independent1000 allowance, with447 source/model checks and independent review
pending. This is not full outer Nat/native/offset scheduling or default support.
The first native-fixture source was rejected for hint-binding setup order;
its fresh successor is pending. No feature-table status is promoted by models.

Continuation06 adds source-reviewed ordinary safe HOL decoded-hint transport
and full-record certified-environment metadata binding (29 author plus9 review
methods, review5823160a), with19 certified backend consumers routed and default
lazy delta still disabled. A separate typed projection-pair successor is under
review. Neither is native feature coverage yet. Hash lookup and full structural
comparisons are not completely metered by proof fuel; external guards remain
necessary. The metadata binding is an OCaml invariant, not a HOL raw-byte
provenance theorem. A newly authorized recovery03 passes the unchanged resource
guards, but no new proof or Arena result is added at this checkpoint.

Continuation05 adds a separately reviewed opt-in HOL lazy-delta source candidate:
bounded step/hint priority, opposite-projection retry, rightmost-first congruence
search and context/backend/budget-scoped failure caching.203 author plus63
independent source/model assertions pass (review9aeee6ad). Real OCaml/HOL loading,
ordinary decoded-hint/certified-history binding, default activation and complete
outer scheduling remain pending. No table status is promoted. The UInt32 codec
checks semantic decoded Int/Z values; it does not establish original token
spelling such as negative zero. Canonical spelling is checked only for retained
text. This narrows the preserved author report, not the validation rules.

Earlier October9 checkpoint: the pinned223-case Rocq ledger has117accept,
82reject,7fuel declines,12unrun,4missing and1stopped/uninspected.199 decided
outcomes are expectation-compatible; this is not full-suite success. Recovery01
then refused pressure2. Subsequent timeout/recovery wiring and HOL arity fixture
work is source/model evidence only, not new executable feature coverage. The
arity fixture's public unequal cases stop before its optimized helper; copied
helper tests are labeled separately. No feature-table status below is promoted.
Older chronological paragraphs retain their historical counts and boundaries.

Reviewed marked-history composition now reaches the fixed gcd contract, with
16 source/model checks and no public safety override. A separate prospective
gcd-specific29/13 validity model implements admission and exact marked-state
extension;15 source tests pass after two retained repairs. This changes a
private object-language model, not default feature coverage. Independent
successor admission review4d2a4882 approves exact source and reproduces15 checks;
actual proof/invariant/native/Arena validation remains pending. No feature-table
status is promoted by these source-only candidates.

The original-wrapper gcd path now automatically proposes witnesses to the fixed
logical contract, rather than requiring external go/eager/seed/lower syntax.
This source-only bridge passes15 pure/model checks, including252 finite dependent
proof-premise examples. It is not a parsed/native HOL feature, admission rule or
Arena result, and does not change table status. Independent reviewffcaadde
approves exact source and reproduces all15 checks. See
hol-gcd-automatic-contract-20261008/CLOSEOUT.txt; input-byte provenance,
marked-input composition, actual admission and default integration remain open.

A reviewed source-only marked-input layer binds WF primitive certificates to
safety/hint/group metadata and prior certified history. Its11 pure checks and
independent test-repair review are not native typing, admission or Arena
evidence. The ordinary protected-name rule is unchanged. Byte provenance,
scheduling validity and the primitive admission bridge remain incomplete.
See hol-wf-marked-binding-20261008/CLOSEOUT.txt; no table status is promoted.

The private generic bitwise original-wrapper consumer now exists as reviewed
source, with full conditional recurrence and typed dependency evidence. Its
ordinary-wrapper exposure/universe-pattern repairs pass15 pure checks and an
independent source review. This is not tested native feature coverage, primitive
admission, default dispatch or a soundness theorem. The feature table remains
unchanged; see hol-bitwise-decoder-consumer-20261008/CLOSEOUT.txt.

A private source-only gcd consumer now follows the compiled wrapper through
the automatic WF decoder and requires typed base/recursive-step equations.
Eleven source/model checks pass after a header-rewrite repair; independent
source review approves the code and reproduces those checks. No positive HOL
construction, admission, default dispatch,
Arena coverage or generalized adequacy theorem is claimed. The feature table
is unchanged; see hol-gcd-decoder-consumer-20261008/CLOSEOUT.txt.

October8 source-only follow-up adds constructor projection candidate generation
to the private HOL WF decoder, guarded by existing exact typed conversion.
Nine pure/model tests and independent source review pass; no native helper
decode, new primitive admission, Arena verdict or default feature claim follows.
The table below therefore does not promote this source-only change to tested
coverage. See hol-nat-wf-decoder-20261007/source-03/REPORT.txt.

Fresh October8 Arena execution:154 whole-file Rocq cases at default fuel512
yield90accept/63reject/1fuel decline,with153 expectation-compatible outcomes.
This is new runtime evidence,not new logical feature coverage or soundness.
The same church-numerals input previously accepted on a different historical
binary at explicit16384fuel; this is not a same-configuration regression.
65available cases remain unrun and4missing. HOL remains unrun this session.

October8 validation follow-up: the retained extracted Rocq CLI accepted one
complete current Arena basicDef file, with an independent exact-capture review.
The complete HOL first-four prefix fixture passes; its seven-phase extension
times out during the fifth admission under180s. New diagnostic markers are
source-reviewed, not executed. Their runtime composition passes pure source
and binding checks; it is not new proof, performance or feature evidence.
The finite223-case Rocq campaign has source
approval/47 pure tests but no native campaign results. None of these changes
closes a feature/soundness gap in the ledger below or promotes a default runner.

Latest private checkpoint (2026-10-07): projection-to-indexed-admission
composition passes49compiles465closed queries49recursive audits and independent
retained verification6954c5. The theorem is conditional operational admission,
not full Lean soundness or a freshly extracted executable. HOL's exact combined
file candidate passes4positive5negative Arena files and a separate forced-fuel
decline; a custom whole-file MH2true fixture passes separately. Neither result
promotes the default server or establishes broader inductive generality.
Lifecycle/platform repair is required before new old-helper HOL/default Arena
runs. These operational blockers and source-only successors do not add coverage.

Status describes executable feature coverage, not an overall soundness proof.
Each implementation must be tested before being called complete. The current
Rocq regression coverage is considerably broader than the HOL coverage.

| Feature | Upstream implementation | Rocq | HOL Light |
|---|---|---|---|
| Structured names, expressions, capture-avoiding substitution | `Expr`, `Instantiate`, `LocalContext` and upstream Lean primitives | implemented; batched substitution proved equivalent to sequential substitution; universe instantiation commutes with lifting/substitution and preserves de Bruijn scope | implemented core, Nat/String literals and projections; strict UTF-8 transport tested |
| Universe normalization/equivalence with imax | `Level.lean` | implemented; semantic soundness and completeness, negative comparison/list witnesses, meta-free sufficient fuel and universe-instantiation semantics proved for natural valuations; Lean correspondence pending | certificate-backed core rules and tests |
| Type inference and checking | `TypeChecker.lean` | implemented; performance work active | theorem-producing core search |
| Reducibility hints and lazy delta priority | `Declaration.lean`, `TypeChecker.lean` | exact hint transport, priority, opposite-projection retry, left-first Nat probes, guarded free-variable/eager policy and upstream application orientation integrated and tested; failed-congruence cache pending; arbitrary-N heights explicitly extend UInt32 | upstream priority parity pending |
| Beta/delta/zeta/iota reduction | `TypeChecker.lean`, `Inductive/Reduce.lean` | implemented; Arena tested | beta/delta/zeta; single-family indexed/higher-order and safe indexed mutual iota; selected integration replay and preserved native suites pass |
| Proof irrelevance and function eta | `TypeChecker.lean` | implemented; Arena tested | implemented core |
| Structure eta, unit-like conversion and projections | `TypeChecker.lean` | implemented; Arena tested | typed projections/congruence, guarded structure/unit eta and nonrecursive structure-major expansion tested; general reducible telescopes pending |
| Constant and declaration validation | `Environment.lean` | axioms, defs, theorems, opaques | environment-indexed certificates for safe declarations; exact decoded-input history and explicit raw-axiom policy authenticated |
| Safety and mutual-definition handling | `Environment.lean` | marked unsafe/partial; mutual defs; unsafe inductives integrated and tested | restricted marked single/mutual definitions integrated as an opt-in API; full marked history distinct from safe projection; original 20-assertion group plus a fresh eight-group/184-assertion continuation pass; no default dispatcher support |
| Inductive positivity and elimination restrictions | `Inductive/Add.lean` | implemented; metadata regenerated | safe single/indexed-mutual families with dependent and function-recursive fields; directed raw function-recursive Type-0 and nonrecursive universally nonzero polymorphic slices integrated; selected integration replay passes, general raw telescopes pending |
| Recursor generation and K behavior | `Inductive/Add.lean`, `Inductive/Reduce.lean` | implemented; generated rule/signature comparison | regenerated single-family and indexed-mutual metadata; neutral single-family K; mutual Prop restricted to small elimination; nested generation pending |
| Mutual and nested inductives | `Inductive/Add.lean` | transformation, restoration and checking integrated | safe nonnested indexed mutual blocks integrated with uniform parameters/universes; selected integration validation passes; nested, unsafe and general raw indexed-mutual blocks pending |
| Quotient admission and computation | `Quot.lean` | implemented; Arena tested | 59 signature/model and 74 focused native checks pass; quotient-enabled 1,450 native checkpoint and full Arena attempt complete; all six exact quotient tutorials accept; mutation audit records 42 declines, not refutations |
| Nat/String literal and primitive behavior | `Primitive.lean`, `TypeChecker.lean` | literal reduction and all primitive classifier branches implemented; unsupported body shapes can decline; exact late String.ofList conversion hook integrated and broader fallback removed | canonical Nat/Bool guards; eight arithmetic contracts (add, pred, sub, mul, beq, ble, pow, shiftLeft); typed Char/String contracts and literal expansion integrated; quotient/string dispatch regression repaired; acceleration and remaining Nat primitives pending |
| Equivalence caches / optimization invariants | `EquivManager.lean` | DAG/depth memoization, collision-safe persistent index and early-header optimization integrated; unconditional complete-result/stream refinement to the corrected ordinary checker and rollback proofs | core search caches; guarded closed lift/substitution/instantiation shortcuts with locally bounded retention integrated; fresh 94-group matrix complete plus separate newer API suites; scale work pending |
| Fuel and fail-closed errors | `FuelConfig.lean`, `TypeChecker.lean` | explicit decline; independent normal/eager WHNF limits integrated with complete-result refinements and production boundary tests; recursive default 512 and other loop accounting still differ from upstream | bounded search and process limits; explicit decline |

Additional boundary: NDJSON transport includes information not present in `Lean.Declaration` input, including exported recursor rules. Its validation is part of an external checker and must not be replaced by trusting an upstream exporter.

The shared parser and handwritten adapters are not formally verified. The Rocq
port has no overall `accept -> Lean typing` theorem. The HOL port has exact
object-judgment certificates with explicit axiom policies and no newly introduced
HOL axioms, but its encoded specification is not yet proved equivalent to Lean.
Neither statement should be shortened to "verified Lean kernel".

An October7 private HOL source successor implements the missing Nat.div/mod
recognizer path: shared fuel-recursion syntax, full reflected-condition and
dependency contracts, theorem production, one guarded admission clause and
normal/safety input routes. No new arithmetic reduction rule is added. The
core model/contracts/producer/consumer now pass fresh HOL loading and schema
validationf07b30 (47sources,22pre/143post, no new HOL axioms, clean cleanup).
The private admission schema intentionally changes from11 to12 clauses;
all29 conversion and old11 admission clauses are byte-preserved, and inherited
invariant proofs are freshly derived under12 clauses. Retained inspection
c69c55 verifies the exact completed run; no old11 proof receipt substitutes.
This does NOT yet establish a positive arithmetic certificate, fresh classifier
build, full input/safety routing or Arena acceptance, so the table still marks
remaining Nat primitives pending. The first56-source constructive dependency run
fails on four fixture module aliases under the HOL lexer, with zero admission
controls. Its fresh alias-only successor passes6ea79c/inspection915693:
56sources22pre143post11controls and one canonical Nat admission from empty.
It does not complete an arithmetic prefix phase or certify div/mod.
The failed original evidence remains preserved.
The later full Basephase passes0aba44/inspection1b847a: ten real admissions,
24declarations16controls56sources22pre143post,71.495s with clean cleanup.
This completes only phase1 of30; the positive div/mod obligation remains open.
The private shiftRight source02 additionally uses a full div
certificate and symbolic zero/step equations, with an appended13th admission
clause. Its corrected dest_list call and fixtures are source only, not validated
coverage. See build/workers/hol-nat-shift-right-source-20261007/REPAIR-02.txt.

The separately audited `rocq/ProjectionPreservation.v` gives exact branch
equations for stuck/successful projections and rejection/decline propagation,
with sixteen small fixtures. These equations quantify over callbacks; they do not
prove those callbacks sound or establish a full Arena performance result.
The221-case snapshot has a protected historical-binary PERF26 run with18 correct
accepts,2 correct rejects and6 published-limit timeouts; it is not evidence for
the new private projection composition. The private composition, including the
fixture dependency split and proof repairs, now passes113 module compiles,
1340 closure queries and113 recursive audit roots across its full84 and deferred
extraction stages. All25 native groups/114 commands then pass against that exact
extraction after generated-interface review. The new CLI build and19 boundary
controls pass, followed by independent native/CLI retained-evidence audits.
The exact new candidate completes PERF26 with18 correct accepts,2 correct
rejects and6 published-limit timeouts. A separate347MB Init run times out at
500s after9546 completed wire records, with no resource-guard stop. Neither is
a full221-case success; Init's last-start record is not an accepted theorem.
This is not part of the shipped checker and does not establish whole-kernel
semantic soundness or all upstream behavior. See `IMPLEMENTATION_PLAN.md` and
the2026-10-05 chronological handoff for exact attempt identities and limitations.

The private HOL negative-file API passes three full-decoded-input negative
fixtures and one later-owner non-rejection control. The opt-in extra-rec public
dispatcher passes11 controls and64 exact closed-schema rechecks before/after,
with an independent retained-evidence audit. A further orphan-ctor public stage
fails exact bytecode-event path identity despite completing logical controls;
it is not a passing integration result. Fresh explicit-bytecode-field successors
then pass for orphan-ctor, orphan-rec and the later-owner decline control, with
independent retained-evidence review. An ordinary valid basicDef fixture also
passes: normal, disabled and enabled public routes each construct closed positive
certificates matching the full decoded history, environment and axiom policy.
These are focused private dispatcher tests. Default integration remains pending.
Reducible mutual headers require an explicitly reviewed raw-history transport
extension, not merely a syntax normalization helper. The private MH1 extension
actually constructs15 exact closed theorem schemas, but its first changed-header
positive control fails after6/35 controls because a named Pi head is compared
with an anonymous generated binder. The strict stage result is STOP, not PASS.
Fresh MH2 source adds a head intermediate plus alpha equality and independent
typed conversion while retaining the complete generator/prefix/policy guard.
The first45-control attempt refuses its4GiB gate. A later human-authorized
512MiB series exposes and repairs existential-witness and accessor-proof
construction defects without weakening the logical statements. Source04/stage05
constructs allfive positive certificates and passes29/45 controls, then hits
the180s deadline: actual exit2, not PASS.15 new schemas and64 pre-checks complete,
but post-checks do not. All pinned files are preserved; cleanup is verified.
The later user-authorized128MiB profile now passes allfive partitioned stages:
all45 original controls,62 occurrences, with complete proof postchecks and a
successful retained-evidence aggregate. The separate11 final-environment
controls and32 full-decoded smoke assertions also pass. All85 original decoded
controls now pass their own21-partition validation and retained aggregate,
with110 occurrences. Smoke32 is not a strict subset and cannot be subtracted
from85. These decoded controls do not exercise the file parser. The positive-fuel
forwarding repair now passes four fresh native stages covering one actual
inductive row and tiny/zero/default budgets. Allfive dispatch branches are
repaired in source, but not independently covered by native positives. This
remains private rather than a promoted default fix. The separate authentic
basicDef whole-file API and opt-in adapter validations pass, including parsing
and exact certificate revalidation. A further adapter stage accepts complete
sparse-name-index, level-index-out-of-order and Empty files, retaining explicit
input axiom policies. This is four distinct files, not a full campaign or server
validation. The combined MH2 owner-negative dispatcher now passes a fresh
whole orphan-ctor stage120643/inspectionf5f1d7,11predicates64prepost checks,
exact closed negative proof for both routes and altered-export refusals.
A further six-file combined batch completesb98ce8/inspectiond0128c in84.8s:
orphan-rec,extra-rec,dup_rec_def2 and BogusRecursor are proved negative; BasicDef
accepts and forced-zero-fuel orphan-ctor declines. All49assertions64prepost
and full preservation/cleanup pass. The forced decline is not an Arena correct
rejection. Duplicate-name uniqueness needs a separate negative proof; other
negative families and default/server integration remain unvalidated.
None is default integration or whole-Lean correspondence.

The private ProjectionTelescope.v successor implements literal telescope
opening, reverse substitution order, capture avoidance fixtures and an
operational bridge to parameter application/non-Prop projection scanning.
Its16 lemmas/8 examples and the six ProjectionSelection results now pass in
the13-module/131-query/13-recursive-audit validation07 cohort, independently
audited in879 retained-evidence checks. The identity-WHNF premise is not a
contract proved for the real recursive checker. Typed projection preservation
remains open. This is private proof validation, not full-project integration.
The separate ProjectionLiteralChecker.v successor now adds six compiled,
closed and recursively audited results replacing the global identity premise
with literal-Pi stability for the actual positive-fuel callback. The fresh
14-module/137-query/14-audit cohort passes;978 independent retained checks pass.
This does not prove the public whnf wrapper accepts arbitrary Pi domains/bodies,
full projection inference succeeds, or dependent typing is preserved. The
Prop-elimination case remains excluded from that earlier result.
The next private cohort passes16 compiles,166 closed-context queries and16
recursive audits. It adds six conditional public-projection/WHNF results and
23 operational maybe_prop results/fixtures beyond the14-module donor. The
Prop branch checks are now covered operationally, including refusal and fuel
propagation, but declarative typed preservation and Lean adequacy remain open.
The next17-module/174-query/17-audit cohort passes1649cc/audite28081 after a
proof-script repair preserving all eight new statements. It derives the
literal-telescope parameter application and subsequent Prop-field selection.
Major inference/WHNF, owner/constructor lookup and metadata, substituted type
shape, arity/field bounds and permitted-domain obligations remain premises.
First-match lookup cannot be inferred from arbitrary list membership alone.
The current pinned Arena inventory is223 records (219available/four missing),
not a fresh checker campaign: the latest new projection-stage preflight stopped
before any checker launch. No new verdict extends the earlier27-input evidence.
A private HOL head-congruence source candidate adds typed application/constant
comparison before eager normalization. Existing inference rules, theorem guards,
casts, cache ownership and resource exceptions are retained;13 source lines and
unrun fixtures are source-reviewed only. It is not validated performance work,
upstream hint parity, default integration or whole-kernel verification.

The Rocq ordinary String conversion now uses the reviewed exact late
String.ofList hook. The formerly broader mixed-literal fallback is removed;
see `docs/ROCQ_DAG_RUNTIME.md` for intentionally changed observations and the
new-ordinary reference target of the optimization proofs.
