# HOL Projection Audit

## Scope and Status

This is a bounded source review and baseline-gated export regression suite, not
a soundness or completeness proof. No production, native, frontend, or client
files were changed. Expected outcomes live only in test runners/manifests and
are never supplied to the checker. No alternate checker or Arena outcome field
was used as an oracle.

The main suite has **76 cases: 30 acceptance controls and 46 negatives**, with
eight positive gates. Seven gates are byte-identical actual Arena exports:
083 And.right, 084 Prod.snd, 085 PProd.snd, 086 PSigma.snd, 089 projProp1,
091 projProp3, and 098 projRed. The eighth retains the complete 086 export and
adds a dependent constructor-projection computation. A separate diagnostic
set has two declaration gates and four valid 078/079 probes. Thus there are
80 non-gate probes in total.

## Provenance

Review snapshot: `tests/hol_projection_audit/snapshot/manifest.json`, SHA256
`49ade84203d704cf207c1594456063af963469dead7eab076e3f30c91f930200`.
It preserves 48 files: the actual local project loader closure and bridge
bytecode/interfaces, explicit frontend sources, test helpers, seven source
exports, and relevant pinned upstream sources. Capture checked the project
closure and copied file bytes again before writing. The manifest pins the
Arena manifest digest but records only seed identity/path/hash/size, not
Arena expected outcomes.

Upstream revision: `8223d223ed98661882e95d9d6a7126df7097cd76`.
Primary reference is the captured `Lean4Lean/TypeChecker.lean`, especially
`inferProj` at lines 233-260 and `reduceProjCore` at lines 343-351.

The assigned 1384-test runtime is a **distinct, earlier snapshot**, identified
by `runtime-provenance.json`, SHA256
`64313f76a1805d102cdb0a4779e380b760a0d3feb4b40c62b5acbb7d48f946dc`.
Its startup closure differs from the review in `hol/core.ml`,
`hol/environment.ml`, `hol/environment_rules.ml`, both projection modules,
`hol/primitive_contracts.ml`, and `hol/primitive_validation.ml`. The bootstrap
matches. This loaded runtime has neither the RBTree converter repair nor the
later structure-eta hooks. Replay cannot validate those later edits.

Keep three checkpoints separate: (1) the **loaded 1384** runtime exercised
here, (2) the parent's later **1450 structure source** checkpoint, and (3) the
subsequent quotient transport/admission/iota work, which was still in progress
and unverified when handed off. The 1450 label is parent-reported; this review
is identified by its own captured file hashes, not by an inferred native test
count. No quotient implementation or later bridge/runtime was exercised or
certified by this audit.

The runner records each differing digest explicitly and refuses a distinct
runtime unless `--allow-distinct-snapshot` is supplied. Startup hashes attest
neither executed bytes nor semantics; external HOL/OCaml/dynamic libraries,
runtime state, and transient restored edits are outside the manifest scope.

## Source Review

No concrete false-acceptance path was identified in this bounded review of
projection typing and reduction. This does not establish completeness of the
premises or a formal correspondence to upstream.

- **Owner and metadata.** `hol/projection_entries.ml:l4_projection_meta`
  ties the owner to the inductive entry, requires exactly one listed
  constructor, checks that constructor's parent/parameter count/field bound,
  and matches universe-parameter lists and application arity. Membership
  premises in `hol/environment_rules.ml` use the same environment. The runner
  mutates expression owners without changing admitted metadata, avoiding a
  mere metadata-replay test in place of projection checking.
- **Dependent contexts.** Parameter substitution precedes field scanning.
  Each earlier field is instantiated with its projection from the same major;
  `l4_uses_bound ... 0` controls the skipped-field dependency guard. The rule
  requires sort proofs for all scanned domains and the ML candidate must
  discharge the exact closed side conditions. The PSigma fixture distinguishes
  `b : B a` from `otherb : B other`, and tests coherent changes as controls.
- **Prop and universes.** The typing rule requires either a proof of universal
  nonzero owner sort, or zero-equivalence proofs for every needed field sort.
  The selected field is always needed; a skipped field is needed when used in
  the remaining telescope. ML attempts choose a proof route but do not replace
  it. Captured `l4_level_nonzero` and `l4_level_equiv` quantify over universe
  valuations. The upstream test is `isNeverZero`/`isAlwaysZero`, not a single
  sample assignment.
- **Reduction.** The projection reduction rule checks the constructor parent,
  number of parameters and fields, universe arity, typed conversion of the
  major to the constructor, typing of the projection, and typing of the
  selected field at the same result type. The 098 tests vary the field order,
  selected index, and claimed Bool endpoint independently.
- **Conservative limitation.** ML projection search currently requires
  syntactic constructor/field Pi telescopes where upstream weak-head reduces
  those telescopes. That is a potential coverage gap, not evidence that the
  rule accepts an invalid term. These fixtures do not claim to cover aliases
  hiding a constructor telescope, mutual/indexed families, or structure eta.

## Why the Prop Cases Differ

The actual `PropStructure` in 089/091 is a Prop with six fields. At universes
`[0,1]`, fields 0, 2, and 5 are `PUnit.0` proofs; fields 1 and 3 are `PUnit.1`
data; field 4 is an equality referring to field 3.

- Projecting field 2 may skip unused data field 1 and should accept.
- Projecting field 1 directly is forbidden, even with a coherently changed
  result type `PUnit.1`.
- Projecting proof field 5 is forbidden because the scan crosses data field 3
  used in field 4. The fact that the chosen field is itself a proof is not
  sufficient.
- At universes `[0,0]`, projection 5 should accept because that skipped field
  is now a proof. With arbitrary second universe it is not always a proof,
  so the universally quantified declaration is invalid.
- Making the first universe arbitrary also invalidates direct projection of
  its `PUnit.u` field from Prop; valuation `u=1` is a concrete counterexample.

These distinctions follow the captured upstream predicate and constructor
telescope, not blind mutation or an assumption that all changes are invalid.

## Construction and Replay

`tests/hol_projection_audit/projection_audit.py` generates deterministic NDJSON
by path-copying expression DAGs. All common owner/index/major mutations leave
inductive claims untouched. Binder anonymity and reverse declaration order
are acceptance controls. Unknown owners are structural names; no file paths
are evaluated as source code. Case metadata stores a rationale, dimension,
source pin, size, and SHA256.

Main generated manifest SHA256:
`3381c7ea296e9bf73bfe5279e9b7de21aa5b1fa074089b0efd5fc6fc7e8178bf`.

Offline verification:

```sh
PYTHONDONTWRITEBYTECODE=1 python3 tests/hol_projection_audit/projection_audit.py --verify
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover -s tests/hol_projection_audit -p 'test_*.py'
```

The 11 offline tests check exact pins, all table references and closed terms,
unchanged inductive claims, canonical equality of transport controls,
dependent de Bruijn contexts, the real Prop dependency, local universe
specialization, deterministic bounds, private no-overwrite reports, and
baseline-gated accounting. These tests do not establish logical verdicts.

Runtime invocation accepts an arbitrary checker argv after `--checker` and
appends the filename. Use `--run --report NEW_PATH --runtime-provenance PATH
--runtime-sha256 SHA`, plus `--allow-distinct-snapshot` only when acknowledging
the recorded differences. Requests are serial, diagnostics are bounded to
4096 bytes each, and fixture/client/provenance hashes are checked around the
run. Code 0 means acceptance, 1 means rejection, 2 means a coverage gap, and
other codes are faults. Any failed positive gate skips its family's mutations
as `not_covered`; negative declines are never successful refutations.

## Runtime Results

The released runtime was replayed serially with a 30-second worker request
limit and a 40-second outer process deadline.

| Set | Positive gates | Code 0 | Code 1 | Code 2 | Faults / wrong verdicts |
| --- | --- | --- | --- | --- | --- |
| Projection audit | 8/8 accepted | 30 | 0 | 46 | 0 / 0 |
| Valid recursor diagnostics | 2/2 accepted | 4 | 0 | 0 | 0 / 0 |

All 30 projection acceptance controls passed, including reverse declaration
ordering, coherent dependent-field substitution, skipped independent data
fields, and the all-Prop dependent scan. All 46 negative cases declined; none
is counted as a successful rejection or refutation. Their diagnostics identify
owner mismatches, field bounds, unestablished typed conversions, or inability
to prove the required zero-universe equality. There were no worker/outer
timeouts in this audit, no truncated diagnostics, and no integrity failures.
The checker/client/provenance observations were unchanged around both runs.

Evidence:

- `tests/hol_projection_audit/projection-report.json`, SHA256
  `3375b6e43d36263225202ed30ff4bed8e48f86b203a6f439634ec596ac360d0d`.
- `tests/hol_projection_audit/recursor-probe-report.json`, SHA256
  `1a2a74af5bcf39cd1729eccf55e6f88e59d16960b54a93debb4877c1facaafbf`.
- `tests/hol_projection_audit/completion.json` records final process cleanup,
  report pins, unchanged client hash, and the selected earlier actual results.

## 078/079 Diagnosis

Both original exports accepted on the unchanged loaded runtime:

| Probe | Result | Seconds |
| --- | --- | --- |
| 078 complete declarations | 0, line 128 / checked 3 | 3.54 |
| 078 original boolRecEqns | 0, line 199 / checked 4 | 8.53 |
| 078 final theorem at universe zero | 0, line 236 / checked 4 | 8.35 |
| 079 complete declarations | 0, line 110 / checked 2 | 2.82 |
| 079 original prodRecEqns | 0, line 205 / checked 3 | 7.88 |
| 079 final theorem at universe zero | 0, line 231 / checked 3 | 7.62 |

The earlier parent report `hol-arena-projection-primitive.json` requested
`--timeout 10`. Its actual diagnostics for these two files were explicitly
`case wall timeout; child killed and reaped`, after 10.11 and 10.12 seconds.
Those are observed resource-limit gaps, not proof-construction failures. This
replay establishes current acceptance at a 30-second cap, but does not identify
the cause of timing variation or prove a performance regression against K.
No remaining-goal instrumentation or proof-search patch is needed to explain
these particular recorded declines. No production code was changed.

At `2026-09-29T21:42:48Z`, there were no worker children of warm HOL parent
84593 and no active clients of `/private/tmp/hol-run-3qgkb1d2/s`. Supervisor
84562 and the warm parent were deliberately left alive, and the socket was
released back to the parent task.
