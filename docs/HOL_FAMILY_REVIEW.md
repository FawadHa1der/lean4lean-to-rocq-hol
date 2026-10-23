# HOL Parameterized Family Review

## Findings

No concrete false-acceptance premise or omitted modeled metadata field was
identified in this bounded source review. This is **not** a completeness,
soundness, kernel-correspondence, or runtime-coverage proof. The observations
below apply to single, non-indexed families with direct recursive fields and
data fields depending only on parameters. They do not establish correctness of
later indexed-family edits, mutual/nested families, or arbitrary dependent
constructor fields.

The important guard boundaries survived inspection: field and parameter
formation in the prior environment, certified elimination flags, distinct
claim names alongside membership matching, exact rule bodies/order, and typed
premises on both sides of iota. Removing any of those premises would require a
new review; successful generated-signature formation alone is insufficient.

## Snapshot Identity

Review inputs were copied and hashed before detailed inspection at
`2026-09-29T19:53:30.246546+00:00`. The immutable review copy contains 36 files
under `tests/hol_family_audit/snapshot/`. Its manifest SHA-256 is:

`777f23467bee30d5563f2510a2efb6f340168bea4e67d632e68a83e41af5dade`.

This is a **distinct source snapshot**, not the loaded family-server snapshot.
Of 25 project inputs in the startup manifest, 24 still matched at capture. The
one difference was `hol/inductive_model.ml`:

| Identity | SHA-256 |
| --- | --- |
| Loaded startup manifest's model | `80d00ffbf41c27bc570a121b8dc0b7923d19f17d25cd17ef19ebf7610132a04d` |
| Reviewed model copy | `bfddc5dac755e334f2bc0fb46e0600e7c1288fd250f63a4832ece19c1e1f4e50` |

The startup manifest is `build/reports/hol-family-runtime.json`, SHA-256
`736c1498de3f35b9f6dbac0ace01945e2018e38a4764a0ad149d3f2cf5156847`.
The snapshot includes its exact bytes as `snapshot/startup-provenance.json`.
Extra source files, such as `frontend/replay.ml`, are review context; their
current source hashes do not establish correspondence to loaded bytecode.
All file-level hashes and match classifications are in `snapshot/manifest.json`.

Upstream reference: the vendored Lean4Lean checkout reports revision
`8223d223ed98661882e95d9d6a7126df7097cd76`. Referenced files were copied and
individually hashed too; reasoning uses those exact local bytes, not an
unpinned current upstream tree. Source references below are relative to
`tests/hol_family_audit/snapshot/`, so later production edits do not change them.
The six referenced upstream files also had no diff from that revision when
checked during this review.

## Premise Audit

### Prop and Universes

`hol/family_syntax.ml:90` permits large elimination exactly when the result
level is universally nonzero, the family is empty, or the sole constructor's
field sorts are all universally Prop. This agrees with
`vendor/lean4lean/Lean4Lean/Inductive/Add.lean:258` for the supported non-indexed
uniform-parameter subset. Upstream also permits certain non-Prop fields that
occur among result indices. That additional indexed case is outside this
review; omitting it here restricts coverage, not the accepted fragment.

K at `family_syntax.ml:93` requires a universally Prop result, exactly one
constructor, and no fields after the parameter prefix. Compare upstream
`Add.lean:289`. A proof-valued constructor field still prevents K, whereas a
proof supplied as a parameter does not. Multiple proof-only constructors do
not authorize large elimination from Prop. Empty families authorize it even
when their result universe can be zero.

The ML `level_sample` at `hol/environment.ml:356` is not the verdict premise.
`level_truth` proves positive statements with universally quantified HOL
arithmetic or proves their negations using an explicit countervaluation.
`environment.ml:431` discharges both exact flag equivalences from
`environment_rules.ml:140`; a bad sample decision cannot replace those proofs.
The field universe bound is separately proved at `environment.ml:407`, not
tested only on sample valuations. The cross-universe witness uses independent
u/v parameters where equal all-zero/all-one samples would miss a bound failure.

### Parameter Contexts

`environment_rules.ml:137` requires formation of the reversed parameter-type
list in the **prior** environment. `environment.ml:386` constructs that raw
de Bruijn context; `hol/core.ml:387` checks the tail before extending it. For
`(A : Type) (a : A)`, the stored second domain is BVar 0 and is checked with
only A in scope. BVar 1 at that location must fail; later binders must not make
an earlier domain well formed.

The named-variable witness builder independently encodes the expected
constructor for a family with parameters A and a, then a field of type A.
Its golden de Bruijn test expects domains `Type`, BVar 0, BVar 1 and result
`Dependent (BVar 2) (BVar 1)`. This tests offsets without calling the ML family
generator or another checker.

The frontend's parameter-prefix removal (`frontend/hol_check.ml:71,98`) is
potentially delicate, but it retains every original constructor claim. The
HOL metadata predicate compares its complete original type with the generated
type, modulo binder display names only. A mismatched constructor parameter
domain therefore cannot be hidden by ML's discarded prefix. Upstream checks
those domains at `Add.lean:218` and uniform result parameters at `:157`.

### Positivity and Formation

Only the exact uniform family application is represented by `Recursive`.
Everything else becomes `Data` after lowering out earlier constructor fields
(`frontend/hol_check.ml:83`). Earlier-field dependence is explicitly declined.
For data, `environment_rules.ml:128` demands scoped universes and typed sort
formation in the prior environment, where the fresh family and constructors
do not exist. `environment.ml:388,402` uses that same prior environment.
Negative and nonuniform occurrences cannot obtain a prior-environment
constant typing premise. Upstream has a broader explicit positivity traversal
at `Add.lean:184`; its uniform-recursion check is at `:157`.

Generated entry types are later checked using the full provisional generated
environment (`environment_rules.ml:145`, `environment.ml:442`). That is needed
for constructors to refer to their inductive and recursor motives/minors to
refer to constructors. It is not independently sufficient evidence that an
arbitrary recursive signature block is valid. Here it is conjoined with the
prior-context/field premises, fixed generated shapes, fresh names, primitive
and nested-name guards, and exact metadata. No API returns a certified
environment until the complete admission rule is applied at
`environment.ml:452`. The ML candidate generator is also compared with the
HOL generator computation at `:421`.

### Metadata Order

`hol/inductive_entries.ml:27` requires equal claim/generated lengths, distinct
claim names, and membership of each anonymized claim in the generated list.
Generated names are distinct across the new block and prior environment by
`environment_rules.ml:142`. Anonymization preserves declaration names. Together
these conditions require a permutation, not a subset or duplicate replacement.
An extra/omitted claim or same-length duplicate substitution cannot satisfy it.
`frontend/replay.ml:49` also rejects duplicate declaration names before HOL.

Anonymization (`hol/inductive_syntax.ml:90`) changes only binder display names;
it does not erase constants, universe names/order, field indices, counts,
constructor parents, recursor flags, or rule bodies. Recursor rule lists remain
ordered inside each claim. Upstream `Replay.lean:153` derives full constructor
and recursor equality for postponed comparisons; `Inductive/Add.lean:419`
generates rules in logical constructor order. Outer claim-table permutation is
therefore an acceptance control, while rule permutation is a negative metadata
target. Some supplied inductive metadata is not independently compared by
upstream replay, so the project's all-field authentication is intentionally
stricter than merely reproducing that replay behavior.

### Iota Extension

`environment_rules.ml:77` authenticates the actual recursor entry and selected
rule, requires zero indices, one motive, safe metadata, matching universe arity,
the correct prefix/parameter/field lengths, and typing proofs for **both** the
original application and instantiated RHS at the same type. The ML adapter at
`environment.ml:185` proposes the step and proves those side conditions;
`hol/core.ml:301` supplies the two typed premises and guards the conclusion.

Constructor parameters are dropped from the reduction arguments, but are not
assumed to match the recursor prefix unchecked: the major application must
first type-check against the recursor's expected family application. This
matches the supported part of upstream `Inductive/Reduce.lean:91`, which
instantiates the rule with recursor levels, prefix arguments, and constructor
fields. The witness with prefix A and major `Wrap.mk B b` targets this boundary.
A separate dependent identity tests the actual reduction result, rather than
only observing that the reduct and redex share a type.

K conversion of arbitrary neutral proofs, structure eta/projections, indexed
recursors, and generalized recursive function fields are not established by
this inspection. A decline on such valid uses is a compatibility gap, not
evidence that an input is invalid.

## Witness Pack

`tests/hol_family_audit/witnesses.py` produces 10 positive baseline gates and
41 cases (10 acceptance controls, 31 negative targets). Fixtures are explicitly
synthetic NDJSON, not claimed to be untouched exporter output. Each case has
an expected result, rationale, dimension, SHA-256, and baseline hash in the
runner manifest; only the input filename is sent to the checker.

The nine family shapes cover polymorphic Wrap, branching direct recursion,
dependent parameters, data-bearing Prop, proof-only singleton Prop, two-way
Prop, nullary Prop with a proof parameter, a varying universe, and an empty
varying-universe family. A tenth gate includes a dependent identity requiring
Wrap iota conversion. Mutations cover coherent elimination changes, K flags,
claim/rule ordering, duplicate/missing/extra claims, cross-universe bounds,
parameter scopes/prefixes, negative/nonuniform/self-constructor data fields,
and wrong iota parameters/results.

Eight infrastructure tests pass. They check table-reference order, term
closure (with one deliberately out-of-scope negative), deterministic hashes,
the independent parameter-offset and branching-recursive RHS examples, retained constructor prefixes,
ordering distinctions, flag mutation coherence, and baseline gating. They do
not prove that any baseline is accepted by HOL.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 tests/hol_family_audit/witnesses.py --generate
PYTHONDONTWRITEBYTECODE=1 python3 -m unittest discover \
  -s tests/hol_family_audit -p test_witnesses.py
```

Runtime requires explicit exclusive access to the existing server, a new
top-level report filename, and its startup digest, for example:

```sh
python3 tests/hol_family_audit/witnesses.py --timeout 25 \
  --report tests/hol_family_audit/family-report.json \
  --runtime-provenance build/reports/hol-family-runtime.json \
  --runtime-sha256 736c1498de3f35b9f6dbac0ace01945e2018e38a4764a0ad149d3f2cf5156847 \
  --checker python3 scripts/hol-check.py \
    --socket /private/tmp/hol-run-ht30uulj/s --timeout 10
```

Each family gate must return 0 before its cases run. Code 1 can cover a negative
target; code 2 is always a decline/coverage gap, including failed proof search
or a server wall timeout. Code 3 is a fault. No baseline acceptance means
`not_covered`, not a successful rejection. Client, helpers, startup manifest,
fixtures, and the retained review snapshot are checked for changes. Report
exit 0 requires complete coverage; gaps yield 2, discrepancies 1, integrity
faults 3. No server is started, reloaded, or stopped by this runner.

## Runtime Results

The parent released exclusive access after its family Arena run. Both replays
used the existing server and recorded startup manifest; no new server or
mutable source reload was used. All requests finished, and the parent was
notified that supervisor 85486 could be stopped. The client SHA-256 stayed
`b71273f60ae608b43294530702bf8f6d180deeee6c6916270890039f342f5d8d`.
These runtime results identify the loaded snapshot, not the distinct reviewed
ML model or later source changes. The fixture manifest retains its pre-run
generation status; the following reports are the execution records.

### Existing Export Suite

An identical generated copy of the previous 97-case suite lives under
`tests/hol_family_audit/exports97/`, preserving the old suite and its report.
`exports97/hol-family-report.json` finished at
`2026-09-29T20:04:48.709981+00:00`. Its SHA-256 is
`237669c4176ad75f0f4f377b9cca1883815e2d1c9610c57c36ebb5e998646df8`.

All 7 gates accepted. Mutations returned **45 accept, 6 reject, 46 decline**;
there were no wrong verdicts, faults, outer timeouts, or integrity failures.
All three constructor-table-order controls (Nat, Bool, Tree) now accept.
All nine unequal-large-literal probes decline in 1.62-1.71 seconds instead of
hitting the worker wall limit. They remain code 2, not proven rejections.
The sole positive gap is `tree/control-iota-dependent-index`, still a
10-second worker timeout. Coverage is 51/97; runner exit is 2, not success.

### New Family Witnesses

`tests/hol_family_audit/family-report.json` finished at
`2026-09-29T20:08:03.975370+00:00`. Its SHA-256 is
`3147c39ec7e31c1919dd74c701559948e25ca2d46340385fe019c8114951eb42`.

All 10 positive gates accepted, including the dependent-parameter and iota
identity gates. The 41 mutations returned **10 accept, 2 reject, 29 decline**,
with no wrong verdicts, faults, outer timeouts, or integrity changes. Coverage
is 12/41; all 29 declines remain gaps and the runner exit is 2.

- Every acceptance control, including the branching-family constructor-table
  permutation, accepted.
- The two code-1 results were duplicate-name transport rejections for the
  same-length duplicate and extra-claim cases; they do not independently test
  the HOL membership predicate in isolation.
- Cross-universe and oversized fields failed HOL universe-bound proof search.
  The malformed parameter scope declined as outside the context; the changed
  constructor prefix declined with unsolved metadata goals.
- Negative/nonuniform/self-constructor data fields declined because their
  constants were not in the certified prior environment.
- The wrong-parameter iota case declined in 2.51 seconds. The independent
  wrong-result case hit the 10-second worker limit, so no quick semantic
  rejection or conversion-failure classification is established for it.

No case in either pack was accepted contrary to its reviewed expectation.
This bounded observation is neither a general soundness theorem nor evidence
that code-2 inputs were proved invalid.
