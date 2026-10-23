# Extracted DAG Runtime

The default Rocq checker now uses the reviewed DAG admission, persistent environment index,
depth-keyed memo cache and early-header preparation guard. The ordinary checker
also has the reviewed String-conversion ordering correction. This is executable
Gallina, extracted normally to OCaml, not an OCaml verdict cache or Lean oracle.

## Runtime Boundary

The handwritten adapter numbers shared input syntax. Gallina decodes those
rows itself, rejects duplicate/missing/forward references, and retains exact
source expressions in installed declarations. Query caches include context,
checking mode and recursive depth. Hash collisions never establish equality.
The indexed route is selected only with positive fuel and at least 64 existing
declarations; the remaining route uses the proved depth-DAG implementation.

Safe definitions, theorems and safe opaques use the indexed DAG entry. Other
declarations and mutual batches retain the ordinary extended checking semantics.
All successful batches now extend a proof-carrying Gallina environment/index
state. Failed admissions preserve the previous state. There is no supplied
frontend lookup function or reusable frontend proof cache. The index is maintained
below the 64-declaration dispatch threshold too; allocation costs remain a
performance question. Ordinary and safety-local checks still use linear lookup.
See [persistent admission](ROCQ_PERSISTENT.md) for the exact refinement boundary.

After decoding and both root lookups, established early header errors can return
without preparing an index. Duplicate-declaration precedence is retained over
duplicate-universe/unscoped-type errors. Every non-early-error input still runs
the original checks. No success flag bypasses inference or primitive validation.

## What Is Proved

`CombinedAdmissionRefinement.v` proves unconditional equality of complete
`result environment` values against the new ordinary decode-then-admit checker,
for every kind, budget, fuel, environment, names, universes, rows and roots.
`CheapHeaderRefinement.v` additionally compares the previous preparation order.
These statements cover error payloads and installed metadata, not only verdicts.
They impose no valid-input or collision-freedom assumption on the public entry.

The ordinary checker itself is not proved sound against Lean's metatheory.
Native resource consumption, compiler/extraction correspondence, NDJSON parsing
and the handwritten syntax-numbering adapter remain separate trust boundaries.
ReferenceDag modules retain older linear-cache algorithms but import the new
ordinary Checker. They are not the old frozen executable semantics.

The String repair places the exact monomorphic String.ofList hook after the
earlier conversion paths and makes an applicable false result conclusive.
Separately linked old/new extractions demonstrate seven intentional changed
observations: six mixed String-alias comparisons become NotDefinitionallyEqual,
and one corresponding theorem becomes TypeMismatch. Structure, projection,
recursor and direct-distinct-literal controls retain their expected results.
This is a compatibility correction, not a demonstrated false-logical-acceptance
witness or proof of whole WHNF equivalence to Lean4Lean.

## Reproduction

```sh
sh scripts/build-rocq.sh
python3 scripts/test_rocq_native.py
bash scripts/audit-build.sh
build/rocq-check --fuel 16384 arena/corpus/tutorial/001_basicDef.ndjson
```

The build discovers and recompiles all 74 local Gallina proof/regression roots
in dependency order. It links the DAG adapter into the default executable and
runs thirteen bounded native suites. Reports and per-command logs are retained in
`build/reports/rocq-native-*`; a missing completion marker, changed source,
nonzero exit or timeout makes the run fail. Every native subprocess is reaped.
The audit independently rechecks the compiled Rocq objects and scans handwritten
and explicitly identified generated sources separately.

The preceding source-only DAG candidate is pinned by
`/private/tmp/rocq-dag-string-cheap-header-20260930/FINAL_AUDIT.json`.
Its 68 modules passed independent kernel checking without axioms, type-in-type,
unsafe fixpoints, assumed positivity or custom extraction substitutions.
The clean parent staging build reproduces the extraction SHA-256
`68aeb263f51effe0f30a50e19acaca51f3ccdc1e67ae7eccfed4ec8b54d0e705`.

Native coverage includes 4,779 admission, 17,371 theorem/opaque, 31,704 indexed,
28,534 depth and 24,228 cheap-header complete-result comparisons. Metadata has
nine admitted positive gates, 180 full-result comparisons and seven direct
reductions. String tests compare exact results through ordinary, prepared and
indexed routes. These are overlapping regression matrices, not distinct Arena
proof files. Full Arena evidence for that preceding executable is recorded
separately below; historical outcomes are not silently attributed to its successor.

The preceding project-directory rebuild completed all nine suites across 44
bounded compile/link/test subprocesses, with stable source hashes and all
children reaped. Evidence is
`build/reports/rocq-native-20260930T011902Z-92009/report.json`.
That executable SHA-256 is
`2daf6e3382a81e756af455e446e14206907250a5b341e59a5a9a7710bb5e6286`.
Its extraction matches the source-only candidate hash above; executable hashes
differ, so a fresh full run was also completed on the exact shipped binary.

That run attempts all 216 available Arena inputs at fuel 16384 with a 30-second
wall cap per case: 116 correct accepts, 71 correct rejects, 18 allowed-either,
11 timeouts and four missing inputs. There are no wrong verdicts, explicit
declines, native faults or integrity failures. Classifications and terminal
diagnostics match both private composition baselines. The 11 timeouts remain
CSLib, Init, Std, fueled-chain, grind-ring-5, and the six magma list/string
performance cases. They are not rejections or passing tests.

The exact report, summary and independent post-exit audit are retained as
`build/reports/rocq-shipped-dag-arena-{30s,summary,audit}.json`.
All 216 native children were reaped, their process groups are absent, and the
81 runtime/build artifacts plus all input hashes were checked after execution.
The sampled peak process-group RSS was 3.098 GiB; this is not an OS-enforced
memory bound or a proof of resource sufficiency at upstream performance limits.

`toolchain/logs/audit-20260930T012213Z-98551` records the successful 68-module
kernel recheck and source scan. The preceding audit's kernel recheck also passed,
but its scanner falsely matched a qualified Declarations.admit name in comments.
The scanner now distinguishes that name from an admit tactic, with positive and
negative self-tests. The failed report is retained, not relabeled successful.

The subsequent persistent-admission rebuild passes twelve suites across 56
bounded compile/link/test subprocesses, with unchanged input hashes and all
children reaped. Its report is
`build/reports/rocq-native-20260930T141052Z-79013/report.json`.
The persistent-only executable SHA-256 for the Arena run below is
`cd06e5a0241562d1f79b465ee484e5d32a9f392882e8562025e98fd007baa12e`,
and its extraction SHA-256 is
`444bfb9f53e0c3c2a7aab2f0c9ef61e97e86e647645670b67503c37e05ed481b`.
The independent 74-module kernel/source audit passes in
`toolchain/logs/audit-20260930T141200Z-98582`. Its separate full available-corpus
attempt records 117 correct accepts, 71 correct rejects, 18 either outcomes,
ten timeouts and four missing inputs. `grind-ring-5` completes in 28.1 seconds;
all other classifications agree with the older binary. No repeatable or causal
performance claim follows from this single deadline crossing. The exact report
is `build/reports/rocq-shipped-persistent-arena-30s.json`.

The later transport scheduler integration retains the Gallina extraction and
adds the permanent old/new suite. Current main binary is
`853e4eae7d746df50eb9c65d70e094652999c0dec545bee239a8be035720eb29`;
thirteen suites and the 74-module audit pass. See
[the scheduler report](REPLAY_SCHEDULER.md) for separate validation scopes.
