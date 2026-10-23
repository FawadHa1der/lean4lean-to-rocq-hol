# Quotient Dependency Fixtures 841

**SOURCE ONLY. All 54 new proof scripts are UNEXECUTED.** Compilation,
`Print Assumptions`, and recursive `rocq check`/`coqchk` are deferred.
Source review is not proof acceptance, runtime verification, or a kernel
soundness theorem. The parent reviews and packages these files independently.

## Scope and Status

Author-owned output: `/private/tmp/rocq-quotient-regression841` only.
The two `.v` files are frozen. The parent's intended preservation destination
is `tests/rocq_quotient841` in
`/Users/fawadhaider/code/lean4 in rocq:hol light`, outside the production `rocq`
recursive build mapping. This handoff does not copy them there or change any
project source, build mapping, resource limit, fuel policy, or HOL839 source.

The intended target is that independent Lean4Lean port, not the separate
`/Users/fawadhaider/code/lean4` compiler checkout. `AGENTS.md` and checkpoint838
were read. Session7090 remains stopped after827. Nothing here authorizes a
probe, import, compiler, prover, test, native retry, failed-output inspection,
reuse of827's tree, or changed accounting. No Git command was used.

Only source reads, source hashing, declaration counting, and local source edits
were used for this artifact. No compiler/prover/import/test execution occurred.
After the freeze request, only packaging text was written, using already
collected source hashes and counts. No fixture-output digest is fabricated:
the parent should record exact frozen-file hashes when preserving the package.

## Counts and Existing Coverage

| Source | Proposed examples | Proposed lemmas | Proof scripts |
| --- | ---: | ---: | ---: |
| `QuotientDependencyFixtures841.v` / `Q841` | 37 | 7 | 44 |
| `QuotientAdmissionFixtures841.v` / `QA841` | 10 | 0 | 10 |
| New841 total | 47 | 7 | 54 |
| Existing `rocq/QuotientDependencyRegression.v` / `QDR` | 15 | 1 | 16 |

These are source-declaration counts, checked against the pre-freeze declaration
listing, not executed tests, distinct matrix cells, or 54 independent new
behaviors. New compiled proofs, assumption audits, native comparisons, and
Arena verdicts: **zero**. `COVERAGE.txt` lists every new declaration for review
and a future exhaustive assumption audit. Existing16 are not counted as new54.

Existing QDR already supplies:

- Checked ordinary-type and ordinary-constructor reachability, Eq/header
  preconditions, rejection of ordinary dependencies for QCtor/QLift/QInd, and
  genuine member admission (length-based observations).
- Four-kind input-signature self-substitution, QType alpha-renaming, QType
  forged tag/value/name/type/arity cases, and stale-universe refusal.
- QType first-visible shadowing, lift without a constructor versus induction,
  missing-Eq/duplicate-name/fuel first errors, and
  `accepted_quotient_requires_dependencies`.

841 imports that real module for admission fixtures; it does not duplicate its
checked environment builders, three ordinary-forgery rejection assertions,
existing simple first-error assertions, or acceptance-implies-dependencies
proof. Existing source is itself labeled unexecuted; importing it in future
requires freshly compiling and auditing it, not assuming historical success.

## Added Coverage

- Direct header matching and singleton dependency authentication for all four
  kinds, not merely canonical input self-substitution.
- All-kind alpha-renaming; QLift `[v; u]` with substituted type accepts, while
  swapping the same parameter list without substituting its type rejects.
- All-kind header/tag/value/type/name/universe-arity mutations and singleton
  dependency controls. The QType rows overlap existing QDR; the widened matrix
  is the increment, not a new claim for each overlapping row.
- Same-arity QLift duplicate universes: arity and exact substituted-type checks
  remain true while uniqueness is false. Both header and dependency reject.
  Existing QDR's two-universe QType also violates arity, so it did not isolate
  the uniqueness gate.
- Empty, type-only, ctor-only, type+ctor, lift+ind-only, forged-type, and
  forged-ctor dependency graphs. QType needs none; QCtor/QLift need QType only;
  QInd needs both QType and QCtor. The lift/type-only row overlaps QDR.
- First-visible versus buried canonical declarations for all four tags,
  unrelated-name skipping, each QInd dependency shadowed separately, and
  independently named type/constructor universe binders.
- Exact installed declarations for genuine admissions, absence of a constructor
  during lift admission, and all-kind renamed inputs installing canonical
  declarations. These strengthen the existing length-based positive witnesses.
- Additional compound ordering: duplicate name versus duplicate universes,
  scope and zero fuel; duplicate QLift universes versus scope and fuel; scope
  versus fuel; unknown header constant versus dependency rejection.
- Seven operational lemmas: dependency equations, first-visible lookup, Eq
  rejection propagation, and header rejection/decline propagation. They do not
  establish typing preservation or correspondence with Lean/HOL.

The checked positive and ordinary-impostor environments are exactly QDR's
environments built from `Metadata.eq_env` through real checked admission.
Expected `Accept` payloads make the new admission observations non-vacuous.
`InputAxiom` in the existing fixture is an object-language declaration input,
not a Rocq axiom or an unchecked proof admission.

## Mutation Provenance

All raw records start from the production `canonical_quotient`. `retag`,
`reheader`, `with_value`, and `renamed` only construct input data; they do not
implement a second checker or return precomputed logical verdicts.

| Mutation | Deliberately changed | Preserved / control |
| --- | --- | --- |
| Wrong kind | Rotate QType/QCtor/QLift/QInd tags | Name, params, type, value, hints |
| Ordinary forgery | DAssumption/DDefinition/DTheorem/DOpaque tag | Canonical header; raw-only except QDR's checked assumptions |
| Unsafe tag | Wrap the correct tag in DUnsafe | All other fields |
| Present value | None becomes Some (ESort LZero) | Correct name, tag, params, type |
| Bad type | Type becomes ESort LZero | Remaining fields; syntactically valid but noncanonical type |
| Wrong name | Fresh unrelated name | Header otherwise retained; lookup-skip control included |
| Alpha rename | Params plus actual subst_levels result | Correct kind/name and no value |
| Stale rename/swap | Params only | Old canonical type intentionally retained |
| Duplicate QLift | Two equal params and consistently substituted type | Same arity; explicit type-equality witness |
| Missing/excess arity | Empty or fresh extra params | Type obtained with the real substitution function |
| Shadowing | List order only | Identical good/bad declarations in opposite orders |

Raw-record positives exercise predicates only; they are not claimed reachable
checked environments. Likewise malformed raw definitions/theorems are not
claimed well-typed. There is no axiom, Admitted, unchecked cast, native compute,
trust-expanding flag, or hand-rolled replacement checker in the new sources.

Several later admission guards return the same `MalformedDeclaration`. Equal
results cannot by themselves distinguish their relative order. The distinct
earlier errors/decline and the general propagation lemmas address observable
ordering; no finer same-error branch-order experiment is claimed.

## Provenance and Pins

`SOURCE_PINS.sha256` contains the exact input-source hashes collected during
this source-only task. Paths are relative to the independent project root,
not this package. It covers the manually traced local `.v` dependency closure,
the existing QDR fixture, target implementation, build-reference files,
instructions/checkpoint, and attribution. It is not a toolchain/Stdlib pin set,
compiled-object manifest, fresh custody grant, or execution receipt.

Primary target `rocq/Quotient.v` SHA-256:
`bedc3b8bbdc8efde0ad685a49a15fdae2c23bf172f8c89135bca5eff79886ea5`.

The project's UPSTREAM.md/NOTICE identify Lean4Lean revision
`8223d223ed98661882e95d9d6a7126df7097cd76`, Mario Carneiro and contributors,
Apache-2.0. The local `vendor/lean4lean/Lean4Lean/Quot.lean`, its license, and
the port's NOTICE/license are pinned. This revision attribution comes from
project source documentation, not a Git lookup. The new fixtures adapt the
port's test construction patterns and existing QDR/Metadata fixtures; preserve
their attribution and Apache-2.0 license when packaging. No upstream proof
admission is used to discharge these statements.

## Future Compilation: Not Run

This is a plan only, contingent on separate fresh authorization and the
parent's reviewed resource, ownership, cleanup, timing and custody controls.
Do not use the stopped session as authority. Do not run this plan now.

1. Parent independently reviews the frozen841 files and captures their hashes
   before copying them byte-for-byte to `tests/rocq_quotient841`. Preserve the
   manifest and notice/license references; do not add them to production
   `rocq/_CoqProject` or a broad recursive compile list.
2. For an authorized run, create an entirely fresh reviewed staging tree with
   `rocq/` and `tests/rocq_quotient841/`. Stage only pinned source inputs and
   frozen fixture sources. Check their exact hashes and independently confirm
   the import closure. Any changed pin requires review, not silent repinning.
3. **Build every LeanPort dependency fresh from those staged pinned sources.**
   Never copy/reuse working-tree `.vo`, `.vos`, `.vok`, `.glob`, `.aux`, extracted
   products, old build mappings, or827 outputs. Do not map production `rocq`
   into the compiler load path. Exclude ambient LeanPort/Quotient841 mappings;
   pin and review the actual compiler, Stdlib and allowed load-path resolution
   separately. The command templates below alone are not that review.
4. Compile in dependency order, keeping the original limits and callbacks.
   Do not use a trust-bypass/quick-admission compilation mode. Compile each
   source with the equivalent of `rocq compile -Q <fresh>/rocq LeanPort`.
   Run from the fresh staging directory: `EnvironmentIndexBenchmark.v` and
   `EnvironmentIndexSuffixBenchmark.v` contain extraction commands that write
   relative output files even though these fixtures request no native build.
   Those writes must be contained and covered by the authorized run plan.

Core dependency order (then the first841 file):

```text
Syntax Universes EagerPolicy NatProbeDispatch WhnfPolicy Checker
InductiveUtils Primitives Declarations Quotient
```

Additional order for the admission file, after that core (source-inspected,
not compiler-validated; parent must confirm the closure before execution):

```text
Inductive EnvironmentIndex EnvironmentIndexBenchmark
EnvironmentIndexSuffixBenchmark LookupIntegration LookupCore LookupRefinement
IndexedChecker RuntimeChecker PreparedDagLookup DagScope DagMemo
DagMemoReference DagArena DagQuery DagInfer DagEntry DagAdmission
DagTheoremOpaque ReferenceDagQuery ReferenceDagInfer ReferenceDagEntry
ReferenceDagAdmission ReferenceDagTheoremOpaque DepthAdmissionRefinement
IndexedDagInfer IndexedDagAdmission CombinedAdmissionRefinement
MetadataFixtures QuotientDependencyRegression
```

Once all required dependencies have been freshly built, the individual841
commands below describe the logical mappings. `FRESH` must be the separately
approved clean stage; `REVIEWED_ROCQ` must be the separately pinned compiler.
These are NOT a runner, grant, or permission to execute:

```sh
"$REVIEWED_ROCQ" compile -Q "$FRESH/rocq" LeanPort \
  -Q "$FRESH/tests/rocq_quotient841" Quotient841 \
  "$FRESH/tests/rocq_quotient841/QuotientDependencyFixtures841.v"

"$REVIEWED_ROCQ" compile -Q "$FRESH/rocq" LeanPort \
  -Q "$FRESH/tests/rocq_quotient841" Quotient841 \
  "$FRESH/tests/rocq_quotient841/QuotientAdmissionFixtures841.v"
```

The first841 file only needs the core closure. The second imports the freshly
built first841 file and the real existing QDR/Metadata modules. Its wider import
closure is incidental to reusing checked fixtures, not replacement kernel scope.

## Future Assumption Audit: Not Run

After successful fresh compilation, prepare a separately reviewed audit source
in the same fresh stage. Import both841 modules and existing QDR, and emit
`Print Assumptions` for **every** name in `COVERAGE.txt`, not just the seven
lemmas. Also audit all15 existing QDR examples and its dependency lemma, since
the admission fixtures rely on their environments and documented witnesses.
Use these qualified prefixes:

```text
Quotient841.QuotientDependencyFixtures841.Q841.
Quotient841.QuotientAdmissionFixtures841.QA841.
LeanPort.QuotientDependencyRegression.QDR.
```

For example, a future audit command in that source is:

```coq
Print Assumptions Quotient841.QuotientDependencyFixtures841.Q841.duplicate_lift_header_and_dependency_are_rejected.
Print Assumptions Quotient841.QuotientAdmissionFixtures841.QA841.alpha_renamed_inputs_install_canonical_declarations_each_kind.
Print Assumptions LeanPort.QuotientDependencyRegression.QDR.accepted_quotient_requires_dependencies.
```

Those three examples are not the exhaustive audit. Compare the full name list
to the frozen sources, require complete output and closed contexts, and retain
any unexpected assumption as a failure rather than hiding it. Perform recursive
`rocq check` (the Rocq counterpart of `coqchk`) over both841 module roots and
the existing QDR root, resolving only freshly built LeanPort objects and the
reviewed Stdlib/toolchain. The source Makefile's `rocq check -silent -o` pattern
is a reference, not evidence that any audit has run. No selective no-check or
admitted-dependency options are permitted.

Retain exact source/output pins, commands, results, complete assumption output,
recursive audit result and required cleanup receipts. Report compilation,
assumption closure and recursive checking separately. A passing future fixture
cohort would establish these concrete operational assertions only, not full
Lean semantics, HOL839 correctness, whole-kernel soundness or Arena coverage.
