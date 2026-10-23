# Trust and Build Audit

This document separates kernel-checked facts, executable behavior, and trusted
interfaces. Neither passing the audit nor passing regression tests establishes
a verified Lean-compatible checker.

## Run

After the parent has finished building the ports and workers stop editing:

```sh
bash scripts/audit-build.sh --self-test
bash scripts/audit-build.sh
```

The script does not rebuild or edit the ports, install packages, start Lean,
or start HOL Light. Reports go to a unique `toolchain/logs/audit-TIMESTAMP-PID/`.
It fails while toolchain setup is active. Required utilities are Bash, ripgrep,
`find`, `sort`, `shasum`, and the local Rocq toolchain.

The audit discovers every `rocq/**/*.vo` and supplies all corresponding
`LeanPort.*` modules to `rocq check -Q rocq LeanPort -o`. Dependencies are also
checked: no `-admit`, `-norec`, or unchecked proof flags are supplied. Missing
objects for `.v` sources and sources newer than their objects fail the audit.
This timestamp check is a freshness warning, not cryptographic evidence that
a particular object was built from a particular source. Before/after input
hashes and inventories detect concurrent changes; a changing tree must be
rebuilt and audited again.

The assumption summary must report no axioms, type-in-type, unsafe fixpoints,
or assumed positivity. The report records the exact selected modules, source
files, Rocq version, hashes, scan hits, freshness failures, and complete checker
output. A kernel check can succeed while the overall audit fails for stale
sources or source-scan findings. These outcomes must not be conflated.

## Source Scan

All `.v`, `.ml`, and `.mli` files below `rocq/`, `hol/`, and `frontend/` are
considered, including files ignored by Git. The known extraction outputs are
the `.ml` and `.mli` pairs below `rocq/` for `lean_core`, `lean_arena`,
`depth_native`, `metadata_native`, `cheap_header_native`, `string_parity`,
`environment_index_extracted`, `environment_index_suffix_extracted`, and
`persistent_tests_native`.
These exact paths are excluded only from the handwritten
inventory; every discovered generated implementation and interface receives a
separate unsafe-operation scan and is listed in `generated-files.txt`. They
remain included in input hashes and change detection. New generated filenames
require an explicit audit-policy review.

`rocq/Extract.v`, `rocq/ArenaExtract.v`, `rocq/NewInductive.v`, and
`rocq/InductiveUtils.v` remain handwritten sources subject to the normal Rocq
scan, object freshness checks, and kernel rechecking. The self-test covers
both generated-output pairs and these handwritten classification boundaries.

The conservative text scan flags:

- Rocq admissions, declared axioms/parameters, disabled guard/positivity/
  universe/elimination checks, and unchecked cast tactics.
- Extraction constant/inductive overrides, disabled safe implicits, and
  standard `ExtrOcaml*`/other-language representation-mapping imports.
- HOL `new_axiom`/`mk_thm`, unsafe `Obj` operations, and unchecked `Marshal`
  deserialization in handwritten OCaml/HOL or generated extraction.

This is not a parser, abstract interpreter, or hostile-code security audit.
Comments and string literals may produce findings requiring human review;
aliases, dynamic loads, unusual syntax, or unrecognized unsafe interfaces may
escape it. Keep the separate kernel assumption check and code review.
The object-language constructor `InputAxiom`, frontend `Wire.Axiom`, and the
checker function named `admit` are not Rocq proof admissions. Scanner fixtures
test these distinctions. Object-language assumptions still affect the meaning
of accepted declarations and must be covered by the checker specification.

## Rocq Proofs

Rocq checks definitions, termination, and theorem bodies in the compiled
objects. Current proved facts include structural helper properties, fuel
declines, guarded-sublevel comparison soundness, declaration edge cases, and
the decomposition of a successful `check` result. Regression propositions
certify particular computations. `check_accepts_conversion` is an operational
decomposition theorem, not a semantic typing-soundness theorem.

The universe component now has separately reviewed proofs of normalization
semantics, comparison soundness/completeness, negative witnesses, sufficient
fuel, and universe-instantiation semantics. Six further theorems establish
syntactic commutation with term lifting/substitution and preservation of
de Bruijn scope. There are 33 public component theorems across these modules;
see `docs/ROCQ_UNIVERSE_SOUNDNESS.md`. These use the port's natural-valued
universe interpretation and are not a correspondence theorem to upstream Lean.
The audit does not supply semantic term-substitution/typing preservation, reduction preservation,
environment/inductive admission or whole-checker inference/conversion
soundness/completeness proofs. Consult `docs/ROCQ.md` for the evolving inventory.
New modules are automatically checked, but their theorem statements must
still be reviewed for whether they establish the intended property.
The batched-substitution theorem proves equivalence to the original sequential
implementation, and the combined DAG/depth/index theorem proves complete-result
refinement to the corrected ordinary checker. Neither is a semantic typing
soundness proof.

## Extraction and Frontend

The current `rocq/Extract.v` and integration entry point `rocq/ArenaExtract.v`
request structural OCaml extraction to `lean_core.ml` and `lean_arena.ml`,
respectively, without custom `Extract Constant` or `Extract Inductive`
replacements. Their generated-output classification does not authorize unsafe
representation mappings or casts. The extracted
program is not an independently proof-checked OCaml executable. Trust remains
in Rocq's extraction implementation, the OCaml compiler/runtime, linking,
the OS, and execution resources. The toolchain's separate bounded successor
smoke uses a machine-integer mapping; that test is not the port's extraction
policy and is deliberately outside this source scan.

The handwritten JSON/NDJSON parser, name interning, AST conversion, numeric
conversion, fuel handling, environment updates, and output-verdict mapping
are another boundary. Yojson and Zarith smoke tests show usable libraries,
not verified serialization or end-to-end semantic preservation. Reject,
decline, unsupported input, exhaustion, and operational errors must remain
distinct. A kernel-rechecked `.vo` does not validate the frontend executable
or bind the final executable to the scanned source.

## HOL Light

Ordinary upstream HOL Light is not axiom-free. Its pinned 3.1.0 core introduces
`ETA_AX` and `SELECT_AX` in `class.ml`, and `INFINITY_AX` in `nums.ml`, using
the primitive axiom interface declared in `fusion.ml`. These are explicit
upstream logical assumptions, not new axioms introduced to discharge this
port's obligations. They are outside the handwritten project scan.

The current HOL port defines object-language datatypes, recursive functions,
and an inductive typing/equality relation, then constructs HOL theorems through
LCF inference. Success is intended to carry a theorem with empty hypotheses
and the exact requested object-language conclusion. That proves the encoded
judgment relative to HOL's core and axioms; it does not prove that the encoded
rules match Lean, that the search is complete, or that the frontend translation
is correct. A successful bounded checker result is not a model-consistency
theorem.

`hol/tests.ml` compares the axiom list before and after loading the port and
checks exact conclusions/empty hypotheses. The parent owns execution of that
regression suite; this audit does not silently substitute the toolchain smoke
for it. `hol_light_module` is not installed, so the optional inliner/module
trust extension is not enabled. OCaml, the HOL parser and kernel, the normal
upstream core, and hardware/OS remain trusted.

## Observed Results

On 2026-09-29 the full toolchain smoke passed: native OCaml Unix operations,
Yojson/Zarith, Rocq proof checking and rejection, object rechecking, executable
extraction, and HOL theorem construction/rejection. ShellCheck and scanner
positive/negative fixtures passed.

The first port audit (`audit-20260929T172606Z-77857`) rechecked all eight objects
then present, including `LeanPort.InductiveUtils`. Rocq reported no axioms,
type-in-type, unsafe fixpoints, or assumed positivity. Handwritten and generated
source scans had no hits. The overall run correctly failed because `Syntax.v`
was newer than `Syntax.vo`. This is historical evidence for those artifacts,
not a clean audit of subsequent shared-directory edits. Rebuild and rerun after
the current edits finish.

The later audit `audit-20260929T220147Z-49253` passes the complete audit on its
unchanging input inventory: **28 Rocq objects**, independent kernel rechecking,
freshness checks, and handwritten/generated unsafe-operation scans. There are
no reported axioms, type-in-type dependencies, unsafe fixpoints or assumed
positivity. Scanner positive/negative fixtures also pass. The preceding run
`audit-20260929T215932Z-45537` rechecked its 27 objects successfully but failed
overall for the missing current `EnvironmentIndexBenchmark.vo`; it is not a
clean-audit result. The normal build now compiles that isolated benchmark from
`build/environment-index-proof`, keeping its extraction outputs out of the
handwritten source tree and its code out of the production executable.

At that historical checkpoint, the production executable SHA-256 remained
`3ef3328088cc6f91a4113947ffb6d97196e840bcb4f6d9445512fa9e5ef86be3`,
and `Checker.v` remained
`bdd3d477db4d16796e48f9e57067cebcf8b2cfd49449888d28e70d8f7780d745`.
The private complete lookup/refinement and cheaper-hash admission candidates
have separate source/build/proof audits; they are not thereby part of this
production executable. This passing audit still does not establish overall
logical soundness, parser correctness or verified native extraction.

The later project-directory build and audit
`audit-20260930T012213Z-98551` rechecked the then-current 68 Rocq modules, with no
axioms, type-in-type, unsafe fixpoints or assumed positivity. Nine native suites
pass through 44 bounded, reaped build/test subprocesses, with stable source
hashes. The current DAG runtime and executable identity are documented in
[the runtime report](ROCQ_DAG_RUNTIME.md); the historical hashes above do not
identify it. The preceding audit passed the kernel recheck but failed a scanner
false positive on qualified `Declarations.admit` names in comments. That failed
report remains retained, and the corrected scanner has positive and negative
regressions. These checks do not remove the trust boundaries described above.

The persistent-admission build is now independently rechecked in
`audit-20260930T141200Z-98582`: all 74 modules, unchanged source/object inventory,
no axioms, type-in-type, unsafe fixpoints or assumed positivity, and clean
handwritten/generated source scans. Its twelve native suites also pass in
`build/reports/rocq-native-20260930T141052Z-79013/report.json`. Persistent-state
proofs establish complete-result refinement to the corrected ordinary checker,
not that checker's overall logical soundness or an OCaml extraction theorem.

The subsequent transport scheduler build is rechecked in
`audit-20260930T144212Z-18766`: all 74 modules and both source scans pass, with
the same absence of unsafe assumptions. Its thirteen native suites pass across
60 bounded compile/link/test steps in
`build/reports/rocq-native-20260930T144114Z-16001/report.json`; before/after source
hashes agree and every child is reaped. Runtime `853e4eae...` retains extraction
`444bfb9f...`; only the handwritten scheduling transport changed. The additional
reference/differential suite is test-only and never supplies checker verdicts.
