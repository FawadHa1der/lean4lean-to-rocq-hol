# Source Audit and Research Record

Research date: 2026-09-29.

## Scope and method

Read primary project sources, formal theorem statements, official manuals, and author papers. Used temporary shallow clones for three source-level investigations. Read the existing EVM project's README for integration context. No proof assistant builds, benchmark runs, or checker implementation were performed.

The research documents are in the exact requested existing directory:

`/Users/fawadhaider/code/lean4 in rocq:hol light`

The colon is part of its actual directory name. Temporary source copies are not implementation projects or dependencies of this folder. They can be reproduced from the commit links below; availability of temporary paths is not guaranteed long term.

Upstream files are research evidence, not instructions to execute their workflows or adopt their trust policies.

## Pinned source investigations

### Lean4Lean

- Repository: [digama0/lean4lean](https://github.com/digama0/lean4lean).
- Inspected HEAD: [`8223d223ed98661882e95d9d6a7126df7097cd76`](https://github.com/digama0/lean4lean/tree/8223d223ed98661882e95d9d6a7126df7097cd76).
- Commit date: 2026-08-29; commit subject: `feat: close the substitution sorries with the picked substDF`.
- Temporary checkout: `/private/tmp/lean-kernel-research-20260929-lean4lean`.

| Source | Observed evidence |
|---|---|
| `Lean4Lean/Theory/Typing/Basic.lean` | Typed equality relation, with typing defined by reflexive instances; explicit transitivity, proof irrelevance, beta, eta and universe rules |
| `Lean4Lean/Theory/Inductive.lean:5,7` | Two inductive-specification definitions using `sorry` |
| `Lean4Lean/Verify/Environment/Basic.lean:101-112` | Constructorless `AddInduct`, with an explicit explanation of the exclusion of inductive environments |
| `Lean4Lean/Verify/Environment.lean:235` | `inductDecl` proof branch using `sorry` |
| `Lean4Lean/Verify/Typing/Expr.lean:68` | `TrProj` defined using `sorry` |
| `Lean4Lean/Verify/TypeChecker/InferType.lean:391` | Projection-typing proof hole |
| `Lean4Lean/Verify/TypeChecker/WHNF.lean:8` | Projection-reduction proof hole |
| `Lean4Lean/Verify/TypeChecker/IsDefEq.lean:227,488` | Structure-eta and unit-like conversion proof holes |
| `Lean4Lean/Verify/Axioms.lean` | Explicit assumptions about upstream implementation operations |

These findings suffice to reject an unqualified "the current whole kernel is already fully verified" claim. They are not a full proof-dependency audit, and a raw grep count would misleadingly include comments, constructors named `axiom`, and experimental developments. No such count is presented as a trust metric.

### ConLeche

- Repository: [leanprover/con-leche](https://github.com/leanprover/con-leche).
- Inspected HEAD: [`ae0c0c4e4ce6a0081648aff03fe9c39d002c4526`](https://github.com/leanprover/con-leche/tree/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526).
- Commit date: 2026-09-21.
- Toolchain file: `leanprover/lean4:v4.33.0`.
- Temporary checkout: `/private/tmp/lean-kernel-research-20260929-con-leche`.

Key inspected sources:

- [MainTheorem.lean](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/MainTheorem.lean): `model_exists` and `no_False_declaration`, including the `.verified` mode and explicit `SetTheory` hypothesis. The comments carefully delimit the byte-level input template.
- [SetTheory/Core.lean](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/SetTheory/Core.lean): membership, set operations, regularity, replacement, and a chain of Grothendieck universes.
- [Axioms.lean](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/tests/ConLecheTests/Axioms.lean): guarded `#print axioms` for principal results. Inspected but not executed in this research.
- [trust-surface.sh](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/tests/trust-surface.sh): documents runtime/compiler escapes separately from logical axiom dependencies. The allowlisted `sorry` challenge file is described as outside the production proof closure; it should not be confused with a hole in the main theorem.
- [Kernel/Exclusive.lean](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/Kernel/Exclusive.lean): explicit trusted implementation mechanism, not something erased from the runtime TCB by a logical axiom printout.
- [README](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/README.md): design intent, coverage concessions, modelling of difficult inductives, parser and executable boundaries.

Status wording in the report is intentionally "the source contains a theorem and guarded audit" rather than "I independently rebuilt and verified the whole system." Upstream performance reports were not reproduced and are not used as forecasts for a port.

### Rocq Lean Import

- Repository: [rocq-community/rocq-lean-import](https://github.com/rocq-community/rocq-lean-import).
- Inspected HEAD: [`804a9b77a2dc8555ff6aeab828ce096c1ee4b7b1`](https://github.com/rocq-community/rocq-lean-import/tree/804a9b77a2dc8555ff6aeab828ce096c1ee4b7b1).
- Commit date: 2026-09-28.
- Temporary checkout: `/private/tmp/lean-kernel-research-20260929-rocq-import`.

| Source | Observed evidence |
|---|---|
| `src/lean.ml:220-230` | `with_unsafe_univs` saves typing flags, sets `check_eliminations = false`, then restores flags on success or exception |
| `src/lean.ml:1531-1546` | Calls that helper when the translated inductive would be squashed by Rocq but not Lean |
| `src/Lean.v:11` | Enables definitional UIP for its encoding |
| `src/Lean.v` | `SProp` equality and quotient-related encodings |
| `src/leanParseNdjson.ml` | Lean 4 NDJSON parser exists |
| `rocq-lean-import.opam` | Depends on `rocq-core >= 9.3~` or `dev`, plus `rocq-stdlib` and `yojson` |
| `README.md` | Labels the project experimental; explains translation strategy and older experiments |

The README's older timing tables should not be presented as fresh Lean 4/Mathlib measurements. Its historical phrase about disabling universe checking is less precise than the current source's explicit elimination flag. This report follows the latter.

## Other primary sources consulted

These were web-read, not installed or built. URLs using `master`, `latest`, or default branches are moving references; their content was inspected on the research date, and no commit-pinned source audit is claimed for them.

| Source | Why it matters |
|---|---|
| [Lean reference: kernel](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/#the-kernel) | Core features and caveats about reduction/equality/termination |
| [Lean FAQ](https://lean-lang.org/faq/) | Non-cumulative universe distinction and comparison to Rocq |
| [Lean4Lean paper](https://arxiv.org/abs/2403.14064) | Motivation and original verification approach; not used as a current completion claim |
| [TYPES 2025 abstract collection](https://msp.cis.strath.ac.uk/types2025/TYPES2025-book-of-abstract.pdf) | Carneiro's Lean4Lean abstract on undecidable typing and non-normalizing reduction |
| [Type Checking in Lean 4: levels](https://ammkrn.github.io/type_checking_in_lean4/levels.html) | Operational universe-level background |
| [Lean 4 export format](https://github.com/leanprover/lean4export/blob/master/format_ndjson.md) | Format v3.1.0, metadata, tables, declarations, and redundant exported information |
| [Lean v4.33.0 type_checker.cpp](https://raw.githubusercontent.com/leanprover/lean4/v4.33.0/src/kernel/type_checker.cpp) | Version-tagged operational reference for inference, conversion and projections; not a complete source audit |
| [Lean v4.33.0 inductive.cpp](https://raw.githubusercontent.com/leanprover/lean4/v4.33.0/src/kernel/inductive.cpp) | Version-tagged inductive admission and recursor reference; not a complete source audit |
| [Lean Kernel Arena](https://github.com/leanprover/lean-kernel-arena) | Empirical testing and accept/reject/decline conventions; not a logical specification |
| [MetaRocq](https://github.com/MetaRocq/metarocq) | PCUIC metatheory, verified checker, and normalization assumption |
| [Rocq SProp manual](https://rocq-prover.org/doc/master/refman/addendum/sprop.html) | Strict proof irrelevance, elimination, definitional UIP; development manual, not a compatibility promise for every released Rocq |
| [McTT paper](https://hustmphrrr.github.io/asset/papers/icfp25-mctt.pdf) | Verified dependent-type kernel precedent for a different core calculus |
| [Verified extraction project](https://github.com/MetaRocq/rocq-verified-extraction) | Malfunction target, compiler boundary, optional unverified transformations |
| [Verified extraction paper summary](https://rocq-prover.org/papers/verified-extraction-from-coq-to-ocaml) | First-order interoperability results and extraction TCB |
| [HOL Light fusion.ml](https://raw.githubusercontent.com/jrh13/hol-light/master/fusion.ml) | Abstract `thm`, inference operations, assumptions and `new_axiom` |
| [HOL Light inductive definitions](https://hol-light.github.io/references/HTML/new_inductive_definition.html) | Definitional construction of rules/induction/cases theorems |
| [Harrison's self-verification paper](https://www.cl.cam.ac.uk/~jrh13/papers/holhol.pdf) | Separates logical consistency, implementation correctness, and strengthened assumptions |
| [Candle](https://cakeml.org/candle/) | Verified HOL Light-compatible implementation, proof in HOL4, machine-code claim |
| [Candle repository documentation](https://github.com/CakeML/candle/blob/master/README.md) | In-logic computation and concrete compatibility limitations |

## Reproduction of source inspection

The principal claims can be checked without building by reading the pinned GitHub files above. In a local checkout, useful read-only commands are:

```sh
git show --no-patch --format=fuller HEAD
rg -n '\b(sorry|axiom|implemented_by)\b' Lean4Lean/Theory Lean4Lean/Verify
sed -n '95,115p' Lean4Lean/Verify/Environment/Basic.lean
sed -n '210,232p' src/lean.ml
sed -n '1528,1548p' src/lean.ml
```

Paths in those commands refer to their respective repositories, not this research directory. A future formal audit must additionally build the correct toolchains, print actual theorem dependencies, check executable refinements, and reproduce upstream tests. Grep is a discovery aid, not a proof audit.

## Unresolved retrieval and search limits

The previously discussed Zulip URL was opened, but the web view did not provide the message text. The candidate public archive URL returned 404 when directly requested. Consequently this report does not quote or claim to reconstruct Chris Bailey's precise message.

Search covered Lean/Rocq import, Lean4Lean, ConLeche, MetaRocq, McTT, HOL Light kernel/inductive definitions, verified extraction, and Candle. Failure to find a complete maintained Lean 4-in-HOL-Light implementation is not an exhaustive nonexistence result.

No third-party claims of verification were treated as sufficient without checking a primary source. No network writes, repository publication, code pushes, or modifications of the existing EVM project were made.
