# A Lean 4 Kernel in Rocq or HOL Light

Research date: 2026-09-29. Research and design only; no checker implementation.

## Executive conclusion

**Yes, either Rocq or HOL Light can host a Lean 4 proof checker and proofs about that checker.** Neither requires changing its own kernel merely to represent Lean terms and validate Lean derivations. The decisive distinction is between representing Lean's logic *as data* and translating Lean mathematics into the host's native logic.

My recommendation for this project is:

1. **Use Rocq for the primary new, executable, verified checker**, with Lean syntax deeply embedded and an explicit, versioned acceptance specification.
2. **Start with a small certificate-assisted checker**, proving that every acceptance is justified. Do not start by promising full compatibility, perfect rejection, or normalization of all Lean terms.
3. **Investigate ConLeche's model-based design before porting Lean4Lean wholesale.** This is a significant new alternative: it makes implementation concessions to simplify the semantic soundness proof.
4. **Use HOL Light as an optional independent certificate-replay backend** if a second logical foundation is worth the additional work. It is viable, not disqualified by its simply typed logic.
5. **Do not describe the Solidity checker as verified as a consequence.** Independent certification validates particular results. Verifying all executions of the existing contract requires a separate refinement argument.

These are engineering recommendations, not claims that a prototype has already demonstrated throughput or full Lean compatibility. The strongest directly relevant sources are the current [Lean4Lean specification](https://github.com/digama0/lean4lean/blob/8223d223ed98661882e95d9d6a7126df7097cd76/Lean4Lean/Theory/Typing/Basic.lean), [ConLeche main theorems](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/MainTheorem.lean), and [MetaRocq project](https://github.com/MetaRocq/metarocq).

## 1. What exactly would we be implementing?

There are several different projects hidden in the phrase "implement Lean in Rocq/HOL Light."

| Project | What successful completion establishes | What it does not establish |
|---|---|---|
| An ordinary external checker | Another implementation accepts/rejects exported Lean declarations | A mathematical guarantee that its implementation is correct |
| A verified syntactic checker | Acceptance implies derivability in a specified Lean object logic | Consistency of that object logic, or equivalence to every reference-kernel decision |
| A verified semantic checker | Acceptance implies a suitable interpretation/model exists, under stated assumptions | Necessarily the same intensional typing judgments as Lean's reference kernel |
| A native proof translator | The host checks a translated theorem/proof in its own logic | Faithfulness of the translation unless separately established |
| A verified deployed executable | The actual executing program refines the verified checker | Correctness of an informal interpretation of the theorem or real-world inputs |

For the syntactic route, an appropriate initial target is conceptually:

```text
check_export(fuel, policy, bytes, expected_claim) = Accepted
  implies
there exist E, p, A such that
  bytes decode to the checked declarations,
  E is a well-formed environment built from those declarations,
  E uses only the axioms permitted by policy,
  E proves p : A,
  A and E are bound to expected_claim.
```

This is deliberately more informative than `check(x) = true -> valid(x)`, which is almost meaningless if `valid` merely restates the code.

An optional second theorem connects the object logic to semantics:

```text
model assumptions + well-formed E + E proves p : A
  imply that A is inhabited in the chosen interpretation.
```

Alternatively, prove the model result directly from successful checking, as ConLeche does. That bypasses some metatheory but changes the principal guarantee. Its actual theorem quantifies over a set-theory interface; it does not manufacture that interface from nothing. [ConLeche theorem](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/MainTheorem.lean), [set-theory assumptions](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/SetTheory/Core.lean).

### Why this is not blocked by incompleteness theorems

Proving that a concrete checker obeys an inductively defined relation is not the same as proving that the relation is consistent. A proof assistant can verify the former without proving its own consistency. A consistency/model theorem needs sufficient metatheoretic strength or explicit assumptions. Using another proof assistant does not remove this distinction. Harrison's HOL Light self-verification work explicitly separates these issues and uses strengthened assumptions or a restricted object logic for its consistency results. [Harrison, *Towards self-verification of HOL Light*](https://www.cl.cam.ac.uk/~jrh13/papers/holhol.pdf).

## 2. Why deep embedding works in both systems

Define ordinary datatypes for Lean names, universe expressions, terms, declarations, contexts, and certificates. Define relations such as:

```text
LevelEquivalent(parameters, u, v)
WellFormedEnvironment(E)
HasType(E, universe_parameters, context, term, type)
DefEq(E, universe_parameters, context, left, right, type)
```

Here a Lean universe is a *syntax value*, such as `IMax (Param 0) Zero`; it is not a host universe. A dependent function type is a constructor containing two expressions; it is not necessarily a dependent function type in the host.

This is why HOL Light can represent Lean even though HOL itself is simply typed. HOL Light has datatype definitions and a definitional mechanism for inductively defined relations that yields rule, induction, and cases theorems. Those are exactly the tools needed to describe a small object logic. [HOL Light inductive-relation documentation](https://hol-light.github.io/references/HTML/new_inductive_definition.html).

**What deep embedding does not give for free:** the HOL theorem `HasType E p A` is a theorem *about Lean syntax*. It is not automatically the native HOL theorem expressed by the mathematical reading of `A`. That additional step requires a semantics/translation theorem. Likewise, a Rocq theorem about encoded Lean terms is not automatically a native Rocq proof of the corresponding arithmetic or analysis statement.

## 3. The most important existing work

### 3.1 Lean4Lean: useful specification and implementation, incomplete verification

I inspected a shallow source checkout at commit `8223d223ed98661882e95d9d6a7126df7097cd76` rather than relying solely on the README.

The executable is distinct from the proof developments. Its abstract relation packages typing and typed definitional equality together and includes explicit proof-irrelevance, beta, eta, universe, application, and conversion rules. This is valuable material to adapt into Rocq or HOL. [Typing relation](https://github.com/digama0/lean4lean/blob/8223d223ed98661882e95d9d6a7126df7097cd76/Lean4Lean/Theory/Typing/Basic.lean).

However, the current tree is not a completed, assumption-free verification of a full Lean kernel:

- `Theory/Inductive.lean` defines inductive well-formedness and environment extension using `sorry`.
- `Verify/Environment/Basic.lean` has an `AddInduct` relation with no constructors. Its comment explains that environments containing inductives are outside that verified relation.
- The final declaration-checking proof has a `sorry` in its inductive-declaration branch.
- Projection translation and several conversion/reduction proofs also have holes.
- `Verify/Axioms.lean` assumes equations for various upstream operations, including opaque/partial implementation helpers.

These are concrete proof-boundary issues, not an assertion that the executable mishandles all inductives. Nor should every `sorry` in experimental files be counted as a dependency of every theorem. [Inductive specification](https://github.com/digama0/lean4lean/blob/8223d223ed98661882e95d9d6a7126df7097cd76/Lean4Lean/Theory/Inductive.lean), [environment relation](https://github.com/digama0/lean4lean/blob/8223d223ed98661882e95d9d6a7126df7097cd76/Lean4Lean/Verify/Environment/Basic.lean#L101-L112), [declaration proof](https://github.com/digama0/lean4lean/blob/8223d223ed98661882e95d9d6a7126df7097cd76/Lean4Lean/Verify/Environment.lean#L235), [implementation assumptions](https://github.com/digama0/lean4lean/blob/8223d223ed98661882e95d9d6a7126df7097cd76/Lean4Lean/Verify/Axioms.lean).

**Consequence:** porting Lean4Lean source is feasible, but porting it does not automatically close these proof obligations. The 2024 paper is background; the inspected 2026 source is the evidence for this status. [Lean4Lean paper](https://arxiv.org/abs/2403.14064).

### 3.2 ConLeche: a materially different and promising route

I inspected commit `ae0c0c4e4ce6a0081648aff03fe9c39d002c4526`, using Lean `v4.33.0`.

ConLeche changes some implementation choices to make a model-based proof tractable. Its main result connects successful declaration checking in `.verified` mode to the existence of a model. That is stronger than merely having a second implementation, but different from proving exact equivalence to Lean's algorithm. [Project overview](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/README.md), [formal main theorem](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/MainTheorem.lean).

Important qualifications from the actual declarations and audit files:

1. The theorem has a `[SetTheory V]` parameter. The interface includes a chain of Grothendieck universes and substantial set-theoretic structure. An axiom printout showing only Lean's standard axioms does **not** remove hypotheses in the theorem's statement. [Interface](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/SetTheory/Core.lean#L90-L133).
2. The project contains guarded axiom checks for its main results, expecting `propext`, `Classical.choice`, and `Quot.sound`. I inspected those guards; I did not rebuild and independently execute them. [Axiom audit](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/tests/ConLecheTests/Axioms.lean).
3. Its byte-level `no_False_declaration` corollary is about the particular `jsonWithTheoremFalse` input shape. The source explicitly cautions that this is one shape, not every possible spelling/encoding of a proof of False. The more general model theorem is stated over parsed declarations and the checked environment. [Exact statements](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/MainTheorem.lean).
4. Logical proof dependencies and executable trust dependencies are separate. The repository documents compiler/runtime mechanisms such as `computed_field` and an `implemented_by` primitive, plus the ordinary runtime and bignum boundary. A three-axiom theorem audit is not an end-to-end machine-code theorem. [Runtime trust audit](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/tests/trust-surface.sh), [exclusive-reference helper](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/Kernel/Exclusive.lean).

For our design, the valuable ideas are extra sort annotations, independently checked models for difficult inductive blocks, and acceptance soundness without demanding an ideal reduction algorithm. These ideas can inform a Rocq or HOL implementation; their Lean proofs do not become Rocq/HOL proofs merely by copying the algorithms.

### 3.3 An existing Lean-to-Rocq importer is not the whole answer

`rocq-community/rocq-lean-import` already supports Lean 4 exports. I inspected commit `804a9b77a2dc8555ff6aeab828ce096c1ee4b7b1` from September 28, 2026. This is an active implementation, not just a historical proposal.

Its approach translates Lean declarations into Rocq declarations, using `SProp`, universe-instance transformations, and custom quotient support. That is a different approach from the proposed deep embedding. [Importer description](https://github.com/rocq-community/rocq-lean-import/blob/804a9b77a2dc8555ff6aeab828ce096c1ee4b7b1/README.md), [primitive encodings](https://github.com/rocq-community/rocq-lean-import/blob/804a9b77a2dc8555ff6aeab828ce096c1ee4b7b1/src/Lean.v).

The decisive caveat is in the current source. `with_unsafe_univs` temporarily sets `check_eliminations = false`, and it is called when Lean permits elimination that the translated Rocq inductive would otherwise have restricted. The README describes this historically as disabling universe checking; the **current code specifically disables elimination checks**. It would be inaccurate to report that the inspected function disables every universe-consistency check. [Flag manipulation](https://github.com/rocq-community/rocq-lean-import/blob/804a9b77a2dc8555ff6aeab828ce096c1ee4b7b1/src/lean.ml#L220-L230), [call site](https://github.com/rocq-community/rocq-lean-import/blob/804a9b77a2dc8555ff6aeab828ce096c1ee4b7b1/src/lean.ml#L1531-L1546).

This does not establish that every imported theorem is false or that every input uses the relaxed path. It does mean that "Rocq imported it" is not, by itself, evidence of independent checking under unchanged strict rules. A fail-closed supported subset could still be valuable, provided the actual declarations, permitted axioms, flags, and translation of the requested statement are audited.

The pinned package requires `rocq-core >= 9.3~` or development Rocq. Do not assume the importer and a separately selected MetaRocq release share a toolchain. [Package requirements](https://github.com/rocq-community/rocq-lean-import/blob/804a9b77a2dc8555ff6aeab828ce096c1ee4b7b1/rocq-lean-import.opam).

### 3.4 MetaRocq and McTT show feasibility, not Lean compatibility

MetaRocq provides deep embeddings, metatheory, and a verified checker for PCUIC, Rocq's own calculus. Its published fuel-free SafeChecker relies on strong normalization of well-typed PCUIC terms. This is a premise to understand, not a ready-made theorem about Lean. [MetaRocq overview and SafeChecker](https://github.com/MetaRocq/metarocq#safe-checker).

McTT provides another substantial example of a verified dependent-type kernel in Rocq, for a core MLTT with a cumulative universe hierarchy. It is a useful architectural reference, but its theory is not full Lean: its paper treats extensions such as general inductive types as future work. Do not use its normalization results as if they covered Lean's proof-irrelevant conversion rules. [Jang et al., *McTT*, ICFP 2025](https://hustmphrrr.github.io/asset/papers/icfp25-mctt.pdf).

## 4. The Lean-specific difficulties

### Universes

Lean has non-cumulative universes and universe expressions involving `max` and `imax`. `imax` is essential because a dependent product ending in a proposition remains a proposition. Native Rocq universe behavior cannot simply be substituted for this. A deep embedding makes these explicit object-level operations and allows their algorithms to be verified separately. [Lean FAQ](https://lean-lang.org/faq/), [universe-level implementation guide](https://ammkrn.github.io/type_checking_in_lean4/levels.html).

### Proof irrelevance and elimination

Lean's definitional proof irrelevance is a conversion rule, not merely an optional theorem about equality of proofs. Rocq's ordinary `Prop` is not a drop-in equivalent. `SProp` provides definitional proof irrelevance, but its elimination conditions and configurable definitional UIP still need attention. The importer's relaxation demonstrates an actual compatibility issue, not just a theoretical concern. [Rocq SProp documentation](https://rocq-prover.org/doc/master/refman/addendum/sprop.html), [importer elimination path](https://github.com/rocq-community/rocq-lean-import/blob/804a9b77a2dc8555ff6aeab828ce096c1ee4b7b1/src/lean.ml#L1531-L1546).

### Conversion is not "normalize both terms and compare"

Lean's reference documentation warns about nontermination, failure of subject reduction, and nontransitive algorithmic equality. An ideal typed equality relation may nevertheless be transitive: Lean4Lean's relation explicitly has a transitivity constructor. These are different layers and must not be conflated. [Lean kernel documentation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/#the-kernel), [Lean4Lean equality rules](https://github.com/digama0/lean4lean/blob/8223d223ed98661882e95d9d6a7126df7097cd76/Lean4Lean/Theory/Typing/Basic.lean).

Therefore, do not assume strong normalization of full Lean in order to copy a Rocq-checker proof. Use structurally bounded computation or finite derivation certificates. Prove that acceptance is sound for every fuel value. Exhaustion means `Unknown`, not mathematical invalidity.

This does not prohibit later proving completeness for a carefully delimited fragment or completeness *relative to a terminating algorithmic run*. It rules out promising a total complete decision procedure for unrestricted ideal Lean typing without confronting its known undecidability. [Carneiro, TYPES 2025 abstract](https://msp.cis.strath.ac.uk/types2025/TYPES2025-book-of-abstract.pdf).

### Inductive declarations are a major proof obligation

Checking an application of a recursor is insufficient. The environment must establish why that inductive type, its constructors, eliminator type, and computation rules are legitimate. Positivity, parameter/index discipline, universe restrictions, mutual/nested blocks, and special elimination rules all matter. The export even carries redundant recursor information that must not be treated as its own justification. [Export format](https://github.com/leanprover/lean4export/blob/master/format_ndjson.md), [Lean4Lean inductive verification gap](https://github.com/digama0/lean4lean/blob/8223d223ed98661882e95d9d6a7126df7097cd76/Lean4Lean/Verify/Environment/Basic.lean#L101-L112).

A sensible choice is either a verified admission algorithm or certified elaboration into a smaller trusted basis. ConLeche supplies concrete motivation for the latter. Whichever route is chosen, the certificate cannot simply declare that a supplied recursor rule is sound.

### Other indispensable boundaries

- Function eta, structure eta, unit-like conversion, projections, and K-style reduction need the correct typing side conditions.
- Quotient primitives need their precise signatures and computational behavior; their soundness axiom belongs in the explicit logical policy.
- Literal acceleration must agree with the declared `Nat`/`String` primitives, not just constants having familiar names.
- Axiom declarations, `sorryAx`, compiler-trust axioms, opaque bodies, and unsafe/partial declarations need separate, version-pinned policies.
- Imported dependencies must be checked, or their assumptions must be exposed. A well-typed axiom `bad : False` is still an axiom, not a proof of consistency.

These are proposed proof-obligation categories, informed by the [Lean kernel feature list](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/#the-kernel), [serialized declaration schema](https://github.com/leanprover/lean4export/blob/master/format_ndjson.md), and [ConLeche primitive/axiom policy](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/README.md).

### Where the specification should come from

There is no single document we should copy and treat as a complete, current, mechanically verified Lean 4 specification. Build a versioned rule ledger using complementary sources:

| Rule family | Starting evidence | Required new artifact |
|---|---|---|
| Core typing and typed equality | Lean4Lean's `Theory/Typing/Basic.lean` | Reviewed object-language judgments in the chosen host |
| Operational conversion, projections, literals | A pinned Lean `type_checker.cpp` | Soundness lemmas for each supported operational step |
| Inductive admission and generated recursors | A pinned Lean `inductive.cpp`, plus the selected abstract/model-based treatment | A proved admission procedure or checked model-construction certificate |
| Semantic interpretation | ConLeche's `Denotes`, main theorem, and set-theory interface | Ported definitions and independently checked host proofs, with explicit assumptions |
| Serialized input | A pinned export schema | Decoder/table-validation theorem and statement-binding contract |

The reference implementation documents behavior; it is not itself a proof that every behavior is sound. Conversely, a clean abstract theory must not silently omit a feature that the executable accepts. Record deliberate divergences rather than forcing compatibility with known algorithmic anomalies. I inspected the [v4.33.0 type checker](https://raw.githubusercontent.com/leanprover/lean4/v4.33.0/src/kernel/type_checker.cpp) and [inductive implementation](https://raw.githubusercontent.com/leanprover/lean4/v4.33.0/src/kernel/inductive.cpp) as versioned operational references, not as a complete code audit.

## 5. Rocq architecture

The recommended structure is an ordinary executable Gallina development with independent logical specifications:

```text
Lean export bytes
    |
    v
Decoder + table validation
    |
    v
Lean syntax / environment / explicit axiom policy
    |
    v
Fuel-bounded checker, optionally assisted by untrusted certificates
    |
    v
Accepted claim + explicit dependencies, or a non-accepting result
```

The proof should factor into manageable obligations: decoding, scoping, substitution, level arithmetic, each admissible conversion step, typing, environment extension, primitive recognition, and the whole export pipeline.

Use simple functional data structures first. Optimized maps, hashes, shared DAGs, machine integers, and caches should later be related to that model by refinement lemmas. Cache entries must include all semantically relevant context; a term checked under one local context is not automatically checked under another.

There are two execution modes:

1. **In-host certification:** produce a Rocq proof of the encoded typing judgment, or use a proved reflection theorem with kernel-checked computation of the verifier result. An external Boolean must not be inserted as an axiom.
2. **Standalone checking:** extract the verified function and run it as a normal executable. Its guarantee then depends on extraction, compilation, runtime, and the wrapper matching the proved function.

MetaRocq's verified extraction targets Malfunction, an intermediate language associated with the OCaml compiler. It does not make the downstream OCaml compiler automatically verified. Its repository also distinguishes verified transformations from optional unsafe ones. A first-order bytes/certificate/verdict interface is a useful fit for the verified-interoperability results. [Extraction implementation](https://github.com/MetaRocq/rocq-verified-extraction), [PLDI 2024 paper summary](https://rocq-prover.org/papers/verified-extraction-from-coq-to-ocaml).

**Important:** no `Admitted`, disabled guard/positivity/elimination checks, unchecked proof casts, or arbitrary extraction overrides may be silently accepted in the trusted path. Library axioms must be enumerated. A convenience evaluator with a larger trust boundary must be described honestly rather than called equivalent to strict kernel reduction.

## 6. HOL Light architecture

### Option H1: LCF certificate replay

Define Lean syntax and its derivability relation inside HOL Light. Prove or obtain the admissible rule theorems from those definitions. An OCaml replay procedure then combines those theorems using HOL Light inference operations.

The important output is a value of abstract type `thm` whose conclusion is the intended encoded judgment, not a Boolean saying that an OCaml function liked the input. If replay is wrong, normal LCF use should fail to construct the required theorem. This relies on the kernel and language abstraction boundary and excludes unsafe OCaml escapes or newly introduced axioms. [HOL Light kernel interface and implementation](https://raw.githubusercontent.com/jrh13/hol-light/master/fusion.ml).

In particular:

- Never implement Lean's inference rules by calling `new_axiom` on each desired rule instance.
- Check the final theorem's hypotheses and exact conclusion, not merely that some `thm` was produced.
- Audit the loaded axiom context; `ASSUME P` produces a theorem with hypothesis `P`, not an unconditional proof of `P`.
- A certificate parser can be outside the logical TCB for derivability, but a misparsed *requested claim* can still certify the wrong statement. Input binding remains necessary.

This route does **not** require proving the entire OCaml certificate producer/replayer correct in advance, provided every claimed result is reconstructed through sound theorem operations. It does require a correct object specification and strict use of that interface.

### Option H2: verified reflective checker

Define an executable certificate checker in HOL, prove its acceptance soundness, and use theorem-producing computation to establish its result on concrete inputs. Simply running an unverified OCaml implementation of that function and trusting its return value is not sufficient.

Reflection can amortize repetitive inference work, but needs a verified relationship between the executable representation and the logical function. Whether H1 or H2 performs better on Lean exports is an empirical question; this research did not benchmark either.

### Option H3: semantic interpretation

Formalize a set-theoretic model and prove that accepted Lean declarations have meanings in it. This can be conditional on a set-theory/universe interface, analogous to ConLeche. It should not be advertised as an assumption-free interpretation of Lean's entire universe hierarchy inside ordinary HOL. The representation of the interface, its satisfiability, and the strength of the assumptions require separate review. [ConLeche set-theory interface](https://github.com/leanprover/con-leche/blob/ae0c0c4e4ce6a0081648aff03fe9c39d002c4526/ConLeche/SetTheory/Core.lean), [Harrison on metatheoretic strength](https://www.cl.cam.ac.uk/~jrh13/papers/holhol.pdf).

### Candle and HOL4 are relevant, but distinct

Candle is a HOL Light-compatible prover implemented using CakeML, with an end-to-end soundness result proved in HOL4. Its authors state a machine-code-level guarantee for exported HOL facts. It also has compatibility limitations, so a HOL Light development cannot be assumed to run unchanged. [Candle project](https://cakeml.org/candle/), [compatibility and computation facilities](https://github.com/CakeML/candle/blob/master/README.md).

This creates two longer-term options: replay our HOL development in Candle, or implement a directly verified checker in HOL4 and compile through CakeML. Neither means that ordinary HOL Light OCaml code automatically inherits CakeML's verification. Nor does either verify an EVM binary.

## 7. What evidence goes in a certificate?

This is a proposed design, not an existing format or a claim of measured compactness.

The original Lean proof term is already proof evidence. An auxiliary certificate supplies the otherwise implicit typing/conversion/environment steps so that a simpler checker need not repeat an expensive search.

| Certificate component | What the verifier independently establishes |
|---|---|
| Format/spec version and complete input identity | The certificate applies to this export and this precise checker specification |
| Expression/level/name tables | All references exist, tags and encodings are legal, and scopes are respected |
| Environment prefix identifier | Every referenced declaration was previously validated or explicitly permitted |
| Context and universe-parameter scope | Local-variable and universe references mean the claimed things |
| Rule tag, conclusion, premise-node references | The node is an instance of a permitted inference rule |
| Conversion evidence | Each claimed beta/delta/zeta/iota/eta/proof-irrelevance step has its required premises |
| Universe-equivalence evidence | The relevant level identities hold, not merely a claimed normalized string |
| Inductive admission evidence | Positivity, eliminator restrictions, recursor signatures and equations are justified |
| Primitive evaluation evidence | Accelerated results agree with the recognized logical definitions |
| Final theorem and assumption manifest | The requested statement, not some other valid theorem, follows from the reported assumptions |

For example, to justify application `f a : B[a]`, the verifier requires validated evidence for `f : (x : A) -> B`, evidence for `a : A` or a justified conversion to `A`, and correctly implemented capture-avoiding substitution. Supplying a tag `APP` and a claimed result type is not enough.

For proof irrelevance, it must establish that the common type really is a proposition and both terms inhabit it. It must not equate arbitrary expressions merely because a producer labeled them "proofs."

Use a topologically ordered DAG to share previously checked derivations. Reject cycles and forward references unless a separately justified representation explicitly supports them. Context-sensitive memoization must not confuse identical-looking terms under different binders or environments.

For a structurally recursive verifier, finite certificate replay avoids requiring global normalization. However, the verifier still needs time and memory to validate every referenced step. Witnesses can be much larger than the original proof term, especially when they expose long computations. No claim of automatic compression, linear overall cost, or cheap on-chain checking follows.

Prefer an exact bytes-to-syntax binding in the formal statement. If the external interface identifies inputs only by a cryptographic hash, separately state the hash/encoding assumptions. A hash by itself does not establish that a displayed theorem, an export, and packed EVM calldata denote the same thing.

Certificate failure establishes that **this certificate did not justify acceptance**, not generally that the underlying Lean theorem is unprovable. Keep `InvalidCertificate`, `Unsupported`, `OutOfResources`, and `InternalError` distinct internally.

## 8. Comparison and decision

| Criterion | Rocq | HOL Light |
|---|---|---|
| Encode Lean syntax and judgments | Well suited | Feasible with datatypes and inductive relations |
| Prove a functional checker's acceptance soundness | Strong default fit | Feasible, but less direct standalone implementation path |
| Reuse verified dependent-type-checking techniques | MetaRocq/McTT offer extensive precedents | Fewer directly applicable Lean-like precedents found |
| Native Lean-to-host translation | Existing experimental importer, with important trust caveats | No complete maintained Lean 4 importer established by this research |
| Independent theorem-producing certificate replay | Possible | Particularly natural under LCF |
| High-performance standalone executable | Extraction is an established route; audit its TCB | Requires a deliberate execution/reflection/refinement strategy |
| Independence from Lean's own kernel | Yes, when proofs/checking are established in Rocq | Yes, when replay/proofs are established in HOL |
| Full universe-model consistency argument | Additional model assumptions/work | Additional model assumptions/work; not blocked for syntactic checking |
| Verified native machine-code route | Further pipeline work | Candle or HOL4/CakeML are relevant separate routes |
| Direct verified Solidity/EVM output | Not supplied by choosing Rocq | Not supplied by choosing HOL Light |

The preference for Rocq is my engineering assessment, not a theorem that HOL Light is unsuitable. A team with deep HOL expertise may reasonably reverse the choice, especially for H1 certificate replay. For this project, building two full kernels concurrently would increase proof and maintenance work before answering the main feasibility questions.

## 9. Relationship to the existing Solidity project

I read the existing project's README for context without changing its files. It describes a stateless, bounded whole-export checker and explicitly says it is not formally verified. Its packed-table encoder, serialized metadata, and on-chain result binding are part of the surrounding system, not automatically covered by a new logical proof.

There are three useful integration levels:

1. **Independent off-chain checker:** run the same export through the EVM checker and the Rocq/HOL checker. This offers differential evidence; the verified checker supplies its own guarantee for its own acceptance.
2. **Proof-carrying result:** an untrusted producer supplies an auxiliary certificate; Rocq/HOL validates it independently. The producer could be a native tool, not necessarily an instrumented contract. This avoids requiring the gas-limited contract to emit an enormous trace.
3. **Verified contract refinement:** prove that the contract's real acceptance path, including decoding/representation and relevant EVM behavior, implies the logical acceptance theorem. This is a separate substantial verification project.

Independent certificates remove the need to trust the original checker *for those certified results*. They do not prove that the original checker always follows the rules. Equally, proving the abstract Rocq checker correct does not prove the current Solidity source, `solc` compilation, or deployed bytecode correct.

For blockchain claims, bind the theorem to the intended chain, block/state commitment, data encoding, contract/storage interpretation, and logical assumption policy. A valid Lean theorem about arbitrary supplied data is not evidence that those data were authenticated on-chain.

The native Rocq/HOL checker need not inherit the EVM project's transaction or file-size bounds. It remains constrained by ordinary memory, CPU, and certificate expansion. Conversely, moving verification off-chain does not make the result enforceable by an on-chain contract without an additional verification/attestation mechanism. This report makes no new claim about current Glamsterdam deployment limits.

## 10. Proposed staged work, not yet implemented

### Stage A: freeze the claim and specification

Choose a Lean/export version, supported fragment, axiom policy, and whether the first principal result is syntactic derivability or direct model soundness. Reproduce ConLeche's main theorem/axiom checks before treating its development as a verified dependency. Write an explicit inventory of anything still assumed.

**Exit gate:** a readable theorem statement whose premises and executable boundary are agreed, plus a feature/specification map. No success criterion consisting only of an Arena score.

### Stage B: prove a small Rocq vertical slice

Implement syntax, contexts, capture-avoiding substitution, universe levels, and a bounded certificate verifier for a small dependent-function fragment. Include `Prop` and proof irrelevance early enough to expose the central mismatch. Keep arbitrary inductives outside the initial claim.

**Exit gate:** an acceptance-soundness theorem without admissions for that fragment, legitimate positive examples, and adversarial certificates that cannot pass. A tiny identity theorem alone is insufficient evidence of full-kernel feasibility.

### Stage C: test the difficult boundary before expanding breadth

Add a controlled inductive basis, large-elimination restrictions, equality/K behavior, quotient behavior, and a representative nested/mutual example through a chosen admission/modeling route. Examine ConLeche's annotations and model-generation strategy here.

**Exit gate:** these difficult cases have proofs, not only tests. Any rejected or unsupported valid Lean inputs are explicitly categorized. If this stage exposes a fundamental specification problem, revise the design before building a large optimized checker.

### Stage D: implement the export boundary and broader support

Verify the decoder or explicitly limit the theorem to decoded ASTs until it is verified. Check the entire dependency closure and requested theorem identity. Add proofs for the remaining features and primitive accelerators. Use the Arena corpus plus malformed tables, forged metadata, and certificate mutations.

**Exit gate:** measured coverage with accepts, rejects, unsupported cases, resource declines, and faults reported separately. Arena tests remain empirical evidence, not a substitute for the theorem.

### Stage E: profile and harden execution

Compare unoptimized verified code, optimized code, and certificate-assisted execution. Record wall time, peak memory, certificate expansion, and dependency size on real exports. Add refinements for caches/DAGs and an audited extraction route only where measurements justify the complexity.

**Exit gate:** reproducible build and test data, proof-assumption report, runtime TCB inventory, no unexplained verdict discrepancies, and explicit behavior for resource exhaustion.

### Stage F: optional independent HOL backend

Replay the same small certificates through HOL Light's theorem interface. Validate the same exact conclusion and assumption policy, then evaluate Candle compatibility if a stronger execution guarantee is important.

**Exit gate:** the backend produces checked theorems, not just agreement between two Boolean programs. A second backend is worthwhile only after the shared semantics and claim-binding format are sufficiently stable.

No fixed completion date is defensible before Stages B/C. A narrow prototype is a bounded engineering experiment; full Lean compatibility with proved inductive admission, optimized execution, and byte-level fidelity is a much larger verification undertaking. Agent-generated proofs still require kernel checking and human review of the statements.

## 11. Confidence and remaining questions

**High confidence:** deep embedding is feasible in either host; no host-kernel extension is intrinsically needed; a rewrite alone is not verification; MetaRocq is not a drop-in Lean checker; certificates cannot bypass inference-rule checks; independent checking does not verify Solidity.

**Directly observed at pinned revisions:** Lean4Lean's listed proof gaps; the importer's `check_eliminations = false` path; ConLeche's precise theorem statements, set-theory parameter, axiom guards, and documented executable trust mechanisms.

**Still to establish experimentally or formally:** which design gives acceptable throughput on this project's exports; whether ConLeche's semantic strategy ports cleanly; how much of its proof infrastructure should be reused conceptually; certificate size; strict importer coverage; compatible Rocq/extraction versions; and a complete input-to-requested-statement theorem.

**Research limitation:** I did not build these large proof developments, run their full tests, implement a prototype, or audit every dependency. I could not retrieve the earlier specific Zulip message from the public archive in this session, so I have not attributed new claims or quotations to Chris Bailey. His earlier discussion is motivation, not a formal premise of these findings. Search did not establish an existing full Lean 4 checker verified in HOL Light; this is not a proof that none exists.

See [SOURCE_AUDIT.md](SOURCE_AUDIT.md) for the source snapshots and reproducibility notes.

## Bottom line

**Proceed with a Rocq feasibility slice if the objective is an independent executable checker with a proved acceptance guarantee. Keep HOL Light certificate replay as a viable second stage. Start from explicit Lean semantics, and study ConLeche's direct model-based approach alongside Lean4Lean, rather than treating a translation into either host as verification by itself.**
