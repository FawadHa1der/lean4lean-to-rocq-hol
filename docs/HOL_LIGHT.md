# HOL Light Lean 4 Kernel: Architecture, Evolution & Layer Guide

> **Directory Guide (Updated 2026-10-26)**: See [`hol/README.md`](../hol/README.md) for a quick-reference overview of the four HOL Light kernel stages:
> - **[`hol/kernel_v3_complete/`](../hol/kernel_v3_complete/)** *(legacy symlink: `hol/full_kernel_candidate839/`)* — **Canonical & complete 13-constructor HOL Light implementation** (full kernel + whole-file driver + `Compute` registry + quotient dependency authentication `839`/`941` + declarative metatheory, soundness bridge, atomic `addQuot`/`quotInit` transaction, `DefEqCache`, and `FuelConfig` `961`–`965`).
> - **[`hol/kernel_v2_full_file/`](../hol/kernel_v2_full_file/)** *(legacy symlink: `hol/full_kernel_candidate652/`)* — Historical full-file admission & `Compute` bundle (`652`), synchronized with the `961`–`965` metatheory modules.
> - **[`hol/kernel_v1_core_only/`](../hol/kernel_v1_core_only/)** *(legacy symlink: `hol/full_kernel_candidate612/`)* — Self-contained 43-module 13-constructor core bundle (`612`, verified via `run_proofs612.ml`).
> - **[`hol/*.ml`](../hol/)** *(v0 baseline layer, documented below)* — Initial 9-constructor LCF theorem-producing checker (`core.ml`, `admission.ml`, `environment.ml`) used by `frontend/hol_check.ml` and `hol/test.sh`.

## Baseline Layer (`hol/*.ml`): Adapter interface (established first)

Load `hol/core.ml` in an initialized HOL Light process, with repository root as
the current directory. It defines module `Lean4hol`:

```ocaml
type name = Anonymous | Str of name * string | Num of name * string
type level = Zero | Succ of level | Max of level * level
           | Imax of level * level | Param of name
type expr = Bvar of int | Sort of level | Const of name * level list
          | App of expr * expr | Lam of name * expr * expr
          | Pi of name * expr * expr | Let of name * expr * expr * expr
          | Natlit of string
type error_kind = Invalid_input | Unsupported | Resource | Proof_failure
type error = { kind : error_kind; message : string }
val infer : ?fuel:int -> expr list -> expr -> (expr * thm, error) result
val check : ?fuel:int -> expr list -> expr -> expr -> (thm, error) result
val convert : ?fuel:int -> expr list -> expr -> expr -> expr -> (thm, error) result
val quote_name : name -> term
val quote_level : level -> term
val quote_expr : expr -> term
val quote_context : expr list -> term
```

Numeric name segments and natural literals are canonical nonnegative decimal strings, not machine
integers. String segments are exact byte strings, represented as HOL natural
number lists; they are not split at dots. Bound-variable indices are native
nonnegative integers. Contexts are nearest binder first; each entry is expressed
relative to the tail context. Binders retain names, but names have no binding
semantics. This core API accepts no environment or admitted constants; the
declaration APIs below provide transparent expansion and native environments.
Universe parameter names denote independent universally quantified natural
assignments, not HOL types. A declaration layer must check that they are
declared by the surrounding declaration; this environment-free core has no
declaration parameter list. Both declaration APIs perform that check in HOL.

On success, `infer g e` returns `(a, th)` and `check g e a` returns `th` with
**no hypotheses** and exact conclusion
`l4_defeq (quote_context g) (quote_expr e) (quote_expr e) (quote_expr a)`.
`convert g e e' a` returns the corresponding typed equality with `e'` in the
third argument. These are object-language judgments, not HOL equality between
OCaml booleans. Context well-formedness is checked before any public operation.

`Invalid_input` is reserved for malformed representations. All unsupported
features, exhausted fuel, and unsuccessful proof search are declines, not
logical refutations. A caller must never translate `Proof_failure` into a claim
that Lean rejects the term. The checker does not invoke Lean or another checker.

## Logical boundary

The implemented core slice is dependent Pi/lambda/application, de Bruijn variables,
sorts with natural-number universe semantics (including `imax`), beta/zeta,
typed conversion, proof irrelevance, and function eta. Structured HOL datatypes,
recursive definitions and inductively defined typed equality are the logical
specification. The OCaml algorithm only assembles HOL inference steps. It is
not itself treated as a trusted evaluator.

This is not a complete Lean4Lean port. General inductives and recursors,
quotient reduction, string literals and metavariables remain outside this
slice. Natural literals and projections require the native environment API;
the pure and transparent-expansion APIs decline their typing. The bounded
native inductive, natural-literal and projection extensions are described below.
Axioms and opaques require the native environment API below; they are not
supported by the pure or transparent-expansion APIs.
The parent frontend owns wire parsing and metadata;
it must decline anything the adapter cannot map.

The inductive relation follows upstream's convention: typing is reflexive
typed equality. Its rules do not carry a well-formed-context premise on every
step. The public API separately constructs an `l4_context` theorem, using
`l4_context []` and extension by a type with a proved sort. Local context
entries are variables, not admitted global axioms.

Substitution and shifting are HOL recursive definitions. OCaml computes
candidate syntax for efficiency, but every rule instance rewrites the HOL
operations using theorem-producing conversions, and the exact conclusion is
checked before returning. This is LCF proof production, not a proof that the
OCaml algorithm is complete, a model/consistency theorem, or a verified mapping
from NDJSON bytes to the decoded AST.

The default fuel is 100000 search/validation/rule steps. Input nesting deeper
than 512 and machine-index overflow decline. Fuel also counts universe case
splits; it is not a wall-clock or hard memory bound on individual HOL tactics.
Name numerals are arbitrary precision subject to this input resource budget.

## Regression command

Using the separately installed project-local toolchain:

```sh
sh hol/test.sh
```

The script launches ordinary HOL Light via `scripts/toolchain-exec.sh`, checks
seven prompt-safe success markers and scans its log for load/proof errors because a HOL
REPL can otherwise exit zero after an error. The tests inspect theorem
conclusions and empty hypothesis lists, exercise negative inputs, and compare
HOL's axiom list before and after loading the layers. The baseline is standard
HOL Light's eta, choice and infinity axioms; this project adds none. Negative
tests establish that the executable declines, not object-language refutations.

## Declaration Layer

Load `hol/admission.ml` for module `Lean4hol_admit` (separate from the stable
environment-free API). Its initial interface is:

```ocaml
type kind = Definition | Theorem
type declaration = {
  kind : kind; name : Lean4hol.name; params : Lean4hol.name list;
  typ : Lean4hol.expr; value : Lean4hol.expr
}
type environment  (* abstract, constructed only by empty and admit *)
val empty : environment
val declarations : environment -> declaration list  (* newest first *)
val quote_decl : declaration -> term
val quote_env : environment -> term
val certificate : environment -> thm
val admit : ?fuel:int -> environment -> declaration ->
  (environment * thm, Lean4hol.error) result
val check : ?fuel:int -> environment -> Lean4hol.expr -> Lean4hol.expr ->
  (thm, Lean4hol.error) result
```

Successful `admit` returns a closed theorem `l4_admitted (quote_env result)`.
It proves freshness, distinct declared universe parameters, parameter scope,
HOL-defined transparent expansion against the prior environment, type
formation, value typing, and a proposition type for theorem declarations.
`check env e a` proves exactly
`l4_env_has_type (quote_env env) (quote_expr e) (quote_expr a)` with no hypotheses.

This is a **transparent macro-expansion judgment**, explicitly defined in HOL,
not the upstream environment-indexed `IsDefEq` relation. Expansion itself has a
HOL proof, including simultaneous universe substitution. Definitions and
theorems both unfold, matching pinned `Declaration.lean`. No conservativity or
equivalence theorem relating this admission judgment to Lean's full declaration
checker is claimed. Declaration regressions cover prior dependencies,
polymorphic instantiation, theorem unfolding, structured-name separation,
duplicate/forward/self references, bad bodies, universe scope and resource
decline. Expansion currently repeats work and is not a corpus-scale performance
implementation.

Adapters must pass only safe, nonmutual definitions/theorems and decline axioms,
opaques, unsafe/partial declarations, inductives, recursors and unsupported
metadata. Those forms deliberately have no constructor in this admission API.
Unknown and forward constants decline; environments grow only after all
premises are proved. There is no trusted Boolean admission path.

## Environment Judgment

Load `hol/environment.ml` for `Lean4hol_env`, without changing the two existing
adapter APIs. This tested layer uses a native
environment-indexed typed equality `l4_edef env context left right type`, not
macro expansion. A separately proved `l4_evalid policy env` certifies sequential
admission. Public checking returns `l4_checked policy env context e e' a`,
which includes environment validity, context validity and typed equality.

Bounded scope: safe nonmutual definitions, theorems, explicit object axioms,
and opaque declarations. An axiom needs a caller-supplied exact permission
(structured name, ordered universe parameters, and original type). The default
policy is empty. An export must never silently supply its own permissions.
An explicitly selected "all input axioms" mode can construct this list from
the input, but then certifies checking relative to that supplied object theory,
not conformance to an independent axiom allowlist. Its certificate must retain
the complete policy and make this mode visible.
Permission is data in the HOL conclusion; it neither introduces a HOL axiom
nor proves the permitted object theory consistent. An opaque must have a checked
body but no delta rule. Definitions and theorems retain delta rules.

Inductives must use `admit_inductive` in the bounded slice below; ordinary
`admit` declines generated roles. Unsupported inductive shapes remain declined.
An inductive or recursor must not be admitted by relabeling it an axiom. There
is no generic "trusted rule" permission.

The stable, runtime-tested adapter-facing API is:

```ocaml
module Lean4hol_env : sig
  type kind = Definition | Theorem | Opaque | Axiom
  type declaration = {
    kind : kind; name : Lean4hol.name; params : Lean4hol.name list;
    typ : Lean4hol.expr; value : Lean4hol.expr option
  }
  type axiom_permission = {
    axiom_name : Lean4hol.name; axiom_params : Lean4hol.name list;
    axiom_type : Lean4hol.expr
  }
  type environment
  val empty : environment
  val with_axioms : ?fuel:int -> axiom_permission list ->
    (environment, Lean4hol.error) result
  val declarations : environment -> declaration list
  val permissions : environment -> axiom_permission list
  val quote_decl : declaration -> term
  val quote_env : environment -> term
  val quote_policy : environment -> term
  val certificate : environment -> thm
  val admit : ?fuel:int -> environment -> declaration ->
    (environment * thm, Lean4hol.error) result
  val infer : ?fuel:int -> environment -> Lean4hol.expr list -> Lean4hol.expr ->
    (Lean4hol.expr * thm, Lean4hol.error) result
  val check : ?fuel:int -> environment -> Lean4hol.expr list ->
    Lean4hol.expr -> Lean4hol.expr -> (thm, Lean4hol.error) result
  val convert : ?fuel:int -> environment -> Lean4hol.expr list ->
    Lean4hol.expr -> Lean4hol.expr -> Lean4hol.expr -> (thm, Lean4hol.error) result
end
```

Use `None` only for `Axiom` and `Some body` for all other kinds. Admission
returns exactly `l4_evalid (quote_policy env') (quote_env env')`. Checking uses
the nearest-first local context convention from the core. It returns exactly
`l4_checked policy env context e e a`; conversion changes the second `e` to the
right-hand term. All results have empty HOL hypothesis lists. A native checked
theorem includes its explicit object assumptions as data, rather than hiding
them in HOL hypotheses or stripping the environment from the conclusion.
`with_axioms` constructs a new empty environment with a fixed policy, not a
mutation of an already checked environment. Granted axioms still need type
formation, fresh names and scoped, distinct universe parameters when admitted.
Opaque bodies are checked against the prior environment and cannot self-reference.
Theorem declarations must have proposition types; both definitions and
theorems delta-unfold, matching the pinned executable. Opaques can still be
related by justified function eta or proof irrelevance, but not by inspecting
their bodies during conversion.

Admission is an instance of the inductively defined `l4_evalid_RULES`, using
HOL proofs of every side condition, type formation and (except axioms) body
typing. In addition to concrete admissions, the following general theorems
are proved from its induction principle:

```text
|- !policy env. l4_evalid policy env ==>
     ALL (\d. l4_entry_tag d = L4AxiomKind ==> MEM d policy) env
|- !policy env. l4_evalid policy env ==>
     l4_names_distinct (MAP l4_entry_name env)
```

These are `l4_evalid_permissions` and `l4_evalid_unique`.
`l4_checked_permissions` carries the permission invariant through public
checking. `l4_opaque_not_delta` proves that opaque entries do not meet the
delta-rule transparency predicate. It is not a proof that opaque constants
can never be definitionally equal by another rule.

The refactored `Lean4hol.Engine` shares the same proof search between the pure
and native layers; its rules, constants, context predicate and typed iota hook
are supplied by the backend. Inference, reduction and conversion memoization
is confined to one budget and one instantiated backend. Cache entries are
ordinary closed HOL theorems and every hit checks its exact conclusion.
The old `Lean4hol` and `Lean4hol_admit` interfaces remain unchanged.
Both declaration layers now require proposition types for theorems, as the
pinned executable's `Environment.addTheorem` requires.

Ordinary admission deliberately omits safety flags, mutual blocks and generated
declaration metadata. Adapters must decline unsafe/partial/mutual inputs and
must not pass inductive or recursor metadata as ordinary declarations.
Ordinary and axiom admission have a HOL-defined reserved-primitive-name guard;
even an exact object axiom permission cannot bypass it. Canonical Nat/Bool
blocks have the separate inductive admission path below. The HOL environment
judgment proves the stated core rules, not all of Lean's declaration-admission
policies. No environment-extension/weakening, universe-substitution preservation,
consistency, or equivalence theorem against upstream's full environment relation
is claimed. Prior certificates refer to their original environment; recheck a
term to obtain a certificate for an extended environment.

## Bounded Inductives

The next API extends `Lean4hol_env` rather than adding a second checking engine.
Existing ordinary declaration calls remain unchanged. The generic admission,
iota and admission-detail certificate paths pass fresh-process regressions.

```ocaml
type rec_rule = { ctor : Lean4hol.name; num_fields : int; rhs : Lean4hol.expr }
type ind_info = {
  num_params : int; num_indices : int; all : Lean4hol.name list;
  ctors : Lean4hol.name list; num_nested : int;
  is_rec : bool; is_reflexive : bool; is_unsafe : bool
}
type ctor_info = {
  induct : Lean4hol.name; index : int; num_params : int;
  num_fields : int; is_unsafe : bool
}
type rec_info = {
  all : Lean4hol.name list; num_params : int; num_indices : int;
  num_motives : int; num_minors : int; rules : rec_rule list;
  k : bool; is_unsafe : bool
}
type role = Inductive_role of ind_info | Constructor_role of ctor_info
          | Recursor_role of rec_info
(* kind gains Generated of role; ordinary admit declines this constructor. *)
type field = Data of Lean4hol.expr | Recursive
type inductive_block = {
  inductive_name : Lean4hol.name; inductive_level : Lean4hol.level;
  constructors : (Lean4hol.name * field list) list;
  claims : declaration list
}
val admit_inductive : ?fuel:int -> environment -> inductive_block ->
  (environment * thm, Lean4hol.error) result
val inductive_certificate : environment -> Lean4hol.name ->
  (thm, Lean4hol.error) result
```

This is a generic schema, not recognition of fixed Bool/Nat declarations.
Constructor names/counts and field counts are arbitrary within the resource
budget. The first bounded slice is one nonmutual, nonnested type with no parameters,
indices or universe parameters, in a proved nonzero universe. `Data a` must be
a closed type in the prior certified environment with universe no greater than
the new datatype's universe. `Recursive` denotes exactly the new datatype.
This admits direct strictly positive recursion, not dependent fields or
function-valued recursive fields. All other shapes must decline.

`claims` must contain exactly the inductive, all constructors and its recursor,
in any table-record order. All have `value = None`. Constructor order in the
inductive metadata, constructor indices and recursor rule order remain exact.
The recursor name is the structured
string child `rec`, with the sole universe parameter named `u` and unrestricted
large elimination justified by the nonzero datatype universe. Generated
metadata is checked in HOL, including all counts, flags, owners, constructor
order and recursor RHSs. Binder names are normalized to anonymous in generated
scaffolding; supplied types/RHSs are compared after the same HOL-defined operation.
The certified environment contains the canonical generated entries, not
unchecked exported rules. Exact metadata mismatch is a decline, not a proven
Lean rejection. No primitive reduction, structure eta, K reduction or Prop
elimination is introduced by this extension.

`admit_inductive` returns exactly `l4_evalid policy extended_env`, preserving the
parent's existing certificate check. `inductive_certificate result name`
additionally returns the closed theorem
`l4_inductive_checked policy prior_env name level constructor_specs claims`.
It binds the original supplied claims to HOL reconstruction and retains all
admission obligations, including field validity, nonzero result universe,
freshness and generated-type formation. This certificate is retained across
later extensions and refers to the original prior environment. No claims are
recovered from unchecked metadata after admission.

The authentication steps are part of the HOL statement, not Boolean gates:

- `l4_fields_valid env u fs` is inductively defined. A data field needs a
  prior-environment typing theorem, closed universe-parameter scope, and
  `l4_level_le field_level u`. A recursive field denotes exactly the new type.
  Data fields are checked before any block names are available; self-references
  are not accepted through `Data`.
- `l4_level_nonzero u` means `!rho. 0 < l4_eval_level u rho`; `rho` assigns HOL
  natural numbers to object universe parameters. This excludes Prop and
  universe-zero cases from unrestricted elimination in this slice.
- `l4_generated` and its recursive helpers construct constructor signatures,
  the dependent motive/minor telescope, recursive hypotheses, metadata and
  recursor RHSs. The OCaml candidate generator is checked against their HOL
  reduction theorem. Every generated signature additionally gets a HOL type
  formation proof in the provisional signature environment.
- `l4_metadata_matches` checks equal table lengths, unique supplied declaration
  names, and membership of every binder-name-normalized claim in the complete
  generated table. The admission rule separately requires unique generated
  names. Thus table presentation order is immaterial without discarding claims
  or permitting duplicate replacements. Every entry's internal ordered fields,
  including constructor lists and recursor rules, remain exact; no arbitrary
  rewrite RHS is permitted.
- `l4_primitive_block` authenticates canonical Nat/Bool shapes at the structured
  root names, including universe, constructor names/order and field arities.
  Every other generated name is checked against the pinned primitive-name list.
  `l4_inductive_checked_primitives` extracts this obligation as a theorem.
  This enables their ordinary constructor/recursor behavior and authenticates
  Nat for the literal extension below, not accelerated primitive arithmetic.
  A single string segment `"Nat.zero"` is
  distinct from the string child `"zero"` of root `"Nat"`.
- `l4_no_nested_aux` traverses all modeled expression forms and forbids constant
  references whose structured name has root prefix `_nested`.
  `l4_no_nested_block` checks reconstructed constructor types;
  `l4_no_nested_claims` checks the supplied constructor-role entry types.
  Both are admission premises, extracted by `l4_inductive_checked_no_nested`.
  This mirrors `Inductive/Add.lean:checkNoNestedAux`, not a blanket name ban:
  an empty `_nested.T` type can be admitted, while a nullary constructor for
  that type or a field referencing it must decline. Constructor names, binder
  names and universe-parameter names are not constant references.
  `l4_no_nested_anon` proves that erasing binder names preserves this predicate.
  Projections traverse both the structure-name reference and major expression.
- The native iota rule checks recursor/rule membership, universe arity, prefix
  and field arities, and typed premises for both sides. The shared engine
  proves major-premise normalization and overapplication through ordinary
  congruence; it neither calls Lean nor Rocq for verdicts.

The helper functions exported with the OCaml model, including `generate`,
only compute candidate syntax. Adapters must obtain `claims` from the actual
input, not replace them with these candidates. The detail theorem authenticates
the quoted claims, not NDJSON bytes or a parent adapter's decoding behavior.

Integration requires restarting a warm HOL process after logical rule changes,
including the primitive and nested-reference admission guards. All returned theorem
hypotheses remain empty. Full parameters/indices, dependent constructor fields,
function-valued recursion, mutual/nested blocks, Prop/singleton/K elimination,
structure eta and other primitive admission/reduction remain declines or adapter
exclusions. No semantic model or full upstream equivalence is established by
these schema-level derivations.

## Native Natural Literals

`L4NatLit num` is object syntax containing a HOL natural numeral. Its OCaml
representation is `Natlit string`, preserving canonical decimal input exactly,
including values larger than machine integers. Quotation does not replace a
literal with a constructor tree. The returned `l4_checked` theorem retains the
original literal, and all literal certificates have empty hypotheses.

Native `l4_edef` rules 0--15 are unchanged. Appended rules are:

- 16: literal reflexive typing at `Nat`, requiring `Nat : Sort (Succ Zero)`.
- 17: `Natlit 0` converts to `Nat.zero`, requiring `Nat.zero : Nat`.
- 18: `Natlit (SUC n)` converts to `Nat.succ (Natlit n)`, requiring
  `Nat.succ : Pi Anonymous Nat Nat`.

Each public certificate also proves `l4_evalid policy env` and context validity.
The canonical primitive guards ensure that a certified environment cannot
substitute an arbitrary declaration for Nat or its constructors. Missing Nat
is an unsupported decline, not permission to assume it. Rule 18's concrete
numeral arithmetic is discharged with `NUM_REDUCE_CONV`; the hook checks that
its conclusion contains the original input numeral exactly.

The shared Engine hooks `nat_literal` and `nat_literal_step` return HOL theorems
for reflexive typing and one constructor-view step, respectively. WHNF exposes
only that step. Ordinary congruence and the authenticated iota rule handle
recursors on literal majors. Large literal typing or one-step conversion does
not require unary expansion, but deeply recursive computations and unequal
literal comparisons can exhaust fuel and decline. This does not yet implement
accelerated Nat arithmetic or strings. Projection rules and the separately owned
guarded primitive admission extension are distinct from the literal rules.

HOL universe scope, universe substitution, binder erasure and `_nested`
traversal cover the new constructor. Macro expansion preserves it syntactically,
but the pure checker used by the old macro layer does not assign it a type.
The parent reran the complete fresh-process suite after the Camlp5 spelling
and HOL variable fixes: all 434 assertions passed, including 62 native literal
assertions. The OCaml constructor is `Natlit`; the HOL constructor is `L4NatLit`.
That verified snapshot was loaded in the parent's warm server. The family
changes below subsequently passed a separate fresh-process 609-assertion run.
The parent then verified 610 assertions with the early `Proof_failure` branch
for distinct canonical literals and its unequal-256-bit-literal regression.

## Family API

The existing `inductive_block` and `admit_inductive` API remains unchanged.
The additive API is implemented for single, index-free families and passed
fresh-process regression validation. Its documented signature is unchanged:

```ocaml
type inductive_family = {
  family_name : Lean4hol.name;
  level_params : Lean4hol.name list;
  parameters : (Lean4hol.name * Lean4hol.expr) list;
  result_level : Lean4hol.level;
  family_constructors : (Lean4hol.name * field list) list;
  family_claims : declaration list
}
val admit_inductive_family : ?fuel:int -> environment -> inductive_family ->
  (environment * thm, Lean4hol.error) result
```

Parameters are listed outermost first; each parameter type is relative to the
preceding parameters. A `Data` field type is relative to the complete parameter
context, not preceding constructor fields. `Recursive` denotes the family
applied to those same parameters. Universe scope and all claims are checked in
HOL. The checker, not an adapter flag, determines small/large elimination and
the recursor's universe parameters from checked result/field universes.
Dependencies on earlier fields, indices and function-valued recursion remain
outside this initial family API. Frontend/Arena coverage of this new API is a
separate integration checkpoint, not established by the native tests below.

`admit_inductive_family` still returns exactly `l4_evalid policy extended_env`
with no hypotheses. For this API, `inductive_certificate` returns
`l4_family_checked policy prior_env name level_params parameters result_level
constructor_specs field_sort_lists large k claims`. The field sorts and flags
are computed by the checker and retained in the theorem. This differs from the
old API's `l4_inductive_checked` detail head; callers checking only `l4_evalid`
need no certificate-shape change.

`l4_family_fields` certifies each data field in the prior environment and full
parameter context, including level-parameter scope. Its sort must be bounded by
the result universe unless that universe is always zero. Recursive descriptors
denote direct applications to the same parameters. `l4_family_ok` also requires
a valid parameter context, distinct and scoped universes, exact metadata-table
matching, formation of every generated signature, and primitive/nested-reference
guards. The generator is HOL-defined and its OCaml candidate is authenticated
by a conversion theorem before admission.

Large elimination is certified exactly for the implemented index-free shape:
a never-zero result universe, no constructors, or a singleton constructor whose
fields all have always-zero sorts. Otherwise the motive is restricted to Prop.
K metadata is true only for an always-zero result with one nullary constructor.
Exposed-constructor iota works with either K flag. Neutral-major K reduction uses
the certified candidate mechanism below. Fresh large-elimination universes follow the pinned order
`u`, `u_1`, `u_2`, etc., and their freshness is a HOL premise. Existing level
parameters retain their original order. No parameterized Nat/Bool impersonation
is permitted by the family primitive guard.

The iota rule now splits constructor parameters from fields, checks the full
recursor prefix length and retains typed premises for both sides. Rule indices
are unchanged, including literal rules 16--18. No core source change is needed.

## Indexed API

The additive entry point preserves both existing inductive APIs:

```ocaml
type indexed_field = Index_data of expr | Index_recursive of expr list
type indexed_constructor = {
  indexed_ctor_name : name;
  indexed_fields : indexed_field list;
  result_indices : expr list
}
type indexed_inductive = {
  indexed_name : name;
  indexed_level_params : name list;
  indexed_parameters : (name * expr) list;
  indices : (name * expr) list;
  indexed_result_level : level;
  indexed_constructors : indexed_constructor list;
  indexed_claims : declaration list
}
val admit_indexed_inductive : ?fuel:int -> environment -> indexed_inductive ->
  (environment * thm, Lean4hol.error) result
```

All telescopes are outermost first. Index domains are relative to the parameters
and earlier indices. Field domains and recursive index arguments are relative
to the parameters and earlier fields. Result indices are relative to parameters
and all fields. `Index_recursive xs` denotes precisely this family at its declared
universe parameters, applied to all unchanged parameters and `xs`. Recursive
occurrences inside `Index_data`, recursive index arguments or result indices
are outside the supported positivity shape. No constructor or recursor forward
reference is permitted during constructor formation. All input claims remain
mandatory, with exact role metadata and ordered recursor rules. This API targets
single families, including Eq, but not mutual/nested/function-valued recursion.
The fresh full suite has passed Eq, dependent fields, dependent index
telescopes and indexed recursive iota. Neutral K reduction uses the same typed
equality rules, with no additional object-language rule.

Successful admission returns exactly `l4_evalid policy extended_env`, with no
hypotheses. The detailed theorem is
`l4_index_checked policy prior_env name level_params parameters indices
result_level constructor_specs field_sort_lists large k claims`.
`l4_index_checked_metadata` and `l4_index_checked_elimination` extract the exact
claim-table and elimination obligations. The global permission and name-uniqueness
invariants also cover this new admission rule.

The HOL-defined `l4_index_ok` checks header formation in the prior environment.
Constructor domains and result indices are checked with only the header added,
never the constructors or recursor being admitted. Fields are processed in
dependency order by the inductive relation `l4_index_fields_valid`, with universe
bounds and syntactic positivity premises. Non-Prop fields of a singleton Prop
constructor must occur as direct variables among the result indices for large
elimination; otherwise elimination remains in Prop. K metadata requires an
always-Prop singleton with no fields. Every generated signature is separately
type-checked, and a HOL conversion authenticates the complete candidate generator.
Protected primitive names decline in this additive path; canonical Nat/Bool remain
available through the two prior APIs. The raw and generated constructor-type
`_nested` traversals are retained.

Native rule 19 adds indexed constructor iota. It checks index and parameter
arities, discards indices only in the generated RHS application, and retains
typed premises for both sides. Rules 0--18 are unchanged. `Native.rule` computes
object substitutions with a fresh symbolic environment and then applies HOL
`INST`; it does not traverse the quoted environment during those computations.
The specialization benchmark compares exact closed rule instances, not logical
verdicts or end-to-end throughput.

## Neutral K

The internal `Engine` hook is now
`major : expr -> (expr * (expr -> expr) * expr option) option`: major premise,
application reconstruction, and optional candidate major. The native candidate
requires a safe, single-motive `k=true` recursor with one nullary constructor rule
and a matching constructor entry. Constructor universe arguments are selected
by declared parameter names from the recursor's instantiation; constructor term
parameters are the recursor's supplied parameters.

The hook returns syntax, not evidence. Core normalizes the original major, then
uses typed application congruence and existing proof irrelevance to authenticate
replacement with the candidate. In particular, `Eq.refl 0` cannot replace a
neutral proof of `Eq 0 1`: both proof types and indices must convert. A failed
candidate leaves the normalized original application available for ordinary
checking. Resource failures propagate rather than being hidden by this fallback.
After successful replacement, ordinary constructor iota applies. The native rule
count stays 20, and final results remain exact closed `l4_checked` certificates.

`Native.member` additionally caches at most 256 proven membership theorems per
immutable native environment, keyed by the full declaration. A cache hit consumes
fuel; applying the native rule still checks the theorem against its exact premise.
This cache cannot transfer a theorem between environments.

## Provenance

Reference: Lean4Lean commit
`8223d223ed98661882e95d9d6a7126df7097cd76`, pinned locally at
`/private/tmp/lean-kernel-research-20260929-lean4lean`.
The typed equality rules follow `Lean4Lean/Theory/Typing/Basic.lean`, the level
semantics follow `Lean4Lean/Theory/VLevel.lean`, and the executable checking
structure is informed by `Lean4Lean/TypeChecker.lean`. Lean4Lean is Apache-2.0;
the HOL implementation is a new, explicitly bounded adaptation, not a claim of
verified equivalence with the entire upstream algorithm. See `hol/NOTICE`.

## Verification status

Verified on 2026-09-29 using OCaml 4.14.2 and HOL Light 3.1.0:

```text
$ HOL_CORE_LOG=/private/tmp/lean4hol-structure-final-20260929.log sh hol/test.sh
#   HOL_CORE_TESTS_PASSED 91
HOL_ADMISSION_TESTS_PASSED 38
HOL_ENVIRONMENT_TESTS_PASSED 95
HOL_INDUCTIVE_TESTS_PASSED 194
HOL_NAT_LITERAL_TESTS_PASSED 63
HOL_FAMILY_TESTS_PASSED 154
HOL_INDEXED_TESTS_PASSED 92
#   HOL_PROJECTION_CORE_TESTS_PASSED 569
HOL_PROJECTION_TESTS_PASSED 88
HOL_STRUCTURE_TESTS_PASSED 66
HOL core proof log: /private/tmp/lean4hol-structure-final-20260929.log
```

The process exits zero, and the wrapper rejects HOL load/proof errors even
when the REPL itself exits zero. `sh -n hol/test.sh` also passes. This fresh
1,450-assertion checkpoint includes unchanged axioms, exact conclusions and no
hypotheses, and extends the earlier 1,384-assertion projection checkpoint. This fresh
run adds projection congruence, structure/unit eta, the parent's guarded core
callbacks, and the fully-applied generator-conversion arity repair. It includes
native projections, the parent-owned transport tests, primitive admission
clause 6, and the parent's indexed-flags rewrite repair. It preserves
the triple major hook, strict `Proof_failure` classification for the mismatched
neutral Eq case, and the environment-local membership cache. Dedicated primitive
contract/consumer regressions are separate from this suite.
The public names are `Lean4hol`, `Bvar` and `Imax`: HOL Light's OCaml lexer
requires these spellings. The object constructors remain `L4BVar` and `L4IMax`.
The core, macro, native-environment, family and indexed interfaces are loaded and tested.
Native regressions include
default axiom denial, exact signature and parameter-order permissions, prior
dependency and type formation, opaque-body checking without unfolding,
polymorphic constants, proof irrelevance, function eta, delta, self-reference
and resource declines. They instantiate the permission and uniqueness theorems.
Inductive regressions cover enumeration, unary recursion, branching recursion
with prior-environment data fields, empty types, dependent motives, repeated
iota, open-context recursion, overapplication and binder-name normalization.
The enum and unary recursor type/RHS expectations are written independently of
the candidate generator. Negative cases mutate metadata, recursor RHSs, counts,
flags and universe lists, and test unsupported positivity/universe shapes.
The run includes canonical Nat/Bool, empty/malformed primitive negatives,
reserved names in unrelated declarations, `_nested` constructor-result and
prior-field negatives, the permitted empty `_nested.T` case, structured-name
distinctions and traversal of every modeled expression form. The nested-reference
authentication theorem is checked for its exact conclusion and empty hypotheses.
The strengthened raw-claim guard and binder-erasure preservation theorem were
loaded by this fresh process. No prohibited inference escape appears in the
`hol/` source scan for `new_axiom`, `mk_thm` or `Obj.magic`.
Admission-detail and metadata-authentication theorem conclusions and hypotheses
are checked explicitly, not just successful return codes.
Family tests additionally cover polymorphic and dependent parameter telescopes,
direct recursive fields and iota, restricted Prop elimination, proof-only
singleton large elimination, K metadata, fresh universe names through `u_11`,
field universe bounds, parameterized primitive impersonation, and nested-name
guards. Constructor-table permutations pass for Nat, Bool, Tree and a family;
duplicate records and permuted recursor-rule arrays decline. The independent
tree dependent-conversion timeout reported by the parent remains unresolved.
Indexed regressions check independently written Eq constructor/recursor types,
constructor iota, dependent fields, dependent index telescopes, direct indexed
recursion, restricted large elimination, raw metadata/RHS mutations, forward
references, positivity, universe bounds, primitive guards, resource classification,
and the global permission/uniqueness theorems. K regressions cover neutral True,
beta/zeta-normalized major premises, neutral Eq, constructor universe
instantiation, mismatched indices and resource classification. The
rule-specialization microbenchmark measured 0.225899 CPU seconds
eager versus 0.001299 symbolic for five rule-0 object computations with 128
synthetic recursor entries; exact conclusions and empty hypotheses matched.
These timings are not admission or end-to-end performance measurements. The
parent separately reported 61 eager/symbolic comparison assertions across all
20 native rules in `hol/rule_specialization_tests.ml`.
No frontend/NDJSON end-to-end,
Arena compatibility, metatheoretic consistency or full-port claim follows from
these tests.

### Projection Integration API

The additive core/native callback contract is fixed as follows:

```ocaml
type projection_services = {
  project_infer : expr -> expr * thm;
  project_sort : expr -> level * thm;
  project_check : expr -> expr -> thm;
  project_reduce : expr -> expr * expr * thm;
  project_convert : expr -> expr -> expr -> thm;
}
val project_type : budget -> expr list -> name -> int -> expr ->
  projection_services -> expr * thm
val project_step : budget -> expr list -> name -> int -> expr ->
  projection_services -> (expr * expr * thm) option
val project_congr : budget -> expr list -> name -> int -> expr -> expr ->
  projection_services -> expr * thm
val structure_equal : budget -> expr list -> expr -> expr ->
  projection_services -> (expr * thm) option
```

Services close the current budget and context and return backend judgments.
For `p = Proj(owner,idx,major)`, `project_type` returns `(a,h)` with exact
`J g p p a`; `project_step` returns `Some(t,a,h)` with exact `J g p t a`,
or `None` for a neutral major. `project_reduce e` returns `(normal,a,h)`
with exact `J g e normal a`. Core guards the exact conclusion and empty
hypotheses. Pure hooks decline. Native callbacks must not invoke engine
inference/checking on the same projection; earlier-field projections decrease
the index. Projection typing/reduction append native rules 20 and 21, leaving
the existing rules and primitive admission clause 6 unchanged.
`project_convert lhs rhs expected_type` proves the exact backend equality at
the requested type, using guarded conversion/casting in the same budget/context.
`project_congr` returns a typed equality between the matching owner/index
projections. `structure_equal` returns a typed equality or `None`; its Pure
implementation returns `None`.

This is an explicit operational projection extension following pinned
`TypeChecker.lean:inferProj`, with HOL-certified metadata, field bounds,
telescope substitution and Prop guards. Correspondence to the upstream
theory's `casesOn` expansion is not yet proved.

Rule 20 authenticates the single-constructor owner, matching universe parameter
lists and actual parameter/index counts. Both the major at the instantiated
owner type and the parameter-applied constructor are typed premises. The
recursive HOL `l4_proj_drop` and `l4_proj_scan` computations reconstruct the
residual telescope, earlier-field substitutions and selected domain; the ML
candidates are accepted only after proving those equations. Every scanned
domain has a typed sort witness. Unless the owner sort is proved nonzero at
every universe valuation, the selected field and each preceding field used
by the remaining telescope must have a universe equivalent to zero.
`l4_uses_bound` tracks the removed binder specifically, including nested
binders, without confusing it with variables of the ambient context.

Rule 21 requires an equality proof reducing the major to the authenticated
constructor application, exact parameter/field arities, the original
projection typing theorem, and a typing theorem for the selected argument at
that same type. The core composes subsequent reductions by existing typed
transitivity. Public results retain the exact closed `l4_checked policy env
g (L4Proj owner idx major) result type` certificate and valid-environment
premise. No HOL axiom is added.

Current bounds: constructor telescopes must expose syntactic Pi nodes; general
WHNF of telescope types is not implemented. Indexed single-constructor owners and dependent fields
are supported; projection typing does not require the nonrecursive/index-free
structure-eta guard. Unsupported shapes and
failed proof construction decline. The positivity traversal conservatively
counts a projection's owner name as a reference as well as traversing its major.

A fresh integrated native regression run passed 88 assertions, including exact
closed conclusions, first/last fields, beta/zeta majors, ambient bound variables,
dependent fields, indexed owners, polymorphic parameters, Prop-only fields,
forbidden non-Prop fields/dependencies, unknown owners, bounds, malformed
indices, resource exhaustion and unchanged HOL axioms. The independent core
transport suite passed 569 assertions in that same fresh process. The complete
integrated checkpoint above totals 1,450 assertions and exited zero without
HOL load/proof errors.

### Structure Eta Extension

Native rule 22 is typed projection congruence: the majors must be proved equal
and both projections must be typed at the same result type. For dependent
fields, typing the second projection may require congruence at an earlier
projection index. Rule 23 is structure eta. Its HOL `l4_eta_meta` premise
authenticates actual environment entries, constructor ownership and arities,
universe parameter lists, and the pinned `isNonRecStructure` guard: nonrecursive,
exactly one constructor, and zero indices. Both the original term and the
HOL-defined constructor expansion must be typed at the same instantiated owner
type. Unit-like equality derives from this same rule with zero fields; it is
not an unrestricted subsingleton rule or a HOL axiom.

The candidate search follows `TypeChecker.tryEtaStructCore` and
`isDefEqUnitLike`. For nonzero-field eta it requires an actual constructor
endpoint; two arbitrary neutral records are not expanded into a circular
comparison. It also skips two constructor endpoints after structural equality
has already compared their fields. Resource failures propagate; failed proof
construction declines. Function eta and proof irrelevance remain separate.

Recursor-major structure expansion is outside this checkpoint: pinned
`Inductive/Reduce.lean:toCtorWhenStruct` additionally requires a provably
nonzero sort, unlike the conversion-side structure guard. No correspondence
proof to upstream environment eta equations or projection expansion is claimed.
The new native regressions and appended rules do not change any of the seven
environment-admission clauses.

A fresh full-suite run passed all 66 structure assertions without HOL load
or proof errors. These check exact closed certificates for unit-like equality,
both eta directions, parameterized and dependent structures, nested projection
congruence and dependent result-type transport. Negatives cover changed fields,
different owners/parameters, recursive/indexed/multiple-constructor metadata,
non-unit neutral comparison termination, and resource classification. The
fresh full-suite checkpoint totals 1,450 assertions, exited zero, and all test
processes were reaped before the parent took ownership for quotient integration.
At this checkpoint there are 24 native equality rules and seven admission
clauses; subsequent quotient additions are outside these verified counts.

For example, the tested identity produces exactly the closed object theorem:

```text
|- l4_defeq []
     (L4Lam L4Anonymous (L4Sort L4Zero) (L4BVar 0))
     (L4Lam L4Anonymous (L4Sort L4Zero) (L4BVar 0))
     (L4Pi L4Anonymous (L4Sort L4Zero) (L4Sort L4Zero))
```

A separately executed native check, granting and admitting `P : Prop`, prints
the following exact closed theorem. The first list is the permission policy;
the second is the certified environment. The dummy final `L4Sort L4Zero` field
on the axiom entry is fixed by the axiom admission rule and is not an axiom body.

```text
|- l4_checked
     [L4Entry L4AxiomKind (L4String L4Anonymous [80]) []
       (L4Sort L4Zero) (L4Sort L4Zero)]
     [L4Entry L4AxiomKind (L4String L4Anonymous [80]) []
       (L4Sort L4Zero) (L4Sort L4Zero)]
     []
     (L4Const (L4String L4Anonymous [80]) [])
     (L4Const (L4String L4Anonymous [80]) [])
     (L4Sort L4Zero)
```
