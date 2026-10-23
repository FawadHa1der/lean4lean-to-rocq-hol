# Recursor-Major Structure Expansion

The integrated HOL checker now supports the pinned Lean4Lean
`Inductive/Reduce.lean:toCtorWhenStruct` path for its existing single-family
structure subset. It constructs the constructor application from certified
projections, proves its typed equality to the neutral major, lifts that equality
through the recursor application, and uses the existing iota rule. This adds no
native object-language rule or HOL axiom.

The guards require a safe, nonrecursive, nonindexed, single-constructor family,
matching recursor ownership and metadata, and a provably nonzero result universe.
Propositional and possibly-propositional families do not use this path. Recursive
structures, indexed families and general higher-order recursive fields are not
made supported by this change.

## Literal And Quotient Boundaries

Branch selection observes ordinary weak-head normalization before expanding a
literal. A String literal expanded to a neutral `String.ofList` result must not
subsequently receive structure expansion: upstream excludes that branch. Nat
literals also use their own branch. Quotient recursors use ordinary reduction,
neither literal-major nor structure-major expansion. The previously integrated
quotient dispatch repair remains in place.

`hol/structure_major.ml` defines the precise evidence predicate. Its conversion
fact is obtained from the existing encoded structure-eta rules, not an OCaml
Boolean assertion. The certificate includes the exact environment, context,
recursor/family/constructor entries, instantiations and major premise. This is
still an encoded-rule certificate, not a proof that the specification is
equivalent to Lean's kernel.

## Validation

The exact private sources integrated into the project pass:

- 54 focused structure-major assertions and 23 String-branch exclusions.
- All 18 full native suite markers: 1,181,728 assertions in 490.161s with no
  HOL errors or source changes. Of these, 1,179,904 are syntax/UTF-8 checks;
  they are not additional proof files or distinct logical theorem cases.
- The authentic Arena `tutorial/075_typeSingletonRecReduction` case accepts in a
  selected 30s run. The other 219 inventory entries are explicitly unselected.
- The rebuilt integrated frontend passes 67 transport checks.

Evidence is retained in `build/reports/hol-extensions-native.{json,log}`,
`hol-extensions-pre-raw-arena-075.json`, and
`hol-extensions-pre-raw-runtime.json`. The complete native run was executed in
`/private/tmp/hol-integrated-extensions-20260929`; all integrated `hol/*.ml`
files were compared byte-for-byte afterward. Its worker was stopped and reaped.
The separate full Arena attempt subsequently completed: 86 correct accepts,
six correct rejects, two allowed-either outcomes, 122 declines and four missing
inputs. All 216 available files were attempted; no wrong verdict or integrity
failure was observed. The sole changed classification versus cache/pow is the
new Arena 075 acceptance. Its worker is also stopped and reaped. Evidence:
`hol-extensions-full-arena-10s.json` and `hol-extensions-full-runtime.json`.

Reproduce the focused suite with
`python3 tests/hol_strings/run_native.py structures`; use `full` for all 18
native suites. The runner retains logs and hashes and fails on timeout, HOL
errors, missing completion markers or source changes.

## Longer-Budget Controls

A separate selected run of eight complete valid inputs at a 60s checker cap
accepts four previously resource-bound cases: 045_rbTreeDef in12.079s,
071_rbTreeRef in17.784s, 080_nRecReduction in10.318s and
081_listRecReduction in29.698s. The three `other/nat-lit-{add,ble,sub}` cases
and 082_RBTree.id_spec still reach the cap and decline. No partial-file result
is substituted for those outcomes. The other212 cases are explicitly skipped;
this does not replace the 10s full-run table. Reports are
`hol-extensions-selected-60s.json` and
`hol-extensions-selected-60s-runtime.json`. The separate worker was reaped.
