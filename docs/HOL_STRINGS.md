# HOL Text and String Checking

The local integrated checker supports strict UTF-8 string literal transport,
Unicode-scalar quotation, literal typing, and authenticated constructor expansion.
It retains seven arithmetic contracts; shiftLeft and further inductive work are
separate private candidates, not part of this checkpoint.

## Implementation and Rules

`Char.ofNat` and `String.ofList` are checked safe definitions with exact typed
interfaces and guarded raw-contract admission. Their actual bodies are retained.
Arbitrary well-typed bodies are allowed, as in the pinned Lean4Lean source; no
host Char/String evaluator, injectivity assumption or standard-library layout
assumption is introduced. Unsafe/partial candidates are declined before the
transport discards their safety tags.

`L4StrLit` holds Unicode scalar lists. The new leaf is covered by every syntax
traversal. The two appended equality clauses require typed interfaces, scalar
validity, literal typing and exact expansion typing. The admission rule binds
the certificate to the exact old environment, name, universes, type and body.
There are now 27 native equality clauses and nine environment admission clauses.
No new HOL axiom, admission, unchecked cast or delegated checker verdict is used.

Ordinary string WHNF stays neutral. Inductive/projection majors expand once to
the specified List/Char applications and then use the admitted bodies. Quotient
eliminators use ordinary WHNF, not that string-aware helper. The late conversion
hook remains limited to the exact `String.ofList.[]` application shape. Distinct
literal comparisons can decline; this is not a certificate of disequality.

## Regression and Review

Independent review found and prompted a repair before integration: the first
candidate incorrectly shared string-aware major reduction with quotient
eliminators. A checked custom environment with `String := Quot Nat (Eq Nat)`
demonstrates the difference. The old candidate passes all setup and constructor
controls, then expands the literal major; the repaired candidate leaves it
neutral. The 34-assertion regression covers literal, delta, beta and zeta majors.
This is a demonstrated operational discrepancy, not false logical acceptance.

The HOL normalizer's existing Nat-literal constructor form and reconstruction
of neutral wrapped majors differ from upstream WHNF ASTs. The regression checks
the absence of string-driven quotient iota, not global WHNF-AST equality.

## Completed Evidence

- The exact private sources subsequently integrated pass 16 native markers,
  totaling 1,181,651 assertions in 431.773s under a 900s cap. Source inventories
  match, there are no HOL errors, and the child is reaped. See
  `build/reports/hol-strings-native-quotient-fix.json` and its `.log` sibling.
- Of that total, 1,179,904 are chiefly exhaustive host UTF-8 checks, not Arena
  cases or metatheory proofs. The native string, text-interface and quotient
  regression groups have 73, 70 and 34 assertions respectively.
- All 22 export fixtures meet expectations: seven accept and fifteen decline.
  Positive gates precede negative controls. Report:
  `build/reports/hol-string-quotient-fix-exports.json`.
- All six exact Arena quotient tutorials accept at a 30s worker limit; 214
  other cases are explicitly unselected. Report:
  `build/reports/hol-string-quotient-fix-arena-selected.json`, paired with
  `hol-string-quotient-fix-runtime.json`. The private worker is stopped/reaped.
- The private frontend and its freshly rebuilt integrated copy each pass 61
  transport checks. The integrated quotient regression independently reproduces
  all 34 assertions in 72.860s, with unchanged sources and a reaped child.
  Both private and integrated runner copies pass all 18 provenance tests with
  local socket access (integrated rerun: 1.839s). A sandboxed attempt failed at
  socket creation, not in a kernel verdict. Earlier witness development failures
  are retained in the work log.

The pre-repair string candidate's full 216-input Arena attempt matched the prior
cache/pow classifications exactly: 85 accepts, six rejects, two either outcomes,
123 declines and four missing inputs. That is not a new full run of the repaired
integrated sources. No claim that all Arena tests pass is made.

## Reproduction and Boundaries

Commands and retained-report behavior are in `tests/hol_strings/README.md`.
The full native command includes a focused pow factory phase, not every primitive
phase. Byte decoding, parsing, scheduling, AST translation and quotation remain
unproved boundaries. HOL certificates establish the encoded object judgments,
not a general equivalence theorem to Lean. Count-limited quotation caches are
not byte-memory bounds, and proof-search fuel is not an allocation bound.
