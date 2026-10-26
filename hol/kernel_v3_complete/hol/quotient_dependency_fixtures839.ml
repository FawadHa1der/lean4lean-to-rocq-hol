(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   SOURCE ONLY / UNCOMPILED / UNRUN. Build once in a fresh guarded HOL session.
   Each case returns a closed HOL equation for the actual dependency predicate.
   Expected Booleans are test assertions, never production computation rules. *)
needs "hol/kernel_compute646.ml";;
needs "hol/kernel_equations647.ml";;

let l4_quotient_dependency_fixtures839 check =
  check ();
  let fixture = new_definition
   `l4_qfixture839 q ps value tag =
     let generated = l4_canonical_quotient608 q in
     L4KDeclaration493 (l4_kdecl_name493 generated) ps
       (l4_ksubst_levels488 (l4_kdecl_params493 generated)
         (MAP L4KParam447 ps) (l4_kdecl_type493 generated))
       value tag L4KHintOpaque493` in
  let state = Kernel_compute646.create ~conversions:l4_kernel_conversions647
    (fixture :: l4_kernel_equations647) in
  check ();
  let case label query expected = label,(fun () ->
    check ();
    let actual,th = Kernel_compute646.boolean state query in
    if actual <> expected || hyp th <> [] || frees(concl th) <> [] then
      failwith ("839: incorrect or open dependency result: " ^ label);
    let left,right = dest_eq(concl th) in
    if not (aconv left query) ||
       not (aconv right (if expected then `T` else `F`)) then
      failwith ("839: wrong dependency theorem: " ^ label);
    check ();
    th) in
  [
    case "canonical-type"
      `l4_quotient_header_matches839 L4KQType493 (l4_canonical_quotient608 L4KQType493)` true;
    case "canonical-ctor"
      `l4_quotient_header_matches839 L4KQCtor493 (l4_canonical_quotient608 L4KQCtor493)` true;
    case "canonical-lift"
      `l4_quotient_header_matches839 L4KQLift493 (l4_canonical_quotient608 L4KQLift493)` true;
    case "canonical-ind"
      `l4_quotient_header_matches839 L4KQInd493 (l4_canonical_quotient608 L4KQInd493)` true;
    case "renamed-type"
      `l4_quotient_header_matches839 L4KQType493
        (l4_qfixture839 L4KQType493 [L4String L4Anonymous [119]] NONE
          (L4KDQuotient493 L4KQType493))` true;
    case "renamed-ctor"
      `l4_quotient_header_matches839 L4KQCtor493
        (l4_qfixture839 L4KQCtor493 [L4String L4Anonymous [119]] NONE
          (L4KDQuotient493 L4KQCtor493))` true;
    case "renamed-lift"
      `l4_quotient_header_matches839 L4KQLift493
        (l4_qfixture839 L4KQLift493
          [L4String L4Anonymous [120];L4String L4Anonymous [121]] NONE
          (L4KDQuotient493 L4KQLift493))` true;
    case "renamed-lift-swaps-universe-names"
      `l4_quotient_header_matches839 L4KQLift493
        (l4_qfixture839 L4KQLift493
          [L4String L4Anonymous [118];L4String L4Anonymous [117]] NONE
          (L4KDQuotient493 L4KQLift493))` true;
    case "swapped-parameters-without-renaming-type"
      `l4_quotient_header_matches839 L4KQLift493
        (L4KDeclaration493 l4_q_lift_name608
          [L4String L4Anonymous [118];L4String L4Anonymous [117]]
          (l4_kdecl_type493 (l4_canonical_quotient608 L4KQLift493))
          NONE (L4KDQuotient493 L4KQLift493) L4KHintOpaque493)` false;
    case "renamed-ind"
      `l4_quotient_header_matches839 L4KQInd493
        (l4_qfixture839 L4KQInd493 [L4String L4Anonymous [119]] NONE
          (L4KDQuotient493 L4KQInd493))` true;
    case "ordinary-constant-is-not-builtin"
      `l4_quotient_header_matches839 L4KQType493
        (l4_qfixture839 L4KQType493 [L4String L4Anonymous [117]] NONE L4KDAssumption493)` false;
    case "wrong-quotient-tag"
      `l4_quotient_header_matches839 L4KQType493
        (l4_qfixture839 L4KQType493 [L4String L4Anonymous [117]] NONE
          (L4KDQuotient493 L4KQCtor493))` false;
    case "unsafe-wrapper-is-not-builtin"
      `l4_quotient_header_matches839 L4KQType493
        (l4_qfixture839 L4KQType493 [L4String L4Anonymous [117]] NONE
          (L4KDUnsafe493 (L4KDQuotient493 L4KQType493)))` false;
    case "builtin-cannot-have-value"
      `l4_quotient_header_matches839 L4KQType493
        (l4_qfixture839 L4KQType493 [L4String L4Anonymous [117]]
          (SOME (L4KSort447 L4KZero447)) (L4KDQuotient493 L4KQType493))` false;
    case "duplicate-universes"
      `l4_quotient_header_matches839 L4KQLift493
        (l4_qfixture839 L4KQLift493
          [L4String L4Anonymous [119];L4String L4Anonymous [119]] NONE
          (L4KDQuotient493 L4KQLift493))` false;
    case "wrong-universe-arity"
      `l4_quotient_header_matches839 L4KQLift493
        (l4_qfixture839 L4KQLift493 [L4String L4Anonymous [119]] NONE
          (L4KDQuotient493 L4KQLift493))` false;
    case "wrong-declaration-name"
      `l4_quotient_header_matches839 L4KQType493
        (L4KDeclaration493 L4Anonymous [L4String L4Anonymous [117]]
          (l4_kdecl_type493 (l4_canonical_quotient608 L4KQType493))
          NONE (L4KDQuotient493 L4KQType493) L4KHintOpaque493)` false;
    case "wrong-type"
      `l4_quotient_header_matches839 L4KQType493
        (L4KDeclaration493 l4_q_name608 [L4String L4Anonymous [117]]
          (L4KSort447 L4KZero447) NONE (L4KDQuotient493 L4KQType493) L4KHintOpaque493)` false;
    case "renaming-parameters-alone-is-not-enough"
      `l4_quotient_header_matches839 L4KQType493
        (L4KDeclaration493 l4_q_name608 [L4String L4Anonymous [119]]
          (l4_kdecl_type493 (l4_canonical_quotient608 L4KQType493))
          NONE (L4KDQuotient493 L4KQType493) L4KHintOpaque493)` false;
    case "hints-do-not-change-quotient-identity"
      `l4_quotient_header_matches839 L4KQType493
        (L4KDeclaration493 l4_q_name608 [L4String L4Anonymous [117]]
          (l4_kdecl_type493 (l4_canonical_quotient608 L4KQType493))
          NONE (L4KDQuotient493 L4KQType493) (L4KHintRegular493 7))` true;
    case "metadata-wrapper-not-erased"
      `l4_quotient_header_matches839 L4KQType493
        (L4KDeclaration493 l4_q_name608 [L4String L4Anonymous [117]]
          (L4KMData447 (l4_kdecl_type493 (l4_canonical_quotient608 L4KQType493)))
          NONE (L4KDQuotient493 L4KQType493) L4KHintOpaque493)` false;
    case "absent-dependency"
      `l4_quotient_dependency839 [] L4KQType493` false;
    case "bad-first-visible-shadows-canonical"
      `l4_quotient_dependency839
        [l4_qfixture839 L4KQType493 [L4String L4Anonymous [117]] NONE L4KDAssumption493;
         l4_canonical_quotient608 L4KQType493] L4KQType493` false;
    case "canonical-first-visible-shadows-bad"
      `l4_quotient_dependency839
        [l4_canonical_quotient608 L4KQType493;
         l4_qfixture839 L4KQType493 [L4String L4Anonymous [117]] NONE L4KDAssumption493]
        L4KQType493` true;
    case "unrelated-entry-skipped"
      `l4_quotient_dependency839
        [l4_canonical_quotient608 L4KQLift493;l4_canonical_quotient608 L4KQType493]
        L4KQType493` true;
    case "type-needs-no-quotient-dependency"
      `l4_quotient_dependencies839 [] L4KQType493` true;
    case "ctor-missing-type"
      `l4_quotient_dependencies839 [] L4KQCtor493` false;
    case "ctor-has-type"
      `l4_quotient_dependencies839 [l4_canonical_quotient608 L4KQType493] L4KQCtor493` true;
    case "lift-missing-type"
      `l4_quotient_dependencies839 [] L4KQLift493` false;
    case "lift-has-type"
      `l4_quotient_dependencies839 [l4_canonical_quotient608 L4KQType493] L4KQLift493` true;
    case "ind-missing-both"
      `l4_quotient_dependencies839 [] L4KQInd493` false;
    case "ind-missing-ctor"
      `l4_quotient_dependencies839 [l4_canonical_quotient608 L4KQType493] L4KQInd493` false;
    case "ind-missing-type"
      `l4_quotient_dependencies839 [l4_canonical_quotient608 L4KQCtor493] L4KQInd493` false;
    case "ind-has-both"
      `l4_quotient_dependencies839
        [l4_canonical_quotient608 L4KQCtor493;l4_canonical_quotient608 L4KQType493]
        L4KQInd493` true
  ];;
