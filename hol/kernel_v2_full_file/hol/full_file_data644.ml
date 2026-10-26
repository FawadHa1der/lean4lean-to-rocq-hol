(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Hand-authored closed full447/493/607/642 fixture DATA. UNCOMPILED.
   No checker results, successful-call premises, new types or runtime evidence.
   Metadata strings/counts below are synthetic fixture literals, not claims
   about a real exporter, Lean version, source hash or observed table sizes. *)
needs "hol/file_driver642.ml";;

let l4_fixture_input644 = new_definition
 `l4_fixture_input644 rows =
   L4FileInput642 [51;46;49;46;48] [102;105;120;116;117;114;101] [] 0 0 0 rows`;;

let l4_fixture_id_name644 = new_definition
 `l4_fixture_id_name644 = L4String L4Anonymous [105;100;54;52;52]`;;
let l4_fixture_second_name644 = new_definition
 `l4_fixture_second_name644 = L4String L4Anonymous [105;100;50;54;52;52]`;;
let l4_fixture_unsafe_name644 = new_definition
 `l4_fixture_unsafe_name644 = L4String L4Anonymous [117;110;115;97;102;101;54;52;52]`;;

(* forall (p : Prop), p -> p. Inside the inner Pi, p has index1. *)
let l4_fixture_id_type644 = new_definition
 `l4_fixture_id_type644 =
   L4KPi447 L4Anonymous L4KDefault447 (L4KSort447 L4KZero447)
     (L4KPi447 L4Anonymous L4KDefault447 (L4KBVar447 0) (L4KBVar447 1))`;;
let l4_fixture_id_body644 = new_definition
 `l4_fixture_id_body644 =
   L4KLam447 L4Anonymous L4KDefault447 (L4KSort447 L4KZero447)
     (L4KLam447 L4Anonymous L4KDefault447 (L4KBVar447 0) (L4KBVar447 0))`;;
let l4_fixture_id_decl644 = new_definition
 `l4_fixture_id_decl644 = L4FileOrdinary642
   (L4InputTheorem607 l4_fixture_id_name644 [] l4_fixture_id_type644 l4_fixture_id_body644)
   [l4_fixture_id_name644]`;;
let l4_fixture_second_decl644 = new_definition
 `l4_fixture_second_decl644 = L4FileOrdinary642
   (L4InputTheorem607 l4_fixture_second_name644 [] l4_fixture_id_type644 l4_fixture_id_body644)
   [l4_fixture_second_name644]`;;

let l4_fixture_empty644 = new_definition
 `l4_fixture_empty644 = l4_fixture_input644 []`;;
let l4_fixture_identity644 = new_definition
 `l4_fixture_identity644 = l4_fixture_input644 [(11,l4_fixture_id_decl644)]`;;
let l4_fixture_invalid_body644 = new_definition
 `l4_fixture_invalid_body644 = l4_fixture_input644
   [(11,L4FileOrdinary642
     (L4InputTheorem607 l4_fixture_id_name644 [] l4_fixture_id_type644 (L4KSort447 L4KZero447))
     [l4_fixture_id_name644])]`;;
let l4_fixture_duplicate_headers644 = new_definition
 `l4_fixture_duplicate_headers644 = l4_fixture_input644
   [(11,l4_fixture_id_decl644);(19,l4_fixture_id_decl644)]`;;
let l4_fixture_two644 = new_definition
 `l4_fixture_two644 = l4_fixture_input644
   [(11,l4_fixture_id_decl644);(19,l4_fixture_second_decl644)]`;;
let l4_fixture_unsafe_to_safe644 = new_definition
 `l4_fixture_unsafe_to_safe644 = l4_fixture_input644
   [(11,L4FileOrdinary642
      (L4InputAxiom607 l4_fixture_unsafe_name644 [] l4_fixture_id_type644 T) []);
    (19,L4FileOrdinary642
      (L4InputTheorem607 l4_fixture_id_name644 [] l4_fixture_id_type644
        (L4KConst447 l4_fixture_unsafe_name644 [])) [l4_fixture_id_name644])]`;;
let l4_fixture_bad_format644 = new_definition
 `l4_fixture_bad_format644 = L4FileInput642 [51;46;49] [] [] 0 0 0 []`;;

(* Independent literal recursor metadata. Source universe u is renamed by509
   to the generated fresh universe; binder display names are ignored by480. *)
let l4_fixture_u644 = new_definition
 `l4_fixture_u644 = L4String L4Anonymous [117]`;;
let l4_fixture_bool_name644 = new_definition
 `l4_fixture_bool_name644 = L4String L4Anonymous [66;111;111;108]`;;
let l4_fixture_false_name644 = new_definition
 `l4_fixture_false_name644 = L4String l4_fixture_bool_name644 [102;97;108;115;101]`;;
let l4_fixture_true_name644 = new_definition
 `l4_fixture_true_name644 = L4String l4_fixture_bool_name644 [116;114;117;101]`;;
let l4_fixture_bool_rec_name644 = new_definition
 `l4_fixture_bool_rec_name644 = L4String l4_fixture_bool_name644 [114;101;99]`;;
let l4_fixture_bool_expr644 = new_definition
 `l4_fixture_bool_expr644 = L4KConst447 l4_fixture_bool_name644 []`;;
let l4_fixture_bool_motive644 = new_definition
 `l4_fixture_bool_motive644 = L4KPi447 L4Anonymous L4KDefault447
   l4_fixture_bool_expr644 (L4KSort447 (L4KParam447 l4_fixture_u644))`;;
let l4_fixture_bool_rec_type644 = new_definition
 `l4_fixture_bool_rec_type644 =
   L4KPi447 L4Anonymous L4KDefault447 l4_fixture_bool_motive644
    (L4KPi447 L4Anonymous L4KDefault447
      (L4KApp447 (L4KBVar447 0) (L4KConst447 l4_fixture_false_name644 []))
      (L4KPi447 L4Anonymous L4KDefault447
        (L4KApp447 (L4KBVar447 1) (L4KConst447 l4_fixture_true_name644 []))
        (L4KPi447 L4Anonymous L4KDefault447 l4_fixture_bool_expr644
          (L4KApp447 (L4KBVar447 3) (L4KBVar447 0)))))`;;
let l4_fixture_bool_rule644 = new_definition
 `l4_fixture_bool_rule644 branch =
   L4KLam447 L4Anonymous L4KDefault447 l4_fixture_bool_motive644
    (L4KLam447 L4Anonymous L4KDefault447
      (L4KApp447 (L4KBVar447 0) (L4KConst447 l4_fixture_false_name644 []))
      (L4KLam447 L4Anonymous L4KDefault447
        (L4KApp447 (L4KBVar447 1) (L4KConst447 l4_fixture_true_name644 []))
        (L4KBVar447 branch)))`;;
let l4_fixture_bool_type_decl644 = new_definition
 `l4_fixture_bool_type_decl644 indices =
   L4KDeclaration493 l4_fixture_bool_name644 [] (L4KSort447 (L4KSucc447 L4KZero447)) NONE
    (L4KDInductive493 (L4KInductiveData493 0 indices [l4_fixture_bool_name644]
      [l4_fixture_false_name644;l4_fixture_true_name644] 0 F F F)) L4KHintOpaque493`;;
let l4_fixture_bool_ctors644 = new_definition
 `l4_fixture_bool_ctors644 =
   [L4KDeclaration493 l4_fixture_false_name644 [] l4_fixture_bool_expr644 NONE
      (L4KDConstructor493 (L4KConstructorData493 l4_fixture_bool_name644 0 0 0 F)) L4KHintOpaque493;
    L4KDeclaration493 l4_fixture_true_name644 [] l4_fixture_bool_expr644 NONE
      (L4KDConstructor493 (L4KConstructorData493 l4_fixture_bool_name644 1 0 0 F)) L4KHintOpaque493]`;;
let l4_fixture_bool_rec644 = new_definition
 `l4_fixture_bool_rec644 =
   L4KDeclaration493 l4_fixture_bool_rec_name644 [l4_fixture_u644] l4_fixture_bool_rec_type644 NONE
    (L4KDRecursor493 (L4KRecursorData493 [l4_fixture_bool_name644] 0 0 1 2
      [L4KRecursorRule493 l4_fixture_false_name644 0 (l4_fixture_bool_rule644 1);
       L4KRecursorRule493 l4_fixture_true_name644 0 (l4_fixture_bool_rule644 0)] F F)) L4KHintOpaque493`;;
let l4_fixture_bool644 = new_definition
 `l4_fixture_bool644 = l4_fixture_input644
   [(31,L4FileInductive642 [l4_fixture_bool_type_decl644 0]
       l4_fixture_bool_ctors644 [l4_fixture_bool_rec644])]`;;
let l4_fixture_forged_inductive644 = new_definition
 `l4_fixture_forged_inductive644 = l4_fixture_input644
   [(31,L4FileInductive642 [l4_fixture_bool_type_decl644 1]
       l4_fixture_bool_ctors644 [l4_fixture_bool_rec644])]`;;

let l4_fixture_nat_name644 = new_definition
 `l4_fixture_nat_name644 = L4String L4Anonymous [78;97;116]`;;
let l4_fixture_zero_name644 = new_definition
 `l4_fixture_zero_name644 = L4String l4_fixture_nat_name644 [122;101;114;111]`;;
let l4_fixture_succ_name644 = new_definition
 `l4_fixture_succ_name644 = L4String l4_fixture_nat_name644 [115;117;99;99]`;;
let l4_fixture_nat_rec_name644 = new_definition
 `l4_fixture_nat_rec_name644 = L4String l4_fixture_nat_name644 [114;101;99]`;;
let l4_fixture_nat_expr644 = new_definition
 `l4_fixture_nat_expr644 = L4KConst447 l4_fixture_nat_name644 []`;;
let l4_fixture_nat_motive644 = new_definition
 `l4_fixture_nat_motive644 = L4KPi447 L4Anonymous L4KDefault447
   l4_fixture_nat_expr644 (L4KSort447 (L4KParam447 l4_fixture_u644))`;;
(* This type is under motive,zero-minor; the two inner binders are n,ih. *)
let l4_fixture_succ_minor644 = new_definition
 `l4_fixture_succ_minor644 = L4KPi447 L4Anonymous L4KDefault447 l4_fixture_nat_expr644
   (L4KPi447 L4Anonymous L4KDefault447 (L4KApp447 (L4KBVar447 2) (L4KBVar447 0))
     (L4KApp447 (L4KBVar447 3)
       (L4KApp447 (L4KConst447 l4_fixture_succ_name644 []) (L4KBVar447 1))))`;;
let l4_fixture_nat_rec_type644 = new_definition
 `l4_fixture_nat_rec_type644 =
   L4KPi447 L4Anonymous L4KDefault447 l4_fixture_nat_motive644
    (L4KPi447 L4Anonymous L4KDefault447
      (L4KApp447 (L4KBVar447 0) (L4KConst447 l4_fixture_zero_name644 []))
      (L4KPi447 L4Anonymous L4KDefault447 l4_fixture_succ_minor644
        (L4KPi447 L4Anonymous L4KDefault447 l4_fixture_nat_expr644
          (L4KApp447 (L4KBVar447 3) (L4KBVar447 0)))))`;;
(* Rule payload is under motive,zero-minor,succ-minor. *)
let l4_fixture_nat_rule644 = new_definition
 `l4_fixture_nat_rule644 body =
   L4KLam447 L4Anonymous L4KDefault447 l4_fixture_nat_motive644
    (L4KLam447 L4Anonymous L4KDefault447
      (L4KApp447 (L4KBVar447 0) (L4KConst447 l4_fixture_zero_name644 []))
      (L4KLam447 L4Anonymous L4KDefault447 l4_fixture_succ_minor644 body))`;;
let l4_fixture_nat_succ_rhs644 = new_definition
 `l4_fixture_nat_succ_rhs644 = l4_fixture_nat_rule644
   (L4KLam447 L4Anonymous L4KDefault447 l4_fixture_nat_expr644
     (L4KApp447 (L4KApp447 (L4KBVar447 1) (L4KBVar447 0))
       (L4KApp447
         (L4KApp447
           (L4KApp447
             (L4KApp447 (L4KConst447 l4_fixture_nat_rec_name644 [L4KParam447 l4_fixture_u644])
               (L4KBVar447 3)) (L4KBVar447 2)) (L4KBVar447 1)) (L4KBVar447 0))))`;;
let l4_fixture_nat_type_decl644 = new_definition
 `l4_fixture_nat_type_decl644 =
   L4KDeclaration493 l4_fixture_nat_name644 [] (L4KSort447 (L4KSucc447 L4KZero447)) NONE
    (L4KDInductive493 (L4KInductiveData493 0 0 [l4_fixture_nat_name644]
      [l4_fixture_zero_name644;l4_fixture_succ_name644] 0 T F F)) L4KHintOpaque493`;;
let l4_fixture_nat_ctors644 = new_definition
 `l4_fixture_nat_ctors644 =
   [L4KDeclaration493 l4_fixture_zero_name644 [] l4_fixture_nat_expr644 NONE
      (L4KDConstructor493 (L4KConstructorData493 l4_fixture_nat_name644 0 0 0 F)) L4KHintOpaque493;
    L4KDeclaration493 l4_fixture_succ_name644 []
      (L4KPi447 L4Anonymous L4KDefault447 l4_fixture_nat_expr644 l4_fixture_nat_expr644) NONE
      (L4KDConstructor493 (L4KConstructorData493 l4_fixture_nat_name644 1 0 1 F)) L4KHintOpaque493]`;;
let l4_fixture_nat_rec644 = new_definition
 `l4_fixture_nat_rec644 =
   L4KDeclaration493 l4_fixture_nat_rec_name644 [l4_fixture_u644] l4_fixture_nat_rec_type644 NONE
    (L4KDRecursor493 (L4KRecursorData493 [l4_fixture_nat_name644] 0 0 1 2
      [L4KRecursorRule493 l4_fixture_zero_name644 0 (l4_fixture_nat_rule644 (L4KBVar447 1));
       L4KRecursorRule493 l4_fixture_succ_name644 1 l4_fixture_nat_succ_rhs644] F F)) L4KHintOpaque493`;;
let l4_fixture_nat644 = new_definition
 `l4_fixture_nat644 = l4_fixture_input644
   [(41,L4FileInductive642 [l4_fixture_nat_type_decl644]
       l4_fixture_nat_ctors644 [l4_fixture_nat_rec644])]`;;

(* Diagnostic observation only: result tags never feed642's checker. *)
let l4_fixture_result_tag644 = new_recursive_definition l4_kresult_RECURSION491
 `(l4_fixture_result_tag644 (L4KAccept491 (env:l4_kdeclaration493 list)) = 0) /\
  (l4_fixture_result_tag644 (L4KReject491 reason) = 1) /\
  (l4_fixture_result_tag644 (L4KDecline491 decline_reason) = 2)`;;


(* Exact fixture-only defining theorems for parent646's local compset.
   Canonical dependency equations and numeric recursion bridges are separate. *)
let l4_fixture_equations644 =
 [l4_fixture_input644;
  l4_fixture_id_name644;
  l4_fixture_second_name644;
  l4_fixture_unsafe_name644;
  l4_fixture_id_type644;
  l4_fixture_id_body644;
  l4_fixture_id_decl644;
  l4_fixture_second_decl644;
  l4_fixture_empty644;
  l4_fixture_identity644;
  l4_fixture_invalid_body644;
  l4_fixture_duplicate_headers644;
  l4_fixture_two644;
  l4_fixture_unsafe_to_safe644;
  l4_fixture_bad_format644;
  l4_fixture_u644;
  l4_fixture_bool_name644;
  l4_fixture_false_name644;
  l4_fixture_true_name644;
  l4_fixture_bool_rec_name644;
  l4_fixture_bool_expr644;
  l4_fixture_bool_motive644;
  l4_fixture_bool_rec_type644;
  l4_fixture_bool_rule644;
  l4_fixture_bool_type_decl644;
  l4_fixture_bool_ctors644;
  l4_fixture_bool_rec644;
  l4_fixture_bool644;
  l4_fixture_forged_inductive644;
  l4_fixture_nat_name644;
  l4_fixture_zero_name644;
  l4_fixture_succ_name644;
  l4_fixture_nat_rec_name644;
  l4_fixture_nat_expr644;
  l4_fixture_nat_motive644;
  l4_fixture_succ_minor644;
  l4_fixture_nat_rec_type644;
  l4_fixture_nat_rule644;
  l4_fixture_nat_succ_rhs644;
  l4_fixture_nat_type_decl644;
  l4_fixture_nat_ctors644;
  l4_fixture_nat_rec644;
  l4_fixture_nat644;
  l4_fixture_result_tag644];;

