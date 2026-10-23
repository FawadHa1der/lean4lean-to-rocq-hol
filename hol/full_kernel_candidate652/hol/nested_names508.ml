(* Copyright 2026 Fawad Haider. Apache-2.0. See ../NOTICE508.txt.
   Actual total naming logic; SOURCE ONLY / UNCOMPILED.
   new_specification below requires a CLOSED proved existence theorem.
   No new axiom, unchecked witness, fuel fallback or external string oracle. *)
needs "hol/nested_allocation437.ml";;
needs "wf.ml";;

let l4_decimal_div_decreases508 = prove
 (`!n. ~(n < 10) ==> n DIV 10 < n`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (SPECL [`n:num`; `10`] DIV_MUL_LE) THEN ASM_ARITH_TAC);;

(* Division by ten strictly decreases on the recursive branch. The digits
   are ASCII numbers, in display order; zero has the single digit [48]. *)
let l4_decimal_exists508 = prove
 (`?digits:num->num list. !n.
    digits n = if n < 10 then [48 + n]
               else APPEND (digits (n DIV 10)) [48 + n MOD 10]`,
  MATCH_MP_TAC (BETA_RULE (ISPEC
    `\digits:num->num list. \n.
       if n < 10 then [48 + n]
       else APPEND (digits (n DIV 10)) [48 + n MOD 10]`
    WF_REC_num)) THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN COND_CASES_TAC THEN
  ASM_REWRITE_TAC [] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  ASM_MESON_TAC [l4_decimal_div_decreases508]);;

let l4_decimal_digits508 = new_specification
  ["l4_decimal_digits508"] l4_decimal_exists508;;

(* This creates ONE string component, e.g. main.rec_12. It is not a numeric
   name child, main.rec.12, nor an extra component named only "12". *)
let l4_indexed_rec_name508 = new_definition
 `l4_indexed_rec_name508 main i =
    L4String main (APPEND [114;101;99;95] (l4_decimal_digits508 i))`;;

(* Names-first order exposes structural list recursion. The original Rocq
   order is auxiliary_rec_names main names i. Preserve duplicates and order. *)
let l4_auxiliary_rec_names508 = new_recursive_definition list_RECURSION
 `(l4_auxiliary_rec_names508 [] main i = []) /\
  (l4_auxiliary_rec_names508 (CONS n ns) main i =
    CONS (l4_nested_rec_name437 n,l4_indexed_rec_name508 main i)
         (l4_auxiliary_rec_names508 ns main (SUC i)))`;;
