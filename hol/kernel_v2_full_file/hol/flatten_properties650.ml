(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   ALL TWELVE PROPOSED PROOF SCRIPTS UNCOMPILED / NOT EXECUTED.
   Ten closed examples and two general list equations; no checker premises. *)
needs "hol/flatten_prelude650.ml";;

let L4_FLAT_EMPTY650 = prove
 (`FLAT ([]:(num list)list) = []`,
  REWRITE_TAC[l4_flat650]);;

let L4_FLAT_EMPTY_ROW650 = prove
 (`FLAT ([[]]:(num list)list) = []`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let L4_FLAT_EMPTY_ROWS650 = prove
 (`FLAT ([[];[];[]]:(num list)list) = []`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let L4_FLAT_SINGLE_ROW650 = prove
 (`FLAT [[1;2;3]] = [1;2;3]`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let L4_FLAT_ORDER650 = prove
 (`FLAT [[3;1];[];[2;4]] = [3;1;2;4]`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let L4_FLAT_DUPLICATES650 = prove
 (`FLAT [[2];[1;2];[2]] = [2;1;2;2]`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let L4_FLAT_BOOL650 = prove
 (`FLAT [[T;F];[];[F;T]] = [T;F;F;T]`,
  REWRITE_TAC[l4_flat650;APPEND]);;

(* Exactly one layer is concatenated: the inner empty row is retained. *)
let L4_FLAT_ONE_LAYER650 = prove
 (`FLAT ([[[1];[]];[];[[2;3]]]:((num list)list)list) = [[1];[];[2;3]]`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let L4_FLAT_MAP650 = prove
 (`FLAT (MAP (\xs:num list. MAP (\n:num. n) xs) [[1;2];[];[2]]) = [1;2;2]`,
  REWRITE_TAC[l4_flat650;MAP;APPEND]);;

let L4_FLAT_APPEND_ROWS650 = prove
 (`FLAT (APPEND [[1];[]] [[2];[3]]) = [1;2;3]`,
  REWRITE_TAC[l4_flat650;APPEND]);;

let L4_FLAT_ITLIST650 = prove
 (`!xss:(A list)list. FLAT xss = ITLIST APPEND xss []`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[l4_flat650;ITLIST]);;

let L4_FLAT_APPEND650 = prove
 (`!(xss:(A list)list) yss.
    FLAT (APPEND xss yss) = APPEND (FLAT xss) (FLAT yss)`,
  LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[l4_flat650;APPEND;APPEND_ASSOC]);;
