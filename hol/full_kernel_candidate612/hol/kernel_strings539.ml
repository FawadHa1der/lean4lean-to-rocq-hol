(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Full447/491 object-language port of local Rocq Checker.v430-487.
   SOURCE ONLY / UNCOMPILED. See ../NOTICE539.txt for the recursion change. *)
needs "hol/literal_readiness533.ml";;
needs "hol/kernel_locals489.ml";;
needs "hol/nested_parameters491.ml";;

let l4_core_list_name539 = new_definition
 `l4_core_list_name539 = L4String L4Anonymous [76;105;115;116]`;;

let l4_core_cont539 = new_definition
 `l4_core_cont539 (b:num) <=> 128 <= b /\ b < 192`;;

let l4_core_digit539 = new_definition
 `l4_core_digit539 (b:num) = b MOD 64`;;

let l4_core_append_digit539 = new_definition
 `l4_core_append_digit539 n b = n * 64 + l4_core_digit539 b`;;

(* List-first structural recursion: pending counts continuation bytes still
   needed; lo/hi constrain the next continuation, then reset to 128/192.
   The public entry point always starts in the idle state. Each input element
   is checked as a byte; unlike Rocq ascii, HOL num admits values above 255. *)
let l4_core_utf8_scan539 = new_recursive_definition list_RECURSION
 `(l4_core_utf8_scan539 [] pending acc lo hi =
      if pending = 0 then SOME ([]:num list) else NONE) /\
  (l4_core_utf8_scan539 (CONS b rest) pending acc lo hi =
    if b < 256 then
      if pending = 0 then
        if b < 128 then
          (match l4_core_utf8_scan539 rest 0 0 128 192 with
           | NONE -> NONE
           | SOME cs -> SOME (CONS b cs))
        else if b < 194 then NONE
        else if b < 224 then
          l4_core_utf8_scan539 rest 1 (b - 192) 128 192
        else if b < 240 then
          l4_core_utf8_scan539 rest 2 (b - 224)
            (if b = 224 then 160 else 128) (if b = 237 then 160 else 192)
        else if b < 245 then
          l4_core_utf8_scan539 rest 3 (b - 240)
            (if b = 240 then 144 else 128) (if b = 244 then 144 else 192)
        else NONE
      else if l4_core_cont539 b /\ lo <= b /\ b < hi then
        if pending = 1 then
          (match l4_core_utf8_scan539 rest 0 0 128 192 with
           | NONE -> NONE
           | SOME cs -> SOME (CONS (l4_core_append_digit539 acc b) cs))
        else l4_core_utf8_scan539 rest (pending - 1)
               (l4_core_append_digit539 acc b) 128 192
      else NONE
    else NONE)`;;

let l4_core_utf8_539 = new_definition
 `l4_core_utf8_539 bytes = l4_core_utf8_scan539 bytes 0 0 128 192`;;

(* This raw builder takes naturals, not necessarily Unicode scalar values.
   Only the decoder/expansion path constrains them. List universes are [0];
   Char, Char.ofNat and String.ofList have no universe arguments. *)
let l4_core_char_list539 = new_recursive_definition list_RECURSION
 `(l4_core_char_list539 [] =
    L4KApp447
      (L4KConst447 (L4String l4_core_list_name539 [110;105;108]) [L4KZero447])
      (L4KConst447 l4_core_char_name533 [])) /\
  (l4_core_char_list539 (CONS c cs) =
    l4_kapply_exprs489
      [L4KConst447 l4_core_char_name533 [];
       L4KApp447 (L4KConst447 l4_core_char_of_nat533 []) (L4KNatLit447 c);
       l4_core_char_list539 cs]
      (L4KConst447 (L4String l4_core_list_name539 [99;111;110;115]) [L4KZero447]))`;;

let l4_core_expand_string539 = new_definition
 `l4_core_expand_string539 bytes =
    match l4_core_utf8_539 bytes with
    | NONE -> L4KReject491 L4KMalformedDeclaration491
    | SOME cs ->
      L4KAccept491 (L4KApp447 (L4KConst447 l4_core_string_of_list533 [])
                             (l4_core_char_list539 cs))`;;
