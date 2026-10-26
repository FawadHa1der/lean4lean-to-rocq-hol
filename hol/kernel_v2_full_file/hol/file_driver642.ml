(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Full447 file dispatch with explicit source-row coverage. SOURCE ONLY.
   See ../API642.txt and ../NOTICE642.txt. No supplied logical verdicts. *)
needs "hol/flatten_prelude650.ml";;
needs "hol/inductive_safety633.ml";;
needs "hol/quotient_admission608.ml";;

let l4_file_decl_INDUCT642,l4_file_decl_RECURSION642 = define_type
 "l4_file_decl642 =
    L4FileOrdinary642 l4_input_decl607 (l4_name list) |
    L4FileQuotient642 l4_name (l4_name list) l4_kexpr447 l4_kquotient493 |
    L4FileInductive642 (l4_kdeclaration493 list) (l4_kdeclaration493 list)
      (l4_kdeclaration493 list)";;
let l4_file_batch_INDUCT642,l4_file_batch_RECURSION642 = define_type
 "l4_file_batch642 = L4FileSingle642 num | L4FileMutual642 num (num list)";;
let l4_file_input_INDUCT642,l4_file_input_RECURSION642 = define_type
 "l4_file_input642 = L4FileInput642 (num list) (num list) (num list)
    num num num ((num # l4_file_decl642) list)";;

let l4_file_rows642 = new_recursive_definition l4_file_input_RECURSION642
 `l4_file_rows642 (L4FileInput642 format lean hash names levels exprs rows) = rows`;;

let l4_file_decl_names642 = new_definition
 `l4_file_decl_names642 decl =
    match decl with
    | L4FileOrdinary642 input all ->
        (match input with
         | L4InputAxiom607 n ps ty unsafe -> [n]
         | L4InputDefinition607 hints n ps ty value safety -> [n]
         | L4InputTheorem607 n ps ty value -> [n]
         | L4InputOpaque607 n ps ty value unsafe -> [n]
         | L4InputUnsupported607 -> [])
    | L4FileQuotient642 n ps ty kind -> [n]
    | L4FileInductive642 types ctors recs ->
        MAP l4_kdecl_name493 (APPEND types (APPEND ctors recs))`;;

let l4_file_all642 = new_definition
 `l4_file_all642 decl =
    match decl with
    | L4FileOrdinary642 input all -> all
    | _ -> []`;;

(* Match Replay.prepare's group trigger, not all unsafe definitions. *)
let l4_file_requires_mutual642 = new_definition
 `l4_file_requires_mutual642 decl <=>
    match decl with
    | L4FileOrdinary642 (L4InputDefinition607 hints n ps ty value mode) all ->
        mode = L4InputPartial607 \/ (mode = L4InputUnsafe607 /\ 1 < LENGTH all)
    | _ -> F`;;

let l4_file_batch_members642 = new_recursive_definition l4_file_batch_RECURSION642
 `(l4_file_batch_members642 (L4FileSingle642 i) = [i]) /\
  (l4_file_batch_members642 (L4FileMutual642 leader members) = members)`;;
let l4_file_schedule_rows642 = new_recursive_definition list_RECURSION
 `(l4_file_schedule_rows642 [] = []) /\
  (l4_file_schedule_rows642 (CONS batch rest) =
    APPEND (l4_file_batch_members642 batch) (l4_file_schedule_rows642 rest))`;;
let l4_file_indices_unique642 = new_recursive_definition list_RECURSION
 `(l4_file_indices_unique642 [] <=> T) /\
  (l4_file_indices_unique642 (CONS i rest) <=>
    ~MEM (i:num) rest /\ l4_file_indices_unique642 rest)`;;

(* Coverage is tied to actual source-row count, never the copied table counts. *)
let l4_file_coverage642 = new_definition
 `l4_file_coverage642 count batches <=>
    let indices = l4_file_schedule_rows642 batches in
    LENGTH indices = count /\ ALL (\i. i < count) indices /\
    l4_file_indices_unique642 indices`;;

let l4_file_same_name_set642 = new_definition
 `l4_file_same_name_set642 xs ys <=>
    LENGTH xs = LENGTH ys /\ ALL (\n:l4_name. MEM n ys) xs`;;

let l4_file_resolve_members642 = new_recursive_definition list_RECURSION
 `(l4_file_resolve_members642 [] rows = L4KAccept491 []) /\
  (l4_file_resolve_members642 (CONS i rest) rows =
    if i < LENGTH rows then
      l4_kr_bind491 (l4_file_resolve_members642 rest rows)
        (\members. L4KAccept491 (CONS (SND (EL i rows)) members))
    else L4KReject491 L4KMalformedDeclaration491)`;;

(* Retain every definition, in leader.all order. Logical header/body/mode/
   parameter checks remain mandatory in the concrete624 mutual admission. *)
let l4_file_mutual_inputs642 = new_recursive_definition list_RECURSION
 `(l4_file_mutual_inputs642 [] all = L4KAccept491 []) /\
  (l4_file_mutual_inputs642 (CONS decl rest) all =
    match decl with
    | L4FileOrdinary642 (L4InputDefinition607 hints n ps ty value mode) members ->
        if l4_names_unique437 members /\ l4_file_same_name_set642 all members then
          l4_kr_bind491 (l4_file_mutual_inputs642 rest all)
            (\inputs. L4KAccept491
              (CONS (L4InputDefinition607 hints n ps ty value mode) inputs))
        else L4KReject491 L4KMalformedDeclaration491
    | _ -> L4KReject491 L4KMalformedDeclaration491)`;;

let l4_file_admit_single642 = new_definition
 `l4_file_admit_single642 fuel env decl =
    if l4_file_requires_mutual642 decl then L4KReject491 L4KMalformedDeclaration491 else
    match decl with
    | L4FileOrdinary642 input all -> l4_admit_extended624 fuel env input
    | L4FileQuotient642 n ps ty kind -> l4_admit_quotient608 fuel env n ps ty kind
    | L4FileInductive642 types ctors recs -> l4_admit_inductive_extended633 fuel env types ctors recs`;;

let l4_file_check_batch642 = new_definition
 `l4_file_check_batch642 fuel env rows batch =
    match batch with
    | L4FileSingle642 i ->
        if i < LENGTH rows then l4_file_admit_single642 fuel env (SND (EL i rows))
        else L4KReject491 L4KMalformedDeclaration491
    | L4FileMutual642 leader indices ->
        if leader < LENGTH rows /\ MEM leader indices then
          let first = SND (EL leader rows) in
          let all = l4_file_all642 first in
          if l4_file_requires_mutual642 first /\ l4_names_unique437 all then
            l4_kr_bind491 (l4_file_resolve_members642 indices rows) (\members.
              l4_kr_bind491 (l4_file_mutual_inputs642 members all) (\inputs.
                if MAP l4_mutual_name624 inputs = all then l4_admit_mutual624 fuel env inputs
                else L4KReject491 L4KMalformedDeclaration491))
          else L4KReject491 L4KMalformedDeclaration491
        else L4KReject491 L4KMalformedDeclaration491`;;

let l4_file_check_batches642 = new_recursive_definition list_RECURSION
 `(l4_file_check_batches642 [] fuel env rows = L4KAccept491 env) /\
  (l4_file_check_batches642 (CONS batch rest) fuel env rows =
    l4_kr_bind491 (l4_file_check_batch642 fuel env rows batch)
      (\next. l4_file_check_batches642 rest fuel next rows))`;;

let l4_check_file642 = new_definition
 `l4_check_file642 fuel input batches =
    match input with
    | L4FileInput642 format lean hash name_count level_count expr_count rows ->
        if ~(format = [51;46;49;46;48]) then
          L4KDecline491 L4KUnsupportedDeclaration491 else
        if ~l4_names_unique437 (l4_kflatten516 (MAP (\row. l4_file_decl_names642 (SND row)) rows))
        then L4KReject491 L4KDuplicateDeclaration491 else
        if ~l4_file_coverage642 (LENGTH rows) batches
        then L4KReject491 L4KMalformedDeclaration491 else
        l4_file_check_batches642 batches fuel [] rows`;;

let l4_file_accepts642 = new_definition
 `l4_file_accepts642 fuel input batches <=>
    match l4_check_file642 fuel input batches with
    | L4KAccept491 env -> T
    | _ -> F`;;

(* Input assumptions are data, not new HOL axioms or proved Lean theorems. *)
let l4_file_axioms642 = new_recursive_definition list_RECURSION
 `(l4_file_axioms642 [] = []) /\
  (l4_file_axioms642 (CONS row rest) =
    match SND row with
    | L4FileOrdinary642 (L4InputAxiom607 n ps ty unsafe) all ->
        CONS (L4InputAxiom607 n ps ty unsafe) (l4_file_axioms642 rest)
    | _ -> l4_file_axioms642 rest)`;;
