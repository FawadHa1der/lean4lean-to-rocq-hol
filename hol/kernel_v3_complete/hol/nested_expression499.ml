(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of rocq/NestedAdmission.v:39-155 and NestedTransform.v:12-19.
   SOURCE ONLY / UNCOMPILED; see ../NOTICE499.txt. Syntax restoration, NOT
   declaration admission. All dependencies remain held source selections. *)
needs "hol/nested_candidate494.ml";;
needs "hol/nested_restoration495.ml";;

(* Context is the full (bound,free) pair, not either projection alone. *)
let l4_knested_elimination_INDUCT499,l4_knested_elimination_RECURSION499 = define_type
 "l4_knested_elimination499 = L4KNestedElimination499 (l4_klocal489 list)
   ((l4_kbinding491 list)#((l4_name#l4_kbinding491)list))
   (l4_kind_spec493 list) ((l4_kexpr447#l4_name)list) (l4_name list) num";;

let l4_knested_params499 = new_recursive_definition l4_knested_elimination_RECURSION499
 `l4_knested_params499 (L4KNestedElimination499 ps ctx specs mapping ns count) = ps`;;
let l4_knested_context499 = new_recursive_definition l4_knested_elimination_RECURSION499
 `l4_knested_context499 (L4KNestedElimination499 ps ctx specs mapping ns count) = ctx`;;
let l4_knested_specs499 = new_recursive_definition l4_knested_elimination_RECURSION499
 `l4_knested_specs499 (L4KNestedElimination499 ps ctx specs mapping ns count) = specs`;;
let l4_knested_mapping499 = new_recursive_definition l4_knested_elimination_RECURSION499
 `l4_knested_mapping499 (L4KNestedElimination499 ps ctx specs mapping ns count) = mapping`;;
let l4_knested_aux_names499 = new_recursive_definition l4_knested_elimination_RECURSION499
 `l4_knested_aux_names499 (L4KNestedElimination499 ps ctx specs mapping ns count) = ns`;;
let l4_knested_aux_count499 = new_recursive_definition l4_knested_elimination_RECURSION499
 `l4_knested_aux_count499 (L4KNestedElimination499 ps ctx specs mapping ns count) = count`;;

(* Total list-first skipn. There is no skipn/DROP in the pinned core lists.ml. *)
let l4_kskipn499 = new_recursive_definition list_RECURSION
 `(l4_kskipn499 [] count = []) /\
 (l4_kskipn499 (CONS x xs) count =
   if count = 0 then CONS x xs else l4_kskipn499 xs (count - 1))`;;

(* Same callback on every cell: list traversal consumes no additional fuel.
   The first rejection/decline is propagated without calling later elements. *)
let l4_kmap_result499 = new_recursive_definition list_RECURSION
 `(l4_kmap_result499 [] f = L4KAccept491 []) /\
 (l4_kmap_result499 (CONS x xs) f =
   l4_kr_bind491 (f x) (\y.
     l4_kr_bind491 (l4_kmap_result499 xs f)
       (\ys. L4KAccept491 (CONS y ys))))`;;

let l4_nested_ctor_pattern499 = new_definition
 `l4_nested_ctor_pattern499 generated res n =
   match l4_kfind_decl493 generated n with
   | NONE -> NONE
   | SOME d ->
     (match l4_kdecl_kind493 d with
      | L4KDConstructor493 c ->
        (match l4_krestore_lookup495 (l4_knested_mapping499 res) (l4_kctor_induct493 c) with
         | NONE -> NONE
         | SOME pattern -> SOME (pattern,l4_kctor_induct493 c))
      | _ -> NONE)`;;

let l4_restore_ctor_name499 = new_definition
 `l4_restore_ctor_name499 fuel generated res n =
   match l4_nested_ctor_pattern499 generated res n with
   | NONE -> L4KAccept491 n
   | SOME hit ->
     (match FST (l4_ksplit_app489 (FST hit)) with
      | L4KConst447 original us ->
        l4_kr_from_na491 (l4_nested_replace_prefix437 n fuel (SND hit) original)
      | _ -> L4KReject491 L4KMalformedDeclaration491)`;;

let l4_rewrite_nested_head499 = new_definition
 `l4_rewrite_nested_head499 fuel generated res rec_map n us args =
   let np = LENGTH (l4_knested_params499 res) in
   match l4_krestore_lookup495 (l4_knested_mapping499 res) n with
   | SOME pattern ->
     if np <= LENGTH args then
       L4KAccept491 (l4_kapply_exprs489 (l4_kskipn499 args np)
         (l4_kinstantiate_locals495 pattern (l4_knested_params499 res)
           (l4_kfirstn494 args np) 0))
     else L4KReject491 L4KMalformedDeclaration491
   | NONE ->
     (match l4_nested_ctor_pattern499 generated res n with
      | SOME hit ->
        if np <= LENGTH args then
          let pattern = l4_kinstantiate_locals495 (FST hit)
            (l4_knested_params499 res) (l4_kfirstn494 args np) 0 in
          let split = l4_ksplit_app489 pattern in
          (match FST split with
           | L4KConst447 original levels ->
             l4_kr_bind491
               (l4_kr_from_na491 (l4_nested_replace_prefix437 n fuel (SND hit) original))
               (\ctor. L4KAccept491
                 (l4_kapply_exprs489 (APPEND (SND split) (l4_kskipn499 args np))
                   (L4KConst447 ctor levels)))
           | _ -> L4KReject491 L4KMalformedDeclaration491)
        else L4KReject491 L4KMalformedDeclaration491
      | NONE -> L4KAccept491
          (l4_kapply_exprs489 args (L4KConst447 (l4_krestore_name495 rec_map n) us)))`;;

(* Fuel recursion permits recursive calls on the split spine's head/arguments.
   Reconstructed or substituted patterns are NOT recursively restored again. *)
let l4_restore_nested_expr499 = new_recursive_definition num_RECURSION
 `(l4_restore_nested_expr499 0 generated res rec_map e = L4KDecline491 L4KOutOfFuel491) /\
 (l4_restore_nested_expr499 (SUC fuel) generated res rec_map e =
   match e with
   | L4KApp447 fn arg ->
     let split = l4_ksplit_app489 e in
     l4_kr_bind491
       (l4_kmap_result499 (SND split) (l4_restore_nested_expr499 fuel generated res rec_map))
       (\args.
         match FST split with
         | L4KConst447 n us -> l4_rewrite_nested_head499 fuel generated res rec_map n us args
         | head -> l4_kr_bind491 (l4_restore_nested_expr499 fuel generated res rec_map head)
             (\restored. L4KAccept491 (l4_kapply_exprs489 args restored)))
   | L4KConst447 n us -> l4_rewrite_nested_head499 fuel generated res rec_map n us []
   | L4KLam447 n bi a b ->
     l4_kr_bind491 (l4_restore_nested_expr499 fuel generated res rec_map a)
       (\domain. l4_kr_bind491 (l4_restore_nested_expr499 fuel generated res rec_map b)
         (\body. L4KAccept491 (L4KLam447 n bi domain body)))
   | L4KPi447 n bi a b ->
     l4_kr_bind491 (l4_restore_nested_expr499 fuel generated res rec_map a)
       (\domain. l4_kr_bind491 (l4_restore_nested_expr499 fuel generated res rec_map b)
         (\body. L4KAccept491 (L4KPi447 n bi domain body)))
   | L4KLet447 n a v b nd ->
     l4_kr_bind491 (l4_restore_nested_expr499 fuel generated res rec_map a)
       (\domain. l4_kr_bind491 (l4_restore_nested_expr499 fuel generated res rec_map v)
         (\value. l4_kr_bind491 (l4_restore_nested_expr499 fuel generated res rec_map b)
           (\body. L4KAccept491 (L4KLet447 n domain value body nd))))
   | L4KProj447 n i a ->
     l4_kr_bind491 (l4_restore_nested_expr499 fuel generated res rec_map a)
       (\value. L4KAccept491 (L4KProj447 n i value))
   | L4KMData447 a ->
     l4_kr_bind491 (l4_restore_nested_expr499 fuel generated res rec_map a)
       (\value. L4KAccept491 (L4KMData447 value))
   | _ -> L4KAccept491 e)`;;

(* Unlike nested_open_params491 this consumes a binder COUNT, not checker fuel;
   raw Pi and Lam are both opened. State is internal; the result is (locals,body). *)
let l4_restore_open499 = new_recursive_definition num_RECURSION
 `(l4_restore_open499 0 state e = L4KAccept491 ([],e)) /\
 (l4_restore_open499 (SUC count) state e =
   match e with
   | L4KPi447 n bi a b ->
     let fresh = l4_kind_fresh491 state n bi a in
     l4_kr_bind491
       (l4_restore_open499 count (SND fresh)
         (l4_kinst447 b (l4_klocal_expr489 (FST fresh))))
       (\rest. L4KAccept491 (CONS (FST fresh) (FST rest),SND rest))
   | L4KLam447 n bi a b ->
     let fresh = l4_kind_fresh491 state n bi a in
     l4_kr_bind491
       (l4_restore_open499 count (SND fresh)
         (l4_kinst447 b (l4_klocal_expr489 (FST fresh))))
       (\rest. L4KAccept491 (CONS (FST fresh) (FST rest),SND rest))
   | _ -> L4KReject491 L4KMalformedDeclaration491)`;;

let l4_restore_nested_type499 = new_definition
 `l4_restore_nested_type499 fuel generated res rec_map e =
   l4_kr_bind491
     (l4_restore_open499 (LENGTH (l4_knested_params499 res)) l4_kinitial_state491 e)
     (\opened.
       let params = FST opened in
       let mapping = MAP (\entry.
         (l4_kinstantiate_locals495 (FST entry) (l4_knested_params499 res)
           (MAP l4_klocal_expr489 params) 0,SND entry)) (l4_knested_mapping499 res) in
       let rebased = L4KNestedElimination499 params (l4_knested_context499 res)
         (l4_knested_specs499 res) mapping (l4_knested_aux_names499 res)
         (l4_knested_aux_count499 res) in
       l4_kr_bind491 (l4_restore_nested_expr499 fuel generated rebased rec_map (SND opened))
         (\body.
           match e with
           | L4KPi447 n bi a b -> L4KAccept491 (l4_kclose_pi489 params body)
           | _ -> L4KAccept491 (l4_kclose_lam489 params body)))`;;
