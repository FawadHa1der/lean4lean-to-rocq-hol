(* Copyright 2026 Fawad Haider. Apache-2.0. See ../NOTICE518.txt.
   SOURCE ONLY / UNCOMPILED. Preserved successor of513. Preparation is NOT logical admission. *)
needs "hol/kernel_declarations493.ml";;
needs "hol/nested_parameters491.ml";;
needs "hol/nested_allocation437.ml";;

(* Preserve requested constructor order and first matching declaration.
   Owners and types are intentionally checked later, not in this collector. *)
let l4_gather_ctors518 = new_recursive_definition list_RECURSION
 `(l4_gather_ctors518 [] ctors = L4KAccept491 []) /\
  (l4_gather_ctors518 (CONS n ns) ctors =
    match l4_kfind_decl493 ctors n with
    | NONE -> L4KReject491 L4KMalformedDeclaration491
    | SOME d ->
      (match l4_kdecl_kind493 d with
       | L4KDConstructor493 info ->
         l4_kr_bind491 (l4_gather_ctors518 ns ctors)
           (\ds. L4KAccept491 (CONS d ds))
       | _ -> L4KReject491 L4KMalformedDeclaration491))`;;

let l4_gather_specs518 = new_recursive_definition list_RECURSION
 `(l4_gather_specs518 [] ctors = L4KAccept491 []) /\
  (l4_gather_specs518 (CONS d ds) ctors =
    match l4_kdecl_kind493 d with
    | L4KDInductive493 info ->
      l4_kr_bind491 (l4_gather_ctors518 (l4_kind_ctors493 info) ctors)
        (\cs. l4_kr_bind491 (l4_gather_specs518 ds ctors)
          (\rest. L4KAccept491 (CONS (L4KIndSpec493 d cs) rest)))
    | _ -> L4KReject491 L4KMalformedDeclaration491)`;;

(* Boolean metadata flags, not Unsafe kind wrappers. Any other exact kind
   fails this preparation guard. The recs list has no exact-role check here. *)
let l4_safety_matches518 = new_definition
 `l4_safety_matches518 unsafe d <=>
    match l4_kdecl_kind493 d with
    | L4KDInductive493 info -> l4_kind_is_unsafe493 info = unsafe
    | L4KDConstructor493 info -> l4_kctor_is_unsafe493 info = unsafe
    | L4KDRecursor493 info -> l4_krec_is_unsafe493 info = unsafe
    | _ -> F`;;

let l4_prepare_inductive518 = new_definition
 `l4_prepare_inductive518 env types ctors recs =
    match types with
    | [] -> L4KReject491 L4KMalformedDeclaration491
    | CONS first rest ->
      (match l4_kdecl_kind493 first with
       | L4KDInductive493 info ->
         let sources = APPEND types (APPEND ctors recs) in
         let ns = MAP l4_kdecl_name493 sources in
         if l4_names_unique437 ns then
           if ALL (\n. l4_kfind_decl493 env n = NONE) ns then
             if ALL (l4_safety_matches518 (l4_kind_is_unsafe493 info)) sources then
               l4_kr_bind491 (l4_gather_specs518 types ctors)
                 (\specs.
                   let names = ITLIST APPEND (MAP (\s. MAP l4_kdecl_name493 (l4_kspec_ctors493 s)) specs) [] in
                   if LENGTH names = LENGTH ctors then
                     if l4_names_unique437 names then
                       L4KAccept491 (l4_kdecl_params493 first,l4_kind_num_params493 info,specs)
                     else L4KReject491 L4KMalformedDeclaration491
                   else L4KReject491 L4KMalformedDeclaration491)
             else L4KReject491 L4KMalformedDeclaration491
           else L4KReject491 L4KDuplicateDeclaration491
         else L4KReject491 L4KDuplicateDeclaration491
       | _ -> L4KReject491 L4KMalformedDeclaration491)`;;
