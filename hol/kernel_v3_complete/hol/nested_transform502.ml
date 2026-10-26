(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed port of local rocq/NestedTransform.v:307-436. See ../NOTICE502.txt.
   DRAFT SOURCE ONLY / UNCOMPILED / NOT INDEPENDENTLY REVIEWED OR TESTED. *)
needs "hol/nested_family498.ml";;
needs "hol/nested_expression499.ml";;
needs "hol/nested_keys480.ml";;

let l4_nested_replace_root502 = new_definition
 `l4_nested_replace_root502 fuel env ps params locals e w =
   l4_kr_bind491 (l4_nested_candidate494 fuel env w e)
    (\candidate. match candidate with
     | NONE -> L4KAccept491 (NONE,w)
     | SOME hit ->
       let d = FST hit in
       let data = FST (SND hit) in
       let us = FST (SND (SND hit)) in
       let args = SND (SND (SND hit)) in
       let oldparams = l4_kfirstn494 args (l4_kind_num_params493 data) in
       l4_kr_bind491
        (l4_kr_from_na491
          (l4_nested_rebase449
            (l4_kapply_exprs489 oldparams (L4KConst447 (l4_kdecl_name493 d) us)) fuel
            (MAP l4_klocal_id489 locals) (MAP l4_klocal_id489 params)))
        (\key. l4_kr_bind491
         (l4_kr_from_na491 (l4_nested_find_mapping480 (l4_knw_mapping494 w) fuel key))
         (\found. l4_kr_bind491
          (match found with
           | SOME aux -> L4KAccept491 w
           | NONE -> l4_nested_expand_family498 (l4_kind_all493 data) fuel
                       env ps params locals us oldparams w)
          (\updated. l4_kr_bind491
           (l4_kr_from_na491
             (l4_nested_find_mapping480 (l4_knw_mapping494 updated) fuel key))
           (\found. match found with
            | SOME aux -> L4KAccept491
                (SOME (l4_kapply_exprs489 (l4_kskipn499 args (l4_kind_num_params493 data))
                  (l4_kapply_locals489 locals (L4KConst447 aux (MAP L4KParam447 ps)))),updated)
            | NONE -> L4KDecline491 L4KUnsupportedDeclaration491)))))`;;

(* Preorder: do not revisit an inserted root. Child calls share remaining
   depth fuel but thread the growing work state strictly left to right. *)
let l4_nested_rewrite502 = new_recursive_definition num_RECURSION
 `(l4_nested_rewrite502 0 env ps params locals e w = L4KDecline491 L4KOutOfFuel491) /\
 (l4_nested_rewrite502 (SUC fuel) env ps params locals e w =
   l4_kr_bind491 (l4_nested_replace_root502 fuel env ps params locals e w)
    (\root.
      let current = SND root in
      match FST root with
      | SOME replacement -> L4KAccept491 (replacement,current)
      | NONE ->
        (match e with
         | L4KApp447 a b ->
           l4_kr_bind491 (l4_nested_rewrite502 fuel env ps params locals a current)
            (\first. l4_kr_bind491
              (l4_nested_rewrite502 fuel env ps params locals b (SND first))
              (\second. L4KAccept491 (L4KApp447 (FST first) (FST second),SND second)))
         | L4KLam447 n bi a b ->
           l4_kr_bind491 (l4_nested_rewrite502 fuel env ps params locals a current)
            (\first. l4_kr_bind491
              (l4_nested_rewrite502 fuel env ps params locals b (SND first))
              (\second. L4KAccept491 (L4KLam447 n bi (FST first) (FST second),SND second)))
         | L4KPi447 n bi a b ->
           l4_kr_bind491 (l4_nested_rewrite502 fuel env ps params locals a current)
            (\first. l4_kr_bind491
              (l4_nested_rewrite502 fuel env ps params locals b (SND first))
              (\second. L4KAccept491 (L4KPi447 n bi (FST first) (FST second),SND second)))
         | L4KLet447 n a v b nd ->
           l4_kr_bind491 (l4_nested_rewrite502 fuel env ps params locals a current)
            (\first. l4_kr_bind491
              (l4_nested_rewrite502 fuel env ps params locals v (SND first))
              (\second. l4_kr_bind491
                (l4_nested_rewrite502 fuel env ps params locals b (SND second))
                (\third. L4KAccept491
                  (L4KLet447 n (FST first) (FST second) (FST third) nd,SND third))))
         | L4KProj447 n i a ->
           l4_kr_bind491 (l4_nested_rewrite502 fuel env ps params locals a current)
             (\first. L4KAccept491 (L4KProj447 n i (FST first),SND first))
         | L4KMData447 a ->
           l4_kr_bind491 (l4_nested_rewrite502 fuel env ps params locals a current)
             (\first. L4KAccept491 (L4KMData447 (FST first),SND first))
         | _ -> L4KAccept491 (e,current))))`;;

let l4_nested_rewrite_ctors502 = new_recursive_definition list_RECURSION
 `(l4_nested_rewrite_ctors502 [] fuel env ps nparams params w = L4KAccept491 ([],w)) /\
 (l4_nested_rewrite_ctors502 (CONS d ctors) fuel env ps nparams params w =
   if fuel = 0 then L4KDecline491 L4KOutOfFuel491 else
   l4_kr_bind491
    (l4_nested_open_params491 nparams (fuel - 1)
      (L4KState491 (l4_knw_next_local494 w) [] []) (l4_kdecl_type493 d))
    (\opened.
      let locals = FST opened in
      let body = FST (SND opened) in
      let state = SND (SND opened) in
      l4_kr_bind491
       (l4_nested_rewrite502 (fuel - 1) env ps params locals body
         (l4_nested_set_local494 w (l4_kstate_next491 state)))
       (\rewritten. l4_kr_bind491
        (l4_nested_rewrite_ctors502 ctors (fuel - 1) env ps nparams params (SND rewritten))
        (\tail. L4KAccept491
          (CONS (L4KDeclaration493 (l4_kdecl_name493 d) (l4_kdecl_params493 d)
            (l4_kclose_pi489 locals (FST rewritten)) (l4_kdecl_value493 d)
            (l4_kdecl_kind493 d) (l4_kdecl_hints493 d)) (FST tail),SND tail)))))`;;

let l4_knth_error502 = new_recursive_definition list_RECURSION
 `(l4_knth_error502 [] idx = NONE) /\
 (l4_knth_error502 (CONS head rest) idx =
   if idx = 0 then SOME head else l4_knth_error502 rest (idx - 1))`;;

(* Fuel precedes index/list shape, unlike make_ctors498's paired-list gate. *)
let l4_nested_replace_spec502 = new_recursive_definition num_RECURSION
 `(l4_nested_replace_spec502 0 idx spec specs = L4KDecline491 L4KOutOfFuel491) /\
 (l4_nested_replace_spec502 (SUC fuel) idx spec specs =
   match specs with
   | [] -> L4KDecline491 L4KUnsupportedDeclaration491
   | CONS head rest ->
     if idx = 0 then L4KAccept491 (CONS spec rest) else
       l4_kr_bind491 (l4_nested_replace_spec502 fuel (idx - 1) spec rest)
         (\replaced. L4KAccept491 (CONS head replaced)))`;;

let l4_nested_worklist502 = new_recursive_definition num_RECURSION
 `(l4_nested_worklist502 0 idx env ps nparams params w = L4KDecline491 L4KOutOfFuel491) /\
 (l4_nested_worklist502 (SUC fuel) idx env ps nparams params w =
   match l4_knth_error502 (l4_knw_specs494 w) idx with
   | NONE -> L4KAccept491 w
   | SOME spec ->
     l4_kr_bind491
      (l4_nested_rewrite_ctors502 (l4_kspec_ctors493 spec) fuel env ps nparams params w)
      (\rewritten. l4_kr_bind491
       (l4_nested_replace_spec502 fuel idx
         (L4KIndSpec493 (l4_kspec_decl493 spec) (FST rewritten))
         (l4_knw_specs494 (SND rewritten)))
       (\specs. l4_nested_worklist502 fuel (SUC idx) env ps nparams params
         (l4_nested_set_specs494 (SND rewritten) specs))))`;;

let l4_eliminate_nested502 = new_recursive_definition num_RECURSION
 `(l4_eliminate_nested502 0 env ps nparams specs = L4KDecline491 L4KOutOfFuel491) /\
 (l4_eliminate_nested502 (SUC remaining) env ps nparams specs =
   match specs with
   | [] -> L4KReject491 L4KMalformedDeclaration491
   | CONS first rest ->
     l4_kr_bind491
      (l4_nested_open_params491 nparams remaining l4_kinitial_state491
        (l4_kdecl_type493 (l4_kspec_decl493 first)))
      (\opened.
        let params = FST opened in
        let state = SND (SND opened) in
        l4_kr_bind491
         (l4_nested_worklist502 remaining 0 env ps nparams params
           (L4KNestedWork494 specs [] 1 (l4_kstate_next491 state)))
         (\w.
           let names = MAP SND (l4_knw_mapping494 w) in
           L4KAccept491 (L4KNestedElimination499 params
             (l4_kstate_bound491 state,l4_kstate_free491 state)
             (l4_knw_specs494 w) (l4_knw_mapping494 w) names (LENGTH names)))))`;;
