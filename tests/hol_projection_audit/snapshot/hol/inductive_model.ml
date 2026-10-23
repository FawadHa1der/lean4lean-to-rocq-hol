(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Candidate generation only; environment.ml proves agreement with HOL definitions. *)
needs "hol/core.ml";;
module Lean4hol_model = struct
  open Lean4hol
  type rec_rule = {ctor:name;num_fields:int;rhs:expr}
  type ind_info = {num_params:int;num_indices:int;all:name list;ctors:name list;
    num_nested:int;is_rec:bool;is_reflexive:bool;is_unsafe:bool}
  type ctor_info = {induct:name;index:int;num_params:int;num_fields:int;is_unsafe:bool}
  type rec_info = {all:name list;num_params:int;num_indices:int;num_motives:int;
    num_minors:int;rules:rec_rule list;k:bool;is_unsafe:bool}
  type role = Inductive_role of ind_info | Constructor_role of ctor_info | Recursor_role of rec_info
  type kind = Definition | Theorem | Opaque | Axiom | Generated of role
  type declaration = {kind:kind;name:name;params:name list;typ:expr;value:expr option}
  type field = Data of expr | Recursive
  type inductive_block = {inductive_name:name;inductive_level:level;
    constructors:(name * field list) list;claims:declaration list}
  type inductive_family = {family_name:name;level_params:name list;
    parameters:(name * expr) list;result_level:level;
    family_constructors:(name * field list) list;family_claims:declaration list}
  type indexed_field = Index_data of expr | Index_recursive of expr list
  type indexed_constructor = {indexed_ctor_name:name;indexed_fields:indexed_field list;
    result_indices:expr list}
  type indexed_inductive = {indexed_name:name;indexed_level_params:name list;
    indexed_parameters:(name * expr) list;indices:(name * expr) list;
    indexed_result_level:level;indexed_constructors:indexed_constructor list;
    indexed_claims:declaration list}

  let elim_name = Str(Anonymous,"u")
  let rec_name i = Str(i,"rec")
  let apps f xs = List.fold_left (fun f a -> App(f,a)) f xs
  let vars n k = List.init n (fun j -> Bvar(k+n-1-j))
  let field_type i = function Data a -> a | Recursive -> Const(i,[])
  let positions fs = List.filter_map (fun (j,f) -> match f with Recursive -> Some j | _ -> None)
    (List.mapi (fun j f -> j,f) fs)
  let bind lam a b = if lam then Lam(Anonymous,a,b) else Pi(Anonymous,a,b)
  let field_binders lam i fs b = List.fold_right (fun f b -> bind lam (field_type i f) b) fs b
  let minor_type i (c,fs) j =
    let k = List.length fs and ps = positions fs in
    let r = List.length ps in
    let base = App(Bvar(j+k+r),apps (Const(c,[])) (vars k r)) in
    let ihs = List.mapi (fun h p -> App(Bvar(j+k+h),Bvar(k-1-p+h))) ps in
    field_binders false i fs (List.fold_right (bind false) ihs base)
  let minor_binders lam i cs b =
    List.fold_right (fun (j,c) b -> bind lam (minor_type i c j) b)
      (List.mapi (fun j c -> j,c) cs) b
  let motive_type i = Pi(Anonymous,Const(i,[]),Sort(Param elim_name))
  let rec_type i cs = Pi(Anonymous,motive_type i,
    minor_binders false i cs (Pi(Anonymous,Const(i,[]),App(Bvar(List.length cs+1),Bvar 0))))
  let rec_rhs i cs j (_,fs) =
    let k = List.length fs and m = List.length cs in
    let recfn = apps (Const(rec_name i,[Param elim_name])) (Bvar(k+m)::vars m k) in
    let ihs = List.map (fun p -> App(recfn,Bvar(k-1-p))) (positions fs) in
    Lam(Anonymous,motive_type i,minor_binders true i cs
      (field_binders true i fs (apps (Bvar(k+m-1-j)) (vars k 0 @ ihs))))
  let generate st b =
    tick st;
    let i = b.inductive_name and cs = b.constructors in
    let mk kind name params typ = {kind;name;params;typ;value=None} in
    let header = mk (Generated(Inductive_role {num_params=0;num_indices=0;all=[i];
      ctors=List.map fst cs;num_nested=0;
      is_rec=List.exists (fun (_,fs) -> List.mem Recursive fs) cs;
      is_reflexive=false;is_unsafe=false})) i [] (Sort b.inductive_level) in
    let ctors = List.mapi (fun index (c,fs) -> tick st;
      mk (Generated(Constructor_role {induct=i;index;num_params=0;
        num_fields=List.length fs;is_unsafe=false})) c []
        (field_binders false i fs (Const(i,[])))) cs in
    let rules = List.mapi (fun j ((c,fs) as spec) -> tick st;
      {ctor=c;num_fields=List.length fs;rhs=rec_rhs i cs j spec}) cs in
    let recursor = mk (Generated(Recursor_role {all=[i];num_params=0;num_indices=0;
      num_motives=1;num_minors=List.length cs;rules;k=false;is_unsafe=false}))
      (rec_name i) [elim_name] (rec_type i cs) in
    header::ctors@[recursor]

  let fresh_universe ps =
    let rec find j =
      let n=if j=0 then elim_name else Str(Anonymous,"u_"^string_of_int j) in
      if List.mem n ps then find(j+1) else n in
    find 0
  let family_rec_params ps large = if large then fresh_universe ps::ps else ps
  let family_elim ps large = if large then Param(fresh_universe ps) else Zero
  let parameter_binders lam pars b = List.fold_right (fun (_,a) b -> bind lam a b) pars b
  let family_app i ps p offset = apps (Const(i,List.map (fun n -> Param n) ps)) (vars p offset)
  let family_dom st i ps p offset = function
    | Data a -> lift st offset 0 a
    | Recursive -> family_app i ps p offset
  let family_binders st lam i ps p offset fs b =
    List.fold_right (fun (j,f) b -> bind lam (family_dom st i ps p (offset+j) f) b)
      (List.mapi (fun j f -> j,f) fs) b
  let family_ctor_type st i ps pars (_,fs) =
    let p=List.length pars in
    parameter_binders false pars
      (family_binders st false i ps p 0 fs (family_app i ps p (List.length fs)))
  let family_minor st i ps p (c,fs) j =
    let k=List.length fs and positions=positions fs in
    let r=List.length positions in
    let target=App(Bvar(j+k+r),apps (Const(c,List.map (fun n -> Param n) ps))
      (vars p (j+k+r+1) @ vars k r)) in
    let ihs=List.mapi (fun h pos -> App(Bvar(j+k+h),Bvar(k-1-pos+h))) positions in
    family_binders st false i ps p (j+1) fs (List.fold_right (bind false) ihs target)
  let family_minors st lam i ps p cs b =
    List.fold_right (fun (j,c) b -> bind lam (family_minor st i ps p c j) b)
      (List.mapi (fun j c -> j,c) cs) b
  let family_motive i ps p large =
    Pi(Anonymous,family_app i ps p 0,Sort(family_elim ps large))
  let family_rec_type st i ps pars cs large =
    let p=List.length pars and m=List.length cs in
    parameter_binders false pars (Pi(Anonymous,family_motive i ps p large,
      family_minors st false i ps p cs
        (Pi(Anonymous,family_app i ps p (m+1),App(Bvar(m+1),Bvar 0)))))
  let family_rhs st i ps pars cs large j (_,fs) =
    let p=List.length pars and m=List.length cs and k=List.length fs in
    let recfn=apps (Const(rec_name i,List.map (fun n -> Param n) (family_rec_params ps large)))
      (vars p (k+m+1) @ (Bvar(k+m)::vars m k)) in
    let ihs=List.map (fun pos -> App(recfn,Bvar(k-1-pos))) (positions fs) in
    parameter_binders true pars (Lam(Anonymous,family_motive i ps p large,
      family_minors st true i ps p cs
        (family_binders st true i ps p (m+1) fs
          (apps (Bvar(k+m-1-j)) (vars k 0 @ ihs)))))
  let generate_family st b ~large ~k =
    tick st;
    let i=b.family_name and ps=b.level_params and pars=b.parameters and cs=b.family_constructors in
    let p=List.length pars in
    let mk kind name params typ = {kind;name;params;typ;value=None} in
    let header=mk (Generated(Inductive_role {num_params=p;num_indices=0;all=[i];
      ctors=List.map fst cs;num_nested=0;is_rec=List.exists (fun (_,fs) -> List.mem Recursive fs) cs;
      is_reflexive=false;is_unsafe=false})) i ps (parameter_binders false pars (Sort b.result_level)) in
    let ctors=List.mapi (fun index ((c,fs) as spec) -> tick st;
      mk (Generated(Constructor_role {induct=i;index;num_params=p;num_fields=List.length fs;is_unsafe=false}))
        c ps (family_ctor_type st i ps pars spec)) cs in
    let rules=List.mapi (fun j ((c,fs) as spec) -> tick st;
      {ctor=c;num_fields=List.length fs;rhs=family_rhs st i ps pars cs large j spec}) cs in
    let recursor=mk (Generated(Recursor_role {all=[i];num_params=p;num_indices=0;num_motives=1;
      num_minors=List.length cs;rules;k;is_unsafe=false})) (rec_name i) (family_rec_params ps large)
      (family_rec_type st i ps pars cs large) in
    header::ctors@[recursor]

  let index_dom i ps p j = function
    | Index_data a -> a
    | Index_recursive xs -> apps (family_app i ps p j) xs
  let index_binders st lam i ps p offset fs b =
    List.fold_right (fun (j,f) b -> bind lam (lift st offset j (index_dom i ps p j f)) b)
      (List.mapi (fun j f -> j,f) fs) b
  let index_telescope st offset inds b =
    List.fold_right (fun (j,(_,a)) b -> bind false (lift st offset j a) b)
      (List.mapi (fun j a -> j,a) inds) b
  let index_positions fs = List.filter_map (fun (j,f) -> match f with
    Index_recursive xs -> Some(j,xs) | _ -> None) (List.mapi (fun j f -> j,f) fs)
  let index_move st offset k pos h a = lift st h 0 (lift st offset k (lift st (k-pos) 0 a))
  let index_ctor_type st i ps pars c =
    parameter_binders false pars (index_binders st false i ps (List.length pars) 0 c.indexed_fields
      (apps (family_app i ps (List.length pars) (List.length c.indexed_fields)) c.result_indices))
  let index_minor st i ps p c j =
    let fs=c.indexed_fields in let k=List.length fs and positions=index_positions fs in
    let r=List.length positions in
    let target=App(apps (Bvar(j+k+r))
      (List.map (fun a -> lift st r 0 (lift st (j+1) k a)) c.result_indices),
      apps (Const(c.indexed_ctor_name,List.map (fun n -> Param n) ps))
        (vars p (j+k+r+1) @ vars k r)) in
    let ihs=List.mapi (fun h (pos,xs) -> App(apps (Bvar(j+k+h))
      (List.map (index_move st (j+1) k pos h) xs),Bvar(k-1-pos+h))) positions in
    index_binders st false i ps p (j+1) fs (List.fold_right (bind false) ihs target)
  let index_minors st lam i ps p cs b = List.fold_right
    (fun (j,c) b -> bind lam (index_minor st i ps p c j) b) (List.mapi (fun j c -> j,c) cs) b
  let index_motive st i ps p inds large =
    index_telescope st 0 inds (Pi(Anonymous,
      apps (family_app i ps p (List.length inds)) (vars (List.length inds) 0),
      Sort(family_elim ps large)))
  let index_rec_type st i ps pars inds cs large =
    let p=List.length pars and ni=List.length inds and m=List.length cs in
    parameter_binders false pars (Pi(Anonymous,index_motive st i ps p inds large,
      index_minors st false i ps p cs (index_telescope st (m+1) inds
        (Pi(Anonymous,apps (family_app i ps p (m+ni+1)) (vars ni 0),
          App(apps (Bvar(m+ni+1)) (vars ni 1),Bvar 0))))))
  let index_rhs st i ps pars inds cs large j c =
    let p=List.length pars and m=List.length cs and k=List.length c.indexed_fields in
    let recfn=apps (Const(rec_name i,List.map (fun n -> Param n) (family_rec_params ps large)))
      (vars p (k+m+1) @ (Bvar(k+m)::vars m k)) in
    let ihs=List.map (fun (pos,xs) -> App(apps recfn
      (List.map (index_move st (m+1) k pos 0) xs),Bvar(k-1-pos))) (index_positions c.indexed_fields) in
    parameter_binders true pars (Lam(Anonymous,index_motive st i ps p inds large,
      index_minors st true i ps p cs (index_binders st true i ps p (m+1) c.indexed_fields
        (apps (Bvar(k+m-1-j)) (vars k 0 @ ihs)))))
  let generate_indexed st b ~large ~k =
    tick st;
    let i=b.indexed_name and ps=b.indexed_level_params and pars=b.indexed_parameters
    and inds=b.indices and cs=b.indexed_constructors in
    let p=List.length pars and ni=List.length inds in
    let mk kind name params typ={kind;name;params;typ;value=None} in
    let header=mk (Generated(Inductive_role {num_params=p;num_indices=ni;all=[i];
      ctors=List.map (fun c -> c.indexed_ctor_name) cs;num_nested=0;
      is_rec=List.exists (fun c -> index_positions c.indexed_fields<>[]) cs;
      is_reflexive=false;is_unsafe=false})) i ps
      (parameter_binders false pars (parameter_binders false inds (Sort b.indexed_result_level))) in
    let ctors=List.mapi (fun index c -> tick st;
      mk (Generated(Constructor_role {induct=i;index;num_params=p;
        num_fields=List.length c.indexed_fields;is_unsafe=false})) c.indexed_ctor_name ps
        (index_ctor_type st i ps pars c)) cs in
    let rules=List.mapi (fun j c -> tick st;
      {ctor=c.indexed_ctor_name;num_fields=List.length c.indexed_fields;
       rhs=index_rhs st i ps pars inds cs large j c}) cs in
    let recursor=mk (Generated(Recursor_role {all=[i];num_params=p;num_indices=ni;num_motives=1;
      num_minors=List.length cs;rules;k;is_unsafe=false})) (rec_name i) (family_rec_params ps large)
      (index_rec_type st i ps pars inds cs large) in
    header::ctors@[recursor]
end;;
