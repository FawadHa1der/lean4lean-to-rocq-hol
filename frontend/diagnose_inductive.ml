(* Diagnostic only. Never used to produce a checker verdict. *)
module C = Lean_arena
module A = Rocq_adapter
let get label = function
  | C.Accept x -> Printf.printf "OK %s\n%!" label; x
  | C.Reject r -> failwith (label ^ ": " ^ A.reject_reason r)
  | C.Decline r -> failwith (label ^ ": " ^ A.decline_reason r)
let rec native_list = function C.Nil -> [] | C.Cons(x,xs) -> x::native_list xs
let rec native_nat = function C.O -> 0 | C.S n -> 1 + native_nat n
let b = function C.True -> true | C.False -> false
let rec str = function
  | C.EmptyString -> ""
  | C.String(C.Ascii(a,b0,c,d,e,f,g,h),s) ->
    let bits = [a;b0;c;d;e;f;g;h] in
    let _,n=List.fold_left(fun(i,n)x->i+1,n lor (if b x then 1 lsl i else 0))(0,0)bits in
    String.make 1 (Char.chr n) ^ str s
let rec name = function
  | C.NameAnon -> "_"
  | C.NameStr(p,s) -> name p ^ "." ^ str s
  | C.NameNum(p,_) -> name p ^ ".#"
let rec level = function
  | C.LZero -> "0" | C.LSucc u -> "S(" ^ level u ^ ")"
  | C.LParam n -> name n | C.LMVar n -> "?" ^ name n
  | C.LMax(u,v) -> "max(" ^ level u ^ "," ^ level v ^ ")"
  | C.LIMax(u,v) -> "imax(" ^ level u ^ "," ^ level v ^ ")"
let rec expr = function
  | C.EBVar n -> "#" ^ string_of_int(native_nat n)
  | C.EFVar n -> "free:" ^ name n | C.EMVar n -> "meta:" ^ name n
  | C.ESort u -> "Sort " ^ level u
  | C.EConst(n,us) -> name n ^ "{" ^ String.concat "," (List.map level (native_list us)) ^ "}"
  | C.EApp(f,a) -> "(" ^ expr f ^ " " ^ expr a ^ ")"
  | C.ELam(_,_,a,e) -> "(lam " ^ expr a ^ " => " ^ expr e ^ ")"
  | C.EPi(_,_,a,e) -> "(Pi " ^ expr a ^ " => " ^ expr e ^ ")"
  | C.ELet(_,a,v,e,_) -> "(let " ^ expr a ^ ":=" ^ expr v ^ ";" ^ expr e ^ ")"
  | C.EProj(n,i,a) -> "proj " ^ name n ^ "." ^ string_of_int(native_nat i) ^ " " ^ expr a
  | C.ELit _ -> "literal" | C.EMData e -> expr e
let debug fuel env types ctors recs =
  let specs=get "gather specs" (C.gather_specs types ctors) in
  let first=List.hd(native_list types) in
  let info=match first.C.decl_kind_of with C.DInductive d->d | _->failwith "not inductive" in
  let ps=first.C.decl_params in
  let C.Pair(C.Pair(params,_),s)=get "parameters" (C.open_parameters info.C.ind_num_params fuel env ps C.initial_ind_state first.C.decl_type) in
  let C.Pair(checked,s)=get "types" (C.check_inductive_types specs fuel env ps params C.None s) in
  let head=List.hd(native_list checked) in
  let stats={C.stats_params=params;stats_types=checked;stats_names=C.ind_names types;
             stats_levels=C.map(fun n->C.LParam n) ps;stats_result=head.C.checked_level;
             stats_unsafe=info.C.ind_is_unsafe;stats_state=s} in
  let inds=C.map (C.derived_inductive stats) checked in
  let ind_env=C.app inds env in
  let C.Pair(constructors,s)=get "constructors" (C.check_all_ctors checked fuel ind_env ps stats s) in
  let ctor_env=C.app constructors ind_env in
  let large=get "large elim" (C.large_elimination fuel ctor_env ps stats s) in
  let k=get "K target" (C.k_target fuel stats) in
  let fresh=get "fresh level" (C.fresh_elim_name (C.S(C.length ps)) C.O ps) in
  let elim=if b large then C.LParam fresh else C.LZero in
  let rec_ps=if b large then C.Cons(fresh,ps) else ps in
  let C.Pair(motives,s)=C.build_motives checked stats elim s in
  let C.Pair(minors,_)=get "minors" (C.build_all_minors checked C.O fuel ctor_env rec_ps stats motives s) in
  let generated=get "recursors" (C.build_recursors motives C.O stats rec_ps motives minors k) in
  List.iter(fun d ->
    let source=match C.find_decl d.C.decl_name recs with C.Some x->x | _->failwith "missing recursor" in
    let expected=C.subst_levels source.C.decl_params (C.map(fun n->C.LParam n)d.C.decl_params)source.C.decl_type in
    Printf.printf "source type: %s\nactual type: %s\n%!" (expr expected)(expr d.C.decl_type);
    ignore(get "recursor compare"(C.verify_rec_metadata source d))) (native_list generated)
let () =
  let export=Wire.read_file Sys.argv.(1) in
  let fuel=A.nat 512 and st=A.create() and env=ref C.Nil in
  List.iter(fun batch->
    let line=Replay.line batch in
    let result=match batch with
      | Replay.Single(_,d)->A.admit fuel !env st d
      | Replay.Mutual(_,ds)->A.mutual fuel !env st ds in
    match result with
    | C.Accept e -> env:=e
    | C.Reject why ->
      Printf.printf "At line %d: %s\n%!" line (A.reject_reason why);
      (match batch with Replay.Single(_,Wire.Inductive(ts,cs,rs))->debug fuel !env (A.list(A.inductive st)ts)
         (A.list(A.constructor st)cs)(A.list(A.recursor st)rs) | _->()); exit 1
    | C.Decline why -> failwith(A.decline_reason why))(Replay.schedule export.declarations)
