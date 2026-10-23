(* Pure OCaml tests of accounting only, not a replacement HOL kernel. *)
open Closed_budget.L4_closed_budget
type ty = V of string | T of string * ty list
type tm = A of string * ty | C of tm * tm
let equal_calls = ref 0
module B = Make(struct
  type term = tm
  type typ = ty
  let term_view = function A(s,t) -> Atom(s,t) | C(a,b) -> Branch(a,b)
  let type_view = function V s -> Type_var s | T(s,ts) -> Type_app(s,ts)
  let equal a b = incr equal_calls; a=b
end)
let checks = ref 0
let test name b = incr checks; if not b then failwith name
let unit_ty = T("num",[])
let atom s = A(s,unit_ty)
let rec tree n leaf = if n=0 then leaf else let x=tree(n-1)leaf in C(x,x)
let reference roots =
  let good = ref true in
  let d n = if n>limits.depth then good:=false in
  let s x = if String.length x>limits.label_bytes then good:=false;
            String.length x in
  let rec typ n = function
    | V x -> d n; 1+s x
    | T(x,xs) -> d n; 1+s x+types(n+1)xs
  and types n = function
    | [] -> d n; 1
    | x::xs -> d n; 1+typ(n+1)x+types(n+1)xs in
  let rec term n = function
    | A(x,t) -> d n; 1+s x+typ(n+1)t
    | C(a,b) -> d n; 1+term(n+1)a+term(n+1)b in
  let rec terms n = function
    | [] -> d n; 1
    | x::xs -> d n; 1+term(n+1)x+terms(n+1)xs in
  let w=terms 0 roots in
  if !good && w<=limits.entry_weight then Some w else None
let random = Random.State.make [|614;128;65536|]
let rand n = Random.State.int random n
let rec gen_ty n = if n=0 || rand 3=0 then V(String.make(rand 12)'t')
  else T(String.make(rand 20)'T',List.init(rand 4)(fun _->gen_ty(n-1)))
let rec gen_tm n = if n=0 || rand 3=0 then
  A(String.make(rand 30)'x',gen_ty 3)
  else C(gen_tm(n-1),gen_tm(n-1))
let invariant c =
  let st=B.stats c in
  test "entry count" (st.count>=0 && st.count<=limits.entries);
  test "retained weight" (st.weight>=0 && st.weight<=limits.total_weight)
let () =
  test "empty root-list weight" (B.measure []=Some 1);
  test "atom/type/list/label weight" (B.measure [atom "x"]=Some 9);
  test "label bound exact" (B.measure [atom(String.make 256 'x')]<>None);
  test "term-label bound" (B.measure [atom(String.make 257 'x')]=None);
  test "type-variable label bound" (B.measure [A("x",V(String.make 257 'a'))]=None);
  test "type-operator label bound" (B.measure [A("x",T(String.make 257 'a',[]))]=None);
  for _=1 to 5000 do
    let roots=List.init(rand 5)(fun _->gen_tm 5) in
    test "independent recursive reference" (B.measure roots=reference roots)
  done;
  let deep=ref(atom "x") and deep_ty=ref unit_ty in
  for _=1 to 250000 do deep:=C(!deep,atom "x"); deep_ty:=T("f",[!deep_ty]) done;
  test "250000-deep term bounded iteratively" (B.measure [!deep]=None);
  test "250000-deep type bounded iteratively" (B.measure [A("x",!deep_ty)]=None);
  test "large type argument list" (B.measure [A("x",T("f",List.init 100000(fun _->unit_ty)))]=None);
  test "large term root list" (B.measure (List.init 100000(fun _->atom "x"))=None);
  test "occurrence accounting shared tree" (B.measure [tree 14 (atom "x")]=None);
  let shared_ty=ref unit_ty in
  for _=1 to 16 do shared_ty:=T("f",[!shared_ty;!shared_ty]) done;
  test "occurrence accounting shared types" (B.measure [A("x",!shared_ty)]=None);
  let boundary=ref(atom "x") and last=ref true and crossings=ref 0 in
  for _=1 to 180 do
    boundary:=C(!boundary,atom "x");
    let actual=B.measure [!boundary] in
    test "exact term depth boundary" (actual=reference [!boundary]);
    if !last && actual=None then incr crossings;
    last:=actual<>None
  done;
  test "one term depth boundary" (!crossings=1);
  let boundary=ref unit_ty and last=ref true and crossings=ref 0 in
  for _=1 to 180 do
    boundary:=T("f",[!boundary]);
    let actual=B.measure [A("x",!boundary)] in
    test "exact type depth boundary" (actual=reference [A("x",!boundary)]);
    if !last && actual=None then incr crossings;
    last:=actual<>None
  done;
  test "one type depth boundary" (!crossings=1);
  let c=B.create(fun (terms:tm list)->terms) in
  test "positive insertion" (B.put c (atom "key") (Some [atom "proof"]));
  test "positive retrieval" (B.find c (atom "key")=Positive [atom "proof"]);
  test "negative insertion" (B.put c (atom "open") None);
  test "negative retrieval" (B.find c (atom "open")=Negative);
  let before= !equal_calls in
  test "oversized key put refused" (not(B.put c !deep None));
  test "oversized key get refused" (B.find c !deep=Missing);
  test "oversized theorem refused" (not(B.put c (atom "key") (Some [!deep])));
  test "no oversized equality" (!equal_calls=before);
  test "oversized replacement keeps existing proof"
    (B.find c (atom "key")=Positive [atom "proof"]);
  B.clear c;
  for i=1 to 1000 do
    test "bounded negative insertion" (B.put c (atom(string_of_int i)) None);
    invariant c
  done;
  test "FIFO maximum count" ((B.stats c).count=64);
  test "oldest negative evicted" (B.find c (atom "1")=Missing);
  test "newest negative retained" (B.find c (atom "1000")=Negative);
  B.clear c;
  for i=1 to 1000 do
    test "weighted positive insertion" (B.put c (atom(string_of_int i))
      (Some [tree 8 (atom "payload")]));
    invariant c
  done;
  test "total weight evicts before count bound" ((B.stats c).count<64);
  test "positive eviction recorded" ((B.stats c).evictions>0);
  (* Compare an independent FIFO accounting model over repeated keys, mixed
     proof/negative entries, and refused entries of varying sizes. *)
  B.clear c;
  let model=ref [] in
  let weight xs=List.fold_left(fun sum (_,_,n)->sum+n)0 xs in
  for _=1 to 12000 do
    let key=atom(string_of_int(rand 200)) in
    let value=if rand 3=0 then None else Some[tree(rand 11)(atom "p")] in
    let incoming=reference(key::(match value with None->[]|Some xs->xs)) in
    let expected=match incoming with
      | Some w when w+2<=limits.entry_weight ->
        model:=List.filter(fun(k,_,_)->k<>key)!model;
        while List.length !model>=limits.entries ||
              weight !model+w+2>limits.total_weight do model:=List.tl !model done;
        model:= !model@[key,value,w+2]; true
      | _ -> false in
    test "reference put result" (B.put c key value=expected);
    invariant c;
    test "reference count" ((B.stats c).count=List.length !model);
    test "reference weight" ((B.stats c).weight=weight !model);
    let sought=atom(string_of_int(rand 200)) in
    let expected=match List.find_opt(fun(k,_,_)->k=sought)!model with
      | None->Missing | Some(_,None,_)->Negative | Some(_,Some v,_)->Positive v in
    test "reference lookup" (B.find c sought=expected)
  done;
  B.clear c;
  let st=B.stats c in
  test "clear empties retention" (st.count=0 && st.weight=0);
  test "clear resets statistics" (st.hits=0 && st.misses=0 && st.refused=0 && st.evictions=0);
  test "clear removes both kinds" (B.find c (atom "key")=Missing && B.find c (atom "open")=Missing);
  Printf.printf "CLOSED_BUDGET_OFFLINE_PASS %d\n%!" !checks
