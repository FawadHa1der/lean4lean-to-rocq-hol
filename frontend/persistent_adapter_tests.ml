(* Transport integration tests. Expected results never enter the checker. *)
module C = Lean_arena
module W = Wire
module A = Rocq_adapter
module D = Dag_adapter
module S = Persistent_adapter.State
let tests=ref 0 and accepts=ref 0 and rejects=ref 0 and declines=ref 0
let eq label a b = incr tests; if a<>b then failwith label
let get label = function C.Accept x -> x | _ -> failwith label
let n s=W.Str(W.Anonymous,s)
let prop=W.Sort W.Zero
let con s=W.Const(n s,[])
let header s typ={W.name=n s;params=[];typ}
let ax s typ=W.Axiom(header s typ,false)
let def ?(safety=W.Safe) s typ value={W.header=header s typ;value;safety;hints=W.Abbrev;all=[n s]}
let project = function C.Accept s -> C.Accept(S.environment s)
  | C.Reject r -> C.Reject r | C.Decline r -> C.Decline r
let run fuel batches =
  let syntax=A.create() and state=ref S.initial in
  List.iter (fun batch ->
    let before=S.environment !state in
    let got,expected=match batch with
      | Replay.Single(_,d) -> S.admit fuel !state syntax d,D.admit fuel before syntax d
      | Replay.Mutual(_,ds) -> S.mutual fuel !state syntax ds,A.mutual fuel before syntax ds in
    eq "full adapter result matches old adapter" (project got) expected;
    match got with
    | C.Accept next -> incr accepts; state:=next
    | C.Reject _ -> incr rejects; eq "reject no caller commit" (S.environment !state) before
    | C.Decline _ -> incr declines; eq "decline no caller commit" (S.environment !state) before
  ) batches;
  !state
let raw ds=List.mapi(fun i d->Replay.Single(i+1,d)) ds
let padding=List.init 64(fun i->ax (Printf.sprintf "padding%d" i) prop)
let p=ax "P" prop and h=ax "h" (con "P")
let proof d=W.Theorem(header d (con "P"),con "h",[n d])
let () =
  let positives=padding@[p;h;W.Definition(def "d" (con "P") (con "h"));proof "t";
    W.Opaque(header "o" (con "P"),con "h",false,[n "o"])] in
  let s=run (A.nat 256) (raw positives) in
  eq "all positives truly accepted" !accepts (List.length positives);
  eq "all stored declarations" (List.length positives)
    (let rec len=function C.Nil->0|C.Cons(_,xs)->1+len xs in len(S.environment s));
  (* Forward input order exercises the same scheduler before either adapter. *)
  let scheduled=Replay.schedule (List.mapi(fun i d->i+1,d)
    (proof "forward" :: h :: p :: padding)) in
  let before= !accepts in
  ignore(run (A.nat 256) scheduled);
  eq "scheduled positives nonvacuous" (!accepts-before) (List.length positives-2);
  List.iter(fun fuel -> ignore(run (A.nat fuel) (raw(positives@[
    p;ax "malformed" (W.BVar Z.zero);ax "unknown" (con "missing");
    W.Axiom(header "restricted" prop,true);
    ax "forbidden" (con "restricted");proof "post-error-positive"])))) [0;1;2;16];
  List.iter(fun safety ->
    let u=def ~safety "u" prop (con "v") in
    let v=def ~safety "v" prop (con "u") in
    let before= !accepts in
    ignore(run (A.nat 256) (raw padding @ [Replay.Mutual(100,[u;v]);
      Replay.Single(101,ax "unsafe-use" (con "u"));
      Replay.Single(102,ax "after-mutual-reject" prop)]));
    eq "mutual and post reject accepted" (!accepts-before) 66
  ) [W.Unsafe;W.Partial];
  if !rejects=0 || !declines=0 then failwith "missing error controls";
  Printf.printf "adapter_assertions=%d accepted_batches=%d rejected_batches=%d declined_batches=%d\n%!"
    !tests !accepts !rejects !declines
