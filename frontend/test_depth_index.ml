module C = Depth_native
let rec nat n = if n = 0 then C.O else C.S (nat (n-1))
let rec pos n = if n = 1 then C.XH else if n land 1 = 0 then C.XO(pos(n/2)) else C.XI(pos(n/2))
let rec huge n = if n = 0 then C.XH else C.XO(huge(n-1))
let list xs = List.fold_right (fun x tail -> C.Cons(x,tail)) xs C.Nil
let pair a b = C.Pair(a,b)
let path depth last = list (List.init depth (fun i ->
  if i = depth-1 then last else pair (pos 1) C.None))
let tests = ref 0
let eq label actual expected = incr tests; if actual <> expected then failwith label
let value i = match i mod 5 with
  | 0 -> C.Accept(C.ESort C.LZero)
  | 1 -> C.Accept(C.EBVar(nat (i mod 11)))
  | 2 -> C.Reject C.TypeMismatch
  | 3 -> C.Decline C.OutOfFuel
  | _ -> C.Decline C.UnsupportedExpression

let contexts = Array.init 256 (fun i ->
  if i < 128 then path i (pair (pos 1) C.None) else
  let id = if i = 255 then huge 512 else pos (1+i mod 17) in
  let v = if i mod 3 = 0 then C.None else C.Some (if i = 254 then huge 512 else pos (1+i)) in
  path 32 (pair id v))
let query i = pair (pos (1+i mod 5)) contexts.(i mod Array.length contexts)

let cache_history () =
  let old = ref C.PositiveMap.empty and indexed = ref C.PositiveMap.empty in
  let rng = Random.State.make [|20260929;77|] in
  for i = 0 to 767 do
    let q = query i and v = value i in
    old := C.frozen_add q v !old; indexed := C.indexed_add q v !indexed;
    eq "newest exact payload" (C.indexed_find q !indexed) (C.Some v);
    for _ = 1 to 16 do
      let q = query (Random.State.int rng 1280) in
      eq "cache history" (C.indexed_find q !indexed) (C.frozen_find q !old)
    done;
    let absent = pair (huge 513) contexts.(i mod 256) in
    eq "absent node" (C.indexed_find absent !indexed) (C.frozen_find absent !old)
  done;
  let new_calls = ref 0 and old_calls = ref 0 in
  for i = 0 to 1279 do
    let q = query i in
    let new_eval _ = incr new_calls; value 1 and old_eval _ = incr old_calls; value 1 in
    let C.Pair(a,c) = C.indexed_memo new_eval !indexed q in
    let C.Pair(b,d) = C.frozen_memo old_eval !old q in
    eq "memo result" a b; eq "memo hit/miss count" !new_calls !old_calls;
    indexed := c; old := d
  done

let rows = list [pair (pos 1)(C.DSort C.LZero);pair(pos 2)(C.DSort(C.LSucc C.LZero));
  pair(pos 3)(C.DBVar C.O);pair(pos 4)(C.DMVar C.NameAnon);
  pair(pos 5)(C.DLam(C.NameAnon,C.BDefault,pos 4,pos 3));
  pair(pos 6)(C.DLam(C.NameAnon,C.BDefault,pos 1,pos 3));
  pair(pos 7)(C.DPi(C.NameAnon,C.BDefault,pos 1,pos 1));
  pair(pos 8)(C.DLet(C.NameAnon,pos 2,pos 1,pos 3,C.False))]
let arena = match C.arena_build C.empty_arena rows with C.Accept a -> a | _ -> failwith "arena"

let recursive_queries () =
  let envs = [C.Nil;list [{C.decl_hints = C.HintOpaque; decl_name =C.NameAnon;decl_params=C.Nil;decl_type=C.ESort C.LZero;
    decl_value=C.None;decl_kind_of=C.DUnsafe C.DAssumption}]] in
  let binding = {C.binding_type=C.ESort C.LZero;binding_value=C.None} in
  let bases = [C.empty_context;{C.bound_context=list [binding];C.free_context=C.Nil}] in
  let paths = [C.Nil;path 1 (pair(pos 1) C.None);path 1 (pair(pos 2) C.None);
    path 1 (pair(pos 1)(C.Some(pos 1)));path 1 (pair(pos 1)(C.Some(pos 2)));
    path 2 (pair(pos 99) C.None)] in
  List.iter (fun env -> List.iter (fun base -> List.iter (fun ps -> List.iter (fun fuel ->
    let rec0 = C.checker (nat fuel) env ps in
    let nc = ref C.indexed_empty and oc = ref C.frozen_empty in
    List.iter (fun budget -> List.iter (fun mode -> List.iter (fun path ->
      for id = 1 to 9 do
        let q = pair(pos id) path in
        let C.Pair(a,an) = C.indexed_state_query rec0 (nat fuel) env ps base arena
          (nat budget) mode q !nc in
        let C.Pair(b,bn) = C.frozen_state_query rec0 (nat fuel) env ps base arena
          (nat budget) mode q !oc in
        eq "recursive mode/context/budget result" a b; nc:=an;oc:=bn
      done) paths) [C.True;C.False]) [32;0;1]) [0;1;8]) [C.Nil;list [C.NameAnon]]) bases) envs

let admissions () =
  let pairs = [C.indexed_definition C.HintOpaque,C.frozen_definition C.HintOpaque;
    C.indexed_theorem,C.frozen_theorem;C.indexed_opaque,C.frozen_opaque] in
  List.iter (fun (a,b) -> List.iter (fun fuel -> List.iter (fun budget ->
    List.iter (fun ps -> for tr = 1 to 9 do for br = 1 to 9 do
      eq "linear-cache/new-Checker admission"
        (a (nat budget)(nat fuel) C.Nil C.NameAnon ps rows (pos tr)(pos br))
        (b (nat budget)(nat fuel) C.Nil C.NameAnon ps rows (pos tr)(pos br))
    done done) [C.Nil;list[C.NameAnon;C.NameAnon]]) [0;1;32]) [0;1;8]) pairs

let () = cache_history (); recursive_queries (); admissions ();
  Printf.printf "%d exact depth/linear-cache comparisons under new Checker passed\n" !tests
