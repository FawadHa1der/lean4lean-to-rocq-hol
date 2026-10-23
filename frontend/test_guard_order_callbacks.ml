(* SPDX-License-Identifier: Apache-2.0
   Adapted from the parent's exact-head synthetic extraction controls.
   These controls are not logical proof-file verdicts. *)
module C = Guard_order_native
let assertions = ref 0
let check label value = incr assertions; if not value then failwith label
let rec nat = function 0 -> C.O | n -> C.S(nat(n-1))
let app a b = C.EApp(a,b)
let constant = C.EConst(C.NameAnon,C.Nil)
let variable = C.EBVar C.O
let unit_sort = C.ESort C.LZero
let succ = C.EConst(C.core_succ_name,C.Nil)
let active = app succ variable
let app_many head n =
  let term = ref head in
  for _ = 1 to n do term := app !term variable done;
  !term
let shared_from base depth =
  let term = ref base in
  for _ = 1 to depth do term := app !term !term done;
  !term
let shared = shared_from constant
let head term = C.nat_probe_head C.find_decl C.core_succ_name C.Nil (C.core_spine term C.Nil)
let pair left right eligible = C.pair_probe_guard (head left) (head right) eligible
let calls = ref 0
let observed truth _ = incr calls; truth
let methods mode =
  let unexpected () = incr calls; failwith "inactive guard called checker callback" in
  {C.method_mode=mode;
   infer_method=(fun _ _ -> unexpected ()); infer_type_method=(fun _ _ -> unexpected ());
   whnf_method=(fun _ _ -> unexpected ()); whnf_core_method=(fun _ _ _ -> unexpected ());
   defeq_method=(fun _ _ _ -> unexpected ()); eager_defeq_method=(fun _ _ _ -> unexpected ())}
let () =
  let inactive = [constant;variable;unit_sort;succ;
    C.EConst(C.core_succ_name,C.Cons(C.LZero,C.Nil));
    app (C.EConst(C.core_succ_name,C.Cons(C.LZero,C.Nil))) variable;
    C.ELam(C.NameAnon,C.BDefault,unit_sort,variable);
    C.EMData active;shared 50] @
    List.init 6 (app_many constant) @
    [app_many succ 2;app_many succ 3;app_many succ 5] @
    List.init 8 (fun i -> C.EBVar(nat i)) in
  List.iter(fun term -> check "inactive head" (head term=C.False)) inactive;
  check "conservative successor head" (head active=C.True);
  List.iter(fun left -> List.iter(fun right ->
    calls:=0;
    check "inactive pair refuses without callback"
      (pair left right (fun _ -> incr calls;failwith "unnecessary eligibility")=C.False);
    check "eligibility never called" (!calls=0)) inactive) inactive;
  List.iter(fun term -> List.iter(fun truth ->
    List.iter(fun(left,right) -> calls:=0;
      check "active pair retains eligibility result"
        (pair left right (observed truth)=truth);
      check "active eligibility called exactly once" (!calls=1))
      [term,active;active,term;active,active]) [C.True;C.False]) inactive;
  List.iter(fun mode -> List.iter(fun accessor ->
    let m = methods mode in
    List.iter(fun right ->
      calls:=0;
      let left = shared 50 in
      let result = if accessor then C.Accessor.core_true_shortcut C.find_decl m C.Nil C.empty_context left right
        else C.core_true_shortcut m C.Nil C.empty_context left right in
      check "nontrue RHS skips shared localness" (result=C.Accept C.False);
      check "nontrue RHS skips callbacks" (!calls=0)) [constant;variable;succ;unit_sort];
    List.iter(fun (base,unknown) ->
      calls:=0;
      let left=shared_from base 50 and right=unit_sort in
      let result = if accessor then C.Accessor.core_lazy_delta C.find_decl (nat 1) m (nat 16) C.Nil C.Nil C.empty_context left right
        else C.core_lazy_delta (nat 1) m (nat 16) C.Nil C.Nil C.empty_context left right in
      check "inactive actual lazy-loop retains validation or stuck result"
        (if unknown then result=C.Reject C.UnknownConstant else
          match result with C.Accept(C.ConversionStuck(a,b)) -> a==left && b==right | _ -> false);
      check "inactive actual loop skips callbacks" (!calls=0)) [constant,true;unit_sort,false]) [false;true])
    [C.NormalReduction;C.EagerReduction];
  Printf.printf "GUARD_ORDER_CALLBACKS_PASS assertions=%d inactive_shapes=%d shared_depth=50 modes=2 implementations=2\n%!"
    !assertions (List.length inactive)
