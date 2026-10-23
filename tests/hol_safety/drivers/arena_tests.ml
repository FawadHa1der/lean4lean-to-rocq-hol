let safety_arena_assertions=ref 0;;
let safety_arena_test label ok =
  incr safety_arena_assertions;
  Printf.printf "SAFETY_ARENA_ASSERT %d %b %s\n%!" !safety_arena_assertions ok label;
  if not ok then failwith("SAFETY ARENA FAILURE "^label);;
List.iter(fun id->
  let path="arena/corpus/tutorial/"^id^".ndjson" in
  let outcome=Hol_safety_check.check_file path in
  safety_arena_test "reject forbidden theorem" (outcome.Hol_safety_check.code=1);
  safety_arena_test "prefix admitted before forbidden theorem"
    (outcome.Hol_safety_check.line=22 && outcome.Hol_safety_check.checked=2);
  let prefix=match outcome.Hol_safety_check.prefix with Some p->p|None->failwith "missing accepted prefix" in
  let proof=Lean4hol_safety.certificate prefix in
  safety_arena_test "prefix exact and closed" (hyp proof=[] && aconv(concl proof)(Lean4hol_safety.expected prefix));
  let forbidden=match outcome.Hol_safety_check.forbidden with Some h->h|None->failwith "missing forbidden-reference proof" in
  safety_arena_test "forbidden reference theorem closed" (hyp forbidden=[] && is_neg(concl forbidden));
  let restricted=List.filter(fun r->r.Lean4hol_safety.safety<>Lean4hol_safety.Safe)
    (Lean4hol_safety.registry prefix) in
  safety_arena_test "actual restricted declaration retained" (List.length restricted=1);
  let raw=List.hd restricted in
  safety_arena_test "loop body retained" (raw.Lean4hol_safety.entry.Lean4hol_env.value=
    Some(Lean4hol.Const(raw.Lean4hol_safety.entry.Lean4hol_env.name,[])));
  safety_arena_test "no unsafe logical grant"
    (Lean4hol_env.permissions(Lean4hol_safety.safe_environment prefix)=[]);
  safety_arena_test "no blanket tag rejection" (List.length(Lean4hol_safety.registry prefix)=3);
  Printf.printf "SAFETY_ARENA_REJECT %s prefix_checked=2 line=22 exact_closed forbidden_closed retained_loop\n%!" id)
  ["140_falseFromUnsafe";"141_falseFromPartial"];;
safety_arena_test "unchanged axioms" (axioms()=private_axioms);;
Printf.printf "SAFETY_ARENA_PASSED %d unchanged_axioms\n%!" !safety_arena_assertions;;
