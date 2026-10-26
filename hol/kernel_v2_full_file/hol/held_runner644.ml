(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   HELD / UNCOMPILED. No fixture is evaluated when this source is loaded.
   Caller supplies sealed Kernel_compute646.t created with the canonical
   l4_kernel_equations647 plus l4_fixture_equations644, NEVER expectations.
   See COMPUTATION for source-only bridge/registry limits.
   This adapter does not install an evaluator, accept a verdict callback,
   establish runtime permission, read files or manufacture a theorem. *)
needs "hol/closed_goals644.ml";;
needs "hol/kernel_compute646.ml";;

let l4_fixture_eval644 state query =
  if frees query <> [] || type_of query <> `:num` then
    failwith "fixture644: query is not closed num";
  let head,args = strip_comb query in
  if head <> `l4_fixture_result_tag644` || List.length args <> 1 then
    failwith "fixture644: not an actual-result-tag query";
  let literal,th = Kernel_compute646.numeral state query in
  if hyp th <> [] || frees (concl th) <> [] || not (is_eq (concl th)) then
    failwith "fixture644: nonclosed or nonequational conversion theorem";
  let left,right = dest_eq (concl th) in
  if left <> query then failwith "fixture644: changed query";
  if literal <> right then failwith "fixture644: literal differs from theorem";
  if not (List.mem right [`0`;`1`;`2`]) then
    failwith "fixture644: unresolved result (not a rejection or acceptance)";
  th;;

(* The optional comparison is diagnostic only. The returned theorem is the
   actual computation equality, even when it disagrees with the expectation. *)
let l4_fixture_check644 state name =
  let _,query,expected =
    List.find (fun (label,_,_) -> label = name) l4_fixture_cases644 in
  let th = l4_fixture_eval644 state query in
  let comparison = match expected with
    | None -> None
    | Some literal -> Some (rhs (concl th) = literal) in
  th,comparison;;

let l4_fixture_prove644 state name =
  let th,comparison = l4_fixture_check644 state name in
  match comparison with
  | Some true -> th
  | Some false -> failwith ("fixture644: expectation mismatch: " ^ name)
  | None -> failwith ("fixture644: no proposed expectation: " ^ name);;

(* Thirteen held proof entrypoints. Each returns its exact closed catalogue
   equality only after stock computation; none has an acceptance premise. *)
let prove_empty644 cs = l4_fixture_prove644 cs "empty";;
let prove_identity644 cs = l4_fixture_prove644 cs "identity";;
let prove_invalid_body644 cs = l4_fixture_prove644 cs "invalid_body_type";;
let prove_duplicate_headers644 cs = l4_fixture_prove644 cs "duplicate_headers";;
let prove_schedule_dropped644 cs = l4_fixture_prove644 cs "schedule_dropped";;
let prove_schedule_duplicate644 cs = l4_fixture_prove644 cs "schedule_duplicate";;
let prove_schedule_out_of_range644 cs = l4_fixture_prove644 cs "schedule_out_of_range";;
let prove_forged_inductive644 cs = l4_fixture_prove644 cs "forged_inductive_metadata";;
let prove_unsafe_to_safe644 cs = l4_fixture_prove644 cs "unsafe_available_to_safe_theorem";;
let prove_bool644 cs = l4_fixture_prove644 cs "complete_bool_block";;
let prove_nat644 cs = l4_fixture_prove644 cs "complete_nat_block";;
let prove_bad_format644 cs = l4_fixture_prove644 cs "bad_format";;
let prove_identity_zero_fuel644 cs = l4_fixture_prove644 cs "identity_zero_fuel";;
