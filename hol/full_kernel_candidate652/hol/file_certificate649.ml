(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   SOURCE ONLY / UNCOMPILED. Held API; loading does not invoke a proof-file check.
   Requires the genuine Wire/Replay host modules and guarded input ownership. *)
needs "hol/file_quotation643.ml";;
needs "hol/kernel_compute646.ml";;
needs "hol/kernel_equations647.ml";;
needs "hol/file_verdict649.ml";;

unset_jrh_lexer;;

module File_certificate649 : sig
  type t
  type verdict = Accepted | Rejected | Declined
  type certificate = private {
    verdict : verdict;
    theorem : thm;
    query : term;
    fuel : term;
    input : term;
    schedule : term;
    row_count : int;
    batch_count : int
  }
  type inconclusive = private { query : term; diagnostic : string }
  type outcome = Certified of certificate | Inconclusive of inconclusive
  exception Invalid_certificate of string
  val create : unit -> t
  val check_channel : t -> Z.t -> in_channel -> outcome
  val check_file : t -> Z.t -> string -> outcome
end = struct
  type t = Kernel_compute646.t
  type verdict = Accepted | Rejected | Declined
  type certificate = {
    verdict : verdict;
    theorem : thm;
    query : term;
    fuel : term;
    input : term;
    schedule : term;
    row_count : int;
    batch_count : int
  }
  type inconclusive = { query : term; diagnostic : string }
  type outcome = Certified of certificate | Inconclusive of inconclusive
  exception Invalid_certificate of string

  let create () = Kernel_compute646.create
    ~conversions:l4_kernel_conversions647
    (l4_file_verdict649 :: l4_kernel_equations647)

  let check_prepared state fuel (prepared:File_quotation643.prepared_file) =
    let query = Full_input610.node "l4_file_verdict649"
      [fuel;prepared.raw_file_term;prepared.schedule_term] in
    try
      let literal,theorem = Kernel_compute646.numeral state query in
      (* This check is repeated at the public certificate boundary so a future
         evaluator change cannot silently certify a different proposition. *)
      if hyp theorem <> [] || frees (concl theorem) <> [] ||
         not (is_eq (concl theorem)) then
        raise (Invalid_certificate "non-closed computation evidence");
      let left,right = dest_eq (concl theorem) in
      if not (aconv left query) || not (aconv right literal) then
        raise (Invalid_certificate "query/result evidence mismatch");
      let verdict =
        if aconv literal (mk_small_numeral 0) then Accepted
        else if aconv literal (mk_small_numeral 1) then Rejected
        else if aconv literal (mk_small_numeral 2) then Declined
        else raise (Invalid_certificate "unknown result code") in
      Certified {verdict;theorem;query;fuel;input=prepared.raw_file_term;
        schedule=prepared.schedule_term;row_count=prepared.row_count;
        batch_count=prepared.batch_count}
    with Kernel_compute646.Undecided diagnostic -> Inconclusive {query;diagnostic}

  let check_channel state fuel ic =
    let fuel = Full_input610.natural fuel in
    check_prepared state fuel (File_quotation643.read_channel ic)

  let check_file state fuel path =
    let fuel = Full_input610.natural fuel in
    check_prepared state fuel (File_quotation643.read_file path)
end;;

set_jrh_lexer;;
