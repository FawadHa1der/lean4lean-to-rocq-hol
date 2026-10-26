(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   PROPOSED ONLY: UNCOMPILED / UNRUN. Requires a separately authorized runtime.
   Loading this source does not call l4_proposed_cases648 or run its cases.
   Call the builder at most once in a fresh disposable guarded HOL session.
   These small test definitions are NOT production checker replacements. *)
needs "hol/kernel_compute646.ml";;
needs "lists.ml";;

let l4_proposed_cases648 () =
  let first = new_recursive_definition num_RECURSION
    `(fixture_first648 0 a b = a) /\
     (fixture_first648 (SUC n) a b = SUC(fixture_first648 n a b))` in
  let middle = new_recursive_definition num_RECURSION
    `(fixture_middle648 a 0 b = a) /\
     (fixture_middle648 a (SUC n) b = SUC(fixture_middle648 a n b))` in
  let last = new_recursive_definition num_RECURSION
    `(fixture_last648 a b 0 = b) /\
     (fixture_last648 a b (SUC n) = SUC(fixture_last648 a b n))` in
  let pick = new_recursive_definition num_RECURSION
    `(fixture_pick648 0 (f:A->B) = f) /\
     (fixture_pick648 (SUC n) f = fixture_pick648 n f)` in
  let both_def = new_definition
    `fixture_both648 m n = PRE m + PRE n` in
  let both = prove
    (`fixture_both648 (SUC m) (SUC n) = m + n`,
     REWRITE_TAC[both_def; PRE]) in
  let positive_def = new_definition `fixture_positive648 (n:num) = T` in
  let positive = prove (`!n. fixture_positive648 n`,
    REWRITE_TAC[positive_def]) in
  let negative_def = new_definition `fixture_negative648 (n:num) = F` in
  let negative = prove (`!n. ~fixture_negative648 n`,
    REWRITE_TAC[negative_def]) in
  let stuck_def = new_definition `fixture_stuck648 = 9` in
  let stuck_bool_def = new_definition `fixture_stuck_bool648 = T` in
  let assert648 label condition = if not condition then failwith label in
  let failure648 label f =
    let refused = try ignore(f()); false with Failure _ -> true in
    assert648 label refused in
  let invalid648 label f =
    let refused = try ignore(f()); false
      with Kernel_compute646.Invalid_equations _ -> true in
    assert648 label refused in
  let undecided648 label f =
    let refused = try ignore(f()); false
      with Kernel_compute646.Undecided _ -> true in
    assert648 label refused in
  let evidence648 query result th =
    assert648 "hypotheses" (hyp th = []);
    assert648 "closed conclusion" (frees(concl th) = []);
    let left,right = dest_eq(concl th) in
    assert648 "original lhs" (aconv left query);
    assert648 "expected rhs" (aconv right result) in
  let step648 eqs query expected =
    evidence648 query expected (Kernel_compute646.numeral_step eqs query) in
  let number648 eqs query expected =
    let result,th = Kernel_compute646.numeral (Kernel_compute646.create eqs) query in
    evidence648 query expected th;
    assert648 "returned numeral" (aconv result expected) in
  let boolean648 eqs query expected =
    let result,th = Kernel_compute646.boolean (Kernel_compute646.create eqs) query in
    evidence648 query (if expected then `T` else `F`) th;
    assert648 "returned boolean" (result = expected) in
  [
    "01-first-position", (fun () -> step648 [first]
      `fixture_first648 2 5 7` `SUC(fixture_first648 1 5 7)`);
    "02-middle-position", (fun () -> step648 [middle]
      `fixture_middle648 7 2 9` `SUC(fixture_middle648 7 1 9)`);
    "03-last-position", (fun () -> step648 [last]
      `fixture_last648 5 7 2` `SUC(fixture_last648 5 7 1)`);
    "04-three-full-recursions", (fun () ->
      number648 [first] `fixture_first648 2 5 7` `7`;
      number648 [middle] `fixture_middle648 7 2 9` `9`;
      number648 [last] `fixture_last648 5 7 2` `9`);
    "05-zero-is-not-successor", (fun () -> failure648 "zero bridge" (fun () ->
      Kernel_compute646.numeral_step [first] `fixture_first648 0 5 7`));
    "06-zero-base-and-one", (fun () ->
      number648 [first] `fixture_first648 0 5 7` `5`;
      number648 [first] `fixture_first648 1 5 7` `6`);
    "07-polymorphic-instance", (fun () -> step648 [pick]
      `fixture_pick648 2 (\x:bool. x)` `fixture_pick648 1 (\x:bool. x)`);
    "08-overapplication-compute-prefix", (fun () -> number648 [pick]
      `fixture_pick648 2 (\x:num. x) 7` `7`);
    "09-overapplication-direct-refusal", (fun () -> failure648 "overapplication"
      (fun () -> Kernel_compute646.numeral_step [pick]
        `fixture_pick648 2 (\x:num. x) 7`));
    "10-partial-arity-refusal", (fun () -> failure648 "partial arity" (fun () ->
      Kernel_compute646.numeral_step [first] `fixture_first648 2 5`));
    "11-wrong-head-refusal", (fun () -> failure648 "wrong head" (fun () ->
      Kernel_compute646.numeral_step [first] `fixture_middle648 7 2 9`));
    "12-nonnumeral-refusal", (fun () -> failure648 "nonnumeral" (fun () ->
      Kernel_compute646.numeral_step [first] `fixture_first648 n 5 7`));
    "13-multiple-successor-positions", (fun () -> step648 [both]
      `fixture_both648 2 3` `1 + 2`);
    "14-shared-pattern-variable-refusal", (fun () ->
      let same = INST [`m:num`,`n:num`] both in
      failure648 "different predecessors" (fun () ->
        Kernel_compute646.numeral_step [same] `fixture_both648 2 3`));
    "15-nested-successor-unsupported", (fun () ->
      let nested = INST [`SUC n`,`n:num`] (SPEC_ALL(CONJUNCT2 first)) in
      failure648 "nested successor" (fun () ->
        Kernel_compute646.numeral_step [nested] `fixture_first648 2 5 7`));
    "16-interleaved-forall-conjunction", (fun () ->
      let clauses = GEN `z:num` (CONJ first (GEN `w:num` middle)) in
      number648 [clauses] `fixture_middle648 7 2 9` `9`);
    "17-hypothesis-refusal", (fun () -> invalid648 "assumed clause" (fun () ->
      Kernel_compute646.create [ADD_ASSUM `T` first]));
    "18-rhs-only-variable-refusal", (fun () -> invalid648 "rhs-only variable"
      (fun () -> Kernel_compute646.create [SYM(EQT_INTRO(REFL `x:num`))]));
    "19-variable-head-refusal", (fun () -> invalid648 "variable head"
      (fun () -> Kernel_compute646.create [REFL `x:num`]));
    "20-expansion-only-is-not-progress", (fun () ->
      failure648 "reflexive successor clause" (fun () ->
        Kernel_compute646.numeral_step
          [REFL `fixture_first648 (SUC n) a b`] `fixture_first648 2 5 7`));
    "21-missing-base-is-undecided", (fun () -> undecided648 "missing base"
      (fun () -> Kernel_compute646.numeral
        (Kernel_compute646.create [CONJUNCT2 first]) `fixture_first648 1 5 7`));
    "22-stuck-closed-numeric-refusal", (fun () -> undecided648 "stuck numeric"
      (fun () -> Kernel_compute646.numeral (Kernel_compute646.create [])
        `fixture_stuck648`));
    "23-stuck-closed-boolean-refusal", (fun () -> undecided648 "stuck boolean"
      (fun () -> Kernel_compute646.boolean (Kernel_compute646.create [])
        `fixture_stuck_bool648`));
    "24-open-query-refusal", (fun () -> undecided648 "open query"
      (fun () -> Kernel_compute646.numeral (Kernel_compute646.create [first])
        `fixture_first648 n 5 7`));
    "25-wrong-result-type-refusal", (fun () -> undecided648 "wrong type"
      (fun () -> Kernel_compute646.boolean (Kernel_compute646.create []) `3`));
    "26-literal-reflexivity-is-valid", (fun () ->
      number648 [] `3` `3`; boolean648 [] `T` true; boolean648 [] `F` false);
    "27-proved-predicate-and-negation", (fun () ->
      boolean648 [positive] `fixture_positive648 2` true;
      boolean648 [negative] `fixture_negative648 2` false);
    "28-list-empty-and-cons", (fun () ->
      number648 [LENGTH] `LENGTH ([]:num list)` `0`;
      number648 [LENGTH] `LENGTH [2;3;5]` `3`);
    "29-cond-both-directions", (fun () ->
      number648 [] `(if T then 7 else fixture_stuck648)` `7`;
      number648 [] `(if F then fixture_stuck648 else 7)` `7`);
    "30-cond-stuck-guard", (fun () -> undecided648 "stuck guard"
      (fun () -> Kernel_compute646.numeral (Kernel_compute646.create [])
        `(if fixture_stuck_bool648 then 7 else 8)`));
    "31-stock-cond-unselected-branch-not-visited", (fun () ->
      let visits = ref 0 in
      let cs = Compute.bool_compset () in
      Compute.set_skip cs `COND:bool->A->A->A` (Some 1);
      Compute.add_conv (`fixture_stuck648`,0,
        (fun _ -> incr visits; failwith "unselected branch visited")) cs;
      let query = `(if T then 7 else fixture_stuck648)` in
      evidence648 query `7` (Compute.WEAK_CBV_CONV cs query);
      assert648 "unselected branch conversion ran" (!visits = 0));
    "32-genuine-attached-rewrite", (fun () ->
      let query = `fixture_stuck648` in
      let cs = Kernel_compute646.create
        ~conversions:[query,0,REWR_CONV stuck_def] [] in
      let result,th = Kernel_compute646.numeral cs query in
      evidence648 query `9` th;
      assert648 "attached result" (aconv result `9`));
    "33-attached-reflexivity-refused", (fun () ->
      let cs = Kernel_compute646.create
        ~conversions:[`fixture_stuck648`,0,REFL] [] in
      undecided648 "attached reflexivity" (fun () ->
        Kernel_compute646.numeral cs `fixture_stuck648`));
    "34-attached-wrong-lhs-refused", (fun () ->
      let cs = Kernel_compute646.create ~conversions:
        [`fixture_stuck648`,0,(fun _ -> NUM_ADD_CONV `1 + 1`)] [] in
      undecided648 "attached wrong lhs" (fun () ->
        Kernel_compute646.numeral cs `fixture_stuck648`));
    "35-attached-hypothesis-refused", (fun () ->
      let cs = Kernel_compute646.create ~conversions:
        [`fixture_stuck648`,0,(fun tm -> ADD_ASSUM `T`
          (REWR_CONV stuck_def tm))] [] in
      undecided648 "attached hypothesis" (fun () ->
        Kernel_compute646.numeral cs `fixture_stuck648`));
    "36-attached-proposition-refused", (fun () ->
      let cs = Kernel_compute646.create
        ~conversions:[`fixture_stuck648`,0,(fun _ -> TRUTH)] [] in
      undecided648 "attached proposition" (fun () ->
        Kernel_compute646.numeral cs `fixture_stuck648`));
    "37-attached-rhs-only-variable-refused", (fun () ->
      let cs = Kernel_compute646.create ~conversions:
        [`fixture_stuck_bool648`,0,(fun tm ->
          TRANS (REWR_CONV stuck_bool_def tm)
            (SYM(EQT_INTRO(REFL `x:num`))))] [] in
      undecided648 "attached rhs-only variable" (fun () ->
        Kernel_compute646.boolean cs `fixture_stuck_bool648`));
    "38-failed-attachment-allows-real-rule", (fun () ->
      let cs = Kernel_compute646.create
        ~conversions:[`fixture_stuck648`,0,REFL] [stuck_def] in
      let result,th = Kernel_compute646.numeral cs `fixture_stuck648` in
      evidence648 `fixture_stuck648` `9` th;
      assert648 "fallback result" (aconv result `9`));
    "39-invalid-attachment-registration", (fun () ->
      invalid648 "negative arity" (fun () -> Kernel_compute646.create
        ~conversions:[`fixture_stuck648`,-1,REFL] []);
      invalid648 "variable head" (fun () -> Kernel_compute646.create
        ~conversions:[`x:num`,0,REFL] []));
    "40-stock-swallows-attached-exception", (fun () ->
      let cs = Kernel_compute646.create
        ~conversions:[`fixture_stuck648`,0,(fun _ -> raise Exit)] [] in
      undecided648 "stock conversion catch-all" (fun () ->
        Kernel_compute646.numeral cs `fixture_stuck648`))
  ];;

(* Deliberately NO invocation, test runner, printed pass count or fixture registry
   for production. Inspect these sources before any separately authorized use. *)
