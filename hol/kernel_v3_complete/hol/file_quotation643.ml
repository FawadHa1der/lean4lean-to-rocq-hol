(* SPDX-License-Identifier: Apache-2.0. Copyright 2026 Fawad Haider.
   Changed full447 file-quotation adapter over genuine Wire/Replay and610.
   SOURCE ONLY / UNCOMPILED / UNEXECUTED. See ../API643.txt and ../NOTICE643.txt.
   Term construction and source-row binding only; no logical evaluation. *)
needs "hol/full_input610.ml";;
needs "hol/file_driver642.ml";;
needs "hol/source_decoder641.ml";;

unset_jrh_lexer;;

module File_quotation643 = struct
  module Q = Full_input610
  exception Invalid_binding of string

  type batch_binding = {
    replay_batch : Replay.batch;
    leader_index : int;
    member_indices : int list;
    source_lines : int list
  }
  type prepared_file = {
    raw_file_term : term;
    schedule_term : term;
    raw_rows : (int * term) list;
    metadata : Wire.metadata;
    name_count : int;
    level_count : int;
    expr_count : int;
    row_count : int;
    batch_count : int;
    source_lines : int list;
    batches : batch_binding list
  }

  let natural_int n = Q.natural (Z.of_int n)
  let safety = function
    | Wire.Safe -> Q.node "L4InputSafe607" []
    | Wire.Partial -> Q.node "L4InputPartial607" []
    | Wire.Unsafe -> Q.node "L4InputUnsafe607" []
  let ordinary input all = Q.node "L4FileOrdinary642" [input;all]
  let raw_declaration = function
    | Q.Axiom (h,unsafe) -> ordinary
        (Q.node "L4InputAxiom607" [h.qname;h.qparams;h.qtype;Q.bool unsafe]) (Q.names [])
    | Q.Definition d -> ordinary
        (Q.node "L4InputDefinition607" [d.qhints;d.qheader.qname;d.qheader.qparams;
          d.qheader.qtype;d.qvalue;safety d.qsafety]) d.qall
    | Q.Theorem (h,value,all) -> ordinary
        (Q.node "L4InputTheorem607" [h.qname;h.qparams;h.qtype;value]) all
    | Q.Opaque (h,value,unsafe,all) -> ordinary
        (Q.node "L4InputOpaque607" [h.qname;h.qparams;h.qtype;value;Q.bool unsafe]) all
    | Q.Quotient (h,kind) ->
        Q.node "L4FileQuotient642" [h.qname;h.qparams;h.qtype;kind]
    | Q.Inductive (types,ctors,recs) -> Q.node "L4FileInductive642"
        [Q.list "l4_kdeclaration493" types;Q.list "l4_kdeclaration493" ctors;
         Q.list "l4_kdeclaration493" recs]

  let bind_schedule input batches =
    let rows = Array.of_list input in
    let by_line = Hashtbl.create (max 16 (Array.length rows)) in
    let definitions = Replay.Names.create (max 16 (Array.length rows)) in
    let previous_line = ref 0 in
    let invalid line message = raise (Invalid_binding
      ("source line " ^ string_of_int line ^ ": " ^ message)) in
    Array.iteri (fun i (line,decl) ->
      if line <= !previous_line then invalid line "source lines must be positive and strictly increasing";
      previous_line := line;
      Hashtbl.add by_line line i;
      match decl with
      | Wire.Definition d ->
          if Replay.Names.mem definitions d.header.name then
            invalid line "duplicate source definition name";
          Replay.Names.add definitions d.header.name (i,d)
      | _ -> ()) rows;
    let source_index line = match Hashtbl.find_opt by_line line with
      | Some i -> i
      | None -> invalid line "batch leader is not an original source row" in
    let consumed = Array.make (Array.length rows) false in
    let claim i =
      if consumed.(i) then invalid (fst rows.(i)) "source row repeated by schedule";
      consumed.(i) <- true in
    let bound = List.map (fun batch ->
      let line = Replay.line batch in
      let leader = source_index line in
      let members = match batch with
        | Replay.Single (_,decl) ->
            if not (snd rows.(leader) == decl) then
              invalid line "single declaration is not the original source object";
            [leader]
        | Replay.Mutual (_,ds) ->
            let members = List.map (fun (d:Wire.definition) ->
              match Replay.Names.find_opt definitions d.header.name with
              | Some (i,original) when original == d -> i
              | Some _ -> invalid line "mutual member was replaced despite matching name"
              | None -> invalid line "mutual member has no source definition") ds in
            if not (List.mem leader members) then
              invalid line "mutual leader is absent from its members";
            members in
      List.iter claim members;
      {replay_batch=batch;leader_index=leader;member_indices=members;
       source_lines=List.map (fun i -> fst rows.(i)) members}) batches in
    Array.iteri (fun i seen ->
      if not seen then invalid (fst rows.(i)) "source row omitted by schedule") consumed;
    bound

  let batch_term (b:batch_binding) = match b.replay_batch with
    | Replay.Single _ -> Q.node "L4FileSingle642" [natural_int b.leader_index]
    | Replay.Mutual _ -> Q.node "L4FileMutual642"
        [natural_int b.leader_index;Q.list "num" (List.map natural_int b.member_indices)]

  (* Quote original rows before using Replay's schedule. The schedule contains
     only bound indices; it never replaces or repairs the original payloads. *)
  let prepare_export (input:Wire.export) =
    let quoted = Q.export input in
    let schedule = Replay.schedule input.declarations in
    let batches = bind_schedule input.declarations schedule in
    let raw_rows = List.map (fun (line,d) -> line,raw_declaration d) quoted.qdeclarations in
    let rows = Q.list "num # l4_file_decl642"
      (List.map (fun (line,d) -> mk_pair (natural_int line,d)) raw_rows) in
    let metadata = quoted.qmetadata in
    let raw_file_term = Q.node "L4FileInput642"
      [Q.bytes metadata.format_version;Q.bytes metadata.lean_version;Q.bytes metadata.lean_hash;
       natural_int quoted.qname_count;natural_int quoted.qlevel_count;
       natural_int quoted.qexpr_count;rows] in
    {raw_file_term;schedule_term=Q.list "l4_file_batch642" (List.map batch_term batches);
     raw_rows;metadata;name_count=quoted.qname_count;level_count=quoted.qlevel_count;
     expr_count=quoted.qexpr_count;row_count=List.length raw_rows;
     batch_count=List.length batches;source_lines=List.map fst raw_rows;batches}

  let read_channel ic = prepare_export (Source_decoder641.read_channel ic)
  let read_file path = prepare_export (Source_decoder641.read_file path)
end;;

set_jrh_lexer;;
