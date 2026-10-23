(* Copyright (c) 2026 Fawad Haider. All rights reserved. *)

module Hol_server = struct
  exception Timeout
  exception Disconnected
  exception Shutdown

  (* Same primitive as Unix._exit; HOL's lexer misclassifies leading underscores. *)
  external child_exit : int -> 'a = "unix_exit"

  let stopping = ref false
  let expired = ref false
  let active_child = ref None
  let max_frame = 32768
  let close fd = try Unix.close fd with Unix.Unix_error _ -> ()

  let bounded_message message =
    let n = min 4096 (String.length message) in
    let prefix = String.init n (fun i ->
      let c = message.[i] in if c >= ' ' && c <= '~' then c else ' ') in
    if n = String.length message then prefix else prefix ^ " [truncated]"

  let response kind code message =
    let data = Buffer.create 128 in
    Buffer.add_string data "{\"version\":1,\"code\":";
    Yojson.Basic.write_int data code;
    Buffer.add_string data ",\"kind\":";
    Yojson.Basic.write_string data kind;
    Buffer.add_string data ",\"message\":";
    Yojson.Basic.write_string data (bounded_message message);
    Buffer.add_string data "}\n";
    Buffer.contents data

  let fault message = response "fault" 3 message

  let arm seconds =
    expired := false;
    ignore(Unix.setitimer Unix.ITIMER_REAL
      {Unix.it_interval = 0.; Unix.it_value = seconds})

  let disarm () = arm 0.

  let check_signals () =
    if !stopping then raise Shutdown;
    if !expired then raise Timeout

  let select reads writes =
    check_signals ();
    try Unix.select reads writes [] 0.05
    with Unix.Unix_error(Unix.EINTR,_,_) -> [],[],[]

  let rec waitpid flags pid =
    try Unix.waitpid flags pid
    with Unix.Unix_error(Unix.EINTR,_,_) -> waitpid flags pid

  let reap () = match !active_child with
    | None -> ()
    | Some pid ->
        (try Unix.kill pid Sys.sigkill with Unix.Unix_error(Unix.ESRCH,_,_) -> ());
        ignore(waitpid [] pid);
        active_child := None

  let read_request fd =
    let data = Buffer.create 256 and bytes = Bytes.create 4096 in
    let rec loop () =
      let readable,_,_ = select [fd] [] in
      if readable = [] then loop () else
      let n = Unix.read fd bytes 0 (Bytes.length bytes) in
      if n = 0 then raise Disconnected;
      Buffer.add_subbytes data bytes 0 n;
      if Buffer.length data > 16384 then failwith "request exceeds 16384 bytes";
      let text = Buffer.contents data in
      match String.index_opt text '\n' with
      | None -> loop ()
      | Some i when i = String.length text - 1 -> text
      | Some _ -> failwith "only one request frame is allowed" in
    loop ()

  let parse_request text =
    let fields = Yojson.Basic.Util.to_assoc (Yojson.Basic.from_string text) in
    let keys = List.map fst fields in
    if List.sort compare keys <> ["path";"timeout_seconds";"version"] then
      failwith "request fields must be version, path, timeout_seconds exactly once";
    if Yojson.Basic.Util.to_int (List.assoc "version" fields) <> 1 then
      failwith "unsupported protocol version";
    let path = Yojson.Basic.Util.to_string (List.assoc "path" fields) in
    if path = "" || Filename.is_relative path || String.contains path '\000' then
      failwith "path must be an absolute file path";
    let seconds = Yojson.Basic.Util.to_number (List.assoc "timeout_seconds" fields) in
    if not(seconds > 0. && seconds <= 86400.) then failwith "invalid case timeout";
    path,seconds

  let send fd text =
    let bytes = Bytes.of_string text in
    let rec loop offset =
      if offset < Bytes.length bytes then begin
        let _,writable,_ = select [] [fd] in
        if writable = [] then loop offset else
        let n = Unix.write fd bytes offset (Bytes.length bytes - offset) in
        if n = 0 then raise Disconnected;
        loop (offset + n)
      end in
    loop 0

  let child listener client input output path =
    close listener; close client; close input;
    disarm ();
    Sys.set_signal Sys.sigterm Sys.Signal_default;
    Sys.set_signal Sys.sigint Sys.Signal_default;
    Sys.set_signal Sys.sigalrm Sys.Signal_default;
    let null = Unix.openfile "/dev/null" [Unix.O_RDWR] 0 in
    Unix.dup2 null Unix.stdin;
    Unix.dup2 null Unix.stdout;
    Unix.dup2 null Unix.stderr;
    close null;
    let result = try
      let code,message = Hol_check.check_file path in
      if code < 0 || code > 3 then fault "checker returned an invalid exit code"
      else response "result" code message
    with exn -> fault ("checker exception: " ^ Printexc.to_string exn) in
    let bytes = Bytes.of_string result in
    let rec write offset =
      if offset < Bytes.length bytes then
        let n = Unix.write output bytes offset (Bytes.length bytes - offset) in
        if n = 0 then child_exit 3 else write (offset + n) in
    (try write 0; close output; child_exit 0 with _ -> child_exit 3)

  let run_case listener client path seconds =
    let input,output = Unix.pipe () in
    Fun.protect ~finally:(fun () -> close input; close output; disarm (); reap ())
      (fun () ->
        flush_all ();
        arm seconds;
        match Unix.fork () with
        | 0 ->
            (try child listener client input output path with _ -> child_exit 3)
        | pid ->
            active_child := Some pid;
            close output;
            Unix.set_nonblock input;
            let data = Buffer.create 256 and bytes = Bytes.create 4096 in
            let eof = ref false and status = ref None in
            let rec collect () =
              check_signals ();
              if !status = None then begin
                let waited,s = waitpid [Unix.WNOHANG] pid in
                if waited <> 0 then (active_child := None; status := Some s)
              end;
              if !eof && !status <> None then () else begin
                let readable,_,_ = select (client :: if !eof then [] else [input]) [] in
                if List.mem client readable then raise Disconnected;
                if List.mem input readable then begin
                  let n = Unix.read input bytes 0 (Bytes.length bytes) in
                  if n = 0 then eof := true else Buffer.add_subbytes data bytes 0 n;
                  if Buffer.length data > max_frame then failwith "oversized child response"
                end;
                collect ()
              end in
            try
              collect ();
              match !status with
              | Some(Unix.WEXITED 0) ->
                  let text = Buffer.contents data in
                  let fields = Yojson.Basic.Util.to_assoc (Yojson.Basic.from_string text) in
                  let code = Yojson.Basic.Util.to_int (List.assoc "code" fields) in
                  if code >= 0 && code <= 3 then text else failwith "invalid child exit code"
              | _ -> fault "checker child terminated abnormally"
            with Timeout ->
              reap ();
              response "timeout" 2 "case wall timeout; child killed and reaped")

  let handle listener client limit =
    Fun.protect ~finally:(fun () -> disarm (); close client; reap ()) (fun () ->
      Unix.set_nonblock client;
      let result = try
        arm 5.;
        let path,requested = parse_request (read_request client) in
        disarm ();
        run_case listener client path (min requested limit)
      with
      | Shutdown -> raise Shutdown
      | Disconnected -> raise Disconnected
      | Timeout -> fault "request read timeout (no case was checked)"
      | exn -> fault ("runner: " ^ Printexc.to_string exn) in
      arm 2.;
      send client result)

  let run () =
    let path = Sys.getenv "HOL_RUNNER_SOCKET" in
    let limit = float_of_string(Sys.getenv "HOL_RUNNER_CASE_TIMEOUT") in
    if Filename.is_relative path || String.length path >= 100 ||
       not(limit > 0. && limit <= 86400.) then failwith "invalid runner configuration";
    let directory = Unix.lstat (Filename.dirname path) in
    if directory.Unix.st_kind <> Unix.S_DIR || directory.Unix.st_uid <> Unix.getuid () ||
       directory.Unix.st_perm land 0o777 <> 0o700 then failwith "socket directory must be private";
    ignore(Unix.umask 0o077);
    Sys.set_signal Sys.sigpipe Sys.Signal_ignore;
    Sys.set_signal Sys.sigterm (Sys.Signal_handle(fun _ -> stopping := true));
    Sys.set_signal Sys.sigint (Sys.Signal_handle(fun _ -> stopping := true));
    Sys.set_signal Sys.sigalrm (Sys.Signal_handle(fun _ -> expired := true));
    let listener = Unix.socket Unix.PF_UNIX Unix.SOCK_STREAM 0 in
    let bound = ref false in
    Fun.protect ~finally:(fun () ->
      disarm (); reap (); close listener;
      if !bound then (try Unix.unlink path with Unix.Unix_error _ -> ())) (fun () ->
      Unix.bind listener (Unix.ADDR_UNIX path);
      bound := true;
      Unix.chmod path 0o600;
      Unix.listen listener 4;
      Unix.set_nonblock listener;
      Printf.printf "%s:%d\n%!" (Sys.getenv "HOL_RUNNER_READY") (Unix.getpid ());
      try
        while not !stopping do
          let readable,_,_ = select [listener] [] in
          if readable <> [] then begin
            let client,_ = Unix.accept listener in
            try handle listener client limit with
            | Shutdown -> raise Shutdown
            | Disconnected | Timeout | Unix.Unix_error _ -> ()
          end
        done
      with Shutdown -> ())
end;;

let () =
  try Hol_server.run (); exit 0
  with exn ->
    prerr_endline ("HOL_RUNNER_FAULT: " ^ Printexc.to_string exn); exit 3;;
