(* Copyright 2026 Fawad Haider. Apache-2.0; see hol/NOTICE.
   Pure bounded accounting; this module cannot construct HOL theorems. *)
module L4_closed_budget = struct
  type limits = {
    entry_weight : int; total_weight : int; entries : int;
    depth : int; label_bytes : int
  }
  let limits = {
    entry_weight = 8192; total_weight = 65536; entries = 64;
    depth = 128; label_bytes = 256
  }
  type ('tm,'ty) term_view = Atom of string * 'ty | Branch of 'tm * 'tm
  type 'ty type_view = Type_var of string | Type_app of string * 'ty list
  type ('tm,'ty) work = Term of 'tm * int | Type of 'ty * int
                     | Terms of 'tm list * int | Types of 'ty list * int
  type 'a lookup = Missing | Negative | Positive of 'a
  type stats = { count : int; weight : int; hits : int; misses : int;
                 refused : int; evictions : int }

  module Make (Input : sig
    type term
    type typ
    val term_view : term -> (term,typ) term_view
    val type_view : typ -> typ type_view
    val equal : term -> term -> bool
  end) : sig
    type 'a cache
    val measure : Input.term list -> int option
    val create : ('a -> Input.term list) -> 'a cache
    val find : 'a cache -> Input.term -> 'a lookup
    val put : 'a cache -> Input.term -> 'a option -> bool
    val clear : 'a cache -> unit
    val stats : 'a cache -> stats
  end = struct
    (* Occurrences, not addresses: shared subtrees are charged every time.
       Lists and type arguments are walked incrementally, without List.map
       on attacker-sized lists or recursive traversal of terms/types. *)
    let measure roots =
      let todo = ref [Terms(roots,0)] in
      let weight = ref 0 and allowed = ref true in
      let charge n =
        if n > limits.entry_weight - !weight then allowed := false
        else weight := !weight + n in
      let label s =
        let n = String.length s in
        if n > limits.label_bytes then allowed := false else charge n in
      let depth d = if d > limits.depth then allowed := false in
      while !allowed && !todo <> [] do
        match !todo with
        | [] -> ()
        | item::rest ->
          todo := rest; charge 1;
          match item with
          | Terms([],d) | Types([],d) -> depth d
          | Terms(t::ts,d) ->
            depth d; todo := Term(t,d+1)::Terms(ts,d+1)::!todo
          | Types(t::ts,d) ->
            depth d; todo := Type(t,d+1)::Types(ts,d+1)::!todo
          | Term(t,d) ->
            depth d;
            if !allowed then (match Input.term_view t with
            | Atom(s,ty) -> label s; todo := Type(ty,d+1)::!todo
            | Branch(a,b) -> todo := Term(a,d+1)::Term(b,d+1)::!todo)
          | Type(ty,d) ->
            depth d;
            if !allowed then (match Input.type_view ty with
            | Type_var s -> label s
            | Type_app(s,args) -> label s; todo := Types(args,d+1)::!todo)
      done;
      if !allowed then Some !weight else None

    type 'a cache = {
      terms : 'a -> Input.term list;
      mutable queue : (Input.term * 'a option * int) list;
      mutable weight : int; mutable hits : int; mutable misses : int;
      mutable refused : int; mutable evictions : int
    }
    let create terms = {terms;queue=[];weight=0;hits=0;misses=0;
                        refused=0;evictions=0}
    let clear c =
      c.queue <- []; c.weight <- 0; c.hits <- 0; c.misses <- 0;
      c.refused <- 0; c.evictions <- 0
    let stats c = {count=List.length c.queue;weight=c.weight;hits=c.hits;
                   misses=c.misses;refused=c.refused;evictions=c.evictions}
    let find c key = match measure [key] with
      | None -> c.refused <- c.refused+1; c.misses <- c.misses+1; Missing
      | Some _ ->
        let rec search = function
          | [] -> c.misses <- c.misses+1; Missing
          | (old,value,_)::rest ->
            if Input.equal old key then (c.hits <- c.hits+1;
              match value with None -> Negative | Some x -> Positive x)
            else search rest in
        search c.queue
    let put c key value =
      let roots = key::(match value with None -> [] | Some v -> c.terms v) in
      match measure roots with
      | None -> c.refused <- c.refused+1; false
      | Some w when w > limits.entry_weight - 2 ->
        c.refused <- c.refused+1; false
      | Some w ->
        let w = w+2 in
        (* Equality is reached only after the complete incoming entry and all
           resident keys have passed the finite size/depth bounds. *)
        let kept = List.filter (fun (old,_,_) -> not(Input.equal key old)) c.queue in
        c.weight <- List.fold_left (fun n (_,_,w) -> n+w) 0 kept;
        c.queue <- kept;
        while List.length c.queue >= limits.entries ||
              c.weight > limits.total_weight - w do
          match c.queue with
          | [] -> assert false
          | (_,_,old)::rest ->
            c.queue <- rest; c.weight <- c.weight-old;
            c.evictions <- c.evictions+1
        done;
        c.queue <- c.queue @ [key,value,w]; c.weight <- c.weight+w; true
  end
end;;
