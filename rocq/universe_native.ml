
type bool =
| True
| False

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

(** val add : nat -> nat -> nat **)

let rec add n0 m =
  match n0 with
  | O -> m
  | S p -> S (add p m)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

module Nat =
 struct
  (** val eqb : nat -> nat -> bool **)

  let rec eqb n0 m =
    match n0 with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n0 m =
    match n0 with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val max : nat -> nat -> nat **)

  let rec max n0 m =
    match n0 with
    | O -> m
    | S n' -> (match m with
               | O -> n0
               | S m' -> S (max n' m'))
 end

(** val existsb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec existsb f = function
| Nil -> False
| Cons (a, l0) -> (match f a with
                   | True -> True
                   | False -> existsb f l0)

(** val forallb : ('a1 -> bool) -> 'a1 list -> bool **)

let rec forallb f = function
| Nil -> True
| Cons (a, l0) -> (match f a with
                   | True -> forallb f l0
                   | False -> False)

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos =
 struct
  (** val eqb : positive -> positive -> bool **)

  let rec eqb p q =
    match p with
    | XI p0 -> (match q with
                | XI q0 -> eqb p0 q0
                | _ -> False)
    | XO p0 -> (match q with
                | XO q0 -> eqb p0 q0
                | _ -> False)
    | XH -> (match q with
             | XH -> True
             | _ -> False)
 end

module N =
 struct
  (** val eqb : n -> n -> bool **)

  let eqb n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> True
             | Npos _ -> False)
    | Npos p -> (match m with
                 | N0 -> False
                 | Npos q -> Pos.eqb p q)
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val eqb0 : ascii -> ascii -> bool **)

let eqb0 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb a0 b0 with
                                       | True -> eqb a1 b1
                                       | False -> False with
                                 | True -> eqb a2 b2
                                 | False -> False with
                           | True -> eqb a3 b3
                           | False -> False with
                     | True -> eqb a4 b4
                     | False -> False with
               | True -> eqb a5 b5
               | False -> False with
         | True -> eqb a6 b6
         | False -> False with
   | True -> eqb a7 b7
   | False -> False)

type string =
| EmptyString
| String of ascii * string

(** val eqb1 : string -> string -> bool **)

let rec eqb1 s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> True
     | String (_, _) -> False)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> False
     | String (c2, s2') ->
       (match eqb0 c1 c2 with
        | True -> eqb1 s1' s2'
        | False -> False))

type name =
| NameAnon
| NameStr of name * string
| NameNum of name * n

(** val name_eqb : name -> name -> bool **)

let rec name_eqb a b =
  match a with
  | NameAnon -> (match b with
                 | NameAnon -> True
                 | _ -> False)
  | NameStr (a0, s) ->
    (match b with
     | NameStr (b0, t) ->
       (match name_eqb a0 b0 with
        | True -> eqb1 s t
        | False -> False)
     | _ -> False)
  | NameNum (a0, n0) ->
    (match b with
     | NameNum (b0, m) ->
       (match name_eqb a0 b0 with
        | True -> N.eqb n0 m
        | False -> False)
     | _ -> False)

(** val name_mem : name -> name list -> bool **)

let name_mem n0 ns =
  existsb (name_eqb n0) ns

type level =
| LZero
| LSucc of level
| LMax of level * level
| LIMax of level * level
| LParam of name
| LMVar of name

(** val level_has_meta : level -> bool **)

let rec level_has_meta = function
| LSucc v -> level_has_meta v
| LMax (a, b) ->
  (match level_has_meta a with
   | True -> True
   | False -> level_has_meta b)
| LIMax (a, b) ->
  (match level_has_meta a with
   | True -> True
   | False -> level_has_meta b)
| LMVar _ -> True
| _ -> False

type reject_reason =
| UnknownConstant
| UnknownFreeVariable
| LooseBoundVariable
| UnknownUniverse
| UniverseArity
| ExpectedSort
| ExpectedPi
| TypeMismatch
| NotDefinitionallyEqual
| DuplicateDeclaration
| DuplicateUniverse
| MalformedDeclaration
| MetaVariable

type decline_reason =
| OutOfFuel
| UnsupportedExpression
| UnsupportedDeclaration

type 'a result =
| Accept of 'a
| Reject of reject_reason
| Decline of decline_reason

(** val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result **)

let bind r f =
  match r with
  | Accept a -> f a
  | Reject e -> Reject e
  | Decline e -> Decline e

(** val level_eval : (name -> nat) -> level -> nat **)

let rec level_eval rho = function
| LSucc v -> S (level_eval rho v)
| LMax (a, b) -> Nat.max (level_eval rho a) (level_eval rho b)
| LIMax (a, b) ->
  (match level_eval rho b with
   | O -> O
   | S n0 -> Nat.max (level_eval rho a) (S n0))
| LParam n0 -> rho n0
| _ -> O

type sublevel =
| SubConst of name list * nat
| SubVar of name list * name * nat

(** val guard_insert : name -> name list -> name list **)

let guard_insert n0 ns =
  match name_mem n0 ns with
  | True -> ns
  | False -> Cons (n0, ns)

(** val const_atom : name list -> nat -> sublevel list **)

let const_atom path k = match k with
| O -> Nil
| S _ -> Cons ((SubConst (path, k)), Nil)

(** val combine_levels :
    sublevel list result -> sublevel list result -> sublevel list result **)

let combine_levels a b =
  bind a (fun xs -> bind b (fun ys -> Accept (app xs ys)))

(** val normalize_aux :
    nat -> level -> name list -> nat -> sublevel list result **)

let rec normalize_aux fuel u path k =
  match fuel with
  | O -> Decline OutOfFuel
  | S fuel0 ->
    (match u with
     | LZero -> Accept (const_atom path k)
     | LSucc v -> normalize_aux fuel0 v path (S k)
     | LMax (a, b) ->
       combine_levels (normalize_aux fuel0 a path k)
         (normalize_aux fuel0 b path k)
     | LIMax (a, b) ->
       (match b with
        | LZero -> Accept (const_atom path k)
        | LSucc v ->
          combine_levels (normalize_aux fuel0 a path k)
            (normalize_aux fuel0 v path (S k))
        | LMax (v, w) ->
          combine_levels (normalize_aux fuel0 (LIMax (a, v)) path k)
            (normalize_aux fuel0 (LIMax (a, w)) path k)
        | LIMax (v, w) ->
          combine_levels (normalize_aux fuel0 (LIMax (a, w)) path k)
            (normalize_aux fuel0 (LIMax (v, w)) path k)
        | LParam n0 ->
          let path' = guard_insert n0 path in
          bind (normalize_aux fuel0 a path' k) (fun xs -> Accept
            (app (const_atom path k) (Cons ((SubVar (path', n0, k)), xs))))
        | LMVar _ -> Reject MetaVariable)
     | LParam n0 ->
       Accept
         (app (const_atom path k) (Cons ((SubVar ((guard_insert n0 path), n0,
           k)), Nil)))
     | LMVar _ -> Reject MetaVariable)

(** val normalize_level : nat -> level -> sublevel list result **)

let normalize_level fuel u =
  match level_has_meta u with
  | True -> Reject MetaVariable
  | False -> normalize_aux fuel u Nil O

(** val guard_subset : name list -> name list -> bool **)

let guard_subset xs ys =
  forallb (fun x -> name_mem x ys) xs

(** val sublevel_le : sublevel -> sublevel -> bool **)

let sublevel_le a b =
  match a with
  | SubConst (p, k) ->
    (match b with
     | SubConst (q, j) ->
       (match guard_subset q p with
        | True -> Nat.leb k j
        | False -> False)
     | SubVar (q, n0, j) ->
       (match match guard_subset q p with
              | True -> name_mem n0 q
              | False -> False with
        | True -> Nat.leb k (S j)
        | False -> False))
  | SubVar (p, n0, k) ->
    (match b with
     | SubConst (_, _) -> False
     | SubVar (q, m, j) ->
       (match match guard_subset q p with
              | True -> name_eqb n0 m
              | False -> False with
        | True -> Nat.leb k j
        | False -> False))

(** val sublevels_le : sublevel list -> sublevel list -> bool **)

let sublevels_le xs ys =
  forallb (fun x -> existsb (sublevel_le x) ys) xs

(** val level_le : nat -> level -> level -> bool result **)

let level_le fuel u v =
  bind (normalize_level fuel u) (fun xs ->
    bind (normalize_level fuel v) (fun ys -> Accept (sublevels_le xs ys)))

(** val level_equiv : nat -> level -> level -> bool result **)

let level_equiv fuel u v =
  bind (normalize_level fuel u) (fun xs ->
    bind (normalize_level fuel v) (fun ys -> Accept
      (match sublevels_le xs ys with
       | True -> sublevels_le ys xs
       | False -> False)))

(** val levels_equiv : nat -> level list -> level list -> bool result **)

let rec levels_equiv fuel us vs =
  match us with
  | Nil -> (match vs with
            | Nil -> Accept True
            | Cons (_, _) -> Accept False)
  | Cons (u, us0) ->
    (match vs with
     | Nil -> Accept False
     | Cons (v, vs0) ->
       bind (level_equiv fuel u v) (fun b ->
         match b with
         | True -> levels_equiv fuel us0 vs0
         | False -> Accept False))

(** val guard_holds : (name -> nat) -> name list -> bool **)

let guard_holds rho ns =
  forallb (fun n0 -> negb (Nat.eqb (rho n0) O)) ns

(** val sublevel_eval : (name -> nat) -> sublevel -> nat **)

let sublevel_eval rho = function
| SubConst (p, k) -> (match guard_holds rho p with
                      | True -> k
                      | False -> O)
| SubVar (p, n0, k) ->
  (match guard_holds rho p with
   | True -> add (rho n0) k
   | False -> O)

(** val sublevels_eval : (name -> nat) -> sublevel list -> nat **)

let rec sublevels_eval rho = function
| Nil -> O
| Cons (s, ss0) -> Nat.max (sublevel_eval rho s) (sublevels_eval rho ss0)

(** val level_nodes : level -> nat **)

let rec level_nodes = function
| LSucc v -> S (level_nodes v)
| LMax (a, b) -> S (add (level_nodes a) (level_nodes b))
| LIMax (a, b) -> S (add (level_nodes a) (level_nodes b))
| _ -> S O
