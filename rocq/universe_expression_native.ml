
type bool =
| True
| False

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val pred : nat -> nat **)

let pred n0 = match n0 with
| O -> n0
| S u -> u

(** val add : nat -> nat -> nat **)

let rec add n0 m =
  match n0 with
  | O -> m
  | S p -> S (add p m)

(** val sub : nat -> nat -> nat **)

let rec sub n0 m =
  match n0 with
  | O -> n0
  | S k -> (match m with
            | O -> n0
            | S l -> sub k l)

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

  (** val ltb : nat -> nat -> bool **)

  let ltb n0 m =
    leb (S n0) m
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, l0) -> Cons ((f a), (map f l0))

(** val nth_error : 'a1 list -> nat -> 'a1 option **)

let rec nth_error l = function
| O -> (match l with
        | Nil -> None
        | Cons (x, _) -> Some x)
| S n1 -> (match l with
           | Nil -> None
           | Cons (_, l') -> nth_error l' n1)

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

type level =
| LZero
| LSucc of level
| LMax of level * level
| LIMax of level * level
| LParam of name
| LMVar of name

(** val lookup_level : name list -> level list -> name -> level **)

let rec lookup_level ps us n0 =
  match ps with
  | Nil -> LParam n0
  | Cons (p, ps0) ->
    (match us with
     | Nil -> LParam n0
     | Cons (u, us0) ->
       (match name_eqb p n0 with
        | True -> u
        | False -> lookup_level ps0 us0 n0))

(** val subst_level : name list -> level list -> level -> level **)

let rec subst_level ps us = function
| LSucc v -> LSucc (subst_level ps us v)
| LMax (a, b) -> LMax ((subst_level ps us a), (subst_level ps us b))
| LIMax (a, b) -> LIMax ((subst_level ps us a), (subst_level ps us b))
| LParam n0 -> lookup_level ps us n0
| x -> x

type binder_info =
| BDefault
| BImplicit
| BStrictImplicit
| BInstImplicit

type literal =
| LitNat of n
| LitString of string

type expr =
| EBVar of nat
| EFVar of name
| EMVar of name
| ESort of level
| EConst of name * level list
| EApp of expr * expr
| ELam of name * binder_info * expr * expr
| EPi of name * binder_info * expr * expr
| ELet of name * expr * expr * expr * bool
| ELit of literal
| EProj of name * nat * expr
| EMData of expr

(** val lift : nat -> nat -> expr -> expr **)

let rec lift amount cutoff e = match e with
| EBVar i ->
  EBVar (match Nat.leb cutoff i with
         | True -> add amount i
         | False -> i)
| EApp (f, a) -> EApp ((lift amount cutoff f), (lift amount cutoff a))
| ELam (n0, bi, a, b) ->
  ELam (n0, bi, (lift amount cutoff a), (lift amount (S cutoff) b))
| EPi (n0, bi, a, b) ->
  EPi (n0, bi, (lift amount cutoff a), (lift amount (S cutoff) b))
| ELet (n0, a, v, b, nd) ->
  ELet (n0, (lift amount cutoff a), (lift amount cutoff v),
    (lift amount (S cutoff) b), nd)
| EProj (n0, i, a) -> EProj (n0, i, (lift amount cutoff a))
| EMData a -> EMData (lift amount cutoff a)
| _ -> e

(** val subst : nat -> expr -> expr -> expr **)

let rec subst index value e = match e with
| EBVar i ->
  (match Nat.eqb i index with
   | True -> (match index with
              | O -> value
              | S _ -> lift index O value)
   | False -> EBVar (match Nat.ltb index i with
                     | True -> pred i
                     | False -> i))
| EApp (f, a) -> EApp ((subst index value f), (subst index value a))
| ELam (n0, bi, a, b) ->
  ELam (n0, bi, (subst index value a), (subst (S index) value b))
| EPi (n0, bi, a, b) ->
  EPi (n0, bi, (subst index value a), (subst (S index) value b))
| ELet (n0, a, v, b, nd) ->
  ELet (n0, (subst index value a), (subst index value v),
    (subst (S index) value b), nd)
| EProj (n0, i, a) -> EProj (n0, i, (subst index value a))
| EMData a -> EMData (subst index value a)
| _ -> e

(** val instantiate : expr -> expr -> expr **)

let instantiate body value =
  subst O value body

(** val subst_many : nat -> expr list -> expr -> expr **)

let rec subst_many index values e = match e with
| EBVar i ->
  (match Nat.ltb i index with
   | True -> e
   | False ->
     (match nth_error values (sub i index) with
      | Some value ->
        (match index with
         | O -> value
         | S _ -> lift index O value)
      | None -> EBVar (sub i (length values))))
| EApp (f, a) ->
  EApp ((subst_many index values f), (subst_many index values a))
| ELam (n0, bi, a, b) ->
  ELam (n0, bi, (subst_many index values a), (subst_many (S index) values b))
| EPi (n0, bi, a, b) ->
  EPi (n0, bi, (subst_many index values a), (subst_many (S index) values b))
| ELet (n0, a, v, b, nd) ->
  ELet (n0, (subst_many index values a), (subst_many index values v),
    (subst_many (S index) values b), nd)
| EProj (n0, i, a) -> EProj (n0, i, (subst_many index values a))
| EMData a -> EMData (subst_many index values a)
| _ -> e

(** val instantiate_many : expr -> expr list -> expr **)

let instantiate_many body values = match values with
| Nil -> body
| Cons (_, _) -> subst_many O values body

(** val subst_levels : name list -> level list -> expr -> expr **)

let rec subst_levels ps us e = match e with
| ESort u -> ESort (subst_level ps us u)
| EConst (n0, vs) -> EConst (n0, (map (subst_level ps us) vs))
| EApp (f, a) -> EApp ((subst_levels ps us f), (subst_levels ps us a))
| ELam (n0, bi, a, b) ->
  ELam (n0, bi, (subst_levels ps us a), (subst_levels ps us b))
| EPi (n0, bi, a, b) ->
  EPi (n0, bi, (subst_levels ps us a), (subst_levels ps us b))
| ELet (n0, a, v, b, nd) ->
  ELet (n0, (subst_levels ps us a), (subst_levels ps us v),
    (subst_levels ps us b), nd)
| EProj (n0, i, a) -> EProj (n0, i, (subst_levels ps us a))
| EMData a -> EMData (subst_levels ps us a)
| _ -> e

(** val scoped : nat -> expr -> bool **)

let rec scoped depth = function
| EBVar i -> Nat.ltb i depth
| EApp (a, b) ->
  (match scoped depth a with
   | True -> scoped depth b
   | False -> False)
| ELam (_, _, a, b) ->
  (match scoped depth a with
   | True -> scoped (S depth) b
   | False -> False)
| EPi (_, _, a, b) ->
  (match scoped depth a with
   | True -> scoped (S depth) b
   | False -> False)
| ELet (_, a, v, b, _) ->
  (match match scoped depth a with
         | True -> scoped depth v
         | False -> False with
   | True -> scoped (S depth) b
   | False -> False)
| EProj (_, _, a) -> scoped depth a
| EMData a -> scoped depth a
| _ -> True
