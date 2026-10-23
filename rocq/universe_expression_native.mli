
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

val length : 'a1 list -> nat

val pred : nat -> nat

val add : nat -> nat -> nat

val sub : nat -> nat -> nat

val eqb : bool -> bool -> bool

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val nth_error : 'a1 list -> nat -> 'a1 option

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos :
 sig
  val eqb : positive -> positive -> bool
 end

module N :
 sig
  val eqb : n -> n -> bool
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val eqb0 : ascii -> ascii -> bool

type string =
| EmptyString
| String of ascii * string

val eqb1 : string -> string -> bool

type name =
| NameAnon
| NameStr of name * string
| NameNum of name * n

val name_eqb : name -> name -> bool

type level =
| LZero
| LSucc of level
| LMax of level * level
| LIMax of level * level
| LParam of name
| LMVar of name

val lookup_level : name list -> level list -> name -> level

val subst_level : name list -> level list -> level -> level

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

val lift : nat -> nat -> expr -> expr

val subst : nat -> expr -> expr -> expr

val instantiate : expr -> expr -> expr

val subst_many : nat -> expr list -> expr -> expr

val instantiate_many : expr -> expr list -> expr

val subst_levels : name list -> level list -> expr -> expr

val scoped : nat -> expr -> bool
