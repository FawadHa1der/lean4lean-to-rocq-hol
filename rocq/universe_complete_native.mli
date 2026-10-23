
type bool =
| True
| False

val negb : bool -> bool

type nat =
| O
| S of nat

type 'a list =
| Nil
| Cons of 'a * 'a list

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : nat -> nat -> nat

val eqb : bool -> bool -> bool

module Nat :
 sig
  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val max : nat -> nat -> nat
 end

val existsb : ('a1 -> bool) -> 'a1 list -> bool

val forallb : ('a1 -> bool) -> 'a1 list -> bool

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

val name_mem : name -> name list -> bool

type level =
| LZero
| LSucc of level
| LMax of level * level
| LIMax of level * level
| LParam of name
| LMVar of name

val level_has_meta : level -> bool

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

val bind : 'a1 result -> ('a1 -> 'a2 result) -> 'a2 result

val level_eval : (name -> nat) -> level -> nat

type sublevel =
| SubConst of name list * nat
| SubVar of name list * name * nat

val guard_insert : name -> name list -> name list

val const_atom : name list -> nat -> sublevel list

val combine_levels :
  sublevel list result -> sublevel list result -> sublevel list result

val normalize_aux : nat -> level -> name list -> nat -> sublevel list result

val normalize_level : nat -> level -> sublevel list result

val guard_subset : name list -> name list -> bool

val sublevel_le : sublevel -> sublevel -> bool

val sublevels_le : sublevel list -> sublevel list -> bool

val level_le : nat -> level -> level -> bool result

val level_equiv : nat -> level -> level -> bool result

val levels_equiv : nat -> level list -> level list -> bool result

val guard_holds : (name -> nat) -> name list -> bool

val sublevel_eval : (name -> nat) -> sublevel -> nat

val sublevels_eval : (name -> nat) -> sublevel list -> nat

val level_nodes : level -> nat

val unit_assignment : name list -> name -> nat

val sublevel_offset : sublevel -> nat

val offset_bound : sublevel list -> nat

val spike_assignment : name list -> name -> nat -> name -> nat

val atom_countervaluation : sublevel -> sublevel list -> name -> nat
