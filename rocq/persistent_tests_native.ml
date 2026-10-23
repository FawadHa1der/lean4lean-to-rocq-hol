
type unit0 =
| Tt

type bool =
| True
| False

(** val xorb : bool -> bool -> bool **)

let xorb b1 b2 =
  match b1 with
  | True -> (match b2 with
             | True -> False
             | False -> True)
  | False -> b2

(** val negb : bool -> bool **)

let negb = function
| True -> False
| False -> True

type nat =
| O
| S of nat

type 'a option =
| Some of 'a
| None

(** val option_map : ('a1 -> 'a2) -> 'a1 option -> 'a2 option **)

let option_map f = function
| Some a -> Some (f a)
| None -> None

type ('a, 'b) prod =
| Pair of 'a * 'b

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x0, _) -> x0

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type 'a list =
| Nil
| Cons of 'a * 'a list

(** val length : 'a1 list -> nat **)

let rec length = function
| Nil -> O
| Cons (_, l') -> S (length l')

(** val app : 'a1 list -> 'a1 list -> 'a1 list **)

let rec app l m =
  match l with
  | Nil -> m
  | Cons (a, l1) -> Cons (a, (app l1 m))

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type sumbool =
| Left
| Right

type uint =
| Nil0
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

(** val revapp : uint -> uint -> uint **)

let rec revapp d d' =
  match d with
  | Nil0 -> d'
  | D0 d0 -> revapp d0 (D0 d')
  | D1 d0 -> revapp d0 (D1 d')
  | D2 d0 -> revapp d0 (D2 d')
  | D3 d0 -> revapp d0 (D3 d')
  | D4 d0 -> revapp d0 (D4 d')
  | D5 d0 -> revapp d0 (D5 d')
  | D6 d0 -> revapp d0 (D6 d')
  | D7 d0 -> revapp d0 (D7 d')
  | D8 d0 -> revapp d0 (D8 d')
  | D9 d0 -> revapp d0 (D9 d')

(** val rev : uint -> uint **)

let rev d =
  revapp d Nil0

module Little =
 struct
  (** val succ : uint -> uint **)

  let rec succ = function
  | Nil0 -> D1 Nil0
  | D0 d0 -> D1 d0
  | D1 d0 -> D2 d0
  | D2 d0 -> D3 d0
  | D3 d0 -> D4 d0
  | D4 d0 -> D5 d0
  | D5 d0 -> D6 d0
  | D6 d0 -> D7 d0
  | D7 d0 -> D8 d0
  | D8 d0 -> D9 d0
  | D9 d0 -> D0 (succ d0)
 end

type uint0 =
| Nil1
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

(** val pred : nat -> nat **)

let pred n0 = match n0 with
| O -> n0
| S u0 -> u0

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n0 m =
   match n0 with
   | O -> m
   | S p0 -> S (add p0 m)
end
include Coq__1

(** val sub : nat -> nat -> nat **)

let rec sub n0 m =
  match n0 with
  | O -> n0
  | S k -> (match m with
            | O -> n0
            | S l -> sub k l)

(** val eqb : nat -> nat -> bool **)

let rec eqb n0 m =
  match n0 with
  | O -> (match m with
          | O -> True
          | S _ -> False)
  | S n' -> (match m with
             | O -> False
             | S m' -> eqb n' m')

(** val tail_add : nat -> nat -> nat **)

let rec tail_add n0 m =
  match n0 with
  | O -> m
  | S n1 -> tail_add n1 (S m)

(** val tail_addmul : nat -> nat -> nat -> nat **)

let rec tail_addmul r n0 m =
  match n0 with
  | O -> r
  | S n1 -> tail_addmul (tail_add m r) n1 m

(** val tail_mul : nat -> nat -> nat **)

let tail_mul n0 m =
  tail_addmul O n0 m

(** val of_uint_acc : uint -> nat -> nat **)

let rec of_uint_acc d acc =
  match d with
  | Nil0 -> acc
  | D0 d0 ->
    of_uint_acc d0 (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)
  | D1 d0 ->
    of_uint_acc d0 (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))
  | D2 d0 ->
    of_uint_acc d0 (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))
  | D3 d0 ->
    of_uint_acc d0 (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))
  | D4 d0 ->
    of_uint_acc d0 (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))
  | D5 d0 ->
    of_uint_acc d0 (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))
  | D6 d0 ->
    of_uint_acc d0 (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))))
  | D7 d0 ->
    of_uint_acc d0 (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))))
  | D8 d0 ->
    of_uint_acc d0 (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc)))))))))
  | D9 d0 ->
    of_uint_acc d0 (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S O)))))))))) acc))))))))))

(** val of_uint : uint -> nat **)

let of_uint d =
  of_uint_acc d O

(** val of_hex_uint_acc : uint0 -> nat -> nat **)

let rec of_hex_uint_acc d acc =
  match d with
  | Nil1 -> acc
  | D10 d0 ->
    of_hex_uint_acc d0
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)
  | D11 d0 ->
    of_hex_uint_acc d0 (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))
  | D12 d0 ->
    of_hex_uint_acc d0 (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))
  | D13 d0 ->
    of_hex_uint_acc d0 (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))
  | D14 d0 ->
    of_hex_uint_acc d0 (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))))
  | D15 d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))))
  | D16 d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))))))
  | D17 d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))))))
  | D18 d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))))))))
  | D19 d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))))))))
  | Da d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))))))))))
  | Db d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))))))))))
  | Dc d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))))))))))))
  | Dd d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))))))))))))
  | De d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc)))))))))))))))
  | Df d0 ->
    of_hex_uint_acc d0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (tail_mul (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) acc))))))))))))))))

(** val of_hex_uint : uint0 -> nat **)

let of_hex_uint d =
  of_hex_uint_acc d O

(** val of_num_uint : uint1 -> nat **)

let of_num_uint = function
| UIntDecimal d0 -> of_uint d0
| UIntHexadecimal d0 -> of_hex_uint d0

(** val eqb0 : bool -> bool -> bool **)

let eqb0 b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

module type EqLtLe =
 sig
  type t
 end

module MakeOrderTac =
 functor (O:EqLtLe) ->
 functor (P:sig
 end) ->
 struct
 end

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

  (** val to_little_uint : nat -> uint -> uint **)

  let rec to_little_uint n0 acc =
    match n0 with
    | O -> acc
    | S n1 -> to_little_uint n1 (Little.succ acc)

  (** val to_uint : nat -> uint **)

  let to_uint n0 =
    rev (to_little_uint n0 (D0 Nil0))
 end

(** val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list **)

let rec map f = function
| Nil -> Nil
| Cons (a, l0) -> Cons ((f a), (map f l0))

(** val seq : nat -> nat -> nat list **)

let rec seq start = function
| O -> Nil
| S len0 -> Cons (start, (seq (S start) len0))

(** val firstn : nat -> 'a1 list -> 'a1 list **)

let rec firstn n0 l =
  match n0 with
  | O -> Nil
  | S n1 ->
    (match l with
     | Nil -> Nil
     | Cons (a, l0) -> Cons (a, (firstn n1 l0)))

(** val skipn : nat -> 'a1 list -> 'a1 list **)

let rec skipn n0 l =
  match n0 with
  | O -> l
  | S n1 -> (match l with
             | Nil -> Nil
             | Cons (_, l0) -> skipn n1 l0)

(** val nth_error : 'a1 list -> nat -> 'a1 option **)

let rec nth_error l = function
| O -> (match l with
        | Nil -> None
        | Cons (x0, _) -> Some x0)
| S n1 -> (match l with
           | Nil -> None
           | Cons (_, l') -> nth_error l' n1)

(** val rev0 : 'a1 list -> 'a1 list **)

let rec rev0 = function
| Nil -> Nil
| Cons (x0, l') -> app (rev0 l') (Cons (x0, Nil))

(** val flat_map : ('a1 -> 'a2 list) -> 'a1 list -> 'a2 list **)

let rec flat_map f = function
| Nil -> Nil
| Cons (x0, l0) -> app (f x0) (flat_map f l0)

(** val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1 **)

let rec fold_left f l a0 =
  match l with
  | Nil -> a0
  | Cons (b, l0) -> fold_left f l0 (f a0 b)

(** val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1 **)

let rec fold_right f a0 = function
| Nil -> a0
| Cons (b, l0) -> f b (fold_right f a0 l0)

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

(** val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list **)

let rec filter f = function
| Nil -> Nil
| Cons (x0, l0) ->
  (match f x0 with
   | True -> Cons (x0, (filter f l0))
   | False -> filter f l0)

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| Nil -> None
| Cons (x0, tl) -> (match f x0 with
                    | True -> Some x0
                    | False -> find f tl)

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p0 -> XO (succ p0)
  | XO p0 -> XI p0
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x0 y =
    match x0 with
    | XI p0 ->
      (match y with
       | XI q0 -> XO (add_carry p0 q0)
       | XO q0 -> XI (add p0 q0)
       | XH -> XO (succ p0))
    | XO p0 ->
      (match y with
       | XI q0 -> XI (add p0 q0)
       | XO q0 -> XO (add p0 q0)
       | XH -> XI p0)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x0 y =
    match x0 with
    | XI p0 ->
      (match y with
       | XI q0 -> XI (add_carry p0 q0)
       | XO q0 -> XO (add_carry p0 q0)
       | XH -> XI (succ p0))
    | XO p0 ->
      (match y with
       | XI q0 -> XO (add_carry p0 q0)
       | XO q0 -> XI (add p0 q0)
       | XH -> XO (succ p0))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p0 -> XI (XO p0)
  | XO p0 -> XI (pred_double p0)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p0 -> Npos (XO p0)
  | XO p0 -> Npos (pred_double p0)
  | XH -> N0

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p0 -> IsPos (XI p0)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p0 -> IsPos (XO p0)
  | x1 -> x1

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p0 -> IsPos (XO (XO p0))
  | XO p0 -> IsPos (XO (pred_double p0))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x0 y =
    match x0 with
    | XI p0 ->
      (match y with
       | XI q0 -> double_mask (sub_mask p0 q0)
       | XO q0 -> succ_double_mask (sub_mask p0 q0)
       | XH -> IsPos (XO p0))
    | XO p0 ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p0 q0)
       | XO q0 -> double_mask (sub_mask p0 q0)
       | XH -> IsPos (pred_double p0))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x0 y =
    match x0 with
    | XI p0 ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p0 q0)
       | XO q0 -> double_mask (sub_mask p0 q0)
       | XH -> IsPos (pred_double p0))
    | XO p0 ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p0 q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p0 q0)
       | XH -> double_pred_mask p0)
    | XH -> IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x0 y =
    match x0 with
    | XI p0 -> add y (XO (mul p0 y))
    | XO p0 -> XO (mul p0 y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x0 = function
  | XI n' -> f (iter f (iter f x0 n') n')
  | XO n' -> iter f (iter f x0 n') n'
  | XH -> f x0

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x0 y =
    match x0 with
    | XI p0 ->
      (match y with
       | XI q0 -> compare_cont r p0 q0
       | XO q0 -> compare_cont Gt p0 q0
       | XH -> Gt)
    | XO p0 ->
      (match y with
       | XI q0 -> compare_cont Lt p0 q0
       | XO q0 -> compare_cont r p0 q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p0 q0 =
    match p0 with
    | XI p1 -> (match q0 with
                | XI q1 -> eqb p1 q1
                | _ -> False)
    | XO p1 -> (match q0 with
                | XO q1 -> eqb p1 q1
                | _ -> False)
    | XH -> (match q0 with
             | XH -> True
             | _ -> False)

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p0 -> Npos (XI p0)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p0 -> Npos (XO p0)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p0 q0 =
    match p0 with
    | XI p1 ->
      (match q0 with
       | XI q1 -> XI (coq_lor p1 q1)
       | XO q1 -> XI (coq_lor p1 q1)
       | XH -> p0)
    | XO p1 ->
      (match q0 with
       | XI q1 -> XI (coq_lor p1 q1)
       | XO q1 -> XO (coq_lor p1 q1)
       | XH -> XI p1)
    | XH -> (match q0 with
             | XO q1 -> XI q1
             | _ -> q0)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p0 q0 =
    match p0 with
    | XI p1 ->
      (match q0 with
       | XI q1 -> coq_Nsucc_double (coq_land p1 q1)
       | XO q1 -> coq_Ndouble (coq_land p1 q1)
       | XH -> Npos XH)
    | XO p1 ->
      (match q0 with
       | XI q1 -> coq_Ndouble (coq_land p1 q1)
       | XO q1 -> coq_Ndouble (coq_land p1 q1)
       | XH -> N0)
    | XH -> (match q0 with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p0 q0 =
    match p0 with
    | XI p1 ->
      (match q0 with
       | XI q1 -> coq_Ndouble (coq_lxor p1 q1)
       | XO q1 -> coq_Nsucc_double (coq_lxor p1 q1)
       | XH -> Npos (XO p1))
    | XO p1 ->
      (match q0 with
       | XI q1 -> coq_Nsucc_double (coq_lxor p1 q1)
       | XO q1 -> coq_Ndouble (coq_lxor p1 q1)
       | XH -> Npos (XI p1))
    | XH ->
      (match q0 with
       | XI q1 -> Npos (XO q1)
       | XO q1 -> Npos (XI q1)
       | XH -> N0)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p0 a =
    match p0 with
    | XI p1 -> op a (iter_op op p1 (op a a))
    | XO p1 -> iter_op op p1 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x0 =
    iter_op Coq__1.add x0 (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x0 -> succ (of_succ_nat x0)
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p0 -> XO (succ p0)
  | XO p0 -> XI p0
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x0 y =
    match x0 with
    | XI p0 ->
      (match y with
       | XI q0 -> XO (add_carry p0 q0)
       | XO q0 -> XI (add p0 q0)
       | XH -> XO (succ p0))
    | XO p0 ->
      (match y with
       | XI q0 -> XI (add p0 q0)
       | XO q0 -> XO (add p0 q0)
       | XH -> XI p0)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x0 y =
    match x0 with
    | XI p0 ->
      (match y with
       | XI q0 -> XI (add_carry p0 q0)
       | XO q0 -> XO (add_carry p0 q0)
       | XH -> XI (succ p0))
    | XO p0 ->
      (match y with
       | XI q0 -> XO (add_carry p0 q0)
       | XO q0 -> XI (add p0 q0)
       | XH -> XO (succ p0))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p0 -> XI (XO p0)
  | XO p0 -> XI (pred_double p0)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p0 -> IsPos (XI p0)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p0 -> IsPos (XO p0)
  | x1 -> x1

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p0 -> IsPos (XO (XO p0))
  | XO p0 -> IsPos (XO (pred_double p0))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x0 y =
    match x0 with
    | XI p0 ->
      (match y with
       | XI q0 -> double_mask (sub_mask p0 q0)
       | XO q0 -> succ_double_mask (sub_mask p0 q0)
       | XH -> IsPos (XO p0))
    | XO p0 ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p0 q0)
       | XO q0 -> double_mask (sub_mask p0 q0)
       | XH -> IsPos (pred_double p0))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x0 y =
    match x0 with
    | XI p0 ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p0 q0)
       | XO q0 -> double_mask (sub_mask p0 q0)
       | XH -> IsPos (pred_double p0))
    | XO p0 ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p0 q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p0 q0)
       | XH -> double_pred_mask p0)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x0 y =
    match sub_mask x0 y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x0 y =
    match x0 with
    | XI p0 -> add y (XO (mul p0 y))
    | XO p0 -> XO (mul p0 y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x0 = function
  | XI n' -> f (iter f (iter f x0 n') n')
  | XO n' -> iter f (iter f x0 n') n'
  | XH -> f x0

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x0 y =
    match x0 with
    | XI p0 ->
      (match y with
       | XI q0 -> compare_cont r p0 q0
       | XO q0 -> compare_cont Gt p0 q0
       | XH -> Gt)
    | XO p0 ->
      (match y with
       | XI q0 -> compare_cont Lt p0 q0
       | XO q0 -> compare_cont r p0 q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val eqb : positive -> positive -> bool **)

  let rec eqb p0 q0 =
    match p0 with
    | XI p1 -> (match q0 with
                | XI q1 -> eqb p1 q1
                | _ -> False)
    | XO p1 -> (match q0 with
                | XO q1 -> eqb p1 q1
                | _ -> False)
    | XH -> (match q0 with
             | XH -> True
             | _ -> False)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x0 -> succ (of_succ_nat x0)

  (** val pow : positive -> positive -> positive **)

  let pow x0 =
    iter (mul x0) XH

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p1 -> S (size_nat p1)
  | XO p1 -> S (size_nat p1)
  | XH -> S O

  (** val size : positive -> positive **)

  let rec size = function
  | XI p1 -> succ (size p1)
  | XO p1 -> succ (size p1)
  | XH -> XH

  (** val gcdn : nat -> positive -> positive -> positive **)

  let rec gcdn n0 a b =
    match n0 with
    | O -> XH
    | S n1 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> a
             | Lt -> gcdn n1 (sub b' a') a
             | Gt -> gcdn n1 (sub a' b') b)
          | XO b0 -> gcdn n1 a b0
          | XH -> XH)
       | XO a0 ->
         (match b with
          | XI _ -> gcdn n1 a0 b
          | XO b0 -> XO (gcdn n1 a0 b0)
          | XH -> XH)
       | XH -> XH)

  (** val gcd : positive -> positive -> positive **)

  let gcd a b =
    gcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val shiftl : positive -> n -> positive **)

  let shiftl p0 = function
  | N0 -> p0
  | Npos n1 -> iter (fun x0 -> XO x0) p0 n1

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p0 x0 =
    match p0 with
    | XI p1 -> (match x0 with
                | XI p2 -> eq_dec p1 p2
                | _ -> Right)
    | XO p1 -> (match x0 with
                | XO p2 -> eq_dec p1 p2
                | _ -> Right)
    | XH -> (match x0 with
             | XH -> Left
             | _ -> Right)
 end

module N =
 struct
  (** val succ_double : n -> n **)

  let succ_double = function
  | N0 -> Npos XH
  | Npos p0 -> Npos (XI p0)

  (** val double : n -> n **)

  let double = function
  | N0 -> N0
  | Npos p0 -> Npos (XO p0)

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Pos.sub_mask n' m' with
          | Pos.IsPos p0 -> Npos p0
          | _ -> N0))

  (** val compare : n -> n -> comparison **)

  let compare n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Eq
             | Npos _ -> Lt)
    | Npos n' -> (match m with
                  | N0 -> Gt
                  | Npos m' -> Pos.compare n' m')

  (** val leb : n -> n -> bool **)

  let leb x0 y =
    match compare x0 y with
    | Gt -> False
    | _ -> True

  (** val pos_div_eucl : positive -> n -> (n, n) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q0, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      (match leb b r' with
       | True -> Pair ((succ_double q0), (sub r' b))
       | False -> Pair ((double q0), r'))
    | XO a' ->
      let Pair (q0, r) = pos_div_eucl a' b in
      let r' = double r in
      (match leb b r' with
       | True -> Pair ((succ_double q0), (sub r' b))
       | False -> Pair ((double q0), r'))
    | XH ->
      (match b with
       | N0 -> Pair (N0, (Npos XH))
       | Npos p0 ->
         (match p0 with
          | XH -> Pair ((Npos XH), N0)
          | _ -> Pair (N0, (Npos XH))))

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p0 -> (match m with
                  | N0 -> n0
                  | Npos q0 -> Npos (Pos.coq_lor p0 q0))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p0 -> (match m with
                  | N0 -> N0
                  | Npos q0 -> Pos.coq_land p0 q0)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p0 -> (match m with
                  | N0 -> n0
                  | Npos q0 -> Pos.coq_lxor p0 q0)

  (** val succ : n -> n **)

  let succ = function
  | N0 -> Npos XH
  | Npos p0 -> Npos (Pos.succ p0)

  (** val pred : n -> n **)

  let pred = function
  | N0 -> N0
  | Npos p0 -> Pos.pred_N p0

  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p0 -> (match m with
                  | N0 -> n0
                  | Npos q0 -> Npos (Coq_Pos.add p0 q0))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p0 -> (match m with
                  | N0 -> N0
                  | Npos q0 -> Npos (Coq_Pos.mul p0 q0))

  (** val eqb : n -> n -> bool **)

  let eqb n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> True
             | Npos _ -> False)
    | Npos p0 -> (match m with
                  | N0 -> False
                  | Npos q0 -> Pos.eqb p0 q0)

  (** val ltb : n -> n -> bool **)

  let ltb x0 y =
    match compare x0 y with
    | Lt -> True
    | _ -> False

  (** val max : n -> n -> n **)

  let max n0 n' =
    match compare n0 n' with
    | Gt -> n0
    | _ -> n'

  (** val div2 : n -> n **)

  let div2 = function
  | N0 -> N0
  | Npos p0 -> (match p0 with
                | XI p1 -> Npos p1
                | XO p1 -> Npos p1
                | XH -> N0)

  (** val pow : n -> n -> n **)

  let pow n0 = function
  | N0 -> Npos XH
  | Npos p1 -> (match n0 with
                | N0 -> N0
                | Npos q0 -> Npos (Coq_Pos.pow q0 p1))

  (** val log2 : n -> n **)

  let log2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p1 -> Npos (Coq_Pos.size p1)
     | XO p1 -> Npos (Coq_Pos.size p1)
     | XH -> N0)

  (** val div_eucl : n -> n -> (n, n) prod **)

  let div_eucl a b =
    match a with
    | N0 -> Pair (N0, N0)
    | Npos na ->
      (match b with
       | N0 -> Pair (N0, a)
       | Npos _ -> pos_div_eucl na b)

  (** val div : n -> n -> n **)

  let div a b =
    fst (div_eucl a b)

  (** val modulo : n -> n -> n **)

  let modulo a b =
    snd (div_eucl a b)

  (** val gcd : n -> n -> n **)

  let gcd a b =
    match a with
    | N0 -> b
    | Npos p0 -> (match b with
                  | N0 -> a
                  | Npos q0 -> Npos (Coq_Pos.gcd p0 q0))

  (** val shiftl : n -> n -> n **)

  let shiftl a n0 =
    match a with
    | N0 -> N0
    | Npos a0 -> Npos (Coq_Pos.shiftl a0 n0)

  (** val shiftr : n -> n -> n **)

  let shiftr a = function
  | N0 -> a
  | Npos p0 -> Pos.iter div2 a p0

  (** val to_nat : n -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p0 -> Pos.to_nat p0

  (** val of_nat : nat -> n **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Pos.of_succ_nat n')

  (** val eq_dec : n -> n -> sumbool **)

  let eq_dec n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> Left
             | Npos _ -> Right)
    | Npos p0 -> (match m with
                  | N0 -> Right
                  | Npos p1 -> Coq_Pos.eq_dec p0 p1)
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val eqb1 : ascii -> ascii -> bool **)

let eqb1 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb0 a0 b0 with
                                       | True -> eqb0 a1 b1
                                       | False -> False with
                                 | True -> eqb0 a2 b2
                                 | False -> False with
                           | True -> eqb0 a3 b3
                           | False -> False with
                     | True -> eqb0 a4 b4
                     | False -> False with
               | True -> eqb0 a5 b5
               | False -> False with
         | True -> eqb0 a6 b6
         | False -> False with
   | True -> eqb0 a7 b7
   | False -> False)

(** val n_of_digits : bool list -> n **)

let rec n_of_digits = function
| Nil -> N0
| Cons (b, l') ->
  N.add (match b with
         | True -> Npos XH
         | False -> N0)
    (N.mul (Npos (XO XH)) (n_of_digits l'))

(** val n_of_ascii : ascii -> n **)

let n_of_ascii = function
| Ascii (a0, a1, a2, a3, a4, a5, a6, a7) ->
  n_of_digits (Cons (a0, (Cons (a1, (Cons (a2, (Cons (a3, (Cons (a4, (Cons
    (a5, (Cons (a6, (Cons (a7, Nil))))))))))))))))

(** val nat_of_ascii : ascii -> nat **)

let nat_of_ascii a =
  N.to_nat (n_of_ascii a)

type string =
| EmptyString
| String of ascii * string

(** val eqb2 : string -> string -> bool **)

let rec eqb2 s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> True
     | String (_, _) -> False)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> False
     | String (c2, s2') ->
       (match eqb1 c1 c2 with
        | True -> eqb2 s1' s2'
        | False -> False))

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p0 -> Zpos (XO p0)
  | Zneg p0 -> Zneg (XO p0)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p0 -> Zpos (XI p0)
  | Zneg p0 -> Zneg (Pos.pred_double p0)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p0 -> Zpos (Pos.pred_double p0)
  | Zneg p0 -> Zneg (XI p0)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x0 y =
    match x0 with
    | XI p0 ->
      (match y with
       | XI q0 -> double (pos_sub p0 q0)
       | XO q0 -> succ_double (pos_sub p0 q0)
       | XH -> Zpos (XO p0))
    | XO p0 ->
      (match y with
       | XI q0 -> pred_double (pos_sub p0 q0)
       | XO q0 -> double (pos_sub p0 q0)
       | XH -> Zpos (Pos.pred_double p0))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x0 y =
    match x0 with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x0
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x0
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x1 -> Zneg x1
  | Zneg x1 -> Zpos x1

  (** val sub : z -> z -> z **)

  let sub m n0 =
    add m (opp n0)

  (** val mul : z -> z -> z **)

  let mul x0 y =
    match x0 with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x0 y =
    match x0 with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val leb : z -> z -> bool **)

  let leb x0 y =
    match compare x0 y with
    | Gt -> False
    | _ -> True

  (** val ltb : z -> z -> bool **)

  let ltb x0 y =
    match compare x0 y with
    | Lt -> True
    | _ -> False

  (** val eqb : z -> z -> bool **)

  let eqb x0 y =
    match x0 with
    | Z0 -> (match y with
             | Z0 -> True
             | _ -> False)
    | Zpos p0 -> (match y with
                  | Zpos q0 -> Pos.eqb p0 q0
                  | _ -> False)
    | Zneg p0 -> (match y with
                  | Zneg q0 -> Pos.eqb p0 q0
                  | _ -> False)

  (** val max : z -> z -> z **)

  let max n0 m =
    match compare n0 m with
    | Lt -> m
    | _ -> n0

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec x0 y =
    match x0 with
    | Z0 -> (match y with
             | Z0 -> Left
             | _ -> Right)
    | Zpos p0 -> (match y with
                  | Zpos p1 -> Coq_Pos.eq_dec p0 p1
                  | _ -> Right)
    | Zneg p0 -> (match y with
                  | Zneg p1 -> Coq_Pos.eq_dec p0 p1
                  | _ -> Right)
 end

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
     | NameStr (b0, t0) ->
       (match name_eqb a0 b0 with
        | True -> eqb2 s t0
        | False -> False)
     | _ -> False)
  | NameNum (a0, n0) ->
    (match b with
     | NameNum (b0, m) ->
       (match name_eqb a0 b0 with
        | True -> N.eqb n0 m
        | False -> False)
     | _ -> False)

(** val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eqb eqb3 xs ys =
  match xs with
  | Nil -> (match ys with
            | Nil -> True
            | Cons (_, _) -> False)
  | Cons (x0, xs0) ->
    (match ys with
     | Nil -> False
     | Cons (y, ys0) ->
       (match eqb3 x0 y with
        | True -> list_eqb eqb3 xs0 ys0
        | False -> False))

(** val name_mem : name -> name list -> bool **)

let name_mem n0 ns =
  existsb (name_eqb n0) ns

(** val names_unique : name list -> bool **)

let rec names_unique = function
| Nil -> True
| Cons (n0, ns0) ->
  (match negb (name_mem n0 ns0) with
   | True -> names_unique ns0
   | False -> False)

type level =
| LZero
| LSucc of level
| LMax of level * level
| LIMax of level * level
| LParam of name
| LMVar of name

(** val level_eqb : level -> level -> bool **)

let rec level_eqb u0 v0 =
  match u0 with
  | LZero -> (match v0 with
              | LZero -> True
              | _ -> False)
  | LSucc u1 -> (match v0 with
                 | LSucc v1 -> level_eqb u1 v1
                 | _ -> False)
  | LMax (a, b) ->
    (match v0 with
     | LMax (c, d) ->
       (match level_eqb a c with
        | True -> level_eqb b d
        | False -> False)
     | _ -> False)
  | LIMax (a, b) ->
    (match v0 with
     | LIMax (c, d) ->
       (match level_eqb a c with
        | True -> level_eqb b d
        | False -> False)
     | _ -> False)
  | LParam a -> (match v0 with
                 | LParam b -> name_eqb a b
                 | _ -> False)
  | LMVar a -> (match v0 with
                | LMVar b -> name_eqb a b
                | _ -> False)

(** val level_wf : name list -> level -> bool **)

let rec level_wf ps = function
| LZero -> True
| LSucc v0 -> level_wf ps v0
| LMax (a, b) ->
  (match level_wf ps a with
   | True -> level_wf ps b
   | False -> False)
| LIMax (a, b) ->
  (match level_wf ps a with
   | True -> level_wf ps b
   | False -> False)
| LParam n0 -> name_mem n0 ps
| LMVar _ -> False

(** val level_has_meta : level -> bool **)

let rec level_has_meta = function
| LSucc v0 -> level_has_meta v0
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

(** val lookup_level : name list -> level list -> name -> level **)

let rec lookup_level ps us n0 =
  match ps with
  | Nil -> LParam n0
  | Cons (p0, ps0) ->
    (match us with
     | Nil -> LParam n0
     | Cons (u0, us0) ->
       (match name_eqb p0 n0 with
        | True -> u0
        | False -> lookup_level ps0 us0 n0))

(** val subst_level : name list -> level list -> level -> level **)

let rec subst_level ps us = function
| LSucc v0 -> LSucc (subst_level ps us v0)
| LMax (a, b) -> LMax ((subst_level ps us a), (subst_level ps us b))
| LIMax (a, b) -> LIMax ((subst_level ps us a), (subst_level ps us b))
| LParam n0 -> lookup_level ps us n0
| x0 -> x0

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

(** val literal_eqb : literal -> literal -> bool **)

let literal_eqb a b =
  match a with
  | LitNat n0 -> (match b with
                  | LitNat m -> N.eqb n0 m
                  | LitString _ -> False)
  | LitString s ->
    (match b with
     | LitNat _ -> False
     | LitString t0 -> eqb2 s t0)

(** val expr_eqb : expr -> expr -> bool **)

let rec expr_eqb a b =
  match a with
  | EBVar n0 -> (match b with
                 | EBVar m -> Nat.eqb n0 m
                 | _ -> False)
  | EFVar n0 -> (match b with
                 | EFVar m -> name_eqb n0 m
                 | _ -> False)
  | EMVar n0 -> (match b with
                 | EMVar m -> name_eqb n0 m
                 | _ -> False)
  | ESort u0 -> (match b with
                 | ESort v0 -> level_eqb u0 v0
                 | _ -> False)
  | EConst (n0, us) ->
    (match b with
     | EConst (m, vs) ->
       (match name_eqb n0 m with
        | True -> list_eqb level_eqb us vs
        | False -> False)
     | _ -> False)
  | EApp (f, x0) ->
    (match b with
     | EApp (g, y) ->
       (match expr_eqb f g with
        | True -> expr_eqb x0 y
        | False -> False)
     | _ -> False)
  | ELam (_, _, a0, b0) ->
    (match b with
     | ELam (_, _, c, d) ->
       (match expr_eqb a0 c with
        | True -> expr_eqb b0 d
        | False -> False)
     | _ -> False)
  | EPi (_, _, a0, b0) ->
    (match b with
     | EPi (_, _, c, d) ->
       (match expr_eqb a0 c with
        | True -> expr_eqb b0 d
        | False -> False)
     | _ -> False)
  | ELet (_, a0, v0, b0, _) ->
    (match b with
     | ELet (_, c, w, d, _) ->
       (match match expr_eqb a0 c with
              | True -> expr_eqb v0 w
              | False -> False with
        | True -> expr_eqb b0 d
        | False -> False)
     | _ -> False)
  | ELit l -> (match b with
               | ELit k -> literal_eqb l k
               | _ -> False)
  | EProj (n0, i, a0) ->
    (match b with
     | EProj (m, j, b0) ->
       (match match name_eqb n0 m with
              | True -> Nat.eqb i j
              | False -> False with
        | True -> expr_eqb a0 b0
        | False -> False)
     | _ -> False)
  | EMData a0 -> (match b with
                  | EMData b0 -> expr_eqb a0 b0
                  | _ -> False)

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
| ELet (n0, a, v0, b, nd) ->
  ELet (n0, (lift amount cutoff a), (lift amount cutoff v0),
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
| ELet (n0, a, v0, b, nd) ->
  ELet (n0, (subst index value a), (subst index value v0),
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
| ELet (n0, a, v0, b, nd) ->
  ELet (n0, (subst_many index values a), (subst_many index values v0),
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
| ESort u0 -> ESort (subst_level ps us u0)
| EConst (n0, vs) -> EConst (n0, (map (subst_level ps us) vs))
| EApp (f, a) -> EApp ((subst_levels ps us f), (subst_levels ps us a))
| ELam (n0, bi, a, b) ->
  ELam (n0, bi, (subst_levels ps us a), (subst_levels ps us b))
| EPi (n0, bi, a, b) ->
  EPi (n0, bi, (subst_levels ps us a), (subst_levels ps us b))
| ELet (n0, a, v0, b, nd) ->
  ELet (n0, (subst_levels ps us a), (subst_levels ps us v0),
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
| ELet (_, a, v0, b, _) ->
  (match match scoped depth a with
         | True -> scoped depth v0
         | False -> False with
   | True -> scoped (S depth) b
   | False -> False)
| EProj (_, _, a) -> scoped depth a
| EMData a -> scoped depth a
| _ -> True

type binding = { binding_type : expr; binding_value : expr option }

type context = { bound_context : binding list;
                 free_context : (name, binding) prod list }

(** val empty_context : context **)

let empty_context =
  { bound_context = Nil; free_context = Nil }

(** val push_binding : context -> expr -> expr option -> context **)

let push_binding g ty0 value =
  { bound_context = (Cons ({ binding_type = ty0; binding_value = value },
    g.bound_context)); free_context = g.free_context }

(** val find_free : name -> (name, binding) prod list -> binding option **)

let rec find_free n0 = function
| Nil -> None
| Cons (p0, xs0) ->
  let Pair (m, b) = p0 in
  (match name_eqb n0 m with
   | True -> Some b
   | False -> find_free n0 xs0)

type inductive_data = { ind_num_params : nat; ind_num_indices : nat;
                        ind_all : name list; ind_ctors : name list;
                        ind_num_nested : nat; ind_is_rec : bool;
                        ind_is_reflexive : bool; ind_is_unsafe : bool }

type constructor_data = { ctor_induct : name; ctor_index : nat;
                          ctor_num_params : nat; ctor_num_fields : nat;
                          ctor_is_unsafe : bool }

type recursor_rule = { rule_ctor : name; rule_nfields : nat; rule_rhs : expr }

type recursor_data = { rec_all : name list; rec_num_params : nat;
                       rec_num_indices : nat; rec_num_motives : nat;
                       rec_num_minors : nat; rec_rules : recursor_rule list;
                       rec_k : bool; rec_is_unsafe : bool }

type primitive_kind =
| PNatAdd
| PNatPred
| PNatSub
| PNatMul
| PNatPow
| PNatGcd
| PNatMod
| PNatDiv
| PNatBEq
| PNatBLE
| PNatLAnd
| PNatLOr
| PNatXor
| PNatBitwise
| PNatShiftLeft
| PNatShiftRight
| PCharOfNat
| PStringOfList

(** val primitive_kind_eqb : primitive_kind -> primitive_kind -> bool **)

let primitive_kind_eqb a b =
  match a with
  | PNatAdd -> (match b with
                | PNatAdd -> True
                | _ -> False)
  | PNatPred -> (match b with
                 | PNatPred -> True
                 | _ -> False)
  | PNatSub -> (match b with
                | PNatSub -> True
                | _ -> False)
  | PNatMul -> (match b with
                | PNatMul -> True
                | _ -> False)
  | PNatPow -> (match b with
                | PNatPow -> True
                | _ -> False)
  | PNatGcd -> (match b with
                | PNatGcd -> True
                | _ -> False)
  | PNatMod -> (match b with
                | PNatMod -> True
                | _ -> False)
  | PNatDiv -> (match b with
                | PNatDiv -> True
                | _ -> False)
  | PNatBEq -> (match b with
                | PNatBEq -> True
                | _ -> False)
  | PNatBLE -> (match b with
                | PNatBLE -> True
                | _ -> False)
  | PNatLAnd -> (match b with
                 | PNatLAnd -> True
                 | _ -> False)
  | PNatLOr -> (match b with
                | PNatLOr -> True
                | _ -> False)
  | PNatXor -> (match b with
                | PNatXor -> True
                | _ -> False)
  | PNatBitwise -> (match b with
                    | PNatBitwise -> True
                    | _ -> False)
  | PNatShiftLeft -> (match b with
                      | PNatShiftLeft -> True
                      | _ -> False)
  | PNatShiftRight -> (match b with
                       | PNatShiftRight -> True
                       | _ -> False)
  | PCharOfNat -> (match b with
                   | PCharOfNat -> True
                   | _ -> False)
  | PStringOfList -> (match b with
                      | PStringOfList -> True
                      | _ -> False)

type quotient_kind =
| QType
| QCtor
| QLift
| QInd

type decl_kind =
| DAssumption
| DDefinition
| DTheorem
| DOpaque
| DUnsupported
| DInductive of inductive_data
| DConstructor of constructor_data
| DRecursor of recursor_data
| DPrimitive of primitive_kind
| DQuotient of quotient_kind
| DUnsafe of decl_kind
| DPartial

type reducibility_hints =
| HintOpaque
| HintAbbrev
| HintRegular of n

(** val hints_lt : reducibility_hints -> reducibility_hints -> bool **)

let hints_lt a b =
  match a with
  | HintOpaque -> (match b with
                   | HintOpaque -> False
                   | _ -> True)
  | HintAbbrev -> False
  | HintRegular n0 ->
    (match b with
     | HintOpaque -> False
     | HintAbbrev -> True
     | HintRegular m -> N.ltb n0 m)

type declaration = { decl_name : name; decl_params : name list;
                     decl_type : expr; decl_value : expr option;
                     decl_kind_of : decl_kind; decl_hints : reducibility_hints }

(** val effective_hints : declaration -> reducibility_hints **)

let effective_hints d =
  match d.decl_kind_of with
  | DDefinition -> d.decl_hints
  | DPrimitive _ -> d.decl_hints
  | _ -> HintOpaque

type environment = declaration list

(** val find_decl : name -> environment -> declaration option **)

let rec find_decl n0 = function
| Nil -> None
| Cons (d, env0) ->
  (match name_eqb n0 d.decl_name with
   | True -> Some d
   | False -> find_decl n0 env0)

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

(** val require : bool -> reject_reason -> unit0 result **)

let require b err =
  match b with
  | True -> Accept Tt
  | False -> Reject err

(** val instantiate_levels : name list -> level list -> expr -> expr **)

let instantiate_levels ps us e =
  match ps with
  | Nil -> e
  | Cons (_, _) -> subst_levels ps us e

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

let rec normalize_aux fuel0 u0 path k =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    (match u0 with
     | LZero -> Accept (const_atom path k)
     | LSucc v0 -> normalize_aux fuel1 v0 path (S k)
     | LMax (a, b) ->
       combine_levels (normalize_aux fuel1 a path k)
         (normalize_aux fuel1 b path k)
     | LIMax (a, b) ->
       (match b with
        | LZero -> Accept (const_atom path k)
        | LSucc v0 ->
          combine_levels (normalize_aux fuel1 a path k)
            (normalize_aux fuel1 v0 path (S k))
        | LMax (v0, w) ->
          combine_levels (normalize_aux fuel1 (LIMax (a, v0)) path k)
            (normalize_aux fuel1 (LIMax (a, w)) path k)
        | LIMax (v0, w) ->
          combine_levels (normalize_aux fuel1 (LIMax (a, w)) path k)
            (normalize_aux fuel1 (LIMax (v0, w)) path k)
        | LParam n0 ->
          let path' = guard_insert n0 path in
          bind (normalize_aux fuel1 a path' k) (fun xs -> Accept
            (app (const_atom path k) (Cons ((SubVar (path', n0, k)), xs))))
        | LMVar _ -> Reject MetaVariable)
     | LParam n0 ->
       Accept
         (app (const_atom path k) (Cons ((SubVar ((guard_insert n0 path), n0,
           k)), Nil)))
     | LMVar _ -> Reject MetaVariable)

(** val normalize_level : nat -> level -> sublevel list result **)

let normalize_level fuel0 u0 =
  match level_has_meta u0 with
  | True -> Reject MetaVariable
  | False -> normalize_aux fuel0 u0 Nil O

(** val guard_subset : name list -> name list -> bool **)

let guard_subset xs ys =
  forallb (fun x0 -> name_mem x0 ys) xs

(** val sublevel_le : sublevel -> sublevel -> bool **)

let sublevel_le a b =
  match a with
  | SubConst (p0, k) ->
    (match b with
     | SubConst (q0, j) ->
       (match guard_subset q0 p0 with
        | True -> Nat.leb k j
        | False -> False)
     | SubVar (q0, n0, j) ->
       (match match guard_subset q0 p0 with
              | True -> name_mem n0 q0
              | False -> False with
        | True -> Nat.leb k (S j)
        | False -> False))
  | SubVar (p0, n0, k) ->
    (match b with
     | SubConst (_, _) -> False
     | SubVar (q0, m, j) ->
       (match match guard_subset q0 p0 with
              | True -> name_eqb n0 m
              | False -> False with
        | True -> Nat.leb k j
        | False -> False))

(** val sublevels_le : sublevel list -> sublevel list -> bool **)

let sublevels_le xs ys =
  forallb (fun x0 -> existsb (sublevel_le x0) ys) xs

(** val level_le : nat -> level -> level -> bool result **)

let level_le fuel0 u0 v0 =
  bind (normalize_level fuel0 u0) (fun xs ->
    bind (normalize_level fuel0 v0) (fun ys -> Accept (sublevels_le xs ys)))

(** val level_equiv : nat -> level -> level -> bool result **)

let level_equiv fuel0 u0 v0 =
  bind (normalize_level fuel0 u0) (fun xs ->
    bind (normalize_level fuel0 v0) (fun ys -> Accept
      (match sublevels_le xs ys with
       | True -> sublevels_le ys xs
       | False -> False)))

(** val levels_equiv : nat -> level list -> level list -> bool result **)

let rec levels_equiv fuel0 us vs =
  match us with
  | Nil -> (match vs with
            | Nil -> Accept True
            | Cons (_, _) -> Accept False)
  | Cons (u0, us0) ->
    (match vs with
     | Nil -> Accept False
     | Cons (v0, vs0) ->
       bind (level_equiv fuel0 u0 v0) (fun b ->
         match b with
         | True -> levels_equiv fuel0 us0 vs0
         | False -> Accept False))

type reduction_mode =
| NormalReduction
| EagerReduction

(** val has_external_local_at : nat -> expr -> bool **)

let rec has_external_local_at depth = function
| EBVar i -> negb (Nat.ltb i depth)
| EFVar _ -> True
| EApp (a, b) ->
  (match has_external_local_at depth a with
   | True -> True
   | False -> has_external_local_at depth b)
| ELam (_, _, a, b) ->
  (match has_external_local_at depth a with
   | True -> True
   | False -> has_external_local_at (S depth) b)
| EPi (_, _, a, b) ->
  (match has_external_local_at depth a with
   | True -> True
   | False -> has_external_local_at (S depth) b)
| ELet (_, a, v0, b, _) ->
  (match match has_external_local_at depth a with
         | True -> True
         | False -> has_external_local_at depth v0 with
   | True -> True
   | False -> has_external_local_at (S depth) b)
| EProj (_, _, a) -> has_external_local_at depth a
| EMData a -> has_external_local_at depth a
| _ -> False

(** val has_external_local : expr -> bool **)

let has_external_local =
  has_external_local_at O

(** val nat_probe_allowed : reduction_mode -> expr -> expr -> bool **)

let nat_probe_allowed mode t0 s =
  match mode with
  | NormalReduction ->
    (match negb (has_external_local t0) with
     | True -> negb (has_external_local s)
     | False -> False)
  | EagerReduction -> True

(** val true_probe_allowed : reduction_mode -> expr -> bool **)

let true_probe_allowed mode t0 =
  match mode with
  | NormalReduction -> negb (has_external_local t0)
  | EagerReduction -> True

(** val eager_reduce_name : name **)

let eager_reduce_name =
  NameStr (NameAnon, (String ((Ascii (True, False, True, False, False, True,
    True, False)), (String ((Ascii (True, False, False, False, False, True,
    True, False)), (String ((Ascii (True, True, True, False, False, True,
    True, False)), (String ((Ascii (True, False, True, False, False, True,
    True, False)), (String ((Ascii (False, True, False, False, True, True,
    True, False)), (String ((Ascii (False, True, False, False, True, False,
    True, False)), (String ((Ascii (True, False, True, False, False, True,
    True, False)), (String ((Ascii (False, False, True, False, False, True,
    True, False)), (String ((Ascii (True, False, True, False, True, True,
    True, False)), (String ((Ascii (True, True, False, False, False, True,
    True, False)), (String ((Ascii (True, False, True, False, False, True,
    True, False)), EmptyString)))))))))))))))))))))))

(** val is_eager_reduce_argument : expr -> bool **)

let is_eager_reduce_argument = function
| EApp (e0, _) ->
  (match e0 with
   | EApp (e2, _) ->
     (match e2 with
      | EConst (n0, _) -> name_eqb n0 eager_reduce_name
      | _ -> False)
   | _ -> False)
| _ -> False

(** val nat_probe_head :
    (name -> environment -> declaration option) -> name -> environment ->
    (expr, expr list) prod -> bool **)

let nat_probe_head resolve succ_name env = function
| Pair (head, args) ->
  (match head with
   | EConst (n0, l) ->
     (match l with
      | Nil ->
        (match args with
         | Nil -> False
         | Cons (_, l0) ->
           (match l0 with
            | Nil ->
              (match name_eqb n0 succ_name with
               | True -> True
               | False ->
                 (match resolve n0 env with
                  | Some d ->
                    (match d.decl_kind_of with
                     | DPrimitive p0 ->
                       (match p0 with
                        | PNatPred -> True
                        | _ -> False)
                     | _ -> False)
                  | None -> False))
            | Cons (_, l1) ->
              (match l1 with
               | Nil ->
                 (match resolve n0 env with
                  | Some d ->
                    (match d.decl_kind_of with
                     | DPrimitive p0 ->
                       (match p0 with
                        | PNatBitwise -> False
                        | _ -> True)
                     | _ -> False)
                  | None -> False)
               | Cons (_, _) -> False)))
      | Cons (_, _) -> False)
   | _ -> False)

(** val pair_probe_guard : bool -> bool -> (unit0 -> bool) -> bool **)

let pair_probe_guard left right eligible =
  match match left with
        | True -> True
        | False -> right with
  | True -> eligible Tt
  | False -> False

(** val normal_whnf_rounds : nat **)

let normal_whnf_rounds =
  of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 (D0 Nil0)))))))

(** val eager_whnf_rounds : nat **)

let eager_whnf_rounds =
  of_num_uint (UIntDecimal (D1 (D0 (D0 (D0 (D0 (D0 (D0 Nil0))))))))

(** val whnf_round_limit : reduction_mode -> nat **)

let whnf_round_limit = function
| NormalReduction -> normal_whnf_rounds
| EagerReduction -> eager_whnf_rounds

type whnf_round =
| WhnfDone of expr
| WhnfContinue of expr

(** val run_whnf_rounds :
    nat -> (expr -> whnf_round result) -> expr -> expr result **)

let rec run_whnf_rounds rounds step e =
  match rounds with
  | O -> Decline OutOfFuel
  | S remaining ->
    bind (step e) (fun round ->
      match round with
      | WhnfDone value -> Accept value
      | WhnfContinue value -> run_whnf_rounds remaining step value)

(** val core_name : string -> name **)

let core_name s =
  NameStr (NameAnon, s)

(** val core_nat_name : name **)

let core_nat_name =
  core_name (String ((Ascii (False, True, True, True, False, False, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))

(** val core_zero_name : name **)

let core_zero_name =
  NameStr (core_nat_name, (String ((Ascii (False, True, False, True, True,
    True, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), (String ((Ascii (False, True, False, False, True,
    True, True, False)), (String ((Ascii (True, True, True, True, False,
    True, True, False)), EmptyString)))))))))

(** val core_succ_name : name **)

let core_succ_name =
  NameStr (core_nat_name, (String ((Ascii (True, True, False, False, True,
    True, True, False)), (String ((Ascii (True, False, True, False, True,
    True, True, False)), (String ((Ascii (True, True, False, False, False,
    True, True, False)), (String ((Ascii (True, True, False, False, False,
    True, True, False)), EmptyString)))))))))

(** val core_bool_name : name **)

let core_bool_name =
  core_name (String ((Ascii (False, True, False, False, False, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), EmptyString))))))))

(** val core_false_name : name **)

let core_false_name =
  NameStr (core_bool_name, (String ((Ascii (False, True, True, False, False,
    True, True, False)), (String ((Ascii (True, False, False, False, False,
    True, True, False)), (String ((Ascii (False, False, True, True, False,
    True, True, False)), (String ((Ascii (True, True, False, False, True,
    True, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), EmptyString)))))))))))

(** val core_true_name : name **)

let core_true_name =
  NameStr (core_bool_name, (String ((Ascii (False, False, True, False, True,
    True, True, False)), (String ((Ascii (False, True, False, False, True,
    True, True, False)), (String ((Ascii (True, False, True, False, True,
    True, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), EmptyString)))))))))

(** val core_char_name : name **)

let core_char_name =
  core_name (String ((Ascii (True, True, False, False, False, False, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))

(** val core_char_of_nat : name **)

let core_char_of_nat =
  NameStr (core_char_name, (String ((Ascii (True, True, True, True, False,
    True, True, False)), (String ((Ascii (False, True, True, False, False,
    True, True, False)), (String ((Ascii (False, True, True, True, False,
    False, True, False)), (String ((Ascii (True, False, False, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), EmptyString)))))))))))

(** val core_string_name : name **)

let core_string_name =
  core_name (String ((Ascii (True, True, False, False, True, False, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, False, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), EmptyString))))))))))))

(** val core_string_of_list : name **)

let core_string_of_list =
  NameStr (core_string_name, (String ((Ascii (True, True, True, True, False,
    True, True, False)), (String ((Ascii (False, True, True, False, False,
    True, True, False)), (String ((Ascii (False, False, True, True, False,
    False, True, False)), (String ((Ascii (True, False, False, True, False,
    True, True, False)), (String ((Ascii (True, True, False, False, True,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), EmptyString)))))))))))))

(** val core_list_name : name **)

let core_list_name =
  core_name (String ((Ascii (False, False, True, True, False, False, True,
    False)), (String ((Ascii (True, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))

(** val core_nat : expr **)

let core_nat =
  EConst (core_nat_name, Nil)

(** val core_spine : expr -> expr list -> (expr, expr list) prod **)

let rec core_spine e args =
  match e with
  | EApp (f, a) -> core_spine f (Cons (a, args))
  | _ -> Pair (e, args)

(** val core_apps : expr -> expr list -> expr **)

let core_apps e args =
  fold_left (fun x0 x1 -> EApp (x0, x1)) args e

(** val core_occurs : nat -> expr -> bool **)

let rec core_occurs index = function
| EBVar i -> Nat.eqb i index
| EApp (a, b) ->
  (match core_occurs index a with
   | True -> True
   | False -> core_occurs index b)
| ELam (_, _, a, b) ->
  (match core_occurs index a with
   | True -> True
   | False -> core_occurs (S index) b)
| EPi (_, _, a, b) ->
  (match core_occurs index a with
   | True -> True
   | False -> core_occurs (S index) b)
| ELet (_, a, v0, b, _) ->
  (match match core_occurs index a with
         | True -> True
         | False -> core_occurs index v0 with
   | True -> True
   | False -> core_occurs (S index) b)
| EProj (_, _, a) -> core_occurs index a
| EMData a -> core_occurs index a
| _ -> False

(** val core_level_positive : level -> bool **)

let rec core_level_positive = function
| LSucc _ -> True
| LMax (a, b) ->
  (match core_level_positive a with
   | True -> True
   | False -> core_level_positive b)
| LIMax (_, b) -> core_level_positive b
| _ -> False

(** val core_inductive : environment -> name -> inductive_data option **)

let core_inductive env n0 =
  match find_decl n0 env with
  | Some d -> (match d.decl_kind_of with
               | DInductive i -> Some i
               | _ -> None)
  | None -> None

(** val core_constructor : environment -> name -> constructor_data option **)

let core_constructor env n0 =
  match find_decl n0 env with
  | Some d -> (match d.decl_kind_of with
               | DConstructor i -> Some i
               | _ -> None)
  | None -> None

(** val core_structure : environment -> name -> bool **)

let core_structure env n0 =
  match core_inductive env n0 with
  | Some i ->
    (match match negb i.ind_is_rec with
           | True -> Nat.eqb i.ind_num_indices O
           | False -> False with
     | True -> Nat.eqb (length i.ind_ctors) (S O)
     | False -> False)
  | None -> False

(** val core_ctor_shape :
    environment -> name -> name -> nat -> nat -> expr -> bool **)

let core_ctor_shape env n0 parent index fields ty0 =
  match find_decl n0 env with
  | Some d ->
    (match d.decl_kind_of with
     | DConstructor c ->
       (match match match match match match name_eqb c.ctor_induct parent with
                                      | True -> Nat.eqb c.ctor_index index
                                      | False -> False with
                                | True -> Nat.eqb c.ctor_num_params O
                                | False -> False with
                          | True -> Nat.eqb c.ctor_num_fields fields
                          | False -> False with
                    | True -> negb c.ctor_is_unsafe
                    | False -> False with
              | True -> Nat.eqb (length d.decl_params) O
              | False -> False with
        | True -> expr_eqb d.decl_type ty0
        | False -> False)
     | _ -> False)
  | None -> False

(** val core_nat_ready : environment -> bool **)

let core_nat_ready env =
  match find_decl core_nat_name env with
  | Some d ->
    (match d.decl_kind_of with
     | DInductive i ->
       (match match match match match match match Nat.eqb
                                                    (length d.decl_params) O with
                                            | True ->
                                              expr_eqb d.decl_type (ESort
                                                (LSucc LZero))
                                            | False -> False with
                                      | True -> Nat.eqb i.ind_num_params O
                                      | False -> False with
                                | True -> Nat.eqb i.ind_num_indices O
                                | False -> False with
                          | True -> negb i.ind_is_unsafe
                          | False -> False with
                    | True ->
                      list_eqb name_eqb i.ind_ctors (Cons (core_zero_name,
                        (Cons (core_succ_name, Nil))))
                    | False -> False with
              | True ->
                core_ctor_shape env core_zero_name core_nat_name O O core_nat
              | False -> False with
        | True ->
          core_ctor_shape env core_succ_name core_nat_name (S O) (S O) (EPi
            (NameAnon, BDefault, core_nat, core_nat))
        | False -> False)
     | _ -> False)
  | None -> False

(** val core_bool_ready : environment -> bool **)

let core_bool_ready env =
  match find_decl core_bool_name env with
  | Some d ->
    (match d.decl_kind_of with
     | DInductive i ->
       (match match match match match match match Nat.eqb
                                                    (length d.decl_params) O with
                                            | True ->
                                              expr_eqb d.decl_type (ESort
                                                (LSucc LZero))
                                            | False -> False with
                                      | True -> Nat.eqb i.ind_num_params O
                                      | False -> False with
                                | True -> Nat.eqb i.ind_num_indices O
                                | False -> False with
                          | True -> negb i.ind_is_unsafe
                          | False -> False with
                    | True ->
                      list_eqb name_eqb i.ind_ctors (Cons (core_false_name,
                        (Cons (core_true_name, Nil))))
                    | False -> False with
              | True ->
                core_ctor_shape env core_false_name core_bool_name O O
                  (EConst (core_bool_name, Nil))
              | False -> False with
        | True ->
          core_ctor_shape env core_true_name core_bool_name (S O) O (EConst
            (core_bool_name, Nil))
        | False -> False)
     | _ -> False)
  | None -> False

(** val core_string_ready : environment -> bool **)

let core_string_ready env =
  match find_decl core_char_of_nat env with
  | Some c ->
    (match find_decl core_string_of_list env with
     | Some s ->
       (match c.decl_kind_of with
        | DPrimitive p0 ->
          (match p0 with
           | PCharOfNat ->
             (match s.decl_kind_of with
              | DPrimitive p1 ->
                (match p1 with
                 | PStringOfList -> core_nat_ready env
                 | _ -> False)
              | _ -> False)
           | _ -> False)
        | _ -> False)
     | None -> False)
  | None -> False

(** val core_supported : environment -> expr -> bool **)

let rec core_supported env = function
| EApp (a, b) ->
  (match core_supported env a with
   | True -> core_supported env b
   | False -> False)
| ELam (_, _, a, b) ->
  (match core_supported env a with
   | True -> core_supported env b
   | False -> False)
| EPi (_, _, a, b) ->
  (match core_supported env a with
   | True -> core_supported env b
   | False -> False)
| ELet (_, a, v0, b, _) ->
  (match match core_supported env a with
         | True -> core_supported env v0
         | False -> False with
   | True -> core_supported env b
   | False -> False)
| ELit l ->
  (match l with
   | LitNat _ -> core_nat_ready env
   | LitString _ -> core_string_ready env)
| EProj (n0, _, a) ->
  (match core_inductive env n0 with
   | Some _ -> core_supported env a
   | None -> False)
| EMData a -> core_supported env a
| _ -> True

(** val check_level : name list -> level -> unit0 result **)

let check_level ps u0 =
  match level_has_meta u0 with
  | True -> Reject MetaVariable
  | False -> require (level_wf ps u0) UnknownUniverse

(** val check_levels : name list -> level list -> unit0 result **)

let rec check_levels ps = function
| Nil -> Accept Tt
| Cons (u0, us0) -> bind (check_level ps u0) (fun _ -> check_levels ps us0)

(** val get_constant :
    environment -> name list -> name -> level list -> declaration result **)

let get_constant env ps n0 us =
  match find_decl n0 env with
  | Some d ->
    (match d.decl_kind_of with
     | DUnsupported -> Decline UnsupportedDeclaration
     | DUnsafe _ -> Reject MalformedDeclaration
     | DPartial -> Reject MalformedDeclaration
     | _ ->
       bind
         (require (Nat.eqb (length d.decl_params) (length us)) UniverseArity)
         (fun _ -> bind (check_levels ps us) (fun _ -> Accept d)))
  | None -> Reject UnknownConstant

type methods = { infer_method : (context -> expr -> expr result);
                 infer_type_method : (context -> expr -> expr result);
                 whnf_method : (context -> expr -> expr result);
                 whnf_core_method : (bool -> context -> expr -> expr result);
                 defeq_method : (context -> expr -> expr -> bool result);
                 method_mode : reduction_mode;
                 eager_defeq_method : (context -> expr -> expr -> bool result) }

(** val inference_only : methods -> methods **)

let inference_only rec0 =
  { infer_method = rec0.infer_type_method; infer_type_method =
    rec0.infer_type_method; whnf_method = rec0.whnf_method;
    whnf_core_method = rec0.whnf_core_method; defeq_method =
    rec0.defeq_method; method_mode = rec0.method_mode; eager_defeq_method =
    rec0.eager_defeq_method }

(** val application_type_defeq :
    methods -> context -> expr -> expr -> expr -> bool result **)

let application_type_defeq rec0 g argument domain argument_type =
  match is_eager_reduce_argument argument with
  | True -> rec0.eager_defeq_method g domain argument_type
  | False -> rec0.defeq_method g domain argument_type

(** val sort_of : methods -> context -> expr -> level result **)

let sort_of rec0 g e =
  bind (rec0.infer_method g e) (fun t0 ->
    bind (rec0.whnf_method g t0) (fun t1 ->
      match t1 with
      | ESort u0 -> Accept u0
      | _ -> Reject ExpectedSort))

(** val core_apply_type :
    methods -> context -> expr -> expr list -> expr result **)

let rec core_apply_type rec0 g ty0 = function
| Nil -> Accept ty0
| Cons (a, args0) ->
  bind (rec0.whnf_method g ty0) (fun ty1 ->
    match ty1 with
    | EPi (_, _, _, body) -> core_apply_type rec0 g (instantiate body a) args0
    | _ -> Reject ExpectedPi)

(** val core_projection_field :
    methods -> nat -> context -> name -> expr -> bool -> nat -> nat -> expr
    -> expr result **)

let rec core_projection_field rec0 fuel0 g owner value maybe_prop skip index ty0 =
  bind (rec0.whnf_method g ty0) (fun reduced ->
    match reduced with
    | EPi (_, _, domain, body) ->
      let verify_prop = fun _ ->
        bind (sort_of rec0 g domain) (fun u0 ->
          bind (level_equiv fuel0 u0 LZero) (fun ok ->
            require ok TypeMismatch))
      in
      (match skip with
       | O ->
         bind
           (match maybe_prop with
            | True -> verify_prop Tt
            | False -> Accept Tt)
           (fun _ -> Accept domain)
       | S skip0 ->
         bind
           (match match maybe_prop with
                  | True -> core_occurs O body
                  | False -> False with
            | True -> verify_prop Tt
            | False -> Accept Tt)
           (fun _ ->
           core_projection_field rec0 fuel0 g owner value maybe_prop skip0 (S
             index) (instantiate body (EProj (owner, index, value)))))
    | _ -> Reject ExpectedPi)

(** val core_infer_projection :
    methods -> nat -> environment -> context -> name -> nat -> expr -> expr
    result **)

let core_infer_projection rec0 fuel0 env g owner index value =
  bind (rec0.infer_method g value) (fun st ->
    bind (rec0.whnf_method g st) (fun st0 ->
      let Pair (head, args) = core_spine st0 Nil in
      (match head with
       | EConst (n0, us) ->
         (match core_inductive env owner with
          | Some info ->
            bind
              (require
                (match name_eqb n0 owner with
                 | True ->
                   Nat.eqb (length args)
                     (add info.ind_num_params info.ind_num_indices)
                 | False -> False)
                TypeMismatch)
              (fun _ ->
              match info.ind_ctors with
              | Nil -> Reject TypeMismatch
              | Cons (ctor, l) ->
                (match l with
                 | Nil ->
                   (match find_decl ctor env with
                    | Some d ->
                      (match d.decl_kind_of with
                       | DConstructor c ->
                         bind
                           (require (Nat.ltb index c.ctor_num_fields)
                             TypeMismatch)
                           (fun _ ->
                           bind
                             (core_apply_type rec0 g
                               (subst_levels d.decl_params us d.decl_type)
                               (firstn info.ind_num_params args))
                             (fun ty0 ->
                             bind (sort_of rec0 g st0) (fun u0 ->
                               core_projection_field rec0 fuel0 g owner value
                                 (negb (core_level_positive u0)) index O ty0)))
                       | _ -> Reject MalformedDeclaration)
                    | None -> Reject UnknownConstant)
                 | Cons (_, _) -> Reject TypeMismatch))
          | None -> Reject TypeMismatch)
       | _ -> Reject TypeMismatch)))

(** val core_nat_value : expr -> n option **)

let core_nat_value = function
| EConst (n0, l) ->
  (match l with
   | Nil ->
     (match name_eqb n0 core_zero_name with
      | True -> Some N0
      | False -> None)
   | Cons (_, _) -> None)
| ELit l -> (match l with
             | LitNat n0 -> Some n0
             | LitString _ -> None)
| _ -> None

(** val core_nat_constructor : n -> expr **)

let core_nat_constructor n0 = match n0 with
| N0 -> EConst (core_zero_name, Nil)
| Npos _ -> EApp ((EConst (core_succ_name, Nil)), (ELit (LitNat (N.pred n0))))

(** val core_shiftr : nat -> n -> n -> n result **)

let core_shiftr fuel0 a b =
  match N.ltb (N.log2 a) b with
  | True -> Accept N0
  | False ->
    (match N.leb b (N.of_nat fuel0) with
     | True -> Accept (N.shiftr a b)
     | False -> Decline OutOfFuel)

(** val core_binary_nat :
    nat -> environment -> primitive_kind -> n -> n -> expr option result **)

let core_binary_nat fuel0 env op a b =
  let numeric = fun n0 -> Accept (Some (ELit (LitNat n0))) in
  let bounded = fun operation ->
    match N.leb b (N.of_nat fuel0) with
    | True -> numeric (operation a b)
    | False -> Decline OutOfFuel
  in
  let boolean = fun b0 ->
    match core_bool_ready env with
    | True ->
      Accept (Some (EConst
        ((match b0 with
          | True -> core_true_name
          | False -> core_false_name),
        Nil)))
    | False -> Decline UnsupportedExpression
  in
  (match op with
   | PNatAdd -> numeric (N.add a b)
   | PNatSub -> numeric (N.sub a b)
   | PNatMul -> numeric (N.mul a b)
   | PNatPow -> bounded N.pow
   | PNatGcd -> numeric (N.gcd a b)
   | PNatMod -> numeric (N.modulo a b)
   | PNatDiv -> numeric (N.div a b)
   | PNatBEq -> boolean (N.eqb a b)
   | PNatBLE -> boolean (N.leb a b)
   | PNatLAnd -> numeric (N.coq_land a b)
   | PNatLOr -> numeric (N.coq_lor a b)
   | PNatXor -> numeric (N.coq_lxor a b)
   | PNatShiftLeft -> bounded N.shiftl
   | PNatShiftRight -> bind (core_shiftr fuel0 a b) numeric
   | _ -> Accept None)

(** val core_reduce_nat :
    methods -> nat -> environment -> context -> expr -> expr option result **)

let core_reduce_nat rec0 fuel0 env g e =
  let Pair (head, args) = core_spine e Nil in
  (match head with
   | EConst (n0, l) ->
     (match l with
      | Nil ->
        (match args with
         | Nil -> Accept None
         | Cons (a, l0) ->
           (match l0 with
            | Nil ->
              let op =
                match name_eqb n0 core_succ_name with
                | True -> Some True
                | False ->
                  (match find_decl n0 env with
                   | Some d ->
                     (match d.decl_kind_of with
                      | DPrimitive p0 ->
                        (match p0 with
                         | PNatPred -> Some False
                         | _ -> None)
                      | _ -> None)
                   | None -> None)
              in
              (match op with
               | Some successor ->
                 (match negb (core_nat_ready env) with
                  | True -> Accept None
                  | False ->
                    bind (rec0.whnf_method g a) (fun a0 ->
                      match core_nat_value a0 with
                      | Some a1 ->
                        Accept (Some (ELit (LitNat
                          (match successor with
                           | True -> N.succ a1
                           | False -> N.pred a1))))
                      | None -> Accept None))
               | None -> Accept None)
            | Cons (b, l1) ->
              (match l1 with
               | Nil ->
                 (match find_decl n0 env with
                  | Some d ->
                    (match d.decl_kind_of with
                     | DPrimitive op ->
                       (match op with
                        | PNatBitwise -> Accept None
                        | _ ->
                          (match negb (core_nat_ready env) with
                           | True -> Accept None
                           | False ->
                             bind (rec0.whnf_method g a) (fun a0 ->
                               bind (rec0.whnf_method g b) (fun b0 ->
                                 match core_nat_value a0 with
                                 | Some a1 ->
                                   (match core_nat_value b0 with
                                    | Some b1 ->
                                      core_binary_nat fuel0 env op a1 b1
                                    | None -> Accept None)
                                 | None -> Accept None))))
                     | _ -> Accept None)
                  | None -> Accept None)
               | Cons (_, _) -> Accept None)))
      | Cons (_, _) -> Accept None)
   | _ -> Accept None)

(** val core_cont : ascii -> bool **)

let core_cont b =
  match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          (nat_of_ascii b) with
  | True ->
    Nat.ltb (nat_of_ascii b) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  | False -> False

(** val core_digit : ascii -> n **)

let core_digit b =
  N.modulo (N.of_nat (nat_of_ascii b)) (Npos (XO (XO (XO (XO (XO (XO XH)))))))

(** val core_append_digit : n -> ascii -> n **)

let core_append_digit n0 b =
  N.add (N.mul n0 (Npos (XO (XO (XO (XO (XO (XO XH)))))))) (core_digit b)

(** val core_utf8 : string -> n list option **)

let rec core_utf8 = function
| EmptyString -> Some Nil
| String (a, rest) ->
  let n0 = nat_of_ascii a in
  (match Nat.ltb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
   | True -> option_map (fun x0 -> Cons ((N.of_nat n0), x0)) (core_utf8 rest)
   | False ->
     (match Nat.ltb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
      | True -> None
      | False ->
        (match Nat.ltb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                 (S (S (S (S (S (S (S
                 O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
         | True ->
           (match rest with
            | EmptyString -> None
            | String (b, tail) ->
              (match core_cont b with
               | True ->
                 option_map (fun x0 -> Cons
                   ((core_append_digit
                      (N.of_nat
                        (sub n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                          (S (S (S (S (S (S (S
                          O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                      b),
                   x0)) (core_utf8 tail)
               | False -> None))
         | False ->
           (match Nat.ltb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
            | True ->
              (match rest with
               | EmptyString -> None
               | String (b, s0) ->
                 (match s0 with
                  | EmptyString -> None
                  | String (c, tail) ->
                    (match match match match core_cont b with
                                       | True -> core_cont c
                                       | False -> False with
                                 | True ->
                                   (match negb
                                            (Nat.eqb n0 (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S
                                              O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
                                    | True -> True
                                    | False ->
                                      Nat.leb (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S
                                        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                        (nat_of_ascii b))
                                 | False -> False with
                           | True ->
                             (match negb
                                      (Nat.eqb n0 (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
                              | True -> True
                              | False ->
                                Nat.ltb (nat_of_ascii b) (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                           | False -> False with
                     | True ->
                       option_map (fun x0 -> Cons
                         ((core_append_digit
                            (core_append_digit
                              (N.of_nat
                                (sub n0 (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                  (S (S
                                  O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                              b)
                            c),
                         x0)) (core_utf8 tail)
                     | False -> None)))
            | False ->
              (match Nat.ltb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
               | True ->
                 (match rest with
                  | EmptyString -> None
                  | String (b, s0) ->
                    (match s0 with
                     | EmptyString -> None
                     | String (c, s1) ->
                       (match s1 with
                        | EmptyString -> None
                        | String (d, tail) ->
                          (match match match match match core_cont b with
                                                   | True -> core_cont c
                                                   | False -> False with
                                             | True -> core_cont d
                                             | False -> False with
                                       | True ->
                                         (match negb
                                                  (Nat.eqb n0 (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S (S (S (S (S (S
                                                    (S (S (S
                                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
                                          | True -> True
                                          | False ->
                                            Nat.leb (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S
                                              O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                              (nat_of_ascii b))
                                       | False -> False with
                                 | True ->
                                   (match negb
                                            (Nat.eqb n0 (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S (S (S (S
                                              (S (S (S (S (S (S (S
                                              O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
                                    | True -> True
                                    | False ->
                                      Nat.ltb (nat_of_ascii b) (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S (S (S (S (S (S
                                        (S (S (S (S (S (S (S
                                        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                 | False -> False with
                           | True ->
                             option_map (fun x0 -> Cons
                               ((core_append_digit
                                  (core_append_digit
                                    (core_append_digit
                                      (N.of_nat
                                        (sub n0 (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S
                                          O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                      b)
                                    c)
                                  d),
                               x0)) (core_utf8 tail)
                           | False -> None))))
               | False -> None)))))

(** val core_char_list : n list -> expr **)

let rec core_char_list cs =
  let char = EConst (core_char_name, Nil) in
  (match cs with
   | Nil ->
     EApp ((EConst ((NameStr (core_list_name, (String ((Ascii (False, True,
       True, True, False, True, True, False)), (String ((Ascii (True, False,
       False, True, False, True, True, False)), (String ((Ascii (False,
       False, True, True, False, True, True, False)), EmptyString)))))))),
       (Cons (LZero, Nil)))), char)
   | Cons (c, cs0) ->
     core_apps (EConst ((NameStr (core_list_name, (String ((Ascii (True,
       True, False, False, False, True, True, False)), (String ((Ascii (True,
       True, True, True, False, True, True, False)), (String ((Ascii (False,
       True, True, True, False, True, True, False)), (String ((Ascii (True,
       True, False, False, True, True, True, False)), EmptyString)))))))))),
       (Cons (LZero, Nil)))) (Cons (char, (Cons ((EApp ((EConst
       (core_char_of_nat, Nil)), (ELit (LitNat c)))), (Cons
       ((core_char_list cs0), Nil)))))))

(** val core_expand_string : string -> expr result **)

let core_expand_string s =
  match core_utf8 s with
  | Some cs ->
    Accept (EApp ((EConst (core_string_of_list, Nil)), (core_char_list cs)))
  | None -> Reject MalformedDeclaration

(** val core_major_induct : nat -> expr -> name option **)

let rec core_major_induct index = function
| EPi (_, _, domain, body) ->
  (match index with
   | O ->
     (match fst (core_spine domain Nil) with
      | EConst (n0, _) -> Some n0
      | _ -> None)
   | S index0 -> core_major_induct index0 body)
| _ -> None

(** val core_make_structure :
    environment -> name -> level list -> expr list -> expr -> expr option **)

let core_make_structure env owner us args value =
  match core_inductive env owner with
  | Some info ->
    (match info.ind_ctors with
     | Nil -> None
     | Cons (ctor, l) ->
       (match l with
        | Nil ->
          (match core_constructor env ctor with
           | Some c ->
             Some
               (core_apps (EConst (ctor, us))
                 (app (firstn c.ctor_num_params args)
                   (map (fun i -> EProj (owner, i, value))
                     (seq O c.ctor_num_fields))))
           | None -> None)
        | Cons (_, _) -> None))
  | None -> None

(** val core_to_constructor :
    methods -> nat -> environment -> context -> name -> bool -> expr -> expr
    result **)

let core_to_constructor rec0 fuel0 env g owner k_rule value =
  bind (rec0.whnf_method g value) (fun reduced ->
    match reduced with
    | ELit l ->
      (match l with
       | LitNat n0 ->
         (match match name_eqb owner core_nat_name with
                | True -> core_nat_ready env
                | False -> False with
          | True -> Accept (core_nat_constructor n0)
          | False -> Accept reduced)
       | LitString s ->
         bind (core_expand_string s) (fun expanded ->
           rec0.whnf_method g expanded))
    | _ ->
      (match fst (core_spine reduced Nil) with
       | EConst (n0, _) ->
         (match core_constructor env n0 with
          | Some _ -> Accept reduced
          | None ->
            (match negb
                     (match k_rule with
                      | True -> True
                      | False -> core_structure env owner) with
             | True -> Accept reduced
             | False ->
               bind (rec0.infer_method g reduced) (fun ty0 ->
                 bind (rec0.whnf_method g ty0) (fun ty1 ->
                   let Pair (head, args) = core_spine ty1 Nil in
                   (match head with
                    | EConst (n1, us) ->
                      (match negb (name_eqb n1 owner) with
                       | True -> Accept reduced
                       | False ->
                         (match core_make_structure env owner us args reduced with
                          | Some candidate ->
                            (match k_rule with
                             | True ->
                               bind (sort_of rec0 g ty1) (fun sort ->
                                 bind (level_equiv fuel0 sort LZero)
                                   (fun prop0 ->
                                   match prop0 with
                                   | True ->
                                     bind (rec0.infer_method g candidate)
                                       (fun ct ->
                                       bind (rec0.defeq_method g ty1 ct)
                                         (fun ok ->
                                         match ok with
                                         | True -> Accept candidate
                                         | False -> Accept reduced))
                                   | False -> Accept reduced))
                             | False ->
                               bind (sort_of rec0 g ty1) (fun sort ->
                                 match core_level_positive sort with
                                 | True -> Accept candidate
                                 | False -> Accept reduced))
                          | None -> Accept reduced))
                    | _ -> Accept reduced)))))
       | _ ->
         (match negb
                  (match k_rule with
                   | True -> True
                   | False -> core_structure env owner) with
          | True -> Accept reduced
          | False ->
            bind (rec0.infer_method g reduced) (fun ty0 ->
              bind (rec0.whnf_method g ty0) (fun ty1 ->
                let Pair (head, args) = core_spine ty1 Nil in
                (match head with
                 | EConst (n0, us) ->
                   (match negb (name_eqb n0 owner) with
                    | True -> Accept reduced
                    | False ->
                      (match core_make_structure env owner us args reduced with
                       | Some candidate ->
                         (match k_rule with
                          | True ->
                            bind (sort_of rec0 g ty1) (fun sort ->
                              bind (level_equiv fuel0 sort LZero)
                                (fun prop0 ->
                                match prop0 with
                                | True ->
                                  bind (rec0.infer_method g candidate)
                                    (fun ct ->
                                    bind (rec0.defeq_method g ty1 ct)
                                      (fun ok ->
                                      match ok with
                                      | True -> Accept candidate
                                      | False -> Accept reduced))
                                | False -> Accept reduced))
                          | False ->
                            bind (sort_of rec0 g ty1) (fun sort ->
                              match core_level_positive sort with
                              | True -> Accept candidate
                              | False -> Accept reduced))
                       | None -> Accept reduced))
                 | _ -> Accept reduced))))))

(** val core_find_rule :
    name -> recursor_rule list -> recursor_rule option **)

let rec core_find_rule n0 = function
| Nil -> None
| Cons (r, rules0) ->
  (match name_eqb n0 r.rule_ctor with
   | True -> Some r
   | False -> core_find_rule n0 rules0)

(** val core_reduce_recursor :
    methods -> nat -> environment -> context -> expr -> expr option result **)

let core_reduce_recursor rec0 fuel0 env g e =
  let Pair (head, args) = core_spine e Nil in
  (match head with
   | EConst (n0, us) ->
     (match find_decl n0 env with
      | Some d ->
        (match d.decl_kind_of with
         | DRecursor info ->
           let first_index =
             add (add info.rec_num_params info.rec_num_motives)
               info.rec_num_minors
           in
           let major_index = add first_index info.rec_num_indices in
           (match nth_error args major_index with
            | Some major ->
              (match core_major_induct major_index d.decl_type with
               | Some owner ->
                 bind
                   (core_to_constructor rec0 fuel0 env g owner info.rec_k
                     major)
                   (fun major0 ->
                   let Pair (ctor, fields) = core_spine major0 Nil in
                   (match ctor with
                    | EConst (cn, _) ->
                      (match core_find_rule cn info.rec_rules with
                       | Some rule ->
                         (match core_constructor env cn with
                          | Some ci ->
                            (match negb
                                     (match match match name_eqb
                                                          ci.ctor_induct owner with
                                                  | True ->
                                                    Nat.eqb (length fields)
                                                      (add ci.ctor_num_params
                                                        ci.ctor_num_fields)
                                                  | False -> False with
                                            | True ->
                                              Nat.eqb rule.rule_nfields
                                                ci.ctor_num_fields
                                            | False -> False with
                                      | True ->
                                        Nat.eqb (length us)
                                          (length d.decl_params)
                                      | False -> False) with
                             | True -> Accept None
                             | False ->
                               Accept (Some
                                 (core_apps
                                   (subst_levels d.decl_params us
                                     rule.rule_rhs)
                                   (app (firstn first_index args)
                                     (app (skipn ci.ctor_num_params fields)
                                       (skipn (S major_index) args))))))
                          | None -> Accept None)
                       | None -> Accept None)
                    | _ -> Accept None))
               | None -> Reject MalformedDeclaration)
            | None -> Accept None)
         | _ -> Accept None)
      | None -> Accept None)
   | _ -> Accept None)

(** val core_reduce_projection_with :
    methods -> (context -> expr -> expr result) -> environment -> context ->
    name -> nat -> expr -> expr option result **)

let core_reduce_projection_with rec0 reduce env g owner index value =
  bind (reduce g value) (fun reduced ->
    bind
      (match reduced with
       | ELit l ->
         (match l with
          | LitNat _ -> Accept reduced
          | LitString s ->
            bind (core_expand_string s) (fun expanded ->
              rec0.whnf_method g expanded))
       | _ -> Accept reduced)
      (fun reduced0 ->
      let Pair (head, args) = core_spine reduced0 Nil in
      (match head with
       | EConst (n0, _) ->
         (match core_constructor env n0 with
          | Some ci ->
            (match match match name_eqb ci.ctor_induct owner with
                         | True -> Nat.ltb index ci.ctor_num_fields
                         | False -> False with
                   | True ->
                     Nat.eqb (length args)
                       (add ci.ctor_num_params ci.ctor_num_fields)
                   | False -> False with
             | True -> Accept (nth_error args (add ci.ctor_num_params index))
             | False -> Accept None)
          | None -> Accept None)
       | _ -> Accept None)))

(** val core_reduce_projection :
    methods -> environment -> context -> name -> nat -> expr -> expr option
    result **)

let core_reduce_projection rec0 =
  core_reduce_projection_with rec0 rec0.whnf_method

(** val core_reduce_quotient :
    methods -> environment -> context -> expr -> expr option result **)

let core_reduce_quotient rec0 env g e =
  let Pair (head, args) = core_spine e Nil in
  (match head with
   | EConst (n0, _) ->
     (match find_decl n0 env with
      | Some d ->
        let major_pos =
          match d.decl_kind_of with
          | DAssumption -> None
          | DDefinition -> None
          | DTheorem -> None
          | DOpaque -> None
          | DUnsupported -> None
          | DInductive _ -> None
          | DConstructor _ -> None
          | DRecursor _ -> None
          | DPrimitive _ -> None
          | DQuotient q0 ->
            (match q0 with
             | QType -> None
             | QCtor -> None
             | QLift -> Some (S (S (S (S (S O)))))
             | QInd -> Some (S (S (S (S O)))))
          | _ -> None
        in
        (match major_pos with
         | Some index ->
           (match nth_error args index with
            | Some major ->
              (match nth_error args (S (S (S O))) with
               | Some fn ->
                 bind (rec0.whnf_method g major) (fun major0 ->
                   let Pair (ctor, cargs) = core_spine major0 Nil in
                   (match ctor with
                    | EConst (cn, _) ->
                      (match cargs with
                       | Nil -> Accept None
                       | Cons (_, l0) ->
                         (match l0 with
                          | Nil -> Accept None
                          | Cons (_, l1) ->
                            (match l1 with
                             | Nil -> Accept None
                             | Cons (representative, l2) ->
                               (match l2 with
                                | Nil ->
                                  (match find_decl cn env with
                                   | Some cd ->
                                     (match cd.decl_kind_of with
                                      | DQuotient q0 ->
                                        (match q0 with
                                         | QCtor ->
                                           Accept (Some
                                             (core_apps (EApp (fn,
                                               representative))
                                               (skipn (S index) args)))
                                         | _ -> Accept None)
                                      | _ -> Accept None)
                                   | None -> Accept None)
                                | Cons (_, _) -> Accept None))))
                    | _ -> Accept None))
               | None -> Accept None)
            | None -> Accept None)
         | None -> Accept None)
      | None -> Accept None)
   | _ -> Accept None)

(** val infer_step :
    methods -> nat -> environment -> name list -> bool -> context -> expr ->
    expr result **)

let rec infer_step rec0 fuel0 env ps checking g = function
| EBVar i ->
  (match nth_error g.bound_context i with
   | Some b -> Accept (lift (S i) O b.binding_type)
   | None -> Reject LooseBoundVariable)
| EFVar n0 ->
  (match find_free n0 g.free_context with
   | Some b -> Accept b.binding_type
   | None -> Reject UnknownFreeVariable)
| EMVar _ -> Reject MetaVariable
| ESort u0 -> bind (check_level ps u0) (fun _ -> Accept (ESort (LSucc u0)))
| EConst (n0, us) ->
  bind (get_constant env ps n0 us) (fun d -> Accept
    (instantiate_levels d.decl_params us d.decl_type))
| EApp (f, a) ->
  bind (infer_step rec0 fuel0 env ps checking g f) (fun ft ->
    bind (rec0.whnf_method g ft) (fun ft0 ->
      match ft0 with
      | EPi (_, _, domain, body) ->
        bind
          (match checking with
           | True ->
             bind (infer_step rec0 fuel0 env ps True g a) (fun arg_type ->
               bind (application_type_defeq rec0 g a domain arg_type)
                 (fun ok -> require ok TypeMismatch))
           | False -> Accept Tt)
          (fun _ -> Accept (instantiate body a))
      | _ -> Reject ExpectedPi))
| ELam (n0, bi, domain, body) ->
  bind
    (match checking with
     | True ->
       bind (infer_step rec0 fuel0 env ps True g domain) (fun dt ->
         bind (rec0.whnf_method g dt) (fun dt0 ->
           match dt0 with
           | EBVar _ -> Reject ExpectedSort
           | EFVar _ -> Reject ExpectedSort
           | EMVar _ -> Reject ExpectedSort
           | ESort _ -> Accept Tt
           | _ -> Reject ExpectedSort))
     | False -> Accept Tt)
    (fun _ ->
    bind
      (infer_step rec0 fuel0 env ps checking (push_binding g domain None)
        body)
      (fun bt0 -> Accept (EPi (n0, bi, domain, bt0))))
| EPi (_, _, domain, body) ->
  bind (infer_step rec0 fuel0 env ps checking g domain) (fun dt ->
    bind (rec0.whnf_method g dt) (fun dt0 ->
      bind (match dt0 with
            | ESort u0 -> Accept u0
            | _ -> Reject ExpectedSort)
        (fun u0 ->
        let gb = push_binding g domain None in
        bind (infer_step rec0 fuel0 env ps checking gb body) (fun bt0 ->
          bind (rec0.whnf_method gb bt0) (fun bt1 ->
            bind
              (match bt1 with
               | ESort v0 -> Accept v0
               | _ -> Reject ExpectedSort)
              (fun v0 -> Accept (ESort (LIMax (u0, v0)))))))))
| ELet (_, ty0, value, body, _) ->
  bind
    (match checking with
     | True ->
       bind (infer_step rec0 fuel0 env ps True g ty0) (fun sort_type ->
         bind (rec0.whnf_method g sort_type) (fun sort_type0 ->
           bind
             (match sort_type0 with
              | EBVar _ -> Reject ExpectedSort
              | EFVar _ -> Reject ExpectedSort
              | EMVar _ -> Reject ExpectedSort
              | ESort _ -> Accept Tt
              | _ -> Reject ExpectedSort)
             (fun _ ->
             bind (infer_step rec0 fuel0 env ps True g value) (fun vt ->
               bind (rec0.defeq_method g vt ty0) (fun ok ->
                 require ok TypeMismatch)))))
     | False -> Accept Tt)
    (fun _ ->
    bind
      (infer_step rec0 fuel0 env ps checking
        (push_binding g ty0 (Some value)) body)
      (fun bt0 -> Accept (instantiate bt0 value)))
| ELit l ->
  (match l with
   | LitNat _ ->
     (match core_nat_ready env with
      | True -> Accept core_nat
      | False -> Decline UnsupportedExpression)
   | LitString s ->
     (match core_string_ready env with
      | True ->
        bind (core_expand_string s) (fun _ -> Accept (EConst
          (core_string_name, Nil)))
      | False -> Decline UnsupportedExpression))
| EProj (owner, index, value) ->
  (match core_inductive env owner with
   | Some _ ->
     core_infer_projection
       (match checking with
        | True -> rec0
        | False -> inference_only rec0)
       fuel0 env g owner index value
   | None -> Decline UnsupportedExpression)
| EMData body -> infer_step rec0 fuel0 env ps checking g body

(** val core_beta_collect : expr -> expr list -> expr list -> expr **)

let rec core_beta_collect head args values =
  match args with
  | Nil -> instantiate_many head values
  | Cons (a, args0) ->
    (match head with
     | ELam (_, _, _, body) -> core_beta_collect body args0 (Cons (a, values))
     | _ -> core_apps (instantiate_many head values) (Cons (a, args0)))

(** val core_beta : expr -> expr list -> expr **)

let core_beta head args =
  core_beta_collect head args Nil

(** val core_unfold :
    environment -> name list -> expr -> expr option result **)

let core_unfold env ps e =
  let Pair (head, args) = core_spine e Nil in
  (match head with
   | EConst (n0, us) ->
     bind (get_constant env ps n0 us) (fun d ->
       match d.decl_kind_of with
       | DDefinition ->
         (match d.decl_value with
          | Some value ->
            Accept (Some
              (core_apps (instantiate_levels d.decl_params us value) args))
          | None -> Reject MalformedDeclaration)
       | DTheorem ->
         (match d.decl_value with
          | Some value ->
            Accept (Some
              (core_apps (instantiate_levels d.decl_params us value) args))
          | None -> Reject MalformedDeclaration)
       | DPrimitive _ ->
         (match d.decl_value with
          | Some value ->
            Accept (Some
              (core_apps (instantiate_levels d.decl_params us value) args))
          | None -> Reject MalformedDeclaration)
       | _ -> Accept None)
   | _ -> Accept None)

(** val whnf_core_step :
    methods -> nat -> environment -> name list -> bool -> context -> expr ->
    expr result **)

let whnf_core_step rec0 fuel0 env ps cheap g e = match e with
| EBVar i ->
  (match nth_error g.bound_context i with
   | Some b ->
     (match b.binding_value with
      | Some v0 -> rec0.whnf_core_method cheap g (lift (S i) O v0)
      | None -> Accept e)
   | None -> Reject LooseBoundVariable)
| EFVar n0 ->
  (match find_free n0 g.free_context with
   | Some b ->
     (match b.binding_value with
      | Some v0 -> rec0.whnf_core_method cheap g v0
      | None -> Accept e)
   | None -> Reject UnknownFreeVariable)
| EMVar _ -> Reject MetaVariable
| ESort u0 -> bind (check_level ps u0) (fun _ -> Accept e)
| EConst (n0, us) -> bind (get_constant env ps n0 us) (fun _ -> Accept e)
| EApp (_, _) ->
  let Pair (head, args) = core_spine e Nil in
  bind (rec0.whnf_core_method cheap g head) (fun fn ->
    match fn with
    | EBVar _ ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot0 ->
        bind
          (match quot0 with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel0 env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | EFVar _ ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot0 ->
        bind
          (match quot0 with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel0 env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | EMVar _ ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot0 ->
        bind
          (match quot0 with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel0 env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | ESort _ ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot0 ->
        bind
          (match quot0 with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel0 env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | EConst (_, _) ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot0 ->
        bind
          (match quot0 with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel0 env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | EApp (_, _) ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot0 ->
        bind
          (match quot0 with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel0 env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | ELam (_, _, _, _) -> rec0.whnf_core_method cheap g (core_beta fn args)
    | EPi (_, _, _, _) ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot0 ->
        bind
          (match quot0 with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel0 env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | ELet (_, _, _, _, _) ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot0 ->
        bind
          (match quot0 with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel0 env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | ELit _ ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot0 ->
        bind
          (match quot0 with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel0 env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | EProj (_, _, _) ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot0 ->
        bind
          (match quot0 with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel0 env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | EMData _ ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot0 ->
        bind
          (match quot0 with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel0 env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt)))
| ELet (_, _, value, body, _) ->
  rec0.whnf_core_method cheap g (instantiate body value)
| ELit l ->
  (match l with
   | LitNat _ -> Accept e
   | LitString s -> bind (core_expand_string s) (fun _ -> Accept e))
| EProj (owner, index, value) ->
  bind
    (core_reduce_projection_with rec0
      (match cheap with
       | True -> rec0.whnf_core_method True
       | False -> rec0.whnf_method)
      env g owner index value)
    (fun step ->
    match step with
    | Some value0 -> rec0.whnf_core_method cheap g value0
    | None -> Accept e)
| EMData body -> rec0.whnf_core_method cheap g body
| _ -> Accept e

(** val finish_whnf_unfold :
    environment -> name list -> expr -> whnf_round result **)

let finish_whnf_unfold env ps e =
  bind (core_unfold env ps e) (fun unfolded -> Accept
    (match unfolded with
     | Some value -> WhnfContinue value
     | None -> WhnfDone e))

(** val whnf_round_step :
    methods -> nat -> environment -> name list -> context -> expr ->
    whnf_round result **)

let whnf_round_step rec0 fuel0 env ps g e =
  bind (whnf_core_step rec0 fuel0 env ps False g e) (fun reduced ->
    match reduced with
    | EBVar _ ->
      bind (core_reduce_nat rec0 fuel0 env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | EFVar _ ->
      bind (core_reduce_nat rec0 fuel0 env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | EMVar _ ->
      bind (core_reduce_nat rec0 fuel0 env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | ESort _ ->
      bind (core_reduce_nat rec0 fuel0 env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | EConst (n0, _) ->
      (match match name_eqb n0 core_zero_name with
             | True -> core_nat_ready env
             | False -> False with
       | True -> Accept (WhnfDone (ELit (LitNat N0)))
       | False -> finish_whnf_unfold env ps reduced)
    | EApp (_, _) ->
      bind (core_reduce_nat rec0 fuel0 env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | ELam (_, _, _, _) ->
      bind (core_reduce_nat rec0 fuel0 env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | EPi (_, _, _, _) ->
      bind (core_reduce_nat rec0 fuel0 env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | ELet (_, _, _, _, _) ->
      bind (core_reduce_nat rec0 fuel0 env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | ELit _ ->
      bind (core_reduce_nat rec0 fuel0 env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | EProj (_, _, _) ->
      bind (core_reduce_nat rec0 fuel0 env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | EMData _ ->
      bind (core_reduce_nat rec0 fuel0 env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced))

(** val whnf_loop :
    nat -> methods -> nat -> environment -> name list -> context -> expr ->
    expr result **)

let whnf_loop rounds rec0 fuel0 env ps g e =
  run_whnf_rounds rounds (whnf_round_step rec0 fuel0 env ps g) e

(** val eta_compare :
    methods -> context -> expr -> expr -> expr -> bool result **)

let eta_compare rec0 g domain body other =
  bind (rec0.infer_method g other) (fun ty0 ->
    bind (rec0.whnf_method g ty0) (fun ty1 ->
      match ty1 with
      | EPi (_, _, domain', _) ->
        bind (rec0.defeq_method g domain domain') (fun ok ->
          match ok with
          | True ->
            rec0.defeq_method (push_binding g domain None) body (EApp
              ((lift (S O) O other), (EBVar O)))
          | False -> Accept False)
      | _ -> Accept False))

(** val core_alpha : nat -> expr -> expr -> (bool, nat) prod **)

let rec core_alpha budget t0 s =
  match budget with
  | O -> Pair (False, O)
  | S budget0 ->
    (match t0 with
     | EBVar i ->
       (match s with
        | EBVar j -> Pair ((Nat.eqb i j), budget0)
        | _ -> Pair (False, budget0))
     | EFVar n0 ->
       (match s with
        | EFVar m -> Pair ((name_eqb n0 m), budget0)
        | _ -> Pair (False, budget0))
     | EMVar n0 ->
       (match s with
        | EMVar m -> Pair ((name_eqb n0 m), budget0)
        | _ -> Pair (False, budget0))
     | ESort u0 ->
       (match s with
        | ESort v0 -> Pair ((level_eqb u0 v0), budget0)
        | _ -> Pair (False, budget0))
     | EConst (n0, us) ->
       (match s with
        | EConst (m, vs) ->
          Pair
            ((match name_eqb n0 m with
              | True -> list_eqb level_eqb us vs
              | False -> False),
            budget0)
        | _ -> Pair (False, budget0))
     | EApp (f, a) ->
       (match s with
        | EApp (h, b) ->
          let Pair (ok, remaining) = core_alpha budget0 f h in
          (match ok with
           | True -> core_alpha remaining a b
           | False -> Pair (False, remaining))
        | _ -> Pair (False, budget0))
     | ELam (_, _, f, a) ->
       (match s with
        | ELam (_, _, h, b) ->
          let Pair (ok, remaining) = core_alpha budget0 f h in
          (match ok with
           | True -> core_alpha remaining a b
           | False -> Pair (False, remaining))
        | _ -> Pair (False, budget0))
     | EPi (_, _, f, a) ->
       (match s with
        | EPi (_, _, h, b) ->
          let Pair (ok, remaining) = core_alpha budget0 f h in
          (match ok with
           | True -> core_alpha remaining a b
           | False -> Pair (False, remaining))
        | _ -> Pair (False, budget0))
     | ELet (_, a, v0, b, _) ->
       (match s with
        | ELet (_, c, w, d, _) ->
          let Pair (ok, remaining) = core_alpha budget0 a c in
          (match ok with
           | True ->
             let Pair (ok0, remaining0) = core_alpha remaining v0 w in
             (match ok0 with
              | True -> core_alpha remaining0 b d
              | False -> Pair (False, remaining0))
           | False -> Pair (False, remaining))
        | _ -> Pair (False, budget0))
     | ELit a ->
       (match s with
        | ELit b -> Pair ((literal_eqb a b), budget0)
        | _ -> Pair (False, budget0))
     | EProj (n0, i, a) ->
       (match s with
        | EProj (m, j, b) ->
          (match match name_eqb n0 m with
                 | True -> Nat.eqb i j
                 | False -> False with
           | True -> core_alpha budget0 a b
           | False -> Pair (False, budget0))
        | _ -> Pair (False, budget0))
     | EMData a ->
       (match s with
        | EMData b -> core_alpha budget0 a b
        | _ -> Pair (False, budget0)))

(** val core_alpha_eq : expr -> expr -> bool **)

let core_alpha_eq t0 s =
  fst
    (core_alpha (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      t0 s)

(** val core_compare_args :
    methods -> context -> expr list -> expr list -> bool result **)

let rec core_compare_args rec0 g xs ys =
  match xs with
  | Nil -> (match ys with
            | Nil -> Accept True
            | Cons (_, _) -> Accept False)
  | Cons (x0, xs0) ->
    (match ys with
     | Nil -> Accept False
     | Cons (y, ys0) ->
       bind (rec0.defeq_method g x0 y) (fun ok ->
         match ok with
         | True -> core_compare_args rec0 g xs0 ys0
         | False -> Accept False))

(** val core_same_head : nat -> expr -> expr -> bool result **)

let core_same_head fuel0 t0 s =
  match t0 with
  | EBVar i ->
    (match s with
     | EBVar j -> Accept (Nat.eqb i j)
     | _ -> Accept False)
  | EFVar n0 ->
    (match s with
     | EFVar m -> Accept (name_eqb n0 m)
     | _ -> Accept False)
  | EConst (n0, us) ->
    (match s with
     | EConst (m, vs) ->
       (match name_eqb n0 m with
        | True -> levels_equiv fuel0 us vs
        | False -> Accept False)
     | _ -> Accept False)
  | _ -> Accept False

(** val core_congruent_apps :
    methods -> nat -> context -> expr -> expr -> bool result **)

let core_congruent_apps rec0 fuel0 g t0 s =
  match t0 with
  | EApp (_, _) ->
    (match s with
     | EApp (_, _) ->
       let Pair (tf, ta) = core_spine t0 Nil in
       let Pair (sf, sa) = core_spine s Nil in
       bind (core_same_head fuel0 tf sf) (fun same ->
         match match same with
               | True -> Nat.eqb (length ta) (length sa)
               | False -> False with
         | True -> core_compare_args rec0 g (rev0 ta) (rev0 sa)
         | False -> Accept False)
     | _ -> Accept False)
  | _ -> Accept False

(** val core_delta_info : environment -> expr -> declaration option **)

let core_delta_info env e =
  match fst (core_spine e Nil) with
  | EConst (n0, us) ->
    (match find_decl n0 env with
     | Some d ->
       (match d.decl_kind_of with
        | DDefinition ->
          (match d.decl_value with
           | Some _ ->
             (match Nat.eqb (length d.decl_params) (length us) with
              | True -> Some d
              | False -> None)
           | None -> None)
        | DTheorem ->
          (match d.decl_value with
           | Some _ ->
             (match Nat.eqb (length d.decl_params) (length us) with
              | True -> Some d
              | False -> None)
           | None -> None)
        | DPrimitive _ ->
          (match d.decl_value with
           | Some _ ->
             (match Nat.eqb (length d.decl_params) (length us) with
              | True -> Some d
              | False -> None)
           | None -> None)
        | _ -> None)
     | None -> None)
  | _ -> None

(** val core_delta_sides :
    environment -> expr -> expr -> (bool, bool) prod **)

let core_delta_sides env t0 s =
  match core_delta_info env t0 with
  | Some dt ->
    (match core_delta_info env s with
     | Some ds ->
       (match hints_lt (effective_hints dt) (effective_hints ds) with
        | True -> Pair (False, True)
        | False ->
          (match hints_lt (effective_hints ds) (effective_hints dt) with
           | True -> Pair (True, False)
           | False -> Pair (True, True)))
     | None -> Pair (True, True))
  | None -> Pair (True, True)

(** val core_erasing_delta : environment -> expr -> bool **)

let core_erasing_delta env e =
  let Pair (head, args) = core_spine e Nil in
  (match head with
   | EConst (n0, _) ->
     (match args with
      | Nil -> False
      | Cons (_, _) ->
        (match find_decl n0 env with
         | Some d ->
           (match d.decl_value with
            | Some e0 ->
              (match e0 with
               | ELam (_, _, _, body) -> negb (core_occurs O body)
               | _ -> False)
            | None -> False)
         | None -> False))
   | _ -> False)

(** val core_delta_congruent :
    methods -> nat -> environment -> context -> expr -> expr -> bool result **)

let core_delta_congruent rec0 fuel0 env g t0 s =
  match core_delta_info env t0 with
  | Some dt ->
    (match core_delta_info env s with
     | Some ds ->
       (match effective_hints dt with
        | HintRegular ht ->
          (match effective_hints ds with
           | HintRegular hs ->
             (match match N.eqb ht hs with
                    | True ->
                      negb
                        (match core_erasing_delta env t0 with
                         | True -> True
                         | False -> core_erasing_delta env s)
                    | False -> False with
              | True -> core_congruent_apps rec0 fuel0 g t0 s
              | False -> Accept False)
           | _ -> Accept False)
        | _ -> Accept False)
     | None -> Accept False)
  | None -> Accept False

(** val compare_heads :
    methods -> nat -> context -> expr -> expr -> bool result **)

let compare_heads rec0 fuel0 g t0 s =
  match t0 with
  | EBVar n0 ->
    (match s with
     | EBVar m -> Accept (Nat.eqb n0 m)
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
     | _ -> Accept False)
  | EFVar n0 ->
    (match s with
     | EFVar m -> Accept (name_eqb n0 m)
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
     | _ -> Accept False)
  | EMVar _ ->
    (match s with
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
     | _ -> Accept False)
  | EConst (n0, us) ->
    (match s with
     | EConst (m, vs) ->
       (match name_eqb n0 m with
        | True -> levels_equiv fuel0 us vs
        | False -> Accept False)
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
     | _ -> Accept False)
  | EApp (_, _) ->
    (match s with
     | EApp (_, _) ->
       let Pair (tf, ta) = core_spine t0 Nil in
       let Pair (sf, sa) = core_spine s Nil in
       (match Nat.eqb (length ta) (length sa) with
        | True ->
          bind (rec0.defeq_method g tf sf) (fun ok ->
            match ok with
            | True -> core_compare_args rec0 g ta sa
            | False -> Accept False)
        | False -> Accept False)
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
     | _ -> Accept False)
  | ELam (_, _, domain, body) -> eta_compare rec0 g domain body s
  | EPi (_, _, _, _) ->
    (match s with
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
     | _ -> Accept False)
  | ELet (_, _, _, _, _) ->
    (match s with
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
     | _ -> Accept False)
  | EProj (n0, i, a) ->
    (match s with
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
     | EProj (m, j, b) ->
       (match match name_eqb n0 m with
              | True -> Nat.eqb i j
              | False -> False with
        | True -> rec0.defeq_method g a b
        | False -> Accept False)
     | _ -> Accept False)
  | _ ->
    (match s with
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
     | _ -> Accept False)

(** val core_compare_fields :
    methods -> context -> name -> expr -> nat -> expr list -> bool result **)

let rec core_compare_fields rec0 g owner value index = function
| Nil -> Accept True
| Cons (field, fields0) ->
  bind (rec0.defeq_method g (EProj (owner, index, value)) field) (fun ok ->
    match ok with
    | True -> core_compare_fields rec0 g owner value (S index) fields0
    | False -> Accept False)

(** val core_structure_eta :
    methods -> environment -> context -> expr -> expr -> bool result **)

let core_structure_eta rec0 env g value constructed =
  let Pair (head, args) = core_spine constructed Nil in
  (match head with
   | EConst (ctor, _) ->
     (match core_constructor env ctor with
      | Some c ->
        (match match core_structure env c.ctor_induct with
               | True ->
                 Nat.eqb (length args)
                   (add c.ctor_num_params c.ctor_num_fields)
               | False -> False with
         | True ->
           bind (rec0.infer_method g value) (fun vt ->
             bind (rec0.infer_method g constructed) (fun ct ->
               bind (rec0.defeq_method g vt ct) (fun ok ->
                 match ok with
                 | True ->
                   core_compare_fields rec0 g c.ctor_induct value O
                     (skipn c.ctor_num_params args)
                 | False -> Accept False)))
         | False -> Accept False)
      | None -> Accept False)
   | _ -> Accept False)

(** val core_unit_like :
    methods -> environment -> context -> expr -> expr -> bool result **)

let core_unit_like rec0 env g t0 s =
  bind (rec0.infer_method g t0) (fun ty0 ->
    bind (rec0.whnf_method g ty0) (fun ty1 ->
      match fst (core_spine ty1 Nil) with
      | EConst (owner, _) ->
        (match core_structure env owner with
         | True ->
           (match core_inductive env owner with
            | Some i ->
              (match i.ind_ctors with
               | Nil -> Accept False
               | Cons (ctor, l) ->
                 (match l with
                  | Nil ->
                    (match core_constructor env ctor with
                     | Some c ->
                       (match Nat.eqb c.ctor_num_fields O with
                        | True ->
                          bind (rec0.infer_method g s) (fun sty ->
                            rec0.defeq_method g ty1 sty)
                        | False -> Accept False)
                     | None -> Accept False)
                  | Cons (_, _) -> Accept False))
            | None -> Accept False)
         | False -> Accept False)
      | _ -> Accept False))

(** val core_try_string_expansion :
    methods -> context -> expr -> expr -> bool option result **)

let core_try_string_expansion rec0 g t0 s =
  let expand = fun text other ->
    bind (core_expand_string text) (fun expanded ->
      bind (rec0.defeq_method g expanded other) (fun ok -> Accept (Some ok)))
  in
  (match t0 with
   | EApp (e, _) ->
     (match e with
      | EConst (n0, l) ->
        (match l with
         | Nil ->
           (match s with
            | ELit l0 ->
              (match l0 with
               | LitNat _ -> Accept None
               | LitString text ->
                 (match name_eqb n0 core_string_of_list with
                  | True -> expand text t0
                  | False -> Accept None))
            | _ -> Accept None)
         | Cons (_, _) -> Accept None)
      | _ -> Accept None)
   | ELit l ->
     (match l with
      | LitNat _ -> Accept None
      | LitString text ->
        (match s with
         | EApp (e, _) ->
           (match e with
            | EConst (n0, l0) ->
              (match l0 with
               | Nil ->
                 (match name_eqb n0 core_string_of_list with
                  | True -> expand text s
                  | False -> Accept None)
               | Cons (_, _) -> Accept None)
            | _ -> Accept None)
         | _ -> Accept None))
   | _ -> Accept None)

(** val core_compare_fallback :
    methods -> nat -> environment -> context -> expr -> expr -> bool result **)

let core_compare_fallback rec0 fuel0 env g t0 s =
  bind (compare_heads rec0 fuel0 g t0 s) (fun ok ->
    match ok with
    | True -> Accept True
    | False ->
      bind (core_structure_eta rec0 env g t0 s) (fun ok0 ->
        match ok0 with
        | True -> Accept True
        | False ->
          bind (core_structure_eta rec0 env g s t0) (fun ok1 ->
            match ok1 with
            | True -> Accept True
            | False ->
              bind (core_try_string_expansion rec0 g t0 s) (fun expanded ->
                match expanded with
                | Some ok2 -> Accept ok2
                | None -> core_unit_like rec0 env g t0 s))))

(** val compare_after_whnf :
    methods -> nat -> environment -> context -> expr -> expr -> bool result **)

let compare_after_whnf rec0 fuel0 env g t0 s =
  match core_alpha_eq t0 s with
  | True -> Accept True
  | False ->
    (match t0 with
     | ESort u0 ->
       (match s with
        | ESort v0 -> level_equiv fuel0 u0 v0
        | _ ->
          bind (rec0.infer_method g t0) (fun tt0 ->
            bind (sort_of rec0 g tt0) (fun sort ->
              bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                match is_prop with
                | True ->
                  bind (rec0.infer_method g s) (fun st ->
                    rec0.defeq_method g tt0 st)
                | False -> core_compare_fallback rec0 fuel0 env g t0 s))))
     | ELam (_, _, a, b) ->
       (match s with
        | ELam (_, _, c, d) ->
          bind (rec0.defeq_method g a c) (fun ok ->
            match ok with
            | True -> rec0.defeq_method (push_binding g a None) b d
            | False -> Accept False)
        | _ ->
          bind (rec0.infer_method g t0) (fun tt0 ->
            bind (sort_of rec0 g tt0) (fun sort ->
              bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                match is_prop with
                | True ->
                  bind (rec0.infer_method g s) (fun st ->
                    rec0.defeq_method g tt0 st)
                | False -> core_compare_fallback rec0 fuel0 env g t0 s))))
     | EPi (_, _, a, b) ->
       (match s with
        | EPi (_, _, c, d) ->
          bind (rec0.defeq_method g a c) (fun ok ->
            match ok with
            | True -> rec0.defeq_method (push_binding g a None) b d
            | False -> Accept False)
        | _ ->
          bind (rec0.infer_method g t0) (fun tt0 ->
            bind (sort_of rec0 g tt0) (fun sort ->
              bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                match is_prop with
                | True ->
                  bind (rec0.infer_method g s) (fun st ->
                    rec0.defeq_method g tt0 st)
                | False -> core_compare_fallback rec0 fuel0 env g t0 s))))
     | ELit l ->
       (match l with
        | LitNat n0 ->
          (match s with
           | ELit l0 ->
             (match l0 with
              | LitNat m -> Accept (N.eqb n0 m)
              | LitString _ ->
                bind (rec0.infer_method g t0) (fun tt0 ->
                  bind (sort_of rec0 g tt0) (fun sort ->
                    bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                      match is_prop with
                      | True ->
                        bind (rec0.infer_method g s) (fun st ->
                          rec0.defeq_method g tt0 st)
                      | False -> core_compare_fallback rec0 fuel0 env g t0 s))))
           | _ ->
             bind (rec0.infer_method g t0) (fun tt0 ->
               bind (sort_of rec0 g tt0) (fun sort ->
                 bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                   match is_prop with
                   | True ->
                     bind (rec0.infer_method g s) (fun st ->
                       rec0.defeq_method g tt0 st)
                   | False -> core_compare_fallback rec0 fuel0 env g t0 s))))
        | LitString a ->
          (match s with
           | ELit l0 ->
             (match l0 with
              | LitNat _ ->
                bind (rec0.infer_method g t0) (fun tt0 ->
                  bind (sort_of rec0 g tt0) (fun sort ->
                    bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                      match is_prop with
                      | True ->
                        bind (rec0.infer_method g s) (fun st ->
                          rec0.defeq_method g tt0 st)
                      | False -> core_compare_fallback rec0 fuel0 env g t0 s)))
              | LitString b -> Accept (eqb2 a b))
           | _ ->
             bind (rec0.infer_method g t0) (fun tt0 ->
               bind (sort_of rec0 g tt0) (fun sort ->
                 bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                   match is_prop with
                   | True ->
                     bind (rec0.infer_method g s) (fun st ->
                       rec0.defeq_method g tt0 st)
                   | False -> core_compare_fallback rec0 fuel0 env g t0 s)))))
     | _ ->
       bind (rec0.infer_method g t0) (fun tt0 ->
         bind (sort_of rec0 g tt0) (fun sort ->
           bind (level_equiv fuel0 sort LZero) (fun is_prop ->
             match is_prop with
             | True ->
               bind (rec0.infer_method g s) (fun st ->
                 rec0.defeq_method g tt0 st)
             | False -> core_compare_fallback rec0 fuel0 env g t0 s))))

(** val core_quick :
    methods -> nat -> context -> expr -> expr -> bool option result **)

let core_quick rec0 fuel0 g t0 s =
  match core_alpha_eq t0 s with
  | True -> Accept (Some True)
  | False ->
    (match t0 with
     | ESort u0 ->
       (match s with
        | ESort v0 ->
          bind (level_equiv fuel0 u0 v0) (fun ok -> Accept (Some ok))
        | _ -> Accept None)
     | ELam (_, _, a, b) ->
       (match s with
        | ELam (_, _, c, d) ->
          bind (rec0.defeq_method g a c) (fun ok ->
            match ok with
            | True ->
              bind (rec0.defeq_method (push_binding g a None) b d)
                (fun ok0 -> Accept (Some ok0))
            | False -> Accept (Some False))
        | _ -> Accept None)
     | EPi (_, _, a, b) ->
       (match s with
        | EPi (_, _, c, d) ->
          bind (rec0.defeq_method g a c) (fun ok ->
            match ok with
            | True ->
              bind (rec0.defeq_method (push_binding g a None) b d)
                (fun ok0 -> Accept (Some ok0))
            | False -> Accept (Some False))
        | _ -> Accept None)
     | ELit a ->
       (match s with
        | ELit b -> Accept (Some (literal_eqb a b))
        | _ -> Accept None)
     | EMData a ->
       (match s with
        | EMData b ->
          bind (rec0.defeq_method g a b) (fun ok -> Accept (Some ok))
        | _ -> Accept None)
     | _ -> Accept None)

(** val core_proof_irrel :
    methods -> nat -> context -> expr -> expr -> bool option result **)

let core_proof_irrel rec0 fuel0 g t0 s =
  bind (rec0.infer_method g t0) (fun ty0 ->
    bind (sort_of rec0 g ty0) (fun sort ->
      bind (level_equiv fuel0 sort LZero) (fun is_prop ->
        match is_prop with
        | True ->
          bind (rec0.infer_method g s) (fun sty ->
            bind (rec0.defeq_method g ty0 sty) (fun ok -> Accept (Some ok)))
        | False -> Accept None)))

type conversion_progress =
| ConversionDone of bool
| ConversionStuck of expr * expr

(** val core_offset :
    methods -> environment -> context -> expr -> expr -> bool option result **)

let core_offset rec0 env g t0 s =
  match core_nat_ready env with
  | True ->
    let pred_of = fun e ->
      match e with
      | EBVar _ -> None
      | EFVar _ -> None
      | EMVar _ -> None
      | ESort _ -> None
      | EConst (_, _) -> None
      | EApp (e0, a) ->
        (match e0 with
         | EBVar _ -> None
         | EFVar _ -> None
         | EMVar _ -> None
         | ESort _ -> None
         | EConst (n0, l) ->
           (match l with
            | Nil ->
              (match name_eqb n0 core_succ_name with
               | True -> Some a
               | False -> None)
            | Cons (_, _) -> None)
         | _ -> None)
      | ELit l ->
        (match l with
         | LitNat n0 ->
           (match N.eqb n0 N0 with
            | True -> None
            | False -> Some (ELit (LitNat (N.pred n0))))
         | LitString _ -> None)
      | _ -> None
    in
    let zero0 = fun e ->
      match e with
      | EConst (n0, l) ->
        (match l with
         | Nil -> name_eqb n0 core_zero_name
         | Cons (_, _) -> False)
      | ELit l ->
        (match l with
         | LitNat n0 -> N.eqb n0 N0
         | LitString _ -> False)
      | _ -> False
    in
    (match match zero0 t0 with
           | True -> zero0 s
           | False -> False with
     | True -> Accept (Some True)
     | False ->
       (match pred_of t0 with
        | Some a ->
          (match pred_of s with
           | Some b ->
             bind (rec0.defeq_method g a b) (fun ok -> Accept (Some ok))
           | None -> Accept None)
        | None -> Accept None))
  | False -> Accept None

(** val core_try_unfold_proj_app :
    methods -> context -> expr -> expr option result **)

let core_try_unfold_proj_app rec0 g e =
  match fst (core_spine e Nil) with
  | EProj (_, _, _) ->
    bind (rec0.whnf_core_method False g e) (fun reduced -> Accept
      (match expr_eqb reduced e with
       | True -> None
       | False -> Some reduced))
  | _ -> Accept None

(** val core_opposite_projection :
    methods -> environment -> context -> expr -> expr -> (expr, expr) prod
    option result **)

let core_opposite_projection rec0 env g t0 s =
  match core_delta_info env t0 with
  | Some _ ->
    (match core_delta_info env s with
     | Some _ -> Accept None
     | None ->
       bind (core_try_unfold_proj_app rec0 g s) (fun reduced -> Accept
         (match reduced with
          | Some s' -> Some (Pair (t0, s'))
          | None -> None)))
  | None ->
    (match core_delta_info env s with
     | Some _ ->
       bind (core_try_unfold_proj_app rec0 g t0) (fun reduced -> Accept
         (match reduced with
          | Some t' -> Some (Pair (t', s))
          | None -> None))
     | None -> Accept None)

(** val core_lazy_delta :
    nat -> methods -> nat -> environment -> name list -> context -> expr ->
    expr -> conversion_progress result **)

let rec core_lazy_delta rounds rec0 fuel0 env ps g t0 s =
  match rounds with
  | O -> Decline OutOfFuel
  | S rounds0 ->
    bind (core_quick rec0 fuel0 g t0 s) (fun quick ->
      match quick with
      | Some ok -> Accept (ConversionDone ok)
      | None ->
        bind (core_offset rec0 env g t0 s) (fun offset ->
          match offset with
          | Some ok -> Accept (ConversionDone ok)
          | None ->
            let eligible =
              pair_probe_guard
                (nat_probe_head find_decl core_succ_name env
                  (core_spine t0 Nil))
                (nat_probe_head find_decl core_succ_name env
                  (core_spine s Nil))
                (fun _ -> nat_probe_allowed rec0.method_mode t0 s)
            in
            bind
              (match eligible with
               | True -> core_reduce_nat rec0 fuel0 env g t0
               | False -> Accept None)
              (fun tn ->
              match tn with
              | Some tn0 ->
                bind (rec0.defeq_method g tn0 s) (fun ok -> Accept
                  (ConversionDone ok))
              | None ->
                bind
                  (match eligible with
                   | True -> core_reduce_nat rec0 fuel0 env g s
                   | False -> Accept None)
                  (fun sn ->
                  match sn with
                  | Some sn0 ->
                    bind (rec0.defeq_method g t0 sn0) (fun ok -> Accept
                      (ConversionDone ok))
                  | None ->
                    bind (core_delta_congruent rec0 fuel0 env g t0 s)
                      (fun same ->
                      match same with
                      | True -> Accept (ConversionDone True)
                      | False ->
                        bind (core_opposite_projection rec0 env g t0 s)
                          (fun projected ->
                          match projected with
                          | Some p0 ->
                            let Pair (tn0, sn0) = p0 in
                            core_lazy_delta rounds0 rec0 fuel0 env ps g tn0
                              sn0
                          | None ->
                            let Pair (unfold_left, unfold_right) =
                              core_delta_sides env t0 s
                            in
                            bind
                              (match unfold_left with
                               | True -> core_unfold env ps t0
                               | False -> Accept None)
                              (fun td ->
                              bind
                                (match unfold_right with
                                 | True -> core_unfold env ps s
                                 | False -> Accept None)
                                (fun sd ->
                                match td with
                                | Some _ ->
                                  bind
                                    (match td with
                                     | Some e ->
                                       rec0.whnf_core_method True g e
                                     | None -> Accept t0)
                                    (fun tn0 ->
                                    bind
                                      (match sd with
                                       | Some e ->
                                         rec0.whnf_core_method True g e
                                       | None -> Accept s)
                                      (fun sn0 ->
                                      core_lazy_delta rounds0 rec0 fuel0 env
                                        ps g tn0 sn0))
                                | None ->
                                  (match sd with
                                   | Some _ ->
                                     bind
                                       (match td with
                                        | Some e ->
                                          rec0.whnf_core_method True g e
                                        | None -> Accept t0)
                                       (fun tn0 ->
                                       bind
                                         (match sd with
                                          | Some e ->
                                            rec0.whnf_core_method True g e
                                          | None -> Accept s)
                                         (fun sn0 ->
                                         core_lazy_delta rounds0 rec0 fuel0
                                           env ps g tn0 sn0))
                                   | None -> Accept (ConversionStuck (t0, s)))))))))))

(** val core_finish_conversion :
    methods -> nat -> environment -> context -> expr -> expr -> bool result **)

let core_finish_conversion rec0 fuel0 env g t0 s =
  let project = fun e ->
    let Pair (head, args) = core_spine e Nil in
    (match head with
     | EBVar _ -> Accept None
     | EFVar _ -> Accept None
     | EMVar _ -> Accept None
     | ESort _ -> Accept None
     | EConst (_, _) -> Accept None
     | EApp (_, _) -> Accept None
     | ELam (_, _, _, _) -> Accept None
     | EPi (_, _, _, _) -> Accept None
     | ELet (_, _, _, _, _) -> Accept None
     | ELit _ -> Accept None
     | EProj (owner, index, value) ->
       bind (core_reduce_projection rec0 env g owner index value)
         (fun field -> Accept (option_map (fun f -> core_apps f args) field))
     | EMData _ -> Accept None)
  in
  bind (project t0) (fun tp ->
    bind (project s) (fun sp ->
      match tp with
      | Some t1 ->
        (match sp with
         | Some s0 -> rec0.defeq_method g t1 s0
         | None -> rec0.defeq_method g t1 s)
      | None ->
        (match sp with
         | Some s0 -> rec0.defeq_method g t0 s0
         | None -> compare_after_whnf rec0 fuel0 env g t0 s)))

(** val core_is_true : expr -> bool **)

let core_is_true = function
| EConst (n0, l) ->
  (match l with
   | Nil -> name_eqb n0 core_true_name
   | Cons (_, _) -> False)
| _ -> False

(** val core_true_shortcut :
    methods -> environment -> context -> expr -> expr -> bool result **)

let core_true_shortcut rec0 env g t0 s =
  match match match core_is_true s with
              | True -> true_probe_allowed rec0.method_mode t0
              | False -> False with
        | True -> core_bool_ready env
        | False -> False with
  | True -> bind (rec0.whnf_method g t0) (fun tn -> Accept (core_is_true tn))
  | False -> Accept False

(** val defeq_step :
    methods -> nat -> environment -> name list -> context -> expr -> expr ->
    bool result **)

let defeq_step rec0 fuel0 env ps g t0 s =
  let rec1 = inference_only rec0 in
  bind (core_quick rec1 fuel0 g t0 s) (fun quick ->
    match quick with
    | Some ok -> Accept ok
    | None ->
      bind (core_true_shortcut rec1 env g t0 s) (fun shortcut ->
        match shortcut with
        | True -> Accept True
        | False ->
          bind (core_proof_irrel rec1 fuel0 g t0 s) (fun irrelevant ->
            match irrelevant with
            | Some ok -> Accept ok
            | None ->
              bind (rec1.whnf_core_method True g t0) (fun tn ->
                bind (rec1.whnf_core_method True g s) (fun sn ->
                  bind (core_lazy_delta (S fuel0) rec1 fuel0 env ps g tn sn)
                    (fun progress ->
                    match progress with
                    | ConversionDone ok -> Accept ok
                    | ConversionStuck (tn0, sn0) ->
                      core_finish_conversion rec1 fuel0 env g tn0 sn0))))))

(** val checker_mode :
    reduction_mode -> nat -> environment -> name list -> methods **)

let rec checker_mode mode fuel0 env ps =
  match fuel0 with
  | O ->
    { infer_method = (fun _ _ -> Decline OutOfFuel); infer_type_method =
      (fun _ _ -> Decline OutOfFuel); whnf_method = (fun _ _ -> Decline
      OutOfFuel); whnf_core_method = (fun _ _ _ -> Decline OutOfFuel);
      defeq_method = (fun _ _ _ -> Decline OutOfFuel); method_mode = mode;
      eager_defeq_method = (fun _ _ _ -> Decline OutOfFuel) }
  | S n0 ->
    { infer_method = (fun g e ->
      let rec0 = checker_mode mode n0 env ps in
      infer_step rec0 n0 env ps True g e); infer_type_method = (fun g e ->
      let rec0 = checker_mode mode n0 env ps in
      infer_step rec0 n0 env ps False g e); whnf_method = (fun g e ->
      let rec0 = checker_mode mode n0 env ps in
      whnf_loop (whnf_round_limit mode) rec0 n0 env ps g e);
      whnf_core_method = (fun cheap g e ->
      let rec0 = checker_mode mode n0 env ps in
      whnf_core_step rec0 n0 env ps cheap g e); defeq_method = (fun g t0 s ->
      let rec0 = checker_mode mode n0 env ps in
      defeq_step rec0 n0 env ps g t0 s); method_mode = mode;
      eager_defeq_method = (fun g t0 s ->
      let rec0 = checker_mode EagerReduction n0 env ps in
      defeq_step rec0 n0 env ps g t0 s) }

(** val checker : nat -> environment -> name list -> methods **)

let checker =
  checker_mode NormalReduction

(** val infer :
    nat -> environment -> name list -> context -> expr -> expr result **)

let infer fuel0 env ps g e =
  (checker fuel0 env ps).infer_method g e

(** val whnf :
    nat -> environment -> name list -> context -> expr -> expr result **)

let whnf fuel0 env ps g e =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S _ ->
    (match core_supported env e with
     | True -> (checker fuel0 env ps).whnf_method g e
     | False -> Decline UnsupportedExpression)

(** val defeq :
    nat -> environment -> name list -> context -> expr -> expr -> bool result **)

let defeq fuel0 env ps g t0 s =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S _ ->
    (match match core_supported env t0 with
           | True -> core_supported env s
           | False -> False with
     | True -> (checker fuel0 env ps).defeq_method g t0 s
     | False -> Decline UnsupportedExpression)

(** val check :
    nat -> environment -> name list -> context -> expr -> expr -> unit0 result **)

let check fuel0 env ps g e ty0 =
  bind (sort_of (checker fuel0 env ps) g ty0) (fun _ ->
    bind (infer fuel0 env ps g e) (fun et ->
      bind (defeq fuel0 env ps g et ty0) (fun ok -> require ok TypeMismatch)))

(** val check_defeq :
    nat -> environment -> name list -> context -> expr -> expr -> unit0 result **)

let check_defeq fuel0 env ps g t0 s =
  bind (infer fuel0 env ps g t0) (fun tt0 ->
    bind (infer fuel0 env ps g s) (fun st ->
      bind (defeq fuel0 env ps g tt0 st) (fun same_type ->
        bind (require same_type TypeMismatch) (fun _ ->
          bind (defeq fuel0 env ps g t0 s) (fun same_term ->
            require same_term NotDefinitionallyEqual)))))

type ind_local = { il_id : name; il_user : name; il_binder : binder_info;
                   il_type : expr }

type ind_state = { ist_next : nat; ist_context : context }

(** val initial_ind_state : ind_state **)

let initial_ind_state =
  { ist_next = O; ist_context = empty_context }

(** val local_expr : ind_local -> expr **)

let local_expr x0 =
  EFVar x0.il_id

(** val local_exprs : ind_local list -> expr list **)

let local_exprs xs =
  map local_expr xs

(** val ind_fresh :
    ind_state -> name -> binder_info -> expr -> (ind_local, ind_state) prod **)

let ind_fresh s user bi ty0 =
  let id = NameNum ((NameStr (NameAnon, (String ((Ascii (True, True, True,
    True, True, False, True, False)), (String ((Ascii (False, True, False,
    False, True, True, True, False)), (String ((Ascii (True, True, True,
    True, False, True, True, False)), (String ((Ascii (True, True, False,
    False, False, True, True, False)), (String ((Ascii (True, False, False,
    False, True, True, True, False)), (String ((Ascii (True, True, True,
    True, True, False, True, False)), (String ((Ascii (True, False, False,
    True, False, True, True, False)), (String ((Ascii (False, True, True,
    True, False, True, True, False)), (String ((Ascii (False, False, True,
    False, False, True, True, False)), EmptyString)))))))))))))))))))),
    (N.of_nat s.ist_next))
  in
  let x0 = { il_id = id; il_user = user; il_binder = bi; il_type = ty0 } in
  let g = s.ist_context in
  Pair (x0, { ist_next = (S s.ist_next); ist_context = { bound_context =
  g.bound_context; free_context = (Cons ((Pair (id, { binding_type = ty0;
  binding_value = None })), g.free_context)) } })

(** val abstract_local : name -> nat -> expr -> expr **)

let rec abstract_local id depth e = match e with
| EFVar n0 -> (match name_eqb id n0 with
               | True -> EBVar depth
               | False -> e)
| EApp (f, a) ->
  EApp ((abstract_local id depth f), (abstract_local id depth a))
| ELam (n0, bi, a, b) ->
  ELam (n0, bi, (abstract_local id depth a), (abstract_local id (S depth) b))
| EPi (n0, bi, a, b) ->
  EPi (n0, bi, (abstract_local id depth a), (abstract_local id (S depth) b))
| ELet (n0, a, v0, b, nd) ->
  ELet (n0, (abstract_local id depth a), (abstract_local id depth v0),
    (abstract_local id (S depth) b), nd)
| EProj (n0, i, a) -> EProj (n0, i, (abstract_local id depth a))
| EMData a -> EMData (abstract_local id depth a)
| _ -> e

(** val close_pi : ind_local list -> expr -> expr **)

let close_pi xs body =
  fold_right (fun x0 b -> EPi (x0.il_user, x0.il_binder, x0.il_type,
    (abstract_local x0.il_id O b))) body xs

(** val close_lam : ind_local list -> expr -> expr **)

let close_lam xs body =
  fold_right (fun x0 b -> ELam (x0.il_user, x0.il_binder, x0.il_type,
    (abstract_local x0.il_id O b))) body xs

(** val apply_exprs : expr -> expr list -> expr **)

let apply_exprs fn args =
  fold_left (fun x0 x1 -> EApp (x0, x1)) args fn

(** val apply_locals : expr -> ind_local list -> expr **)

let apply_locals fn args =
  apply_exprs fn (local_exprs args)

(** val split_app_aux : expr -> expr list -> (expr, expr list) prod **)

let rec split_app_aux e args =
  match e with
  | EApp (f, a) -> split_app_aux f (Cons (a, args))
  | _ -> Pair (e, args)

(** val split_app : expr -> (expr, expr list) prod **)

let split_app e =
  split_app_aux e Nil

(** val has_inductive : name list -> expr -> bool **)

let rec has_inductive names = function
| EConst (n0, _) -> name_mem n0 names
| EApp (a, b) ->
  (match has_inductive names a with
   | True -> True
   | False -> has_inductive names b)
| ELam (_, _, a, b) ->
  (match has_inductive names a with
   | True -> True
   | False -> has_inductive names b)
| EPi (_, _, a, b) ->
  (match has_inductive names a with
   | True -> True
   | False -> has_inductive names b)
| ELet (_, a, v0, b, _) ->
  (match match has_inductive names a with
         | True -> True
         | False -> has_inductive names v0 with
   | True -> True
   | False -> has_inductive names b)
| EProj (n0, _, a) ->
  (match name_mem n0 names with
   | True -> True
   | False -> has_inductive names a)
| EMData a -> has_inductive names a
| _ -> False

(** val raw_arity : expr -> nat **)

let rec raw_arity = function
| EPi (_, _, _, body) -> S (raw_arity body)
| _ -> O

(** val recursive_constructor : name list -> expr -> bool **)

let rec recursive_constructor names = function
| EPi (_, _, a, b) ->
  (match has_inductive names a with
   | True -> True
   | False -> recursive_constructor names b)
| _ -> False

(** val reflexive_constructor : name list -> expr -> bool **)

let rec reflexive_constructor names = function
| EPi (_, _, a, b) ->
  (match match a with
         | EPi (_, _, _, _) -> has_inductive names a
         | _ -> False with
   | True -> True
   | False -> reflexive_constructor names b)
| _ -> False

(** val level_never_zero : level -> bool **)

let rec level_never_zero = function
| LSucc _ -> True
| LMax (a, b) ->
  (match level_never_zero a with
   | True -> True
   | False -> level_never_zero b)
| LIMax (_, b) -> level_never_zero b
| _ -> False

(** val ind_sort :
    nat -> environment -> name list -> ind_state -> expr -> level result **)

let ind_sort fuel0 env ps s e =
  bind (infer fuel0 env ps s.ist_context e) (fun ty0 ->
    bind (whnf fuel0 env ps s.ist_context ty0) (fun ty1 ->
      match ty1 with
      | ESort u0 -> Accept u0
      | _ -> Reject ExpectedSort))

(** val consume_type_annotations : expr -> expr **)

let rec consume_type_annotations e = match e with
| EApp (e0, a) ->
  (match e0 with
   | EConst (n0, _) ->
     (match match name_eqb n0 (NameStr (NameAnon, (String ((Ascii (True,
                    True, True, True, False, True, True, False)), (String
                    ((Ascii (True, False, True, False, True, True, True,
                    False)), (String ((Ascii (False, False, True, False,
                    True, True, True, False)), (String ((Ascii (False, False,
                    False, False, True, False, True, False)), (String ((Ascii
                    (True, False, False, False, False, True, True, False)),
                    (String ((Ascii (False, True, False, False, True, True,
                    True, False)), (String ((Ascii (True, False, False,
                    False, False, True, True, False)), (String ((Ascii (True,
                    False, True, True, False, True, True, False)),
                    EmptyString)))))))))))))))))) with
            | True -> True
            | False ->
              name_eqb n0 (NameStr (NameAnon, (String ((Ascii (True, True,
                False, False, True, True, True, False)), (String ((Ascii
                (True, False, True, False, False, True, True, False)),
                (String ((Ascii (True, False, True, True, False, True, True,
                False)), (String ((Ascii (True, False, False, True, False,
                True, True, False)), (String ((Ascii (True, True, True, True,
                False, False, True, False)), (String ((Ascii (True, False,
                True, False, True, True, True, False)), (String ((Ascii
                (False, False, True, False, True, True, True, False)),
                (String ((Ascii (False, False, False, False, True, False,
                True, False)), (String ((Ascii (True, False, False, False,
                False, True, True, False)), (String ((Ascii (False, True,
                False, False, True, True, True, False)), (String ((Ascii
                (True, False, False, False, False, True, True, False)),
                (String ((Ascii (True, False, True, True, False, True, True,
                False)), EmptyString)))))))))))))))))))))))))) with
      | True -> consume_type_annotations a
      | False -> e)
   | EApp (e1, a0) ->
     (match e1 with
      | EConst (n0, _) ->
        (match match name_eqb n0 (NameStr (NameAnon, (String ((Ascii (True,
                       True, True, True, False, True, True, False)), (String
                       ((Ascii (False, False, False, False, True, True, True,
                       False)), (String ((Ascii (False, False, True, False,
                       True, True, True, False)), (String ((Ascii (False,
                       False, False, False, True, False, True, False)),
                       (String ((Ascii (True, False, False, False, False,
                       True, True, False)), (String ((Ascii (False, True,
                       False, False, True, True, True, False)), (String
                       ((Ascii (True, False, False, False, False, True, True,
                       False)), (String ((Ascii (True, False, True, True,
                       False, True, True, False)),
                       EmptyString)))))))))))))))))) with
               | True -> True
               | False ->
                 name_eqb n0 (NameStr (NameAnon, (String ((Ascii (True,
                   False, False, False, False, True, True, False)), (String
                   ((Ascii (True, False, True, False, True, True, True,
                   False)), (String ((Ascii (False, False, True, False, True,
                   True, True, False)), (String ((Ascii (True, True, True,
                   True, False, True, True, False)), (String ((Ascii (False,
                   False, False, False, True, False, True, False)), (String
                   ((Ascii (True, False, False, False, False, True, True,
                   False)), (String ((Ascii (False, True, False, False, True,
                   True, True, False)), (String ((Ascii (True, False, False,
                   False, False, True, True, False)), (String ((Ascii (True,
                   False, True, True, False, True, True, False)),
                   EmptyString)))))))))))))))))))) with
         | True -> consume_type_annotations a0
         | False -> e)
      | _ -> e)
   | _ -> e)
| _ -> e

(** val checked_domain :
    nat -> environment -> name list -> ind_state -> expr -> expr result **)

let checked_domain fuel0 env ps s a =
  let cleaned = consume_type_annotations a in
  (match expr_eqb a cleaned with
   | True -> Accept a
   | False ->
     bind (defeq fuel0 env ps s.ist_context a cleaned) (fun ok ->
       bind (require ok TypeMismatch) (fun _ -> Accept cleaned)))

(** val open_telescope :
    nat -> nat -> environment -> name list -> ind_state -> expr ->
    ((ind_local list, expr) prod, ind_state) prod result **)

let rec open_telescope depth fuel0 env ps s ty0 =
  match depth with
  | O -> Decline OutOfFuel
  | S depth0 ->
    bind (whnf fuel0 env ps s.ist_context ty0) (fun ty1 ->
      match ty1 with
      | EPi (n0, bi, a, b) ->
        bind (checked_domain fuel0 env ps s a) (fun a0 ->
          let Pair (x0, s0) = ind_fresh s n0 bi a0 in
          bind
            (open_telescope depth0 fuel0 env ps s0
              (instantiate b (local_expr x0)))
            (fun rest ->
            let Pair (p0, s1) = rest in
            let Pair (xs, body) = p0 in
            Accept (Pair ((Pair ((Cons (x0, xs)), body)), s1))))
      | _ -> Accept (Pair ((Pair (Nil, ty1)), s)))

(** val open_parameters :
    nat -> nat -> environment -> name list -> ind_state -> expr ->
    ((ind_local list, expr) prod, ind_state) prod result **)

let rec open_parameters count fuel0 env ps s ty0 =
  match count with
  | O -> Accept (Pair ((Pair (Nil, ty0)), s))
  | S count0 ->
    bind (whnf fuel0 env ps s.ist_context ty0) (fun ty1 ->
      match ty1 with
      | EPi (n0, bi, a, b) ->
        bind (checked_domain fuel0 env ps s a) (fun a0 ->
          let Pair (x0, s0) = ind_fresh s n0 bi a0 in
          bind
            (open_parameters count0 fuel0 env ps s0
              (instantiate b (local_expr x0)))
            (fun rest ->
            let Pair (p0, s1) = rest in
            let Pair (xs, body) = p0 in
            Accept (Pair ((Pair ((Cons (x0, xs)), body)), s1))))
      | _ -> Reject MalformedDeclaration)

(** val apply_parameters :
    ind_local list -> nat -> environment -> name list -> ind_state -> expr ->
    expr result **)

let rec apply_parameters params fuel0 env ps s ty0 =
  match params with
  | Nil -> Accept ty0
  | Cons (x0, xs) ->
    bind (whnf fuel0 env ps s.ist_context ty0) (fun ty1 ->
      match ty1 with
      | EPi (_, _, a, b) ->
        bind (defeq fuel0 env ps s.ist_context a x0.il_type) (fun ok ->
          bind (require ok TypeMismatch) (fun _ ->
            apply_parameters xs fuel0 env ps s (instantiate b (local_expr x0))))
      | _ -> Reject MalformedDeclaration)

(** val primitive_name : primitive_kind -> name **)

let primitive_name = function
| PNatAdd ->
  NameStr (core_nat_name, (String ((Ascii (True, False, False, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, False,
    True, True, False)), EmptyString)))))))
| PNatPred ->
  NameStr (core_nat_name, (String ((Ascii (False, False, False, False, True,
    True, True, False)), (String ((Ascii (False, True, False, False, True,
    True, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, False,
    True, True, False)), EmptyString)))))))))
| PNatSub ->
  NameStr (core_nat_name, (String ((Ascii (True, True, False, False, True,
    True, True, False)), (String ((Ascii (True, False, True, False, True,
    True, True, False)), (String ((Ascii (False, True, False, False, False,
    True, True, False)), EmptyString)))))))
| PNatMul ->
  NameStr (core_nat_name, (String ((Ascii (True, False, True, True, False,
    True, True, False)), (String ((Ascii (True, False, True, False, True,
    True, True, False)), (String ((Ascii (False, False, True, True, False,
    True, True, False)), EmptyString)))))))
| PNatPow ->
  NameStr (core_nat_name, (String ((Ascii (False, False, False, False, True,
    True, True, False)), (String ((Ascii (True, True, True, True, False,
    True, True, False)), (String ((Ascii (True, True, True, False, True,
    True, True, False)), EmptyString)))))))
| PNatGcd ->
  NameStr (core_nat_name, (String ((Ascii (True, True, True, False, False,
    True, True, False)), (String ((Ascii (True, True, False, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, False,
    True, True, False)), EmptyString)))))))
| PNatMod ->
  NameStr (core_nat_name, (String ((Ascii (True, False, True, True, False,
    True, True, False)), (String ((Ascii (True, True, True, True, False,
    True, True, False)), (String ((Ascii (False, False, True, False, False,
    True, True, False)), EmptyString)))))))
| PNatDiv ->
  NameStr (core_nat_name, (String ((Ascii (False, False, True, False, False,
    True, True, False)), (String ((Ascii (True, False, False, True, False,
    True, True, False)), (String ((Ascii (False, True, True, False, True,
    True, True, False)), EmptyString)))))))
| PNatBEq ->
  NameStr (core_nat_name, (String ((Ascii (False, True, False, False, False,
    True, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), (String ((Ascii (True, False, False, False, True,
    True, True, False)), EmptyString)))))))
| PNatBLE ->
  NameStr (core_nat_name, (String ((Ascii (False, True, False, False, False,
    True, True, False)), (String ((Ascii (False, False, True, True, False,
    True, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), EmptyString)))))))
| PNatLAnd ->
  NameStr (core_nat_name, (String ((Ascii (False, False, True, True, False,
    True, True, False)), (String ((Ascii (True, False, False, False, False,
    True, True, False)), (String ((Ascii (False, True, True, True, False,
    True, True, False)), (String ((Ascii (False, False, True, False, False,
    True, True, False)), EmptyString)))))))))
| PNatLOr ->
  NameStr (core_nat_name, (String ((Ascii (False, False, True, True, False,
    True, True, False)), (String ((Ascii (True, True, True, True, False,
    True, True, False)), (String ((Ascii (False, True, False, False, True,
    True, True, False)), EmptyString)))))))
| PNatXor ->
  NameStr (core_nat_name, (String ((Ascii (False, False, False, True, True,
    True, True, False)), (String ((Ascii (True, True, True, True, False,
    True, True, False)), (String ((Ascii (False, True, False, False, True,
    True, True, False)), EmptyString)))))))
| PNatBitwise ->
  NameStr (core_nat_name, (String ((Ascii (False, True, False, False, False,
    True, True, False)), (String ((Ascii (True, False, False, True, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), (String ((Ascii (True, True, True, False, True,
    True, True, False)), (String ((Ascii (True, False, False, True, False,
    True, True, False)), (String ((Ascii (True, True, False, False, True,
    True, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), EmptyString)))))))))))))))
| PNatShiftLeft ->
  NameStr (core_nat_name, (String ((Ascii (True, True, False, False, True,
    True, True, False)), (String ((Ascii (False, False, False, True, False,
    True, True, False)), (String ((Ascii (True, False, False, True, False,
    True, True, False)), (String ((Ascii (False, True, True, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), (String ((Ascii (False, False, True, True, False,
    False, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), (String ((Ascii (False, True, True, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), EmptyString)))))))))))))))))))
| PNatShiftRight ->
  NameStr (core_nat_name, (String ((Ascii (True, True, False, False, True,
    True, True, False)), (String ((Ascii (False, False, False, True, False,
    True, True, False)), (String ((Ascii (True, False, False, True, False,
    True, True, False)), (String ((Ascii (False, True, True, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), (String ((Ascii (False, True, False, False, True,
    False, True, False)), (String ((Ascii (True, False, False, True, False,
    True, True, False)), (String ((Ascii (True, True, True, False, False,
    True, True, False)), (String ((Ascii (False, False, False, True, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), EmptyString)))))))))))))))))))))
| PCharOfNat -> core_char_of_nat
| PStringOfList -> core_string_of_list

(** val primitive_kinds : primitive_kind list **)

let primitive_kinds =
  Cons (PNatAdd, (Cons (PNatPred, (Cons (PNatSub, (Cons (PNatMul, (Cons
    (PNatPow, (Cons (PNatGcd, (Cons (PNatMod, (Cons (PNatDiv, (Cons (PNatBEq,
    (Cons (PNatBLE, (Cons (PNatBitwise, (Cons (PNatLAnd, (Cons (PNatLOr,
    (Cons (PNatXor, (Cons (PNatShiftLeft, (Cons (PNatShiftRight, (Cons
    (PCharOfNat, (Cons (PStringOfList, Nil)))))))))))))))))))))))))))))))))))

(** val primitive_lookup : name -> primitive_kind option **)

let primitive_lookup n0 =
  find (fun op -> name_eqb n0 (primitive_name op)) primitive_kinds

(** val primitive_bitwise_name : name **)

let primitive_bitwise_name =
  NameStr (core_nat_name, (String ((Ascii (False, True, False, False, False,
    True, True, False)), (String ((Ascii (True, False, False, True, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), (String ((Ascii (True, True, True, False, True,
    True, True, False)), (String ((Ascii (True, False, False, True, False,
    True, True, False)), (String ((Ascii (True, True, False, False, True,
    True, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), EmptyString)))))))))))))))

(** val primitive_bool : expr **)

let primitive_bool =
  EConst (core_bool_name, Nil)

(** val primitive_char : expr **)

let primitive_char =
  EConst (core_char_name, Nil)

(** val primitive_string : expr **)

let primitive_string =
  EConst (core_string_name, Nil)

(** val primitive_list_char : expr **)

let primitive_list_char =
  EApp ((EConst (core_list_name, (Cons (LZero, Nil)))), primitive_char)

(** val primitive_arrow : expr -> expr -> expr **)

let primitive_arrow a b =
  EPi (NameAnon, BDefault, a, b)

(** val primitive_signature : primitive_kind -> expr **)

let primitive_signature = function
| PNatPred -> primitive_arrow core_nat core_nat
| PNatBEq ->
  primitive_arrow core_nat (primitive_arrow core_nat primitive_bool)
| PNatBLE ->
  primitive_arrow core_nat (primitive_arrow core_nat primitive_bool)
| PNatBitwise ->
  primitive_arrow
    (primitive_arrow primitive_bool
      (primitive_arrow primitive_bool primitive_bool))
    (primitive_arrow core_nat (primitive_arrow core_nat core_nat))
| PCharOfNat -> primitive_arrow core_nat primitive_char
| PStringOfList -> primitive_arrow primitive_list_char primitive_string
| _ -> primitive_arrow core_nat (primitive_arrow core_nat core_nat)

(** val primitive_zero : expr **)

let primitive_zero =
  EConst (core_zero_name, Nil)

(** val primitive_succ : expr -> expr **)

let primitive_succ e =
  EApp ((EConst (core_succ_name, Nil)), e)

(** val primitive_one : expr **)

let primitive_one =
  primitive_succ primitive_zero

(** val primitive_two : expr **)

let primitive_two =
  primitive_succ primitive_one

(** val primitive_true : expr **)

let primitive_true =
  EConst (core_true_name, Nil)

(** val primitive_false : expr **)

let primitive_false =
  EConst (core_false_name, Nil)

(** val primitive_call : primitive_kind -> expr list -> expr **)

let primitive_call op args =
  core_apps (EConst ((primitive_name op), Nil)) args

(** val primitive_check_signature : nat -> expr -> expr -> unit0 result **)

let rec primitive_check_signature fuel0 actual expected0 =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    (match actual with
     | EApp (a, b) ->
       (match expected0 with
        | EApp (c, d) ->
          bind (primitive_check_signature fuel1 a c) (fun _ ->
            primitive_check_signature fuel1 b d)
        | _ -> require (expr_eqb actual expected0) TypeMismatch)
     | EPi (_, _, a, b) ->
       (match expected0 with
        | EPi (_, _, c, d) ->
          bind (primitive_check_signature fuel1 a c) (fun _ ->
            primitive_check_signature fuel1 b d)
        | _ -> require (expr_eqb actual expected0) TypeMismatch)
     | EMData a -> primitive_check_signature fuel1 a expected0
     | _ -> require (expr_eqb actual expected0) TypeMismatch)

(** val primitive_authenticated :
    nat -> environment -> primitive_kind -> unit0 result **)

let primitive_authenticated fuel0 env op =
  match find_decl (primitive_name op) env with
  | Some d ->
    (match d.decl_kind_of with
     | DPrimitive actual ->
       (match d.decl_value with
        | Some _ ->
          bind
            (require
              (match primitive_kind_eqb actual op with
               | True -> Nat.eqb (length d.decl_params) O
               | False -> False)
              MalformedDeclaration)
            (fun _ ->
            primitive_check_signature fuel0 d.decl_type
              (primitive_signature op))
        | None -> Reject MalformedDeclaration)
     | _ -> Reject MalformedDeclaration)
  | None -> Reject MalformedDeclaration

(** val primitive_dependencies :
    nat -> environment -> primitive_kind -> unit0 result **)

let primitive_dependencies fuel0 env op =
  bind (require (core_nat_ready env) MalformedDeclaration) (fun _ ->
    match op with
    | PNatSub -> primitive_authenticated fuel0 env PNatPred
    | PNatMul -> primitive_authenticated fuel0 env PNatAdd
    | PNatPow -> primitive_authenticated fuel0 env PNatMul
    | PNatBEq -> require (core_bool_ready env) MalformedDeclaration
    | PNatBLE -> require (core_bool_ready env) MalformedDeclaration
    | PNatShiftLeft -> primitive_authenticated fuel0 env PNatMul
    | PNatShiftRight -> primitive_authenticated fuel0 env PNatDiv
    | _ -> Accept Tt)

(** val primitive_closed : nat -> nat -> expr -> unit0 result **)

let rec primitive_closed fuel0 depth e =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    (match e with
     | EBVar i -> require (Nat.ltb i depth) LooseBoundVariable
     | EFVar _ -> Reject UnknownFreeVariable
     | EMVar _ -> Reject MetaVariable
     | EApp (a, b) ->
       bind (primitive_closed fuel1 depth a) (fun _ ->
         primitive_closed fuel1 depth b)
     | ELam (_, _, a, b) ->
       bind (primitive_closed fuel1 depth a) (fun _ ->
         primitive_closed fuel1 (S depth) b)
     | EPi (_, _, a, b) ->
       bind (primitive_closed fuel1 depth a) (fun _ ->
         primitive_closed fuel1 (S depth) b)
     | ELet (_, a, v0, b, _) ->
       bind (primitive_closed fuel1 depth a) (fun _ ->
         bind (primitive_closed fuel1 depth v0) (fun _ ->
           primitive_closed fuel1 (S depth) b))
     | EProj (_, _, a) -> primitive_closed fuel1 depth a
     | EMData a -> primitive_closed fuel1 depth a
     | _ -> Accept Tt)

type primitive_equation = { primitive_context : context;
                            primitive_lhs : expr; primitive_rhs : expr }

(** val primitive_equation_at :
    context -> expr -> expr -> primitive_equation **)

let primitive_equation_at g a b =
  { primitive_context = g; primitive_lhs = a; primitive_rhs = b }

(** val primitive_x_context : context **)

let primitive_x_context =
  push_binding empty_context core_nat None

(** val primitive_xy_context : context **)

let primitive_xy_context =
  push_binding primitive_x_context core_nat None

(** val primitive_equations :
    primitive_kind -> expr -> primitive_equation list option **)

let primitive_equations op body =
  let eq0 = primitive_equation_at empty_context in
  let eqx = primitive_equation_at primitive_x_context in
  let eqxy = primitive_equation_at primitive_xy_context in
  let f = fun x0 y -> core_apps body (Cons (x0, (Cons (y, Nil)))) in
  let x0 = EBVar O in
  let xx = EBVar (S O) in
  let y = EBVar O in
  let base = fun z0 -> eqx (f x0 primitive_zero) z0 in
  let step = fun z0 -> eqxy (f xx (primitive_succ y)) z0 in
  (match op with
   | PNatAdd ->
     Some (Cons ((base x0), (Cons ((step (primitive_succ (f xx y))), Nil))))
   | PNatPred ->
     Some (Cons ((eq0 (EApp (body, primitive_zero)) primitive_zero), (Cons
       ((eqx (EApp (body, (primitive_succ x0))) x0), Nil))))
   | PNatSub ->
     Some (Cons ((base x0), (Cons
       ((step (primitive_call PNatPred (Cons ((f xx y), Nil)))), Nil))))
   | PNatMul ->
     Some (Cons ((base primitive_zero), (Cons
       ((step (primitive_call PNatAdd (Cons ((f xx y), (Cons (xx, Nil)))))),
       Nil))))
   | PNatPow ->
     Some (Cons ((base primitive_one), (Cons
       ((step (primitive_call PNatMul (Cons ((f xx y), (Cons (xx, Nil)))))),
       Nil))))
   | PNatBEq ->
     Some (Cons ((eq0 (f primitive_zero primitive_zero) primitive_true),
       (Cons
       ((eqx (f primitive_zero (primitive_succ x0))
          (match op with
           | PNatBEq -> primitive_false
           | _ -> primitive_true)),
       (Cons ((eqx (f (primitive_succ x0) primitive_zero) primitive_false),
       (Cons ((eqxy (f (primitive_succ xx) (primitive_succ y)) (f xx y)),
       Nil))))))))
   | PNatBLE ->
     Some (Cons ((eq0 (f primitive_zero primitive_zero) primitive_true),
       (Cons
       ((eqx (f primitive_zero (primitive_succ x0))
          (match op with
           | PNatBEq -> primitive_false
           | _ -> primitive_true)),
       (Cons ((eqx (f (primitive_succ x0) primitive_zero) primitive_false),
       (Cons ((eqxy (f (primitive_succ xx) (primitive_succ y)) (f xx y)),
       Nil))))))))
   | PNatShiftLeft ->
     Some (Cons ((base x0), (Cons
       ((step
          (f
            (primitive_call PNatMul (Cons (primitive_two, (Cons (xx, Nil)))))
            y)),
       Nil))))
   | PNatShiftRight ->
     Some (Cons ((base x0), (Cons
       ((step
          (primitive_call PNatDiv (Cons ((f xx y), (Cons (primitive_two,
            Nil)))))),
       Nil))))
   | _ -> None)

(** val primitive_check_equations :
    nat -> nat -> environment -> primitive_equation list -> unit0 result **)

let rec primitive_check_equations steps fuel0 env = function
| Nil -> Accept Tt
| Cons (e, es) ->
  (match steps with
   | O -> Decline OutOfFuel
   | S steps0 ->
     bind
       (check_defeq fuel0 env Nil e.primitive_context e.primitive_lhs
         e.primitive_rhs)
       (fun _ -> primitive_check_equations steps0 fuel0 env es))

(** val primitive_path : string list -> name **)

let primitive_path parts =
  fold_left (fun x0 x1 -> NameStr (x0, x1)) parts NameAnon

(** val primitive_const : string list -> level list -> expr **)

let primitive_const parts us =
  EConst ((primitive_path parts), us)

module PrimitiveQuote =
 struct
  type term = nat -> expr

  (** val embed : expr -> term **)

  let embed e depth =
    lift depth O e

  (** val app : term -> term -> term **)

  let app f a depth =
    EApp ((f depth), (a depth))

  (** val apps : term -> term list -> term **)

  let apps f args depth =
    core_apps (f depth) (map (fun a -> a depth) args)

  (** val lam : term -> (term -> term) -> term **)

  let lam a b depth =
    ELam (NameAnon, BDefault, (a depth),
      (b (fun d -> EBVar (sub d (S depth))) (S depth)))

  (** val pi : term -> (term -> term) -> term **)

  let pi a b depth =
    EPi (NameAnon, BDefault, (a depth),
      (b (fun d -> EBVar (sub d (S depth))) (S depth)))

  (** val arrow : term -> term -> term **)

  let arrow a b =
    pi a (fun _ -> b)

  (** val run : term -> expr **)

  let run e =
    e O

  (** val const : string list -> level list -> term **)

  let const parts us =
    embed (primitive_const parts us)

  (** val prop : term **)

  let prop =
    embed (ESort LZero)

  (** val type0 : term **)

  let type0 =
    embed (ESort (LSucc LZero))

  (** val nat : term **)

  let nat =
    embed core_nat

  (** val bool : term **)

  let bool =
    embed primitive_bool

  (** val tru : term **)

  let tru =
    embed primitive_true

  (** val fal : term **)

  let fal =
    embed primitive_false

  (** val zero : term **)

  let zero =
    embed primitive_zero

  (** val one : term **)

  let one =
    embed primitive_one

  (** val two : term **)

  let two =
    embed primitive_two

  (** val succ : term -> term **)

  let succ n0 =
    app (embed (EConst (core_succ_name, Nil))) n0

  (** val call : primitive_kind -> term list -> term **)

  let call op args =
    apps (embed (EConst ((primitive_name op), Nil))) args

  (** val eq : term -> term -> term -> term **)

  let eq a x0 y =
    apps
      (const (Cons ((String ((Ascii (True, False, True, False, False, False,
        True, False)), (String ((Ascii (True, False, False, False, True,
        True, True, False)), EmptyString)))), Nil)) (Cons ((LSucc LZero),
        Nil)))
      (Cons (a, (Cons (x0, (Cons (y, Nil))))))

  (** val refl : term -> term -> term **)

  let refl a x0 =
    apps
      (const (Cons ((String ((Ascii (True, False, True, False, False, False,
        True, False)), (String ((Ascii (True, False, False, False, True,
        True, True, False)), EmptyString)))), (Cons ((String ((Ascii (False,
        True, False, False, True, True, True, False)), (String ((Ascii (True,
        False, True, False, False, True, True, False)), (String ((Ascii
        (False, True, True, False, False, True, True, False)), (String
        ((Ascii (False, False, True, True, False, True, True, False)),
        EmptyString)))))))), Nil)))) (Cons ((LSucc LZero), Nil)))
      (Cons (a, (Cons (x0, Nil))))

  (** val not : term -> term **)

  let not p0 =
    app
      (const (Cons ((String ((Ascii (False, True, True, True, False, False,
        True, False)), (String ((Ascii (True, True, True, True, False, True,
        True, False)), (String ((Ascii (False, False, True, False, True,
        True, True, False)), EmptyString)))))), Nil)) Nil)
      p0

  (** val dec : term -> term **)

  let dec p0 =
    app
      (const (Cons ((String ((Ascii (False, False, True, False, False, False,
        True, False)), (String ((Ascii (True, False, True, False, False,
        True, True, False)), (String ((Ascii (True, True, False, False,
        False, True, True, False)), (String ((Ascii (True, False, False,
        True, False, True, True, False)), (String ((Ascii (False, False,
        True, False, False, True, True, False)), (String ((Ascii (True,
        False, False, False, False, True, True, False)), (String ((Ascii
        (False, True, False, False, False, True, True, False)), (String
        ((Ascii (False, False, True, True, False, True, True, False)),
        (String ((Ascii (True, False, True, False, False, True, True,
        False)), EmptyString)))))))))))))))))), Nil)) Nil)
      p0

  (** val is_true : term -> term -> term **)

  let is_true p0 h =
    apps
      (const (Cons ((String ((Ascii (False, False, True, False, False, False,
        True, False)), (String ((Ascii (True, False, True, False, False,
        True, True, False)), (String ((Ascii (True, True, False, False,
        False, True, True, False)), (String ((Ascii (True, False, False,
        True, False, True, True, False)), (String ((Ascii (False, False,
        True, False, False, True, True, False)), (String ((Ascii (True,
        False, False, False, False, True, True, False)), (String ((Ascii
        (False, True, False, False, False, True, True, False)), (String
        ((Ascii (False, False, True, True, False, True, True, False)),
        (String ((Ascii (True, False, True, False, False, True, True,
        False)), EmptyString)))))))))))))))))), (Cons ((String ((Ascii (True,
        False, False, True, False, True, True, False)), (String ((Ascii
        (True, True, False, False, True, True, True, False)), (String ((Ascii
        (False, False, True, False, True, False, True, False)), (String
        ((Ascii (False, True, False, False, True, True, True, False)),
        (String ((Ascii (True, False, True, False, True, True, True, False)),
        (String ((Ascii (True, False, True, False, False, True, True,
        False)), EmptyString)))))))))))), Nil)))) Nil)
      (Cons (p0, (Cons (h, Nil))))

  (** val is_false : term -> term -> term **)

  let is_false p0 h =
    apps
      (const (Cons ((String ((Ascii (False, False, True, False, False, False,
        True, False)), (String ((Ascii (True, False, True, False, False,
        True, True, False)), (String ((Ascii (True, True, False, False,
        False, True, True, False)), (String ((Ascii (True, False, False,
        True, False, True, True, False)), (String ((Ascii (False, False,
        True, False, False, True, True, False)), (String ((Ascii (True,
        False, False, False, False, True, True, False)), (String ((Ascii
        (False, True, False, False, False, True, True, False)), (String
        ((Ascii (False, False, True, True, False, True, True, False)),
        (String ((Ascii (True, False, True, False, False, True, True,
        False)), EmptyString)))))))))))))))))), (Cons ((String ((Ascii (True,
        False, False, True, False, True, True, False)), (String ((Ascii
        (True, True, False, False, True, True, True, False)), (String ((Ascii
        (False, True, True, False, False, False, True, False)), (String
        ((Ascii (True, False, False, False, False, True, True, False)),
        (String ((Ascii (False, False, True, True, False, True, True,
        False)), (String ((Ascii (True, True, False, False, True, True, True,
        False)), (String ((Ascii (True, False, True, False, False, True,
        True, False)), EmptyString)))))))))))))), Nil)))) Nil)
      (Cons (p0, (Cons (h, Nil))))

  (** val ite : term -> term -> term -> term -> term -> term **)

  let ite ty0 p0 d t0 e =
    apps
      (const (Cons ((String ((Ascii (True, False, False, True, False, True,
        True, False)), (String ((Ascii (False, False, True, False, True,
        True, True, False)), (String ((Ascii (True, False, True, False,
        False, True, True, False)), EmptyString)))))), Nil)) (Cons ((LSucc
        LZero), Nil)))
      (Cons (ty0, (Cons (p0, (Cons (d, (Cons (t0, (Cons (e, Nil))))))))))

  (** val dite :
      term -> term -> term -> (term -> term) -> (term -> term) -> term **)

  let dite ty0 p0 d t0 e =
    apps
      (const (Cons ((String ((Ascii (False, False, True, False, False, True,
        True, False)), (String ((Ascii (True, False, False, True, False,
        True, True, False)), (String ((Ascii (False, False, True, False,
        True, True, True, False)), (String ((Ascii (True, False, True, False,
        False, True, True, False)), EmptyString)))))))), Nil)) (Cons ((LSucc
        LZero), Nil)))
      (Cons (ty0, (Cons (p0, (Cons (d, (Cons ((lam p0 t0), (Cons
      ((lam (not p0) e), Nil))))))))))

  (** val bool_dec : term -> term **)

  let bool_dec b =
    apps
      (const (Cons ((String ((Ascii (False, True, False, False, False, False,
        True, False)), (String ((Ascii (True, True, True, True, False, True,
        True, False)), (String ((Ascii (True, True, True, True, False, True,
        True, False)), (String ((Ascii (False, False, True, True, False,
        True, True, False)), EmptyString)))))))), (Cons ((String ((Ascii
        (False, False, True, False, False, True, True, False)), (String
        ((Ascii (True, False, True, False, False, True, True, False)),
        (String ((Ascii (True, True, False, False, False, True, True,
        False)), (String ((Ascii (True, False, True, False, False, False,
        True, False)), (String ((Ascii (True, False, False, False, True,
        True, True, False)), EmptyString)))))))))), Nil)))) Nil)
      (Cons (b, (Cons (tru, Nil))))
 end

module PQ = PrimitiveQuote

type primitive_reflection = { reflection_type : expr; reflection_true : 
                              expr; reflection_false : expr;
                              reflection_dec : expr }

(** val primitive_reflection_type : bool -> expr **)

let primitive_reflection_type false_eq =
  PQ.run
    (PQ.lam PQ.prop (fun p0 ->
      PQ.lam PQ.bool (fun b ->
        PQ.pi PQ.prop (fun q0 ->
          PQ.arrow
            (PQ.arrow (PQ.arrow (PQ.eq PQ.bool b PQ.tru) p0)
              (PQ.arrow
                (PQ.arrow
                  (match false_eq with
                   | True -> PQ.eq PQ.bool b PQ.fal
                   | False -> PQ.not (PQ.eq PQ.bool b PQ.tru))
                  (PQ.not p0))
                q0))
            q0))))

(** val primitive_reflection_make : bool -> primitive_reflection **)

let primitive_reflection_make false_eq =
  let rt = primitive_reflection_type false_eq in
  let relation0 = fun p0 b ->
    PQ.apps (PQ.embed rt) (Cons (p0, (Cons (b, Nil))))
  in
  { reflection_type = rt; reflection_true =
  (PQ.run
    (PQ.lam PQ.prop (fun p0 ->
      PQ.lam (relation0 p0 PQ.tru) (fun h ->
        PQ.apps h (Cons (p0, (Cons
          ((PQ.lam (PQ.arrow (PQ.eq PQ.bool PQ.tru PQ.tru) p0) (fun hp ->
             PQ.lam
               (PQ.arrow
                 (match false_eq with
                  | True -> PQ.eq PQ.bool PQ.tru PQ.fal
                  | False -> PQ.not (PQ.eq PQ.bool PQ.tru PQ.tru))
                 (PQ.not p0))
               (fun _ -> PQ.app hp (PQ.refl PQ.bool PQ.tru)))),
          Nil))))))));
  reflection_false =
  (PQ.run
    (PQ.lam PQ.prop (fun p0 ->
      PQ.lam (relation0 p0 PQ.fal) (fun h ->
        PQ.apps h (Cons ((PQ.not p0), (Cons
          ((PQ.lam (PQ.arrow (PQ.eq PQ.bool PQ.fal PQ.tru) p0) (fun _ ->
             PQ.lam
               (PQ.arrow
                 (match false_eq with
                  | True -> PQ.eq PQ.bool PQ.fal PQ.fal
                  | False -> PQ.not (PQ.eq PQ.bool PQ.fal PQ.tru))
                 (PQ.not p0))
               (fun hn ->
               PQ.app hn
                 (match false_eq with
                  | True -> PQ.refl PQ.bool PQ.fal
                  | False ->
                    PQ.lam (PQ.eq PQ.bool PQ.fal PQ.tru) (fun bad ->
                      PQ.apps
                        (PQ.const (Cons ((String ((Ascii (False, True, False,
                          False, False, False, True, False)), (String ((Ascii
                          (True, True, True, True, False, True, True,
                          False)), (String ((Ascii (True, True, True, True,
                          False, True, True, False)), (String ((Ascii (False,
                          False, True, True, False, True, True, False)),
                          EmptyString)))))))), (Cons ((String ((Ascii (False,
                          True, True, True, False, True, True, False)),
                          (String ((Ascii (True, True, True, True, False,
                          True, True, False)), (String ((Ascii (True, True,
                          False, False, False, False, True, False)), (String
                          ((Ascii (True, True, True, True, False, True, True,
                          False)), (String ((Ascii (False, True, True, True,
                          False, True, True, False)), (String ((Ascii (False,
                          True, True, False, False, True, True, False)),
                          (String ((Ascii (True, False, True, False, True,
                          True, True, False)), (String ((Ascii (True, True,
                          False, False, True, True, True, False)), (String
                          ((Ascii (True, False, False, True, False, True,
                          True, False)), (String ((Ascii (True, True, True,
                          True, False, True, True, False)), (String ((Ascii
                          (False, True, True, True, False, True, True,
                          False)), EmptyString)))))))))))))))))))))), Nil))))
                          (Cons (LZero, Nil)))
                        (Cons
                        ((PQ.const (Cons ((String ((Ascii (False, True, True,
                           False, False, False, True, False)), (String
                           ((Ascii (True, False, False, False, False, True,
                           True, False)), (String ((Ascii (False, False,
                           True, True, False, True, True, False)), (String
                           ((Ascii (True, True, False, False, True, True,
                           True, False)), (String ((Ascii (True, False, True,
                           False, False, True, True, False)),
                           EmptyString)))))))))), Nil)) Nil),
                        (Cons (PQ.fal, (Cons (PQ.tru, (Cons (bad, Nil))))))))))))),
          Nil))))))));
  reflection_dec =
  (PQ.run
    (PQ.lam PQ.prop (fun p0 ->
      PQ.lam PQ.bool (fun b ->
        PQ.lam (relation0 p0 b) (fun h ->
          let pos = fun hp ->
            PQ.is_true p0
              (PQ.apps h (Cons (p0, (Cons
                ((PQ.lam (PQ.arrow (PQ.eq PQ.bool b PQ.tru) p0) (fun yes ->
                   PQ.lam
                     (PQ.arrow
                       (match false_eq with
                        | True -> PQ.eq PQ.bool b PQ.fal
                        | False -> PQ.not (PQ.eq PQ.bool b PQ.tru))
                       (PQ.not p0))
                     (fun _ -> PQ.app yes hp))),
                Nil)))))
          in
          let neg = fun hn ->
            PQ.is_false p0
              (PQ.apps h (Cons ((PQ.not p0), (Cons
                ((PQ.lam (PQ.arrow (PQ.eq PQ.bool b PQ.tru) p0) (fun _ ->
                   PQ.lam
                     (PQ.arrow
                       (match false_eq with
                        | True -> PQ.eq PQ.bool b PQ.fal
                        | False -> PQ.not (PQ.eq PQ.bool b PQ.tru))
                       (PQ.not p0))
                     (fun no -> PQ.app no hn))),
                Nil)))))
          in
          (match false_eq with
           | True ->
             PQ.app
               (PQ.apps
                 (PQ.const (Cons ((String ((Ascii (False, True, False, False,
                   False, False, True, False)), (String ((Ascii (True, True,
                   True, True, False, True, True, False)), (String ((Ascii
                   (True, True, True, True, False, True, True, False)),
                   (String ((Ascii (False, False, True, True, False, True,
                   True, False)), EmptyString)))))))), (Cons ((String ((Ascii
                   (False, True, False, False, True, True, True, False)),
                   (String ((Ascii (True, False, True, False, False, True,
                   True, False)), (String ((Ascii (True, True, False, False,
                   False, True, True, False)), EmptyString)))))), Nil))))
                   (Cons ((LSucc LZero), Nil)))
                 (Cons
                 ((PQ.lam PQ.bool (fun b' ->
                    PQ.arrow (PQ.eq PQ.bool b b') (PQ.dec p0))),
                 (Cons ((PQ.lam (PQ.eq PQ.bool b PQ.fal) neg), (Cons
                 ((PQ.lam (PQ.eq PQ.bool b PQ.tru) pos), (Cons (b,
                 Nil)))))))))
               (PQ.refl PQ.bool b)
           | False ->
             PQ.dite (PQ.dec p0) (PQ.eq PQ.bool b PQ.tru) (PQ.bool_dec b) pos
               neg)))))) }

(** val primitive_reflection_ite : primitive_reflection -> expr **)

let primitive_reflection_ite r =
  PQ.run
    (PQ.lam PQ.prop (fun p0 ->
      PQ.lam PQ.bool (fun b ->
        PQ.lam
          (PQ.apps (PQ.embed r.reflection_type) (Cons (p0, (Cons (b, Nil)))))
          (fun h ->
          PQ.lam PQ.type0 (fun a ->
            PQ.apps
              (PQ.const (Cons ((String ((Ascii (True, False, False, True,
                False, True, True, False)), (String ((Ascii (False, False,
                True, False, True, True, True, False)), (String ((Ascii
                (True, False, True, False, False, True, True, False)),
                EmptyString)))))), Nil)) (Cons ((LSucc LZero), Nil)))
              (Cons (a, (Cons (p0, (Cons
              ((PQ.apps (PQ.embed r.reflection_dec) (Cons (p0, (Cons (b,
                 (Cons (h, Nil))))))),
              Nil)))))))))))

(** val primitive_reflection_dite : primitive_reflection -> expr **)

let primitive_reflection_dite r =
  PQ.run
    (PQ.lam PQ.prop (fun p0 ->
      PQ.lam PQ.bool (fun b ->
        PQ.lam
          (PQ.apps (PQ.embed r.reflection_type) (Cons (p0, (Cons (b, Nil)))))
          (fun h ->
          PQ.apps
            (PQ.const (Cons ((String ((Ascii (False, False, True, False,
              False, True, True, False)), (String ((Ascii (True, False,
              False, True, False, True, True, False)), (String ((Ascii
              (False, False, True, False, True, True, True, False)), (String
              ((Ascii (True, False, True, False, False, True, True, False)),
              EmptyString)))))))), Nil)) (Cons ((LSucc LZero), Nil)))
            (Cons (PQ.nat, (Cons (p0, (Cons
            ((PQ.apps (PQ.embed r.reflection_dec) (Cons (p0, (Cons (b, (Cons
               (h, Nil))))))),
            Nil))))))))))

(** val primitive_eq_closed :
    nat -> environment -> PQ.term -> PQ.term -> unit0 result **)

let primitive_eq_closed fuel0 env a b =
  check_defeq fuel0 env Nil empty_context (PQ.run a) (PQ.run b)

(** val primitive_check_closed :
    nat -> environment -> PQ.term -> PQ.term -> unit0 result **)

let primitive_check_closed fuel0 env a ty0 =
  check fuel0 env Nil empty_context (PQ.run a) (PQ.run ty0)

(** val primitive_check_reflection :
    nat -> environment -> primitive_reflection -> bool -> bool -> unit0 result **)

let primitive_check_reflection fuel0 env r with_ite with_dite =
  let relation0 = fun p0 b ->
    PQ.apps (PQ.embed r.reflection_type) (Cons (p0, (Cons (b, Nil))))
  in
  bind
    (primitive_check_closed fuel0 env (PQ.embed r.reflection_type)
      (PQ.arrow PQ.prop (PQ.arrow PQ.bool PQ.prop)))
    (fun _ ->
    bind
      (match with_ite with
       | True ->
         let it = PQ.embed (primitive_reflection_ite r) in
         bind
           (primitive_check_closed fuel0 env it
             (PQ.pi PQ.prop (fun p0 ->
               PQ.pi PQ.bool (fun b ->
                 PQ.arrow (relation0 p0 b)
                   (PQ.pi PQ.type0 (fun a -> PQ.arrow a (PQ.arrow a a)))))))
           (fun _ ->
           bind
             (primitive_eq_closed fuel0 env
               (PQ.lam PQ.prop (fun p0 ->
                 PQ.lam (relation0 p0 PQ.tru) (fun h ->
                   PQ.apps it (Cons (p0, (Cons (PQ.tru, (Cons (h, Nil)))))))))
               (PQ.lam PQ.prop (fun p0 ->
                 PQ.lam (relation0 p0 PQ.tru) (fun _ ->
                   PQ.lam PQ.type0 (fun a ->
                     PQ.lam a (fun x0 -> PQ.lam a (fun _ -> x0)))))))
             (fun _ ->
             primitive_eq_closed fuel0 env
               (PQ.lam PQ.prop (fun p0 ->
                 PQ.lam (relation0 p0 PQ.fal) (fun h ->
                   PQ.apps it (Cons (p0, (Cons (PQ.fal, (Cons (h, Nil)))))))))
               (PQ.lam PQ.prop (fun p0 ->
                 PQ.lam (relation0 p0 PQ.fal) (fun _ ->
                   PQ.lam PQ.type0 (fun a ->
                     PQ.lam a (fun _ -> PQ.lam a (fun x0 -> x0))))))))
       | False -> Accept Tt)
      (fun _ ->
      match with_dite with
      | True ->
        let di = PQ.embed (primitive_reflection_dite r) in
        bind
          (primitive_check_closed fuel0 env
            (PQ.const (Cons ((String ((Ascii (False, True, True, True, False,
              False, True, False)), (String ((Ascii (True, True, True, True,
              False, True, True, False)), (String ((Ascii (False, False,
              True, False, True, True, True, False)), EmptyString)))))),
              Nil)) Nil)
            (PQ.arrow PQ.prop PQ.prop))
          (fun _ ->
          bind
            (primitive_check_closed fuel0 env di
              (PQ.pi PQ.prop (fun p0 ->
                PQ.pi PQ.bool (fun b ->
                  PQ.arrow (relation0 p0 b)
                    (PQ.arrow (PQ.arrow p0 PQ.nat)
                      (PQ.arrow (PQ.arrow (PQ.not p0) PQ.nat) PQ.nat))))))
            (fun _ ->
            bind
              (primitive_check_closed fuel0 env (PQ.embed r.reflection_true)
                (PQ.pi PQ.prop (fun p0 -> PQ.arrow (relation0 p0 PQ.tru) p0)))
              (fun _ ->
              bind
                (primitive_check_closed fuel0 env
                  (PQ.embed r.reflection_false)
                  (PQ.pi PQ.prop (fun p0 ->
                    PQ.arrow (relation0 p0 PQ.fal) (PQ.not p0))))
                (fun _ ->
                let lhs = fun b ->
                  PQ.lam PQ.prop (fun p0 ->
                    PQ.lam (PQ.arrow p0 PQ.nat) (fun yes ->
                      PQ.lam (PQ.arrow (PQ.not p0) PQ.nat) (fun no ->
                        PQ.lam (relation0 p0 b) (fun h ->
                          PQ.apps di (Cons (p0, (Cons (b, (Cons (h, (Cons
                            (yes, (Cons (no, Nil))))))))))))))
                in
                let rhs = fun b positive0 ->
                  PQ.lam PQ.prop (fun p0 ->
                    PQ.lam (PQ.arrow p0 PQ.nat) (fun yes ->
                      PQ.lam (PQ.arrow (PQ.not p0) PQ.nat) (fun no ->
                        PQ.lam (relation0 p0 b) (fun h ->
                          PQ.app
                            (match positive0 with
                             | True -> yes
                             | False -> no)
                            (PQ.apps
                              (PQ.embed
                                (match positive0 with
                                 | True -> r.reflection_true
                                 | False -> r.reflection_false))
                              (Cons (p0, (Cons (h, Nil)))))))))
                in
                bind
                  (primitive_eq_closed fuel0 env (lhs PQ.tru)
                    (rhs PQ.tru True))
                  (fun _ ->
                  primitive_eq_closed fuel0 env (lhs PQ.fal)
                    (rhs PQ.fal False))))))
      | False -> Accept Tt))

type primitive_condition =
| PCBool
| PCNatLE
| PCNatEq

(** val primitive_condition_prop : primitive_condition -> expr **)

let primitive_condition_prop = function
| PCBool -> PQ.run (PQ.lam PQ.bool (fun b -> PQ.eq PQ.bool b PQ.tru))
| PCNatLE ->
  primitive_const (Cons ((String ((Ascii (False, True, True, True, False,
    False, True, False)), (String ((Ascii (True, False, False, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), EmptyString)))))), (Cons ((String ((Ascii (False,
    False, True, True, False, True, True, False)), (String ((Ascii (True,
    False, True, False, False, True, True, False)), EmptyString)))), Nil))))
    Nil
| PCNatEq ->
  EApp
    ((primitive_const (Cons ((String ((Ascii (True, False, True, False,
       False, False, True, False)), (String ((Ascii (True, False, False,
       False, True, True, True, False)), EmptyString)))), Nil)) (Cons ((LSucc
       LZero), Nil))),
    core_nat)

(** val primitive_condition_dec : primitive_condition -> expr **)

let primitive_condition_dec = function
| PCBool -> PQ.run (PQ.lam PQ.bool PQ.bool_dec)
| PCNatLE ->
  primitive_const (Cons ((String ((Ascii (False, True, True, True, False,
    False, True, False)), (String ((Ascii (True, False, False, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), EmptyString)))))), (Cons ((String ((Ascii (False,
    False, True, False, False, True, True, False)), (String ((Ascii (True,
    False, True, False, False, True, True, False)), (String ((Ascii (True,
    True, False, False, False, True, True, False)), (String ((Ascii (False,
    False, True, True, False, False, True, False)), (String ((Ascii (True,
    False, True, False, False, True, True, False)), EmptyString)))))))))),
    Nil)))) Nil
| PCNatEq ->
  primitive_const (Cons ((String ((Ascii (False, True, True, True, False,
    False, True, False)), (String ((Ascii (True, False, False, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), EmptyString)))))), (Cons ((String ((Ascii (False,
    False, True, False, False, True, True, False)), (String ((Ascii (True,
    False, True, False, False, True, True, False)), (String ((Ascii (True,
    True, False, False, False, True, True, False)), (String ((Ascii (True,
    False, True, False, False, False, True, False)), (String ((Ascii (True,
    False, False, False, True, True, True, False)), EmptyString)))))))))),
    Nil)))) Nil

(** val primitive_condition_ite :
    primitive_condition -> PQ.term -> PQ.term list -> PQ.term -> PQ.term ->
    PQ.term **)

let primitive_condition_ite c a args t0 e =
  PQ.ite a (PQ.apps (PQ.embed (primitive_condition_prop c)) args)
    (PQ.apps (PQ.embed (primitive_condition_dec c)) args) t0 e

(** val primitive_condition_dite :
    primitive_condition -> PQ.term list -> (PQ.term -> PQ.term) -> (PQ.term
    -> PQ.term) -> PQ.term **)

let primitive_condition_dite c args t0 e =
  PQ.dite PQ.nat (PQ.apps (PQ.embed (primitive_condition_prop c)) args)
    (PQ.apps (PQ.embed (primitive_condition_dec c)) args) t0 e

(** val primitive_condition_decide :
    primitive_condition -> PQ.term list -> PQ.term **)

let primitive_condition_decide c args =
  primitive_condition_ite c PQ.bool args PQ.tru PQ.fal

(** val primitive_condition_proof : primitive_condition -> expr **)

let primitive_condition_proof c =
  let is_eq = match c with
              | PCNatEq -> True
              | _ -> False in
  PQ.run
    (PQ.lam PQ.nat (fun x0 ->
      PQ.lam PQ.nat (fun y ->
        let p0 =
          PQ.apps (PQ.embed (primitive_condition_prop c)) (Cons (x0, (Cons
            (y, Nil))))
        in
        let b =
          PQ.call (match is_eq with
                   | True -> PNatBEq
                   | False -> PNatBLE)
            (Cons (x0, (Cons (y, Nil))))
        in
        PQ.lam PQ.prop (fun q0 ->
          PQ.lam
            (PQ.arrow (PQ.arrow (PQ.eq PQ.bool b PQ.tru) p0)
              (PQ.arrow
                (PQ.arrow
                  (match is_eq with
                   | True -> PQ.eq PQ.bool b PQ.fal
                   | False -> PQ.not (PQ.eq PQ.bool b PQ.tru))
                  (PQ.not p0))
                q0))
            (fun h ->
            PQ.apps h (Cons
              ((PQ.apps
                 (PQ.const (Cons ((String ((Ascii (False, True, True, True,
                   False, False, True, False)), (String ((Ascii (True, False,
                   False, False, False, True, True, False)), (String ((Ascii
                   (False, False, True, False, True, True, True, False)),
                   EmptyString)))))), (Cons
                   ((match is_eq with
                     | True ->
                       String ((Ascii (True, False, True, False, False, True,
                         True, False)), (String ((Ascii (True, False, False,
                         False, True, True, True, False)), (String ((Ascii
                         (True, True, True, True, True, False, True, False)),
                         (String ((Ascii (True, True, True, True, False,
                         True, True, False)), (String ((Ascii (False, True,
                         True, False, False, True, True, False)), (String
                         ((Ascii (True, True, True, True, True, False, True,
                         False)), (String ((Ascii (False, True, False, False,
                         False, True, True, False)), (String ((Ascii (True,
                         False, True, False, False, True, True, False)),
                         (String ((Ascii (True, False, False, False, True,
                         True, True, False)), (String ((Ascii (True, True,
                         True, True, True, False, True, False)), (String
                         ((Ascii (True, False, True, False, False, True,
                         True, False)), (String ((Ascii (True, False, False,
                         False, True, True, True, False)), (String ((Ascii
                         (True, True, True, True, True, False, True, False)),
                         (String ((Ascii (False, False, True, False, True,
                         True, True, False)), (String ((Ascii (False, True,
                         False, False, True, True, True, False)), (String
                         ((Ascii (True, False, True, False, True, True, True,
                         False)), (String ((Ascii (True, False, True, False,
                         False, True, True, False)),
                         EmptyString)))))))))))))))))))))))))))))))))
                     | False ->
                       String ((Ascii (False, False, True, True, False, True,
                         True, False)), (String ((Ascii (True, False, True,
                         False, False, True, True, False)), (String ((Ascii
                         (True, True, True, True, True, False, True, False)),
                         (String ((Ascii (True, True, True, True, False,
                         True, True, False)), (String ((Ascii (False, True,
                         True, False, False, True, True, False)), (String
                         ((Ascii (True, True, True, True, True, False, True,
                         False)), (String ((Ascii (False, True, False, False,
                         False, True, True, False)), (String ((Ascii (False,
                         False, True, True, False, True, True, False)),
                         (String ((Ascii (True, False, True, False, False,
                         True, True, False)), (String ((Ascii (True, True,
                         True, True, True, False, True, False)), (String
                         ((Ascii (True, False, True, False, False, True,
                         True, False)), (String ((Ascii (True, False, False,
                         False, True, True, True, False)), (String ((Ascii
                         (True, True, True, True, True, False, True, False)),
                         (String ((Ascii (False, False, True, False, True,
                         True, True, False)), (String ((Ascii (False, True,
                         False, False, True, True, True, False)), (String
                         ((Ascii (True, False, True, False, True, True, True,
                         False)), (String ((Ascii (True, False, True, False,
                         False, True, True, False)),
                         EmptyString)))))))))))))))))))))))))))))))))),
                   Nil)))) Nil)
                 (Cons (x0, (Cons (y, Nil))))),
              (Cons
              ((PQ.apps
                 (PQ.const (Cons ((String ((Ascii (False, True, True, True,
                   False, False, True, False)), (String ((Ascii (True, False,
                   False, False, False, True, True, False)), (String ((Ascii
                   (False, False, True, False, True, True, True, False)),
                   EmptyString)))))), (Cons
                   ((match is_eq with
                     | True ->
                       String ((Ascii (False, True, True, True, False, True,
                         True, False)), (String ((Ascii (True, False, True,
                         False, False, True, True, False)), (String ((Ascii
                         (True, True, True, True, True, False, True, False)),
                         (String ((Ascii (True, True, True, True, False,
                         True, True, False)), (String ((Ascii (False, True,
                         True, False, False, True, True, False)), (String
                         ((Ascii (True, True, True, True, True, False, True,
                         False)), (String ((Ascii (False, True, False, False,
                         False, True, True, False)), (String ((Ascii (True,
                         False, True, False, False, True, True, False)),
                         (String ((Ascii (True, False, False, False, True,
                         True, True, False)), (String ((Ascii (True, True,
                         True, True, True, False, True, False)), (String
                         ((Ascii (True, False, True, False, False, True,
                         True, False)), (String ((Ascii (True, False, False,
                         False, True, True, True, False)), (String ((Ascii
                         (True, True, True, True, True, False, True, False)),
                         (String ((Ascii (False, True, True, False, False,
                         True, True, False)), (String ((Ascii (True, False,
                         False, False, False, True, True, False)), (String
                         ((Ascii (False, False, True, True, False, True,
                         True, False)), (String ((Ascii (True, True, False,
                         False, True, True, True, False)), (String ((Ascii
                         (True, False, True, False, False, True, True,
                         False)),
                         EmptyString)))))))))))))))))))))))))))))))))))
                     | False ->
                       String ((Ascii (False, True, True, True, False, True,
                         True, False)), (String ((Ascii (True, True, True,
                         True, False, True, True, False)), (String ((Ascii
                         (False, False, True, False, True, True, True,
                         False)), (String ((Ascii (True, True, True, True,
                         True, False, True, False)), (String ((Ascii (False,
                         False, True, True, False, True, True, False)),
                         (String ((Ascii (True, False, True, False, False,
                         True, True, False)), (String ((Ascii (True, True,
                         True, True, True, False, True, False)), (String
                         ((Ascii (True, True, True, True, False, True, True,
                         False)), (String ((Ascii (False, True, True, False,
                         False, True, True, False)), (String ((Ascii (True,
                         True, True, True, True, False, True, False)),
                         (String ((Ascii (False, True, True, True, False,
                         True, True, False)), (String ((Ascii (True, True,
                         True, True, False, True, True, False)), (String
                         ((Ascii (False, False, True, False, True, True,
                         True, False)), (String ((Ascii (True, True, True,
                         True, True, False, True, False)), (String ((Ascii
                         (False, True, False, False, False, True, True,
                         False)), (String ((Ascii (False, False, True, True,
                         False, True, True, False)), (String ((Ascii (True,
                         False, True, False, False, True, True, False)),
                         (String ((Ascii (True, True, True, True, True,
                         False, True, False)), (String ((Ascii (True, False,
                         True, False, False, True, True, False)), (String
                         ((Ascii (True, False, False, False, True, True,
                         True, False)), (String ((Ascii (True, True, True,
                         True, True, False, True, False)), (String ((Ascii
                         (False, False, True, False, True, True, True,
                         False)), (String ((Ascii (False, True, False, False,
                         True, True, True, False)), (String ((Ascii (True,
                         False, True, False, True, True, True, False)),
                         (String ((Ascii (True, False, True, False, False,
                         True, True, False)),
                         EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))),
                   Nil)))) Nil)
                 (Cons (x0, (Cons (y, Nil))))),
              Nil)))))))))

(** val primitive_check_condition :
    nat -> environment -> primitive_condition -> bool -> bool -> unit0 result **)

let primitive_check_condition fuel0 env c with_ite with_dite =
  bind (require (core_bool_ready env) MalformedDeclaration) (fun _ ->
    bind (infer fuel0 env Nil empty_context (primitive_condition_dec c))
      (fun _ ->
      match c with
      | PCBool ->
        bind
          (primitive_check_closed fuel0 env
            (PQ.embed (primitive_condition_prop c))
            (PQ.arrow PQ.bool PQ.prop))
          (fun _ ->
          bind
            (match with_ite with
             | True ->
               let it =
                 PQ.lam PQ.bool (fun b ->
                   PQ.apps
                     (PQ.const (Cons ((String ((Ascii (True, False, False,
                       True, False, True, True, False)), (String ((Ascii
                       (False, False, True, False, True, True, True, False)),
                       (String ((Ascii (True, False, True, False, False,
                       True, True, False)), EmptyString)))))), Nil)) (Cons
                       ((LSucc LZero), Nil)))
                     (Cons (PQ.nat, (Cons
                     ((PQ.apps (PQ.embed (primitive_condition_prop c)) (Cons
                        (b, Nil))),
                     (Cons
                     ((PQ.apps (PQ.embed (primitive_condition_dec c)) (Cons
                        (b, Nil))),
                     Nil)))))))
               in
               bind
                 (primitive_check_closed fuel0 env it
                   (PQ.arrow PQ.bool
                     (PQ.arrow PQ.nat (PQ.arrow PQ.nat PQ.nat))))
                 (fun _ ->
                 bind
                   (primitive_eq_closed fuel0 env (PQ.app it PQ.tru)
                     (PQ.lam PQ.nat (fun a -> PQ.lam PQ.nat (fun _ -> a))))
                   (fun _ ->
                   primitive_eq_closed fuel0 env (PQ.app it PQ.fal)
                     (PQ.lam PQ.nat (fun _ -> PQ.lam PQ.nat (fun a -> a)))))
             | False -> Accept Tt)
            (fun _ ->
            match with_dite with
            | True -> Decline UnsupportedDeclaration
            | False -> Accept Tt))
      | _ ->
        let is_eq = match c with
                    | PCNatEq -> True
                    | _ -> False in
        let op = match is_eq with
                 | True -> PNatBEq
                 | False -> PNatBLE in
        bind (primitive_authenticated fuel0 env op) (fun _ ->
          let r = primitive_reflection_make is_eq in
          bind (primitive_check_reflection fuel0 env r with_ite with_dite)
            (fun _ ->
            let gadget =
              PQ.lam PQ.nat (fun x0 ->
                PQ.lam PQ.nat (fun y ->
                  PQ.apps
                    (PQ.lam PQ.prop (fun p0 ->
                      PQ.lam PQ.bool (fun b ->
                        PQ.lam
                          (PQ.apps (PQ.embed r.reflection_type) (Cons (p0,
                            (Cons (b, Nil)))))
                          (fun h ->
                          PQ.apps (PQ.embed r.reflection_dec) (Cons (p0,
                            (Cons (b, (Cons (h, Nil))))))))))
                    (Cons
                    ((PQ.apps (PQ.embed (primitive_condition_prop c)) (Cons
                       (x0, (Cons (y, Nil))))),
                    (Cons ((PQ.call op (Cons (x0, (Cons (y, Nil))))), (Cons
                    ((PQ.apps (PQ.embed (primitive_condition_proof c)) (Cons
                       (x0, (Cons (y, Nil))))),
                    Nil))))))))
            in
            primitive_eq_closed fuel0 env gadget
              (PQ.embed (primitive_condition_dec c))))))

(** val primitive_go_name : bool -> name **)

let primitive_go_name = function
| True ->
  primitive_path (Cons ((String ((Ascii (False, True, True, True, False,
    False, True, False)), (String ((Ascii (True, False, False, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), EmptyString)))))), (Cons ((String ((Ascii (True,
    False, True, True, False, True, True, False)), (String ((Ascii (True,
    True, True, True, False, True, True, False)), (String ((Ascii (False,
    False, True, False, False, True, True, False)), (String ((Ascii (True,
    True, False, False, False, False, True, False)), (String ((Ascii (True,
    True, True, True, False, True, True, False)), (String ((Ascii (False,
    True, False, False, True, True, True, False)), (String ((Ascii (True,
    False, True, False, False, True, True, False)),
    EmptyString)))))))))))))), (Cons ((String ((Ascii (True, True, True,
    False, False, True, True, False)), (String ((Ascii (True, True, True,
    True, False, True, True, False)), EmptyString)))), Nil))))))
| False ->
  primitive_path (Cons ((String ((Ascii (False, True, True, True, False,
    False, True, False)), (String ((Ascii (True, False, False, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), EmptyString)))))), (Cons ((String ((Ascii (False,
    False, True, False, False, True, True, False)), (String ((Ascii (True,
    False, False, True, False, True, True, False)), (String ((Ascii (False,
    True, True, False, True, True, True, False)), EmptyString)))))), (Cons
    ((String ((Ascii (True, True, True, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    EmptyString)))), Nil))))))

(** val primitive_le : PQ.term -> PQ.term -> PQ.term **)

let primitive_le x0 y =
  PQ.apps (PQ.embed (primitive_condition_prop PCNatLE)) (Cons (x0, (Cons (y,
    Nil))))

(** val primitive_go_type : expr **)

let primitive_go_type =
  PQ.run
    (PQ.pi PQ.nat (fun y ->
      PQ.arrow (primitive_le PQ.one y)
        (PQ.pi PQ.nat (fun fuel0 ->
          PQ.pi PQ.nat (fun x0 ->
            PQ.arrow (primitive_le (PQ.succ x0) fuel0) PQ.nat)))))

(** val primitive_fuel_top : bool -> expr **)

let primitive_fuel_top modulo0 =
  let go = PQ.embed (EConst ((primitive_go_name modulo0), Nil)) in
  PQ.run
    (PQ.lam PQ.nat (fun x0 ->
      PQ.lam PQ.nat (fun y ->
        let n0 = match modulo0 with
                 | True -> PQ.succ x0
                 | False -> x0 in
        let inner =
          primitive_condition_dite PCNatLE (Cons (PQ.one, (Cons (y, Nil))))
            (fun hy ->
            PQ.apps go (Cons (y, (Cons (hy, (Cons ((PQ.succ n0), (Cons (n0,
              (Cons
              ((PQ.app
                 (PQ.const (Cons ((String ((Ascii (False, True, True, True,
                   False, False, True, False)), (String ((Ascii (True, False,
                   False, False, False, True, True, False)), (String ((Ascii
                   (False, False, True, False, True, True, True, False)),
                   EmptyString)))))), (Cons ((String ((Ascii (False, False,
                   True, True, False, True, True, False)), (String ((Ascii
                   (False, False, True, False, True, True, True, False)),
                   (String ((Ascii (True, True, True, True, True, False,
                   True, False)), (String ((Ascii (True, True, False, False,
                   True, True, True, False)), (String ((Ascii (True, False,
                   True, False, True, True, True, False)), (String ((Ascii
                   (True, True, False, False, False, True, True, False)),
                   (String ((Ascii (True, True, False, False, False, True,
                   True, False)), (String ((Ascii (True, True, True, True,
                   True, False, True, False)), (String ((Ascii (True, True,
                   False, False, True, True, True, False)), (String ((Ascii
                   (True, False, True, False, False, True, True, False)),
                   (String ((Ascii (False, False, True, True, False, True,
                   True, False)), (String ((Ascii (False, True, True, False,
                   False, True, True, False)),
                   EmptyString)))))))))))))))))))))))), Nil)))) Nil)
                 n0),
              Nil)))))))))))
            (fun _ -> match modulo0 with
                      | True -> n0
                      | False -> PQ.zero)
        in
        (match modulo0 with
         | True ->
           primitive_condition_ite PCNatLE PQ.nat (Cons (y, (Cons (n0,
             Nil)))) inner n0
         | False -> inner))))

(** val primitive_fuel_step : bool -> bool -> expr **)

let primitive_fuel_step modulo0 rhs =
  let go = PQ.embed (EConst ((primitive_go_name modulo0), Nil)) in
  PQ.run
    (PQ.lam PQ.nat (fun x0 ->
      PQ.lam PQ.nat (fun y ->
        PQ.lam (primitive_le PQ.one y) (fun hy ->
          PQ.lam PQ.nat (fun t0 ->
            PQ.lam (primitive_le (PQ.succ x0) (PQ.succ t0)) (fun h ->
              match rhs with
              | True ->
                primitive_condition_dite PCNatLE (Cons (y, (Cons (x0, Nil))))
                  (fun hle ->
                  let rec0 =
                    PQ.apps go (Cons (y, (Cons (hy, (Cons (t0, (Cons
                      ((PQ.call PNatSub (Cons (x0, (Cons (y, Nil))))), (Cons
                      ((PQ.apps
                         (PQ.const (Cons ((String ((Ascii (False, True, True,
                           True, False, False, True, False)), (String ((Ascii
                           (True, False, False, False, False, True, True,
                           False)), (String ((Ascii (False, False, True,
                           False, True, True, True, False)),
                           EmptyString)))))), (Cons ((String ((Ascii (False,
                           False, True, False, False, True, True, False)),
                           (String ((Ascii (True, False, False, True, False,
                           True, True, False)), (String ((Ascii (False, True,
                           True, False, True, True, True, False)), (String
                           ((Ascii (True, True, True, True, True, False,
                           True, False)), (String ((Ascii (False, True,
                           False, False, True, True, True, False)), (String
                           ((Ascii (True, False, True, False, False, True,
                           True, False)), (String ((Ascii (True, True, False,
                           False, False, True, True, False)), (String ((Ascii
                           (True, True, True, True, True, False, True,
                           False)), (String ((Ascii (False, True, True,
                           False, False, True, True, False)), (String ((Ascii
                           (True, False, True, False, True, True, True,
                           False)), (String ((Ascii (True, False, True,
                           False, False, True, True, False)), (String ((Ascii
                           (False, False, True, True, False, True, True,
                           False)), (String ((Ascii (True, True, True, True,
                           True, False, True, False)), (String ((Ascii
                           (False, False, True, True, False, True, True,
                           False)), (String ((Ascii (True, False, True,
                           False, False, True, True, False)), (String ((Ascii
                           (True, False, True, True, False, True, True,
                           False)), (String ((Ascii (True, False, True, True,
                           False, True, True, False)), (String ((Ascii (True,
                           False, False, False, False, True, True, False)),
                           EmptyString)))))))))))))))))))))))))))))))))))),
                           Nil)))) Nil)
                         (Cons (x0, (Cons (y, (Cons (t0, (Cons (hy, (Cons
                         (hle, (Cons (h, Nil))))))))))))),
                      Nil))))))))))
                  in
                  (match modulo0 with
                   | True -> rec0
                   | False -> PQ.succ rec0))
                  (fun _ -> match modulo0 with
                            | True -> x0
                            | False -> PQ.zero)
              | False ->
                PQ.apps go (Cons (y, (Cons (hy, (Cons ((PQ.succ t0), (Cons
                  (x0, (Cons (h, Nil))))))))))))))))

(** val primitive_check_fuel_rec :
    nat -> environment -> bool -> expr -> unit0 result **)

let primitive_check_fuel_rec fuel0 env modulo0 body =
  bind
    (require
      (match core_nat_ready env with
       | True -> core_bool_ready env
       | False -> False)
      MalformedDeclaration)
    (fun _ ->
    bind (primitive_authenticated fuel0 env PNatSub) (fun _ ->
      bind
        (primitive_check_closed fuel0 env
          (PQ.embed (primitive_condition_prop PCNatLE))
          (PQ.arrow PQ.nat (PQ.arrow PQ.nat PQ.prop)))
        (fun _ ->
        bind
          (check fuel0 env Nil empty_context (EConst
            ((primitive_go_name modulo0), Nil)) primitive_go_type)
          (fun _ ->
          bind (primitive_check_condition fuel0 env PCNatLE modulo0 True)
            (fun _ ->
            bind
              (match modulo0 with
               | True ->
                 primitive_eq_closed fuel0 env
                   (PQ.lam PQ.nat (fun x0 ->
                     PQ.apps (PQ.embed body) (Cons (PQ.zero, (Cons (x0,
                       Nil))))))
                   (PQ.lam PQ.nat (fun _ -> PQ.zero))
               | False -> Accept Tt)
              (fun _ ->
              bind
                (primitive_eq_closed fuel0 env
                  (PQ.lam PQ.nat (fun x0 ->
                    PQ.lam PQ.nat (fun y ->
                      PQ.apps (PQ.embed body) (Cons
                        ((match modulo0 with
                          | True -> PQ.succ x0
                          | False -> x0),
                        (Cons (y, Nil)))))))
                  (PQ.embed (primitive_fuel_top modulo0)))
                (fun _ ->
                check_defeq fuel0 env Nil empty_context
                  (primitive_fuel_step modulo0 False)
                  (primitive_fuel_step modulo0 True))))))))

(** val primitive_whnf_core :
    nat -> environment -> context -> expr -> expr result **)

let primitive_whnf_core fuel0 env g e =
  (checker fuel0 env Nil).whnf_core_method False g e

(** val primitive_unfold : environment -> expr -> expr result **)

let primitive_unfold env e =
  let Pair (head, args) = core_spine e Nil in
  (match head with
   | EConst (n0, us) ->
     bind (get_constant env Nil n0 us) (fun d ->
       match d.decl_kind_of with
       | DDefinition ->
         (match d.decl_value with
          | Some v0 ->
            Accept (core_apps (subst_levels d.decl_params us v0) args)
          | None -> Decline UnsupportedDeclaration)
       | DPrimitive _ ->
         (match d.decl_value with
          | Some v0 ->
            Accept (core_apps (subst_levels d.decl_params us v0) args)
          | None -> Decline UnsupportedDeclaration)
       | _ -> Decline UnsupportedDeclaration)
   | _ -> Decline UnsupportedDeclaration)

(** val primitive_lambda_telescope :
    nat -> nat -> environment -> ind_state -> expr -> ((ind_local list, expr)
    prod, ind_state) prod result **)

let rec primitive_lambda_telescope depth fuel0 env s e =
  match depth with
  | O -> Decline OutOfFuel
  | S depth0 ->
    (match e with
     | ELam (n0, bi, ty0, b) ->
       bind (sort_of (checker fuel0 env Nil) s.ist_context ty0) (fun _ ->
         let Pair (x0, s0) = ind_fresh s n0 bi ty0 in
         bind
           (primitive_lambda_telescope depth0 fuel0 env s0
             (instantiate b (local_expr x0)))
           (fun rest ->
           let Pair (p0, s1) = rest in
           let Pair (xs, b0) = p0 in
           Accept (Pair ((Pair ((Cons (x0, xs)), b0)), s1))))
     | EMData e0 -> primitive_lambda_telescope depth0 fuel0 env s e0
     | _ -> Accept (Pair ((Pair (Nil, e)), s)))

(** val primitive_no_free : nat -> name -> expr -> unit0 result **)

let rec primitive_no_free fuel0 n0 e =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    (match e with
     | EFVar m -> require (negb (name_eqb n0 m)) MalformedDeclaration
     | EApp (a, b) ->
       bind (primitive_no_free fuel1 n0 a) (fun _ ->
         primitive_no_free fuel1 n0 b)
     | ELam (_, _, a, b) ->
       bind (primitive_no_free fuel1 n0 a) (fun _ ->
         primitive_no_free fuel1 n0 b)
     | EPi (_, _, a, b) ->
       bind (primitive_no_free fuel1 n0 a) (fun _ ->
         primitive_no_free fuel1 n0 b)
     | ELet (_, a, v0, b, _) ->
       bind (primitive_no_free fuel1 n0 a) (fun _ ->
         bind (primitive_no_free fuel1 n0 v0) (fun _ ->
           primitive_no_free fuel1 n0 b))
     | EProj (_, _, a) -> primitive_no_free fuel1 n0 a
     | EMData a -> primitive_no_free fuel1 n0 a
     | _ -> Accept Tt)

(** val primitive_proof :
    nat -> environment -> context -> expr -> unit0 result **)

let primitive_proof fuel0 env g e =
  bind (infer fuel0 env Nil g e) (fun ty0 ->
    bind (sort_of (checker fuel0 env Nil) g ty0) (fun u0 ->
      bind (level_equiv fuel0 u0 LZero) (fun is_prop ->
        require is_prop TypeMismatch)))

type primitive_probe = { probe_pack : expr; probe_dom : expr;
                         probe_functional : expr }

(** val primitive_check_go :
    nat -> environment -> ind_state -> expr -> unit0 result **)

let primitive_check_go fuel0 env s go =
  bind (primitive_unfold env go) (fun value ->
    bind (primitive_lambda_telescope fuel0 fuel0 env s value) (fun opened ->
      let Pair (p0, st) = opened in
      let Pair (xs, b) = p0 in
      (match xs with
       | Nil -> Decline UnsupportedDeclaration
       | Cons (_, l) ->
         (match l with
          | Nil -> Decline UnsupportedDeclaration
          | Cons (_, l0) ->
            (match l0 with
             | Nil -> Decline UnsupportedDeclaration
             | Cons (_, l1) ->
               (match l1 with
                | Nil -> Decline UnsupportedDeclaration
                | Cons (f, l2) ->
                  (match l2 with
                   | Nil -> Decline UnsupportedDeclaration
                   | Cons (t0, l3) ->
                     (match l3 with
                      | Nil ->
                        (match b with
                         | EApp (nat_rec, t') ->
                           bind
                             (require (expr_eqb t' (local_expr t0))
                               NotDefinitionallyEqual)
                             (fun _ ->
                             bind (primitive_no_free fuel0 t0.il_id nat_rec)
                               (fun _ ->
                               bind
                                 (infer fuel0 env Nil st.ist_context
                                   (primitive_succ (local_expr t0)))
                                 (fun _ ->
                                 let next = EApp (nat_rec,
                                   (primitive_succ (local_expr t0)))
                                 in
                                 bind
                                   (infer fuel0 env Nil st.ist_context next)
                                   (fun _ ->
                                   bind
                                     (primitive_whnf_core fuel0 env
                                       st.ist_context next)
                                     (fun next0 ->
                                     bind
                                       (primitive_lambda_telescope fuel0
                                         fuel0 env st next0)
                                       (fun opened0 ->
                                       let Pair (p1, st0) = opened0 in
                                       let Pair (ys, b0) = p1 in
                                       (match ys with
                                        | Nil ->
                                          Decline UnsupportedDeclaration
                                        | Cons (x0, l4) ->
                                          (match l4 with
                                           | Nil ->
                                             Decline UnsupportedDeclaration
                                           | Cons (_, l5) ->
                                             (match l5 with
                                              | Nil ->
                                                (match b0 with
                                                 | EApp (fx, ih) ->
                                                   bind
                                                     (require
                                                       (expr_eqb fx (EApp
                                                         ((local_expr f),
                                                         (local_expr x0))))
                                                       NotDefinitionallyEqual)
                                                     (fun _ ->
                                                     bind
                                                       (primitive_lambda_telescope
                                                         fuel0 fuel0 env st0
                                                         ih)
                                                       (fun opened1 ->
                                                       let Pair (p2, st1) =
                                                         opened1
                                                       in
                                                       let Pair (zs, b1) = p2
                                                       in
                                                       (match zs with
                                                        | Nil ->
                                                          Decline
                                                            UnsupportedDeclaration
                                                        | Cons (y, l6) ->
                                                          (match l6 with
                                                           | Nil ->
                                                             Decline
                                                               UnsupportedDeclaration
                                                           | Cons (_, l7) ->
                                                             (match l7 with
                                                              | Nil ->
                                                                (match b1 with
                                                                 | EApp (
                                                                    recursive_call,
                                                                    pf) ->
                                                                   bind
                                                                    (primitive_proof
                                                                    fuel0 env
                                                                    st1.ist_context
                                                                    pf)
                                                                    (fun _ ->
                                                                    require
                                                                    (expr_eqb
                                                                    recursive_call
                                                                    (core_apps
                                                                    nat_rec
                                                                    (Cons
                                                                    ((local_expr
                                                                    t0),
                                                                    (Cons
                                                                    ((local_expr
                                                                    y),
                                                                    Nil))))))
                                                                    NotDefinitionallyEqual)
                                                                 | _ ->
                                                                   Decline
                                                                    UnsupportedDeclaration)
                                                              | Cons (_, _) ->
                                                                Decline
                                                                  UnsupportedDeclaration)))))
                                                 | _ ->
                                                   Decline
                                                     UnsupportedDeclaration)
                                              | Cons (_, _) ->
                                                Decline UnsupportedDeclaration)))))))))
                         | _ -> Decline UnsupportedDeclaration)
                      | Cons (_, _) -> Decline UnsupportedDeclaration))))))))

(** val primitive_unfold_nat_well_founded :
    nat -> environment -> ind_state -> expr -> expr -> primitive_probe result **)

let primitive_unfold_nat_well_founded fuel0 env s e measure =
  bind (primitive_lambda_telescope fuel0 fuel0 env s measure) (fun opened ->
    let Pair (p0, st) = opened in
    let Pair (locals, measure_body) = p0 in
    let applied = apply_locals e locals in
    bind (infer fuel0 env Nil st.ist_context applied) (fun _ ->
      bind (primitive_whnf_core fuel0 env st.ist_context applied) (fun top ->
        bind (primitive_unfold env top) (fun top0 ->
          bind (primitive_whnf_core fuel0 env st.ist_context top0)
            (fun top1 ->
            let Pair (fix_head, args) = core_spine top1 Nil in
            (match fix_head with
             | EConst (fix_name, l) ->
               (match l with
                | Nil -> Decline UnsupportedDeclaration
                | Cons (_, l0) ->
                  (match l0 with
                   | Nil -> Decline UnsupportedDeclaration
                   | Cons (_, l1) ->
                     (match l1 with
                      | Nil ->
                        (match args with
                         | Nil -> Decline UnsupportedDeclaration
                         | Cons (alpha, l2) ->
                           (match l2 with
                            | Nil -> Decline UnsupportedDeclaration
                            | Cons (motive, l3) ->
                              (match l3 with
                               | Nil -> Decline UnsupportedDeclaration
                               | Cons (meas, l4) ->
                                 (match l4 with
                                  | Nil -> Decline UnsupportedDeclaration
                                  | Cons (functional, l5) ->
                                    (match l5 with
                                     | Nil -> Decline UnsupportedDeclaration
                                     | Cons (packed, l6) ->
                                       (match l6 with
                                        | Nil ->
                                          bind
                                            (require
                                              (name_eqb fix_name
                                                (primitive_path (Cons
                                                  ((String ((Ascii (True,
                                                  True, True, False, True,
                                                  False, True, False)),
                                                  (String ((Ascii (True,
                                                  False, True, False, False,
                                                  True, True, False)),
                                                  (String ((Ascii (False,
                                                  False, True, True, False,
                                                  True, True, False)),
                                                  (String ((Ascii (False,
                                                  False, True, True, False,
                                                  True, True, False)),
                                                  (String ((Ascii (False,
                                                  True, True, False, False,
                                                  False, True, False)),
                                                  (String ((Ascii (True,
                                                  True, True, True, False,
                                                  True, True, False)),
                                                  (String ((Ascii (True,
                                                  False, True, False, True,
                                                  True, True, False)),
                                                  (String ((Ascii (False,
                                                  True, True, True, False,
                                                  True, True, False)),
                                                  (String ((Ascii (False,
                                                  False, True, False, False,
                                                  True, True, False)),
                                                  (String ((Ascii (True,
                                                  False, True, False, False,
                                                  True, True, False)),
                                                  (String ((Ascii (False,
                                                  False, True, False, False,
                                                  True, True, False)),
                                                  EmptyString)))))))))))))))))))))),
                                                  (Cons ((String ((Ascii
                                                  (False, True, True, True,
                                                  False, False, True,
                                                  False)), (String ((Ascii
                                                  (True, False, False, False,
                                                  False, True, True, False)),
                                                  (String ((Ascii (False,
                                                  False, True, False, True,
                                                  True, True, False)),
                                                  EmptyString)))))), (Cons
                                                  ((String ((Ascii (False,
                                                  True, True, False, False,
                                                  True, True, False)),
                                                  (String ((Ascii (True,
                                                  False, False, True, False,
                                                  True, True, False)),
                                                  (String ((Ascii (False,
                                                  False, False, True, True,
                                                  True, True, False)),
                                                  EmptyString)))))),
                                                  Nil))))))))
                                              MalformedDeclaration)
                                            (fun _ ->
                                            bind
                                              (infer fuel0 env Nil
                                                st.ist_context packed)
                                              (fun ty0 ->
                                              let Pair (a, sa) =
                                                ind_fresh st NameAnon
                                                  BDefault ty0
                                              in
                                              let av = local_expr a in
                                              bind
                                                (check fuel0 env Nil
                                                  sa.ist_context (EApp (meas,
                                                  av)) core_nat)
                                                (fun _ ->
                                                bind
                                                  (check_defeq fuel0 env Nil
                                                    sa.ist_context (EApp
                                                    (meas, packed))
                                                    measure_body)
                                                  (fun _ ->
                                                  bind
                                                    (primitive_unfold env
                                                      (core_apps fix_head
                                                        (Cons (alpha, (Cons
                                                        (motive, (Cons (meas,
                                                        (Cons (functional,
                                                        (Cons (av,
                                                        Nil))))))))))))
                                                    (fun unfolded ->
                                                    bind
                                                      (primitive_whnf_core
                                                        fuel0 env
                                                        sa.ist_context
                                                        unfolded)
                                                      (fun unfolded0 ->
                                                      let Pair (go, args0) =
                                                        core_spine unfolded0
                                                          Nil
                                                      in
                                                      (match args0 with
                                                       | Nil ->
                                                         Decline
                                                           UnsupportedDeclaration
                                                       | Cons (alpha', l7) ->
                                                         (match l7 with
                                                          | Nil ->
                                                            Decline
                                                              UnsupportedDeclaration
                                                          | Cons (motive', l8) ->
                                                            (match l8 with
                                                             | Nil ->
                                                               Decline
                                                                 UnsupportedDeclaration
                                                             | Cons (
                                                                 meas', l9) ->
                                                               (match l9 with
                                                                | Nil ->
                                                                  Decline
                                                                    UnsupportedDeclaration
                                                                | Cons (
                                                                    functional',
                                                                    l10) ->
                                                                  (match l10 with
                                                                   | Nil ->
                                                                    Decline
                                                                    UnsupportedDeclaration
                                                                   | Cons (
                                                                    fuel_expr,
                                                                    l11) ->
                                                                    (match l11 with
                                                                    | Nil ->
                                                                    Decline
                                                                    UnsupportedDeclaration
                                                                    | Cons (
                                                                    av', l12) ->
                                                                    (match l12 with
                                                                    | Nil ->
                                                                    Decline
                                                                    UnsupportedDeclaration
                                                                    | Cons (
                                                                    pf, l13) ->
                                                                    (match l13 with
                                                                    | Nil ->
                                                                    bind
                                                                    (require
                                                                    (list_eqb
                                                                    expr_eqb
                                                                    (Cons
                                                                    (alpha,
                                                                    (Cons
                                                                    (motive,
                                                                    (Cons
                                                                    (meas,
                                                                    (Cons
                                                                    (functional,
                                                                    (Cons
                                                                    (av,
                                                                    Nil))))))))))
                                                                    (Cons
                                                                    (alpha',
                                                                    (Cons
                                                                    (motive',
                                                                    (Cons
                                                                    (meas',
                                                                    (Cons
                                                                    (functional',
                                                                    (Cons
                                                                    (av',
                                                                    Nil)))))))))))
                                                                    NotDefinitionallyEqual)
                                                                    (fun _ ->
                                                                    bind
                                                                    (primitive_proof
                                                                    fuel0 env
                                                                    sa.ist_context
                                                                    pf)
                                                                    (fun _ ->
                                                                    match fuel_expr with
                                                                    | EApp (
                                                                    eager, n0) ->
                                                                    bind
                                                                    (check_defeq
                                                                    fuel0 env
                                                                    Nil
                                                                    sa.ist_context
                                                                    n0
                                                                    (primitive_succ
                                                                    (EApp
                                                                    (meas,
                                                                    av))))
                                                                    (fun _ ->
                                                                    bind
                                                                    (primitive_authenticated
                                                                    fuel0 env
                                                                    PNatBEq)
                                                                    (fun _ ->
                                                                    let Pair (
                                                                    x0, sx) =
                                                                    ind_fresh
                                                                    sa
                                                                    NameAnon
                                                                    BDefault
                                                                    core_nat
                                                                    in
                                                                    let xv =
                                                                    PQ.embed
                                                                    (local_expr
                                                                    x0)
                                                                    in
                                                                    bind
                                                                    (check_defeq
                                                                    fuel0 env
                                                                    Nil
                                                                    sx.ist_context
                                                                    (EApp
                                                                    (eager,
                                                                    (local_expr
                                                                    x0)))
                                                                    (PQ.run
                                                                    (primitive_condition_ite
                                                                    PCBool
                                                                    PQ.nat
                                                                    (Cons
                                                                    ((PQ.call
                                                                    PNatBEq
                                                                    (Cons
                                                                    (xv,
                                                                    (Cons
                                                                    (xv,
                                                                    Nil))))),
                                                                    Nil)) xv
                                                                    xv)))
                                                                    (fun _ ->
                                                                    bind
                                                                    (primitive_check_go
                                                                    fuel0 env
                                                                    s go)
                                                                    (fun _ ->
                                                                    bind
                                                                    (infer
                                                                    fuel0 env
                                                                    Nil
                                                                    s.ist_context
                                                                    functional)
                                                                    (fun fty ->
                                                                    bind
                                                                    (whnf
                                                                    fuel0 env
                                                                    Nil
                                                                    s.ist_context
                                                                    fty)
                                                                    (fun fty0 ->
                                                                    match fty0 with
                                                                    | EPi (
                                                                    _, _,
                                                                    domain,
                                                                    cod) ->
                                                                    bind
                                                                    (check_defeq
                                                                    fuel0 env
                                                                    Nil
                                                                    st.ist_context
                                                                    ty0
                                                                    domain)
                                                                    (fun _ ->
                                                                    let Pair (
                                                                    z0, sz) =
                                                                    ind_fresh
                                                                    s
                                                                    NameAnon
                                                                    BDefault
                                                                    domain
                                                                    in
                                                                    bind
                                                                    (whnf
                                                                    fuel0 env
                                                                    Nil
                                                                    sz.ist_context
                                                                    (instantiate
                                                                    cod
                                                                    (local_expr
                                                                    z0)))
                                                                    (fun cod0 ->
                                                                    match cod0 with
                                                                    | EPi (
                                                                    _, _,
                                                                    ih_domain,
                                                                    _) ->
                                                                    let dom =
                                                                    close_lam
                                                                    (Cons
                                                                    (z0,
                                                                    Nil))
                                                                    ih_domain
                                                                    in
                                                                    let pack =
                                                                    close_lam
                                                                    locals
                                                                    packed
                                                                    in
                                                                    bind
                                                                    (infer
                                                                    fuel0 env
                                                                    Nil
                                                                    s.ist_context
                                                                    pack)
                                                                    (fun _ ->
                                                                    bind
                                                                    (infer
                                                                    fuel0 env
                                                                    Nil
                                                                    s.ist_context
                                                                    dom)
                                                                    (fun _ ->
                                                                    Accept
                                                                    { probe_pack =
                                                                    pack;
                                                                    probe_dom =
                                                                    dom;
                                                                    probe_functional =
                                                                    functional }))
                                                                    | _ ->
                                                                    Reject
                                                                    ExpectedPi))
                                                                    | _ ->
                                                                    Reject
                                                                    ExpectedPi))))))
                                                                    | _ ->
                                                                    Decline
                                                                    UnsupportedDeclaration))
                                                                    | Cons (
                                                                    _, _) ->
                                                                    Decline
                                                                    UnsupportedDeclaration))))))))))))))
                                        | Cons (_, _) ->
                                          Decline UnsupportedDeclaration))))))
                      | Cons (_, _) -> Decline UnsupportedDeclaration)))
             | _ -> Decline UnsupportedDeclaration))))))

(** val primitive_run_probe :
    nat -> environment -> ind_state -> primitive_probe -> expr list -> (expr
    -> expr) -> unit0 result **)

let primitive_run_probe fuel0 env s p0 args rhs =
  let a = core_apps p0.probe_pack args in
  let Pair (ih, si) = ind_fresh s NameAnon BDefault (EApp (p0.probe_dom, a))
  in
  check_defeq fuel0 env Nil si.ist_context
    (core_apps p0.probe_functional (Cons (a, (Cons ((local_expr ih), Nil)))))
    (rhs (local_expr ih))

(** val primitive_first_measure : expr **)

let primitive_first_measure =
  PQ.run (PQ.lam PQ.nat (fun m -> PQ.lam PQ.nat (fun _ -> m)))

(** val primitive_check_gcd : nat -> environment -> expr -> unit0 result **)

let primitive_check_gcd fuel0 env body =
  bind
    (require
      (match core_nat_ready env with
       | True -> core_bool_ready env
       | False -> False)
      MalformedDeclaration)
    (fun _ ->
    bind (primitive_authenticated fuel0 env PNatMod) (fun _ ->
      bind (primitive_check_condition fuel0 env PCBool True False) (fun _ ->
        bind
          (primitive_unfold_nat_well_founded fuel0 env initial_ind_state body
            primitive_first_measure)
          (fun p0 ->
          let Pair (n0, sn) =
            ind_fresh initial_ind_state NameAnon BDefault core_nat
          in
          bind
            (primitive_run_probe fuel0 env sn p0 (Cons (primitive_zero, (Cons
              ((local_expr n0), Nil)))) (fun _ -> local_expr n0))
            (fun _ ->
            let Pair (m, sm) = ind_fresh sn NameAnon BDefault core_nat in
            primitive_run_probe fuel0 env sm p0 (Cons
              ((primitive_succ (local_expr m)), (Cons ((local_expr n0),
              Nil)))) (fun ih ->
              let mm = PQ.embed (local_expr m) in
              let nn = PQ.embed (local_expr n0) in
              PQ.run
                (PQ.apps (PQ.embed ih) (Cons
                  ((PQ.apps (PQ.embed p0.probe_pack) (Cons
                     ((PQ.call PNatMod (Cons (nn, (Cons ((PQ.succ mm),
                        Nil))))),
                     (Cons ((PQ.succ mm), Nil))))),
                  (Cons
                  ((PQ.apps
                     (PQ.const (Cons ((String ((Ascii (False, True, True,
                       True, False, False, True, False)), (String ((Ascii
                       (True, False, False, False, False, True, True,
                       False)), (String ((Ascii (False, False, True, False,
                       True, True, True, False)), EmptyString)))))), (Cons
                       ((String ((Ascii (True, False, True, True, False,
                       True, True, False)), (String ((Ascii (True, True,
                       True, True, False, True, True, False)), (String
                       ((Ascii (False, False, True, False, False, True, True,
                       False)), (String ((Ascii (True, True, True, True,
                       True, False, True, False)), (String ((Ascii (False,
                       False, True, True, False, True, True, False)), (String
                       ((Ascii (False, False, True, False, True, True, True,
                       False)), EmptyString)))))))))))), Nil)))) Nil)
                     (Cons (nn, (Cons ((PQ.succ mm), (Cons
                     ((PQ.app
                        (PQ.const (Cons ((String ((Ascii (False, True, True,
                          True, False, False, True, False)), (String ((Ascii
                          (True, False, False, False, False, True, True,
                          False)), (String ((Ascii (False, False, True,
                          False, True, True, True, False)),
                          EmptyString)))))), (Cons ((String ((Ascii (False,
                          True, False, True, True, True, True, False)),
                          (String ((Ascii (True, False, True, False, False,
                          True, True, False)), (String ((Ascii (False, True,
                          False, False, True, True, True, False)), (String
                          ((Ascii (True, True, True, True, False, True, True,
                          False)), (String ((Ascii (True, True, True, True,
                          True, False, True, False)), (String ((Ascii (False,
                          False, True, True, False, True, True, False)),
                          (String ((Ascii (False, False, True, False, True,
                          True, True, False)), (String ((Ascii (True, True,
                          True, True, True, False, True, False)), (String
                          ((Ascii (True, True, False, False, True, True,
                          True, False)), (String ((Ascii (True, False, True,
                          False, True, True, True, False)), (String ((Ascii
                          (True, True, False, False, False, True, True,
                          False)), (String ((Ascii (True, True, False, False,
                          False, True, True, False)),
                          EmptyString)))))))))))))))))))))))), Nil)))) Nil)
                        mm),
                     Nil))))))),
                  Nil)))))))))))

(** val primitive_bool_operator_type : expr **)

let primitive_bool_operator_type =
  primitive_arrow primitive_bool
    (primitive_arrow primitive_bool primitive_bool)

(** val primitive_check_bitwise :
    nat -> environment -> expr -> unit0 result **)

let primitive_check_bitwise fuel0 env body =
  bind
    (require
      (match core_nat_ready env with
       | True -> core_bool_ready env
       | False -> False)
      MalformedDeclaration)
    (fun _ ->
    bind (primitive_authenticated fuel0 env PNatAdd) (fun _ ->
      bind (primitive_authenticated fuel0 env PNatDiv) (fun _ ->
        bind (primitive_authenticated fuel0 env PNatMod) (fun _ ->
          bind (primitive_check_condition fuel0 env PCNatEq True True)
            (fun _ ->
            bind (primitive_check_condition fuel0 env PCBool True False)
              (fun _ ->
              let Pair (f, sf) =
                ind_fresh initial_ind_state NameAnon BDefault
                  primitive_bool_operator_type
              in
              bind
                (primitive_unfold_nat_well_founded fuel0 env sf (EApp (body,
                  (local_expr f))) primitive_first_measure)
                (fun p0 ->
                let Pair (n0, sn) = ind_fresh sf NameAnon BDefault core_nat in
                let Pair (m, sm) = ind_fresh sn NameAnon BDefault core_nat in
                primitive_run_probe fuel0 env sm p0 (Cons ((local_expr n0),
                  (Cons ((local_expr m), Nil)))) (fun ih ->
                  let f0 = PQ.embed (local_expr f) in
                  let n1 = PQ.embed (local_expr n0) in
                  let m0 = PQ.embed (local_expr m) in
                  let bool_ite = fun b ->
                    primitive_condition_ite PCBool PQ.nat (Cons (b, Nil))
                  in
                  PQ.run
                    (primitive_condition_dite PCNatEq (Cons (n1, (Cons
                      (PQ.zero, Nil)))) (fun _ ->
                      bool_ite
                        (PQ.apps f0 (Cons (PQ.fal, (Cons (PQ.tru, Nil))))) m0
                        PQ.zero)
                      (fun hn ->
                      primitive_condition_ite PCNatEq PQ.nat (Cons (m0, (Cons
                        (PQ.zero, Nil))))
                        (bool_ite
                          (PQ.apps f0 (Cons (PQ.tru, (Cons (PQ.fal, Nil)))))
                          n1 PQ.zero)
                        (let n' =
                           PQ.call PNatDiv (Cons (n1, (Cons (PQ.two, Nil))))
                         in
                         let m' =
                           PQ.call PNatDiv (Cons (m0, (Cons (PQ.two, Nil))))
                         in
                         let b1 =
                           primitive_condition_decide PCNatEq (Cons
                             ((PQ.call PNatMod (Cons (n1, (Cons (PQ.two,
                                Nil))))),
                             (Cons (PQ.one, Nil))))
                         in
                         let b2 =
                           primitive_condition_decide PCNatEq (Cons
                             ((PQ.call PNatMod (Cons (m0, (Cons (PQ.two,
                                Nil))))),
                             (Cons (PQ.one, Nil))))
                         in
                         let r =
                           PQ.apps (PQ.embed ih) (Cons
                             ((PQ.apps (PQ.embed p0.probe_pack) (Cons (n',
                                (Cons (m', Nil))))),
                             (Cons
                             ((PQ.apps
                                (PQ.const (Cons ((String ((Ascii (False,
                                  True, True, True, False, False, True,
                                  False)), (String ((Ascii (True, False,
                                  False, False, False, True, True, False)),
                                  (String ((Ascii (False, False, True, False,
                                  True, True, True, False)),
                                  EmptyString)))))), (Cons ((String ((Ascii
                                  (False, True, False, False, False, True,
                                  True, False)), (String ((Ascii (True,
                                  False, False, True, False, True, True,
                                  False)), (String ((Ascii (False, False,
                                  True, False, True, True, True, False)),
                                  (String ((Ascii (True, True, True, False,
                                  True, True, True, False)), (String ((Ascii
                                  (True, False, False, True, False, True,
                                  True, False)), (String ((Ascii (True, True,
                                  False, False, True, True, True, False)),
                                  (String ((Ascii (True, False, True, False,
                                  False, True, True, False)), (String ((Ascii
                                  (True, True, True, True, True, False, True,
                                  False)), (String ((Ascii (False, True,
                                  False, False, True, True, True, False)),
                                  (String ((Ascii (True, False, True, False,
                                  False, True, True, False)), (String ((Ascii
                                  (True, True, False, False, False, True,
                                  True, False)), (String ((Ascii (True, True,
                                  True, True, True, False, True, False)),
                                  (String ((Ascii (False, False, True, True,
                                  False, True, True, False)), (String ((Ascii
                                  (True, False, True, False, False, True,
                                  True, False)), (String ((Ascii (True,
                                  False, True, True, False, True, True,
                                  False)), (String ((Ascii (True, False,
                                  True, True, False, True, True, False)),
                                  (String ((Ascii (True, False, False, False,
                                  False, True, True, False)),
                                  EmptyString)))))))))))))))))))))))))))))))))),
                                  Nil)))) Nil)
                                (Cons (n1, (Cons (hn, Nil))))),
                             Nil))))
                         in
                         let rr = PQ.call PNatAdd (Cons (r, (Cons (r, Nil))))
                         in
                         bool_ite (PQ.apps f0 (Cons (b1, (Cons (b2, Nil)))))
                           (PQ.call PNatAdd (Cons (rr, (Cons (PQ.one, Nil)))))
                           rr)))))))))))

(** val primitive_check_boolean_operator :
    nat -> environment -> primitive_kind -> expr -> unit0 result **)

let primitive_check_boolean_operator fuel0 env op operator =
  bind
    (check fuel0 env Nil empty_context operator primitive_bool_operator_type)
    (fun _ ->
    let f = PQ.embed operator in
    let fx = fun b ->
      PQ.lam PQ.bool (fun x0 -> PQ.apps f (Cons (b, (Cons (x0, Nil)))))
    in
    (match op with
     | PNatLAnd ->
       bind
         (primitive_eq_closed fuel0 env (fx PQ.fal)
           (PQ.lam PQ.bool (fun _ -> PQ.fal)))
         (fun _ ->
         primitive_eq_closed fuel0 env (fx PQ.tru)
           (PQ.lam PQ.bool (fun x0 -> x0)))
     | PNatLOr ->
       bind
         (primitive_eq_closed fuel0 env (fx PQ.fal)
           (PQ.lam PQ.bool (fun x0 -> x0)))
         (fun _ ->
         primitive_eq_closed fuel0 env (fx PQ.tru)
           (PQ.lam PQ.bool (fun _ -> PQ.tru)))
     | PNatXor ->
       bind
         (primitive_eq_closed fuel0 env
           (PQ.apps f (Cons (PQ.fal, (Cons (PQ.fal, Nil))))) PQ.fal)
         (fun _ ->
         bind
           (primitive_eq_closed fuel0 env
             (PQ.apps f (Cons (PQ.tru, (Cons (PQ.fal, Nil))))) PQ.tru)
           (fun _ ->
           bind
             (primitive_eq_closed fuel0 env
               (PQ.apps f (Cons (PQ.fal, (Cons (PQ.tru, Nil))))) PQ.tru)
             (fun _ ->
             primitive_eq_closed fuel0 env
               (PQ.apps f (Cons (PQ.tru, (Cons (PQ.tru, Nil))))) PQ.fal)))
     | _ -> Decline UnsupportedDeclaration))

(** val primitive_check_bitwise_instance :
    nat -> environment -> primitive_kind -> expr -> unit0 result **)

let primitive_check_bitwise_instance fuel0 env op body =
  bind (primitive_authenticated fuel0 env PNatBitwise) (fun _ ->
    match body with
    | EApp (e, operator) ->
      (match e with
       | EConst (n0, l) ->
         (match l with
          | Nil ->
            bind
              (require (name_eqb n0 primitive_bitwise_name)
                MalformedDeclaration)
              (fun _ ->
              primitive_check_boolean_operator fuel0 env op operator)
          | Cons (_, _) -> Decline UnsupportedDeclaration)
       | _ -> Decline UnsupportedDeclaration)
    | _ -> Decline UnsupportedDeclaration)

(** val primitive_is_text : primitive_kind -> bool **)

let primitive_is_text = function
| PCharOfNat -> True
| PStringOfList -> True
| _ -> False

(** val primitive_ensure_type : nat -> environment -> expr -> unit0 result **)

let primitive_ensure_type fuel0 env e =
  bind (sort_of (checker fuel0 env Nil) empty_context e) (fun _ -> Accept Tt)

(** val primitive_check_text_interface :
    nat -> environment -> primitive_kind -> unit0 result **)

let primitive_check_text_interface fuel0 env = function
| PCharOfNat ->
  bind (require (core_nat_ready env) MalformedDeclaration) (fun _ ->
    primitive_ensure_type fuel0 env primitive_char)
| PStringOfList ->
  bind (primitive_ensure_type fuel0 env primitive_list_char) (fun _ ->
    bind (primitive_ensure_type fuel0 env primitive_char) (fun _ ->
      bind
        (check fuel0 env Nil empty_context (EApp ((EConst ((NameStr
          (core_list_name, (String ((Ascii (False, True, True, True, False,
          True, True, False)), (String ((Ascii (True, False, False, True,
          False, True, True, False)), (String ((Ascii (False, False, True,
          True, False, True, True, False)), EmptyString)))))))), (Cons
          (LZero, Nil)))), primitive_char)) primitive_list_char)
        (fun _ ->
        check fuel0 env Nil empty_context (EApp ((EConst ((NameStr
          (core_list_name, (String ((Ascii (True, True, False, False, False,
          True, True, False)), (String ((Ascii (True, True, True, True,
          False, True, True, False)), (String ((Ascii (False, True, True,
          True, False, True, True, False)), (String ((Ascii (True, True,
          False, False, True, True, True, False)), EmptyString)))))))))),
          (Cons (LZero, Nil)))), primitive_char))
          (primitive_arrow primitive_char
            (primitive_arrow primitive_list_char primitive_list_char)))))
| _ -> Accept Tt

(** val primitive_check_nat_equations :
    nat -> environment -> primitive_kind -> expr -> unit0 result **)

let primitive_check_nat_equations fuel0 env op body =
  match primitive_equations op body with
  | Some equations ->
    bind (primitive_dependencies fuel0 env op) (fun _ ->
      primitive_check_equations fuel0 fuel0 env equations)
  | None ->
    (match op with
     | PNatGcd -> primitive_check_gcd fuel0 env body
     | PNatMod -> primitive_check_fuel_rec fuel0 env True body
     | PNatDiv -> primitive_check_fuel_rec fuel0 env False body
     | PNatLAnd -> primitive_check_bitwise_instance fuel0 env op body
     | PNatLOr -> primitive_check_bitwise_instance fuel0 env op body
     | PNatXor -> primitive_check_bitwise_instance fuel0 env op body
     | PNatBitwise -> primitive_check_bitwise fuel0 env body
     | _ -> Decline UnsupportedDeclaration)

(** val classify_primitive :
    nat -> environment -> name -> name list -> expr -> expr -> primitive_kind
    option result **)

let classify_primitive fuel0 env n0 params ty0 body =
  match primitive_lookup n0 with
  | Some op ->
    bind
      (match find_decl n0 env with
       | Some _ -> Reject DuplicateDeclaration
       | None -> Accept Tt)
      (fun _ ->
      bind (require (Nat.eqb (length params) O) UniverseArity) (fun _ ->
        bind (primitive_check_signature fuel0 ty0 (primitive_signature op))
          (fun _ ->
          bind (primitive_closed fuel0 O body) (fun _ ->
            bind
              (match primitive_is_text op with
               | True -> primitive_check_text_interface fuel0 env op
               | False -> primitive_check_nat_equations fuel0 env op body)
              (fun _ -> Accept (Some op))))))
  | None ->
    (match name_mem n0 (Cons (core_nat_name, (Cons (core_zero_name, (Cons
             (core_succ_name, (Cons (core_bool_name, (Cons (core_false_name,
             (Cons (core_true_name, Nil)))))))))))) with
     | True -> Reject MalformedDeclaration
     | False -> Accept None)

(** val nat_name : name **)

let nat_name =
  NameStr (NameAnon, (String ((Ascii (False, True, True, True, False, False,
    True, False)), (String ((Ascii (True, False, False, False, False, True,
    True, False)), (String ((Ascii (False, False, True, False, True, True,
    True, False)), EmptyString)))))))

(** val bool_name : name **)

let bool_name =
  NameStr (NameAnon, (String ((Ascii (False, True, False, False, False,
    False, True, False)), (String ((Ascii (True, True, True, True, False,
    True, True, False)), (String ((Ascii (True, True, True, True, False,
    True, True, False)), (String ((Ascii (False, False, True, True, False,
    True, True, False)), EmptyString)))))))))

(** val reserved_names : name list **)

let reserved_names =
  Cons (nat_name, (Cons ((NameStr (nat_name, (String ((Ascii (False, True,
    False, True, True, True, True, False)), (String ((Ascii (True, False,
    True, False, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, True, False)), (String ((Ascii (True, True,
    True, True, False, True, True, False)), EmptyString)))))))))), (Cons
    ((NameStr (nat_name, (String ((Ascii (True, True, False, False, True,
    True, True, False)), (String ((Ascii (True, False, True, False, True,
    True, True, False)), (String ((Ascii (True, True, False, False, False,
    True, True, False)), (String ((Ascii (True, True, False, False, False,
    True, True, False)), EmptyString)))))))))), (Cons ((NameStr (nat_name,
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, False, True, True, False)),
    EmptyString)))))))), (Cons ((NameStr (nat_name, (String ((Ascii (False,
    False, False, False, True, True, True, False)), (String ((Ascii (False,
    True, False, False, True, True, True, False)), (String ((Ascii (True,
    False, True, False, False, True, True, False)), (String ((Ascii (False,
    False, True, False, False, True, True, False)), EmptyString)))))))))),
    (Cons ((NameStr (nat_name, (String ((Ascii (True, True, False, False,
    True, True, True, False)), (String ((Ascii (True, False, True, False,
    True, True, True, False)), (String ((Ascii (False, True, False, False,
    False, True, True, False)), EmptyString)))))))), (Cons ((NameStr
    (nat_name, (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), EmptyString)))))))), (Cons ((NameStr (nat_name, (String ((Ascii
    (False, False, False, False, True, True, True, False)), (String ((Ascii
    (True, True, True, True, False, True, True, False)), (String ((Ascii
    (True, True, True, False, True, True, True, False)), EmptyString)))))))),
    (Cons ((NameStr (nat_name, (String ((Ascii (True, True, True, False,
    False, True, True, False)), (String ((Ascii (True, True, False, False,
    False, True, True, False)), (String ((Ascii (False, False, True, False,
    False, True, True, False)), EmptyString)))))))), (Cons ((NameStr
    (nat_name, (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), EmptyString)))))))), (Cons ((NameStr (nat_name, (String ((Ascii
    (False, False, True, False, False, True, True, False)), (String ((Ascii
    (True, False, False, True, False, True, True, False)), (String ((Ascii
    (False, True, True, False, True, True, True, False)),
    EmptyString)))))))), (Cons ((NameStr (nat_name, (String ((Ascii (False,
    True, False, False, False, True, True, False)), (String ((Ascii (True,
    False, True, False, False, True, True, False)), (String ((Ascii (True,
    False, False, False, True, True, True, False)), EmptyString)))))))),
    (Cons ((NameStr (nat_name, (String ((Ascii (False, True, False, False,
    False, True, True, False)), (String ((Ascii (False, False, True, True,
    False, True, True, False)), (String ((Ascii (True, False, True, False,
    False, True, True, False)), EmptyString)))))))), (Cons ((NameStr
    (nat_name, (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), EmptyString)))))))))))))))), (Cons ((NameStr (nat_name, (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (True, False, False, False, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, False, True, True, False)),
    EmptyString)))))))))), (Cons ((NameStr (nat_name, (String ((Ascii (False,
    False, True, True, False, True, True, False)), (String ((Ascii (True,
    True, True, True, False, True, True, False)), (String ((Ascii (False,
    True, False, False, True, True, True, False)), EmptyString)))))))), (Cons
    ((NameStr (nat_name, (String ((Ascii (False, False, False, True, True,
    True, True, False)), (String ((Ascii (True, True, True, True, False,
    True, True, False)), (String ((Ascii (False, True, False, False, True,
    True, True, False)), EmptyString)))))))), (Cons ((NameStr (nat_name,
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, True, True, False, False, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString)))))))))))))))))))), (Cons ((NameStr (nat_name, (String
    ((Ascii (True, True, False, False, True, True, True, False)), (String
    ((Ascii (False, False, False, True, False, True, True, False)), (String
    ((Ascii (True, False, False, True, False, True, True, False)), (String
    ((Ascii (False, True, True, False, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)), (String
    ((Ascii (False, True, False, False, True, False, True, False)), (String
    ((Ascii (True, False, False, True, False, True, True, False)), (String
    ((Ascii (True, True, True, False, False, True, True, False)), (String
    ((Ascii (False, False, False, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString)))))))))))))))))))))), (Cons (bool_name, (Cons ((NameStr
    (bool_name, (String ((Ascii (False, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), EmptyString)))))))))))), (Cons ((NameStr (bool_name, (String
    ((Ascii (False, False, True, False, True, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (True, False, True, False, False, True, True, False)),
    EmptyString)))))))))), (Cons ((NameStr ((NameStr (NameAnon, (String
    ((Ascii (True, True, False, False, True, False, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, True, False)), (String
    ((Ascii (True, False, False, True, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (True, True, True, False, False, True, True, False)),
    EmptyString)))))))))))))), (String ((Ascii (True, True, True, True,
    False, True, True, False)), (String ((Ascii (False, True, True, False,
    False, True, True, False)), (String ((Ascii (False, False, True, True,
    False, False, True, False)), (String ((Ascii (True, False, False, True,
    False, True, True, False)), (String ((Ascii (True, True, False, False,
    True, True, True, False)), (String ((Ascii (False, False, True, False,
    True, True, True, False)), EmptyString)))))))))))))), (Cons ((NameStr
    ((NameStr (NameAnon, (String ((Ascii (True, True, False, False, False,
    False, True, False)), (String ((Ascii (False, False, False, True, False,
    True, True, False)), (String ((Ascii (True, False, False, False, False,
    True, True, False)), (String ((Ascii (False, True, False, False, True,
    True, True, False)), EmptyString)))))))))), (String ((Ascii (True, True,
    True, True, False, True, True, False)), (String ((Ascii (False, True,
    True, False, False, True, True, False)), (String ((Ascii (False, True,
    True, True, False, False, True, False)), (String ((Ascii (True, False,
    False, False, False, True, True, False)), (String ((Ascii (False, False,
    True, False, True, True, True, False)), EmptyString)))))))))))),
    Nil)))))))))))))))))))))))))))))))))))))))))))))))

type input_safety =
| InputSafe
| InputPartial
| InputUnsafe

type input_decl =
| InputAxiom of name * name list * expr * bool
| InputDefinition of reducibility_hints * name * name list * expr * expr
   * input_safety
| InputTheorem of name * name list * expr * expr
| InputOpaque of name * name list * expr * expr * bool
| InputUnsupported

(** val check_header :
    nat -> environment -> name -> name list -> expr -> unit0 result **)

let check_header fuel0 env n0 ps ty0 =
  match find_decl n0 env with
  | Some _ -> Reject DuplicateDeclaration
  | None ->
    (match negb (names_unique ps) with
     | True -> Reject DuplicateUniverse
     | False ->
       (match negb (scoped O ty0) with
        | True -> Reject MalformedDeclaration
        | False ->
          bind (infer fuel0 env ps empty_context ty0) (fun inferred ->
            bind (whnf fuel0 env ps empty_context inferred) (fun reduced ->
              match reduced with
              | ESort _ -> Accept Tt
              | _ -> Reject ExpectedSort))))

(** val check_proposition :
    nat -> environment -> name list -> expr -> unit0 result **)

let check_proposition fuel0 env ps ty0 =
  bind (infer fuel0 env ps empty_context ty0) (fun inferred ->
    bind (whnf fuel0 env ps empty_context inferred) (fun reduced ->
      match reduced with
      | ESort u0 ->
        bind (level_equiv fuel0 u0 LZero) (fun is_zero ->
          match is_zero with
          | True -> Accept Tt
          | False -> Reject MalformedDeclaration)
      | _ -> Reject ExpectedSort))

(** val checked_constant :
    nat -> environment -> name -> name list -> expr -> expr option ->
    decl_kind -> environment result **)

let checked_constant fuel0 env n0 ps ty0 body kind =
  bind (check_header fuel0 env n0 ps ty0) (fun _ ->
    bind
      (match body with
       | Some value ->
         (match scoped O value with
          | True -> check fuel0 env ps empty_context value ty0
          | False -> Reject MalformedDeclaration)
       | None -> Accept Tt)
      (fun _ -> Accept (Cons ({ decl_name = n0; decl_params = ps; decl_type =
      ty0; decl_value = body; decl_kind_of = kind; decl_hints = HintOpaque },
      env))))

(** val admit : nat -> environment -> input_decl -> environment result **)

let admit fuel0 env = function
| InputAxiom (n0, ps, ty0, unsafe) ->
  (match unsafe with
   | True -> Decline UnsupportedDeclaration
   | False ->
     (match name_mem n0 reserved_names with
      | True -> Reject MalformedDeclaration
      | False -> checked_constant fuel0 env n0 ps ty0 None DAssumption))
| InputDefinition (hints, n0, ps, ty0, body, i) ->
  (match i with
   | InputSafe ->
     bind (check_header fuel0 env n0 ps ty0) (fun _ ->
       bind (require (scoped O body) MalformedDeclaration) (fun _ ->
         bind (check fuel0 env ps empty_context body ty0) (fun _ ->
           bind (classify_primitive fuel0 env n0 ps ty0 body)
             (fun primitive ->
             let kind =
               match primitive with
               | Some p0 -> DPrimitive p0
               | None -> DDefinition
             in
             Accept (Cons ({ decl_name = n0; decl_params = ps; decl_type =
             ty0; decl_value = (Some body); decl_kind_of = kind; decl_hints =
             hints }, env))))))
   | _ -> Decline UnsupportedDeclaration)
| InputTheorem (n0, ps, ty0, body) ->
  (match name_mem n0 reserved_names with
   | True -> Reject MalformedDeclaration
   | False ->
     bind (check_header fuel0 env n0 ps ty0) (fun _ ->
       bind (check_proposition fuel0 env ps ty0) (fun _ ->
         checked_constant fuel0 env n0 ps ty0 (Some body) DTheorem)))
| InputOpaque (n0, ps, ty0, body, unsafe) ->
  (match unsafe with
   | True -> Decline UnsupportedDeclaration
   | False ->
     (match name_mem n0 reserved_names with
      | True -> Reject MalformedDeclaration
      | False -> checked_constant fuel0 env n0 ps ty0 (Some body) DOpaque))
| InputUnsupported -> Decline UnsupportedDeclaration

type ind_spec = { spec_decl : declaration; spec_ctors : declaration list }

type ind_checked = { checked_spec : ind_spec;
                     checked_indices : ind_local list; checked_level : 
                     level }

type ind_stats = { stats_params : ind_local list;
                   stats_types : ind_checked list; stats_names : name list;
                   stats_levels : level list; stats_result : level;
                   stats_unsafe : bool; stats_state : ind_state }

type ind_motive = { motive_type_info : ind_checked; motive_local : ind_local;
                    motive_major : ind_local }

type ind_recursive_arg = { ra_field : ind_local;
                           ra_arguments : ind_local list; ra_inductive : 
                           nat; ra_indices : expr list }

type ind_minor = { minor_ctor : declaration; minor_owner : nat;
                   minor_local : ind_local; minor_fields : ind_local list;
                   minor_recursive : ind_recursive_arg list }

(** val same_names : name list -> name list -> bool **)

let same_names =
  list_eqb name_eqb

(** val ind_names : declaration list -> name list **)

let ind_names types =
  map (fun d -> d.decl_name) types

(** val all_ctor_names : ind_spec list -> name list **)

let all_ctor_names specs =
  flat_map (fun s -> map (fun d -> d.decl_name) s.spec_ctors) specs

(** val rec_name : name -> name **)

let rec_name n0 =
  NameStr (n0, (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), EmptyString)))))))

(** val gather_ctors :
    name list -> declaration list -> declaration list result **)

let rec gather_ctors ns ctors =
  match ns with
  | Nil -> Accept Nil
  | Cons (n0, ns0) ->
    (match find_decl n0 ctors with
     | Some d ->
       (match d.decl_kind_of with
        | DConstructor _ ->
          bind (gather_ctors ns0 ctors) (fun ds -> Accept (Cons (d, ds)))
        | _ -> Reject MalformedDeclaration)
     | None -> Reject MalformedDeclaration)

(** val gather_specs :
    declaration list -> declaration list -> ind_spec list result **)

let rec gather_specs types ctors =
  match types with
  | Nil -> Accept Nil
  | Cons (d, ds) ->
    (match d.decl_kind_of with
     | DInductive data ->
       bind (gather_ctors data.ind_ctors ctors) (fun cs ->
         bind (gather_specs ds ctors) (fun rest -> Accept (Cons
           ({ spec_decl = d; spec_ctors = cs }, rest))))
     | _ -> Reject MalformedDeclaration)

(** val check_primitive_inductive :
    name list -> nat -> ind_spec list -> bool **)

let check_primitive_inductive ps nparams specs =
  match ps with
  | Nil ->
    (match nparams with
     | O ->
       (match specs with
        | Nil -> False
        | Cons (s, l) ->
          (match l with
           | Nil ->
             let d = s.spec_decl in
             (match expr_eqb d.decl_type (ESort (LSucc LZero)) with
              | True ->
                (match s.spec_ctors with
                 | Nil -> False
                 | Cons (a, l0) ->
                   (match l0 with
                    | Nil -> False
                    | Cons (b, l1) ->
                      (match l1 with
                       | Nil ->
                         let head = EConst (d.decl_name, Nil) in
                         (match name_eqb d.decl_name nat_name with
                          | True ->
                            (match match match name_eqb a.decl_name (NameStr
                                                 (nat_name, (String ((Ascii
                                                 (False, True, False, True,
                                                 True, True, True, False)),
                                                 (String ((Ascii (True,
                                                 False, True, False, False,
                                                 True, True, False)), (String
                                                 ((Ascii (False, True, False,
                                                 False, True, True, True,
                                                 False)), (String ((Ascii
                                                 (True, True, True, True,
                                                 False, True, True, False)),
                                                 EmptyString)))))))))) with
                                         | True ->
                                           name_eqb b.decl_name (NameStr
                                             (nat_name, (String ((Ascii
                                             (True, True, False, False, True,
                                             True, True, False)), (String
                                             ((Ascii (True, False, True,
                                             False, True, True, True,
                                             False)), (String ((Ascii (True,
                                             True, False, False, False, True,
                                             True, False)), (String ((Ascii
                                             (True, True, False, False,
                                             False, True, True, False)),
                                             EmptyString))))))))))
                                         | False -> False with
                                   | True -> expr_eqb a.decl_type head
                                   | False -> False with
                             | True ->
                               expr_eqb b.decl_type (EPi (NameAnon, BDefault,
                                 head, head))
                             | False -> False)
                          | False ->
                            (match name_eqb d.decl_name bool_name with
                             | True ->
                               (match match match name_eqb a.decl_name
                                                    (NameStr (bool_name,
                                                    (String ((Ascii (False,
                                                    True, True, False, False,
                                                    True, True, False)),
                                                    (String ((Ascii (True,
                                                    False, False, False,
                                                    False, True, True,
                                                    False)), (String ((Ascii
                                                    (False, False, True,
                                                    True, False, True, True,
                                                    False)), (String ((Ascii
                                                    (True, True, False,
                                                    False, True, True, True,
                                                    False)), (String ((Ascii
                                                    (True, False, True,
                                                    False, False, True, True,
                                                    False)),
                                                    EmptyString)))))))))))) with
                                            | True ->
                                              name_eqb b.decl_name (NameStr
                                                (bool_name, (String ((Ascii
                                                (False, False, True, False,
                                                True, True, True, False)),
                                                (String ((Ascii (False, True,
                                                False, False, True, True,
                                                True, False)), (String
                                                ((Ascii (True, False, True,
                                                False, True, True, True,
                                                False)), (String ((Ascii
                                                (True, False, True, False,
                                                False, True, True, False)),
                                                EmptyString))))))))))
                                            | False -> False with
                                      | True -> expr_eqb a.decl_type head
                                      | False -> False with
                                | True -> expr_eqb b.decl_type head
                                | False -> False)
                             | False -> False))
                       | Cons (_, _) -> False)))
              | False -> False)
           | Cons (_, _) -> False))
     | S _ -> False)
  | Cons (_, _) -> False

(** val check_inductive_types :
    ind_spec list -> nat -> environment -> name list -> ind_local list ->
    level option -> ind_state -> (ind_checked list, ind_state) prod result **)

let rec check_inductive_types specs fuel0 env ps params result_level s =
  match specs with
  | Nil -> Accept (Pair (Nil, s))
  | Cons (spec, specs0) ->
    let d = spec.spec_decl in
    bind (require (same_names d.decl_params ps) MalformedDeclaration)
      (fun _ ->
      bind (check_header fuel0 env d.decl_name ps d.decl_type) (fun _ ->
        bind (apply_parameters params fuel0 env ps s d.decl_type) (fun ty0 ->
          bind (open_telescope fuel0 fuel0 env ps s ty0) (fun opened ->
            let Pair (p0, s0) = opened in
            let Pair (indices, body) = p0 in
            (match body with
             | ESort u0 ->
               bind
                 (match result_level with
                  | Some v0 ->
                    bind (level_equiv fuel0 u0 v0) (fun ok ->
                      require ok MalformedDeclaration)
                  | None -> Accept Tt)
                 (fun _ ->
                 bind
                   (check_inductive_types specs0 fuel0 env ps params (Some
                     u0) s0)
                   (fun tail ->
                   let Pair (rest, s1) = tail in
                   Accept (Pair ((Cons ({ checked_spec = spec;
                   checked_indices = indices; checked_level = u0 }, rest)),
                   s1))))
             | _ -> Reject ExpectedSort)))))

(** val valid_ind_app_at :
    ind_checked list -> ind_stats -> expr -> expr list -> nat -> nat option **)

let rec valid_ind_app_at types stats head args i =
  match types with
  | Nil -> None
  | Cons (t0, ts) ->
    let d = t0.checked_spec.spec_decl in
    (match match match match expr_eqb head (EConst (d.decl_name,
                               stats.stats_levels)) with
                       | True ->
                         Nat.eqb (length args)
                           (add (length stats.stats_params)
                             (length t0.checked_indices))
                       | False -> False with
                 | True ->
                   list_eqb expr_eqb
                     (firstn (length stats.stats_params) args)
                     (local_exprs stats.stats_params)
                 | False -> False with
           | True ->
             negb
               (existsb (has_inductive stats.stats_names)
                 (skipn (length stats.stats_params) args))
           | False -> False with
     | True -> Some i
     | False -> valid_ind_app_at ts stats head args (S i))

(** val valid_ind_app : ind_stats -> expr -> nat option **)

let valid_ind_app stats e =
  let Pair (h, args) = split_app e in
  valid_ind_app_at stats.stats_types stats h args O

(** val ind_app_indices : ind_stats -> expr -> expr list **)

let ind_app_indices stats e =
  skipn (length stats.stats_params) (snd (split_app e))

(** val check_positive :
    nat -> nat -> environment -> name list -> ind_stats -> ind_state -> expr
    -> unit0 result **)

let rec check_positive depth fuel0 env ps stats s e =
  match depth with
  | O -> Decline OutOfFuel
  | S depth0 ->
    bind (whnf fuel0 env ps s.ist_context e) (fun e0 ->
      match negb (has_inductive stats.stats_names e0) with
      | True -> Accept Tt
      | False ->
        (match e0 with
         | EPi (n0, bi, a, b) ->
           bind
             (require (negb (has_inductive stats.stats_names a))
               MalformedDeclaration)
             (fun _ ->
             let Pair (x0, s0) = ind_fresh s n0 bi a in
             check_positive depth0 fuel0 env ps stats s0
               (instantiate b (local_expr x0)))
         | _ ->
           (match valid_ind_app stats e0 with
            | Some _ -> Accept Tt
            | None -> Reject MalformedDeclaration)))

(** val derived_inductive : ind_stats -> ind_checked -> declaration **)

let derived_inductive stats t0 =
  let specs = map (fun i -> i.checked_spec) stats.stats_types in
  let ctors = flat_map (fun i -> i.spec_ctors) specs in
  let d = t0.checked_spec.spec_decl in
  { decl_name = d.decl_name; decl_params = d.decl_params; decl_type =
  d.decl_type; decl_value = None; decl_kind_of = (DInductive
  { ind_num_params = (length stats.stats_params); ind_num_indices =
  (length t0.checked_indices); ind_all = stats.stats_names; ind_ctors =
  (map (fun d0 -> d0.decl_name) t0.checked_spec.spec_ctors); ind_num_nested =
  O; ind_is_rec =
  (existsb (fun c -> recursive_constructor stats.stats_names c.decl_type)
    ctors);
  ind_is_reflexive =
  (existsb (fun c -> reflexive_constructor stats.stats_names c.decl_type)
    ctors);
  ind_is_unsafe = stats.stats_unsafe }); decl_hints = d.decl_hints }

(** val inductive_data_eqb : inductive_data -> inductive_data -> bool **)

let inductive_data_eqb a b =
  match match match match match match match Nat.eqb a.ind_num_params
                                              b.ind_num_params with
                                      | True ->
                                        Nat.eqb a.ind_num_indices
                                          b.ind_num_indices
                                      | False -> False with
                                | True -> same_names a.ind_all b.ind_all
                                | False -> False with
                          | True -> same_names a.ind_ctors b.ind_ctors
                          | False -> False with
                    | True -> Nat.eqb a.ind_num_nested b.ind_num_nested
                    | False -> False with
              | True -> eqb0 a.ind_is_rec b.ind_is_rec
              | False -> False with
        | True -> eqb0 a.ind_is_reflexive b.ind_is_reflexive
        | False -> False with
  | True -> eqb0 a.ind_is_unsafe b.ind_is_unsafe
  | False -> False

(** val constructor_data_eqb :
    constructor_data -> constructor_data -> bool **)

let constructor_data_eqb a b =
  match match match match name_eqb a.ctor_induct b.ctor_induct with
                    | True -> Nat.eqb a.ctor_index b.ctor_index
                    | False -> False with
              | True -> Nat.eqb a.ctor_num_params b.ctor_num_params
              | False -> False with
        | True -> Nat.eqb a.ctor_num_fields b.ctor_num_fields
        | False -> False with
  | True -> eqb0 a.ctor_is_unsafe b.ctor_is_unsafe
  | False -> False

(** val map_result : ('a1 -> 'a2 result) -> 'a1 list -> 'a2 list result **)

let rec map_result f = function
| Nil -> Accept Nil
| Cons (x0, xs0) ->
  bind (f x0) (fun y ->
    bind (map_result f xs0) (fun ys -> Accept (Cons (y, ys))))

(** val check_field :
    nat -> environment -> name list -> ind_stats -> ind_state -> ind_local ->
    unit0 result **)

let check_field fuel0 env ps stats s field =
  bind (ind_sort fuel0 env ps s field.il_type) (fun u0 ->
    bind (level_equiv fuel0 stats.stats_result LZero) (fun prop0 ->
      bind
        (match prop0 with
         | True -> Accept Tt
         | False ->
           bind (level_le fuel0 u0 stats.stats_result) (fun ok ->
             require ok MalformedDeclaration))
        (fun _ ->
        match stats.stats_unsafe with
        | True -> Accept Tt
        | False -> check_positive fuel0 fuel0 env ps stats s field.il_type)))

(** val check_ctors :
    declaration list -> name -> nat -> nat -> environment -> name list ->
    ind_stats -> ind_state -> (declaration list, ind_state) prod result **)

let rec check_ctors ctors owner index fuel0 env ps stats s =
  match ctors with
  | Nil -> Accept (Pair (Nil, s))
  | Cons (d, ctors0) ->
    bind (require (same_names d.decl_params ps) MalformedDeclaration)
      (fun _ ->
      bind (check_header fuel0 env d.decl_name ps d.decl_type) (fun _ ->
        bind (apply_parameters stats.stats_params fuel0 env ps s d.decl_type)
          (fun ty0 ->
          bind (open_telescope fuel0 fuel0 env ps s ty0) (fun opened ->
            let Pair (p0, s0) = opened in
            let Pair (fields, body) = p0 in
            bind (map_result (check_field fuel0 env ps stats s0) fields)
              (fun _ ->
              bind
                (match valid_ind_app stats body with
                 | Some i ->
                   (match nth_error stats.stats_names i with
                    | Some n0 ->
                      require (name_eqb n0 owner) MalformedDeclaration
                    | None -> Reject MalformedDeclaration)
                 | None -> Reject MalformedDeclaration)
                (fun _ ->
                let actual = { ctor_induct = owner; ctor_index = index;
                  ctor_num_params = (length stats.stats_params);
                  ctor_num_fields = (length fields); ctor_is_unsafe =
                  stats.stats_unsafe }
                in
                bind
                  (require
                    (Nat.eqb (raw_arity d.decl_type)
                      (add (length stats.stats_params) (length fields)))
                    MalformedDeclaration)
                  (fun _ ->
                  let generated = { decl_name = d.decl_name; decl_params =
                    ps; decl_type = d.decl_type; decl_value = None;
                    decl_kind_of = (DConstructor actual); decl_hints =
                    d.decl_hints }
                  in
                  bind
                    (check_ctors ctors0 owner (S index) fuel0 env ps stats s0)
                    (fun tail ->
                    let Pair (rest, s1) = tail in
                    Accept (Pair ((Cons (generated, rest)), s1))))))))))

(** val check_all_ctors :
    ind_checked list -> nat -> environment -> name list -> ind_stats ->
    ind_state -> (declaration list, ind_state) prod result **)

let rec check_all_ctors types fuel0 env ps stats s =
  match types with
  | Nil -> Accept (Pair (Nil, s))
  | Cons (t0, types0) ->
    let spec = t0.checked_spec in
    bind
      (check_ctors spec.spec_ctors spec.spec_decl.decl_name O fuel0 env ps
        stats s)
      (fun first ->
      let Pair (ctors, s0) = first in
      bind (check_all_ctors types0 fuel0 env ps stats s0) (fun tail ->
        let Pair (rest, s1) = tail in Accept (Pair ((app ctors rest), s1))))

(** val large_elimination :
    nat -> environment -> name list -> ind_stats -> ind_state -> bool result **)

let large_elimination fuel0 env ps stats s =
  match level_never_zero stats.stats_result with
  | True -> Accept True
  | False ->
    (match stats.stats_types with
     | Nil -> Accept False
     | Cons (t0, l) ->
       (match l with
        | Nil ->
          (match t0.checked_spec.spec_ctors with
           | Nil -> Accept True
           | Cons (c, l0) ->
             (match l0 with
              | Nil ->
                bind
                  (apply_parameters stats.stats_params fuel0 env ps s
                    c.decl_type)
                  (fun ty0 ->
                  bind (open_telescope fuel0 fuel0 env ps s ty0)
                    (fun opened ->
                    let Pair (p0, s0) = opened in
                    let Pair (fields, body) = p0 in
                    let args = snd (split_app body) in
                    bind
                      (map_result (fun x0 ->
                        bind (ind_sort fuel0 env ps s0 x0.il_type) (fun u0 ->
                          bind (level_equiv fuel0 u0 LZero) (fun prop0 ->
                            Accept
                            (match prop0 with
                             | True -> True
                             | False ->
                               existsb (expr_eqb (local_expr x0)) args))))
                        fields)
                      (fun checks -> Accept (forallb (fun x0 -> x0) checks))))
              | Cons (_, _) -> Accept False))
        | Cons (_, _) -> Accept False))

(** val k_target : nat -> ind_stats -> bool result **)

let k_target fuel0 stats =
  bind (level_equiv fuel0 stats.stats_result LZero) (fun prop0 ->
    match prop0 with
    | True ->
      (match stats.stats_types with
       | Nil -> Accept False
       | Cons (t0, l) ->
         (match l with
          | Nil ->
            (match t0.checked_spec.spec_ctors with
             | Nil -> Accept False
             | Cons (c, l0) ->
               (match l0 with
                | Nil ->
                  Accept
                    (Nat.leb (raw_arity c.decl_type)
                      (length stats.stats_params))
                | Cons (_, _) -> Accept False))
          | Cons (_, _) -> Accept False))
    | False -> Accept False)

(** val fresh_elim_name : nat -> nat -> name list -> name result **)

let rec fresh_elim_name fuel0 index ps =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    let n0 = NameNum ((NameStr (NameAnon, (String ((Ascii (True, True, True,
      True, True, False, True, False)), (String ((Ascii (False, True, False,
      False, True, True, True, False)), (String ((Ascii (True, True, True,
      True, False, True, True, False)), (String ((Ascii (True, True, False,
      False, False, True, True, False)), (String ((Ascii (True, False, False,
      False, True, True, True, False)), (String ((Ascii (True, True, True,
      True, True, False, True, False)), (String ((Ascii (True, False, True,
      False, False, True, True, False)), (String ((Ascii (False, False, True,
      True, False, True, True, False)), (String ((Ascii (True, False, False,
      True, False, True, True, False)), (String ((Ascii (True, False, True,
      True, False, True, True, False)), EmptyString)))))))))))))))))))))),
      (N.of_nat index))
    in
    (match name_mem n0 ps with
     | True -> fresh_elim_name fuel1 (S index) ps
     | False -> Accept n0)

(** val build_motives :
    ind_checked list -> ind_stats -> level -> ind_state -> (ind_motive list,
    ind_state) prod **)

let rec build_motives types stats elim s =
  match types with
  | Nil -> Pair (Nil, s)
  | Cons (t0, types0) ->
    let head = EConst (t0.checked_spec.spec_decl.decl_name,
      stats.stats_levels)
    in
    let major_ty =
      apply_locals (apply_locals head stats.stats_params) t0.checked_indices
    in
    let Pair (major, s0) =
      ind_fresh s (NameStr (NameAnon, (String ((Ascii (False, False, True,
        False, True, True, True, False)), EmptyString)))) BDefault major_ty
    in
    let motive_ty =
      close_pi t0.checked_indices (close_pi (Cons (major, Nil)) (ESort elim))
    in
    let Pair (motive, s1) =
      ind_fresh s0 (NameStr (NameAnon, (String ((Ascii (True, False, True,
        True, False, True, True, False)), (String ((Ascii (True, True, True,
        True, False, True, True, False)), (String ((Ascii (False, False,
        True, False, True, True, True, False)), (String ((Ascii (True, False,
        False, True, False, True, True, False)), (String ((Ascii (False,
        True, True, False, True, True, True, False)), (String ((Ascii (True,
        False, True, False, False, True, True, False)),
        EmptyString)))))))))))))) BDefault motive_ty
    in
    let Pair (rest, s2) = build_motives types0 stats elim s1 in
    Pair ((Cons ({ motive_type_info = t0; motive_local = motive;
    motive_major = major }, rest)), s2)

(** val build_recursive_args :
    ind_local list -> nat -> environment -> name list -> ind_stats ->
    ind_state -> (ind_recursive_arg list, ind_state) prod result **)

let rec build_recursive_args fields fuel0 env ps stats s =
  match fields with
  | Nil -> Accept (Pair (Nil, s))
  | Cons (x0, fields0) ->
    bind (open_telescope fuel0 fuel0 env ps s x0.il_type) (fun opened ->
      let Pair (p0, s0) = opened in
      let Pair (args, body) = p0 in
      bind (build_recursive_args fields0 fuel0 env ps stats s0) (fun tail ->
        let Pair (rest, s1) = tail in
        (match valid_ind_app stats body with
         | Some i ->
           Accept (Pair ((Cons ({ ra_field = x0; ra_arguments = args;
             ra_inductive = i; ra_indices = (ind_app_indices stats body) },
             rest)), s1))
         | None -> Accept (Pair (rest, s1)))))

(** val build_ihs :
    ind_recursive_arg list -> ind_motive list -> ind_state -> (ind_local
    list, ind_state) prod result **)

let rec build_ihs args motives s =
  match args with
  | Nil -> Accept (Pair (Nil, s))
  | Cons (a, args0) ->
    (match nth_error motives a.ra_inductive with
     | Some m ->
       let ih_ty =
         close_pi a.ra_arguments (EApp
           ((apply_exprs (local_expr m.motive_local) a.ra_indices),
           (apply_locals (local_expr a.ra_field) a.ra_arguments)))
       in
       let Pair (ih, s0) =
         ind_fresh s (NameStr (NameAnon, (String ((Ascii (True, False, False,
           True, False, True, True, False)), (String ((Ascii (False, False,
           False, True, False, True, True, False)), EmptyString))))))
           BDefault ih_ty
       in
       bind (build_ihs args0 motives s0) (fun tail ->
         let Pair (rest, s1) = tail in Accept (Pair ((Cons (ih, rest)), s1)))
     | None -> Reject MalformedDeclaration)

(** val build_minors :
    declaration list -> nat -> nat -> environment -> name list -> ind_stats
    -> ind_motive list -> ind_state -> (ind_minor list, ind_state) prod result **)

let rec build_minors ctors owner fuel0 env ps stats motives s =
  match ctors with
  | Nil -> Accept (Pair (Nil, s))
  | Cons (c, ctors0) ->
    bind (apply_parameters stats.stats_params fuel0 env ps s c.decl_type)
      (fun ty0 ->
      bind (open_telescope fuel0 fuel0 env ps s ty0) (fun opened ->
        let Pair (p0, s0) = opened in
        let Pair (fields, body) = p0 in
        bind (build_recursive_args fields fuel0 env ps stats s0)
          (fun recursive ->
          let Pair (recursive0, s1) = recursive in
          bind (build_ihs recursive0 motives s1) (fun ihs ->
            let Pair (ihs0, s2) = ihs in
            (match nth_error motives owner with
             | Some m ->
               let ctor_app =
                 apply_locals
                   (apply_locals (EConst (c.decl_name, stats.stats_levels))
                     stats.stats_params)
                   fields
               in
               let minor_ty =
                 close_pi fields
                   (close_pi ihs0 (EApp
                     ((apply_exprs (local_expr m.motive_local)
                        (ind_app_indices stats body)),
                     ctor_app)))
               in
               let Pair (minor, s3) =
                 ind_fresh s2 c.decl_name BDefault minor_ty
               in
               bind (build_minors ctors0 owner fuel0 env ps stats motives s3)
                 (fun tail ->
                 let Pair (rest, s4) = tail in
                 Accept (Pair ((Cons ({ minor_ctor = c; minor_owner = owner;
                 minor_local = minor; minor_fields = fields;
                 minor_recursive = recursive0 }, rest)), s4)))
             | None -> Reject MalformedDeclaration)))))

(** val build_all_minors :
    ind_checked list -> nat -> nat -> environment -> name list -> ind_stats
    -> ind_motive list -> ind_state -> (ind_minor list, ind_state) prod result **)

let rec build_all_minors types owner fuel0 env ps stats motives s =
  match types with
  | Nil -> Accept (Pair (Nil, s))
  | Cons (t0, types0) ->
    bind
      (build_minors t0.checked_spec.spec_ctors owner fuel0 env ps stats
        motives s)
      (fun first ->
      let Pair (minors, s0) = first in
      bind (build_all_minors types0 (S owner) fuel0 env ps stats motives s0)
        (fun tail ->
        let Pair (rest, s1) = tail in Accept (Pair ((app minors rest), s1))))

(** val recursive_value :
    ind_stats -> level list -> ind_motive list -> ind_minor list ->
    ind_recursive_arg -> expr result **)

let recursive_value stats rec_levels motives minors a =
  match nth_error stats.stats_names a.ra_inductive with
  | Some n0 ->
    let f =
      apply_locals (EConst ((rec_name n0), rec_levels)) stats.stats_params
    in
    let f0 = apply_locals f (map (fun i -> i.motive_local) motives) in
    let f1 = apply_locals f0 (map (fun i -> i.minor_local) minors) in
    let f2 = apply_exprs f1 a.ra_indices in
    Accept
    (close_lam a.ra_arguments (EApp (f2,
      (apply_locals (local_expr a.ra_field) a.ra_arguments))))
  | None -> Reject MalformedDeclaration

(** val build_rule :
    ind_stats -> level list -> ind_motive list -> ind_minor list -> ind_minor
    -> recursor_rule result **)

let build_rule stats rec_levels motives minors m =
  bind
    (map_result (recursive_value stats rec_levels motives minors)
      m.minor_recursive)
    (fun rec_values ->
    let body =
      apply_exprs (apply_locals (local_expr m.minor_local) m.minor_fields)
        rec_values
    in
    Accept { rule_ctor = m.minor_ctor.decl_name; rule_nfields =
    (length m.minor_fields); rule_rhs =
    (close_lam stats.stats_params
      (close_lam (map (fun i -> i.motive_local) motives)
        (close_lam (map (fun i -> i.minor_local) minors)
          (close_lam m.minor_fields body)))) })

(** val build_recursor :
    ind_stats -> name list -> ind_motive list -> ind_minor list -> bool ->
    nat -> ind_motive -> declaration result **)

let build_recursor stats rec_ps motives minors k index m =
  let t0 = m.motive_type_info in
  let major = m.motive_major in
  let ty0 =
    close_pi stats.stats_params
      (close_pi (map (fun i -> i.motive_local) motives)
        (close_pi (map (fun i -> i.minor_local) minors)
          (close_pi t0.checked_indices
            (close_pi (Cons (major, Nil)) (EApp
              ((apply_locals (local_expr m.motive_local) t0.checked_indices),
              (local_expr major)))))))
  in
  bind
    (map_result
      (build_rule stats (map (fun x0 -> LParam x0) rec_ps) motives minors)
      (filter (fun x0 -> Nat.eqb x0.minor_owner index) minors))
    (fun rules -> Accept { decl_name =
    (rec_name t0.checked_spec.spec_decl.decl_name); decl_params = rec_ps;
    decl_type = ty0; decl_value = None; decl_kind_of = (DRecursor { rec_all =
    stats.stats_names; rec_num_params = (length stats.stats_params);
    rec_num_indices = (length t0.checked_indices); rec_num_motives =
    (length motives); rec_num_minors = (length minors); rec_rules = rules;
    rec_k = k; rec_is_unsafe = stats.stats_unsafe }); decl_hints =
    HintOpaque })

(** val build_recursors :
    ind_motive list -> nat -> ind_stats -> name list -> ind_motive list ->
    ind_minor list -> bool -> declaration list result **)

let rec build_recursors remaining index stats rec_ps motives minors k =
  match remaining with
  | Nil -> Accept Nil
  | Cons (m, remaining0) ->
    bind (build_recursor stats rec_ps motives minors k index m) (fun d ->
      bind
        (build_recursors remaining0 (S index) stats rec_ps motives minors k)
        (fun ds -> Accept (Cons (d, ds))))

(** val rule_eqb :
    name list -> name list -> recursor_rule -> recursor_rule -> bool **)

let rule_eqb source_ps target_ps a b =
  match match name_eqb a.rule_ctor b.rule_ctor with
        | True -> Nat.eqb a.rule_nfields b.rule_nfields
        | False -> False with
  | True ->
    expr_eqb
      (subst_levels source_ps (map (fun x0 -> LParam x0) target_ps)
        a.rule_rhs)
      b.rule_rhs
  | False -> False

(** val recursor_data_eqb :
    name list -> name list -> recursor_data -> recursor_data -> bool **)

let recursor_data_eqb source_ps target_ps a b =
  match match match match match match match same_names a.rec_all b.rec_all with
                                      | True ->
                                        Nat.eqb a.rec_num_params
                                          b.rec_num_params
                                      | False -> False with
                                | True ->
                                  Nat.eqb a.rec_num_indices b.rec_num_indices
                                | False -> False with
                          | True ->
                            Nat.eqb a.rec_num_motives b.rec_num_motives
                          | False -> False with
                    | True -> Nat.eqb a.rec_num_minors b.rec_num_minors
                    | False -> False with
              | True -> eqb0 a.rec_k b.rec_k
              | False -> False with
        | True -> eqb0 a.rec_is_unsafe b.rec_is_unsafe
        | False -> False with
  | True -> list_eqb (rule_eqb source_ps target_ps) a.rec_rules b.rec_rules
  | False -> False

(** val verify_rec_metadata : declaration -> declaration -> unit0 result **)

let verify_rec_metadata source generated =
  let sps = source.decl_params in
  let gps = generated.decl_params in
  bind
    (require
      (match names_unique sps with
       | True -> Nat.eqb (length sps) (length gps)
       | False -> False)
      MalformedDeclaration)
    (fun _ ->
    bind
      (require (name_eqb source.decl_name generated.decl_name)
        MalformedDeclaration)
      (fun _ ->
      bind
        (require
          (expr_eqb
            (subst_levels sps (map (fun x0 -> LParam x0) gps)
              source.decl_type)
            generated.decl_type)
          MalformedDeclaration)
        (fun _ ->
        match source.decl_kind_of with
        | DRecursor a ->
          (match generated.decl_kind_of with
           | DRecursor b ->
             require (recursor_data_eqb sps gps a b) MalformedDeclaration
           | _ -> Reject MalformedDeclaration)
        | _ -> Reject MalformedDeclaration)))

(** val derive_inductive :
    nat -> environment -> name list -> nat -> ind_spec list -> declaration
    list result **)

let derive_inductive fuel0 env ps np specs = match specs with
| Nil -> Reject MalformedDeclaration
| Cons (first_spec, _) ->
  let first = first_spec.spec_decl in
  let unsafe =
    match first.decl_kind_of with
    | DInductive i -> i.ind_is_unsafe
    | _ -> False
  in
  let types = map (fun i -> i.spec_decl) specs in
  let ns = ind_names types in
  let derived_names = app ns (app (all_ctor_names specs) (map rec_name ns)) in
  bind (require (names_unique derived_names) DuplicateDeclaration) (fun _ ->
    bind
      (require
        (forallb (fun n0 ->
          match find_decl n0 env with
          | Some _ -> False
          | None -> True) derived_names)
        DuplicateDeclaration)
      (fun _ ->
      bind (require (names_unique ps) DuplicateUniverse) (fun _ ->
        bind
          (require
            (match match negb unsafe with
                   | True -> check_primitive_inductive ps np specs
                   | False -> False with
             | True -> True
             | False ->
               negb
                 (existsb (fun n0 -> name_mem n0 reserved_names)
                   derived_names))
            MalformedDeclaration)
          (fun _ ->
          bind
            (open_parameters np fuel0 env ps initial_ind_state
              first.decl_type)
            (fun params ->
            let Pair (p0, s) = params in
            let Pair (params0, _) = p0 in
            bind (check_inductive_types specs fuel0 env ps params0 None s)
              (fun checked ->
              let Pair (checked0, s0) = checked in
              (match checked0 with
               | Nil -> Reject MalformedDeclaration
               | Cons (head, _) ->
                 let stats = { stats_params = params0; stats_types =
                   checked0; stats_names = (ind_names types); stats_levels =
                   (map (fun x0 -> LParam x0) ps); stats_result =
                   head.checked_level; stats_unsafe = unsafe; stats_state =
                   s0 }
                 in
                 let inds = map (derived_inductive stats) checked0 in
                 let ind_env = app inds env in
                 bind (check_all_ctors checked0 fuel0 ind_env ps stats s0)
                   (fun constructors ->
                   let Pair (constructors0, s1) = constructors in
                   let ctor_env = app constructors0 ind_env in
                   bind (large_elimination fuel0 ctor_env ps stats s1)
                     (fun large ->
                     bind (k_target fuel0 stats) (fun k ->
                       bind (fresh_elim_name (S (length ps)) O ps)
                         (fun fresh ->
                         let elim =
                           match large with
                           | True -> LParam fresh
                           | False -> LZero
                         in
                         let rec_ps =
                           match large with
                           | True -> Cons (fresh, ps)
                           | False -> ps
                         in
                         let Pair (motives, s2) =
                           build_motives checked0 stats elim s1
                         in
                         bind
                           (build_all_minors checked0 O fuel0 ctor_env rec_ps
                             stats motives s2)
                           (fun minors ->
                           let Pair (minors0, _) = minors in
                           bind
                             (build_recursors motives O stats rec_ps motives
                               minors0 k)
                             (fun generated -> Accept
                             (app generated (app constructors0 inds)))))))))))))))

(** val verify_member_metadata :
    declaration -> declaration -> unit0 result **)

let verify_member_metadata source actual =
  match source.decl_kind_of with
  | DInductive i ->
    bind
      (require
        (match match name_eqb source.decl_name actual.decl_name with
               | True -> same_names source.decl_params actual.decl_params
               | False -> False with
         | True -> expr_eqb source.decl_type actual.decl_type
         | False -> False)
        MalformedDeclaration)
      (fun _ ->
      match actual.decl_kind_of with
      | DInductive b -> require (inductive_data_eqb i b) MalformedDeclaration
      | _ -> Reject MalformedDeclaration)
  | DConstructor c ->
    bind
      (require
        (match match name_eqb source.decl_name actual.decl_name with
               | True -> same_names source.decl_params actual.decl_params
               | False -> False with
         | True -> expr_eqb source.decl_type actual.decl_type
         | False -> False)
        MalformedDeclaration)
      (fun _ ->
      match actual.decl_kind_of with
      | DConstructor b ->
        require (constructor_data_eqb c b) MalformedDeclaration
      | _ -> Reject MalformedDeclaration)
  | DRecursor r ->
    let sk = DRecursor r in
    (match actual.decl_kind_of with
     | DRecursor _ -> verify_rec_metadata source actual
     | x0 ->
       bind
         (require
           (match match name_eqb source.decl_name actual.decl_name with
                  | True -> same_names source.decl_params actual.decl_params
                  | False -> False with
            | True -> expr_eqb source.decl_type actual.decl_type
            | False -> False)
           MalformedDeclaration)
         (fun _ ->
         match sk with
         | DInductive a ->
           (match x0 with
            | DInductive b ->
              require (inductive_data_eqb a b) MalformedDeclaration
            | _ -> Reject MalformedDeclaration)
         | DConstructor a ->
           (match x0 with
            | DConstructor b ->
              require (constructor_data_eqb a b) MalformedDeclaration
            | _ -> Reject MalformedDeclaration)
         | _ -> Reject MalformedDeclaration))
  | _ ->
    bind
      (require
        (match match name_eqb source.decl_name actual.decl_name with
               | True -> same_names source.decl_params actual.decl_params
               | False -> False with
         | True -> expr_eqb source.decl_type actual.decl_type
         | False -> False)
        MalformedDeclaration)
      (fun _ -> Reject MalformedDeclaration)

(** val verify_members :
    declaration list -> declaration list -> unit0 result **)

let rec verify_members sources actual =
  match sources with
  | Nil -> require (Nat.eqb (length actual) O) MalformedDeclaration
  | Cons (source, sources0) ->
    (match find_decl source.decl_name actual with
     | Some derived ->
       bind (verify_member_metadata source derived) (fun _ ->
         verify_members sources0
           (filter (fun d -> negb (name_eqb d.decl_name source.decl_name))
             actual))
     | None -> Reject MalformedDeclaration)

(** val prepare_inductive :
    environment -> declaration list -> declaration list -> declaration list
    -> ((name list, nat) prod, ind_spec list) prod result **)

let prepare_inductive env types ctors recs =
  match types with
  | Nil -> Reject MalformedDeclaration
  | Cons (first, _) ->
    (match first.decl_kind_of with
     | DInductive info ->
       let sources = app types (app ctors recs) in
       let ns = ind_names sources in
       bind (require (names_unique ns) DuplicateDeclaration) (fun _ ->
         bind
           (require
             (forallb (fun n0 ->
               match find_decl n0 env with
               | Some _ -> False
               | None -> True) ns)
             DuplicateDeclaration)
           (fun _ ->
           bind
             (require
               (forallb (fun d ->
                 match d.decl_kind_of with
                 | DInductive i -> eqb0 i.ind_is_unsafe info.ind_is_unsafe
                 | DConstructor c -> eqb0 c.ctor_is_unsafe info.ind_is_unsafe
                 | DRecursor r -> eqb0 r.rec_is_unsafe info.ind_is_unsafe
                 | _ -> False) sources)
               MalformedDeclaration)
             (fun _ ->
             bind (gather_specs types ctors) (fun specs ->
               bind
                 (require
                   (match Nat.eqb (length (all_ctor_names specs))
                            (length ctors) with
                    | True -> names_unique (all_ctor_names specs)
                    | False -> False)
                   MalformedDeclaration)
                 (fun _ -> Accept (Pair ((Pair (first.decl_params,
                 info.ind_num_params)), specs)))))))
     | _ -> Reject MalformedDeclaration)

(** val admit_inductive :
    nat -> environment -> declaration list -> declaration list -> declaration
    list -> environment result **)

let admit_inductive fuel0 env types ctors recs =
  bind (prepare_inductive env types ctors recs) (fun prepared ->
    let Pair (p0, specs) = prepared in
    let Pair (ps, np) = p0 in
    bind
      (match existsb (fun d ->
               match d.decl_kind_of with
               | DInductive i -> negb (Nat.eqb i.ind_num_nested O)
               | _ -> False) types with
       | True -> Decline UnsupportedDeclaration
       | False -> Accept Tt)
      (fun _ ->
      bind (derive_inductive fuel0 env ps np specs) (fun generated ->
        bind (verify_members (app types (app ctors recs)) generated)
          (fun _ -> Accept (app generated env)))))

(** val q_name : name **)

let q_name =
  NameStr (NameAnon, (String ((Ascii (True, False, False, False, True, False,
    True, False)), (String ((Ascii (True, False, True, False, True, True,
    True, False)), (String ((Ascii (True, True, True, True, False, True,
    True, False)), (String ((Ascii (False, False, True, False, True, True,
    True, False)), EmptyString)))))))))

(** val q_mk_name : name **)

let q_mk_name =
  NameStr (q_name, (String ((Ascii (True, False, True, True, False, True,
    True, False)), (String ((Ascii (True, True, False, True, False, True,
    True, False)), EmptyString)))))

(** val q_lift_name : name **)

let q_lift_name =
  NameStr (q_name, (String ((Ascii (False, False, True, True, False, True,
    True, False)), (String ((Ascii (True, False, False, True, False, True,
    True, False)), (String ((Ascii (False, True, True, False, False, True,
    True, False)), (String ((Ascii (False, False, True, False, True, True,
    True, False)), EmptyString)))))))))

(** val q_ind_name : name **)

let q_ind_name =
  NameStr (q_name, (String ((Ascii (True, False, False, True, False, True,
    True, False)), (String ((Ascii (False, True, True, True, False, True,
    True, False)), (String ((Ascii (False, False, True, False, False, True,
    True, False)), EmptyString)))))))

(** val q_eq_name : name **)

let q_eq_name =
  NameStr (NameAnon, (String ((Ascii (True, False, True, False, False, False,
    True, False)), (String ((Ascii (True, False, False, False, True, True,
    True, False)), EmptyString)))))

(** val q_arrow : expr -> expr -> expr **)

let q_arrow a b =
  EPi (NameAnon, BDefault, a, (lift (S O) O b))

(** val q_local :
    ind_state -> string -> binder_info -> expr -> (ind_local, ind_state) prod **)

let q_local s label0 bi ty0 =
  ind_fresh s (NameStr (NameAnon, label0)) bi ty0

(** val quotient_eq_type : level -> expr **)

let quotient_eq_type u0 =
  let Pair (a, _) =
    q_local initial_ind_state (String ((Ascii (True, False, False, False,
      False, True, True, False)), (String ((Ascii (False, False, True, True,
      False, True, True, False)), (String ((Ascii (False, False, False,
      False, True, True, True, False)), (String ((Ascii (False, False, False,
      True, False, True, True, False)), (String ((Ascii (True, False, False,
      False, False, True, True, False)), EmptyString)))))))))) BImplicit
      (ESort u0)
  in
  close_pi (Cons (a, Nil))
    (q_arrow (local_expr a) (q_arrow (local_expr a) (ESort LZero)))

(** val quotient_eq_refl_type : level -> expr **)

let quotient_eq_refl_type u0 =
  let Pair (alpha, s) =
    q_local initial_ind_state (String ((Ascii (True, False, False, False,
      False, True, True, False)), (String ((Ascii (False, False, True, True,
      False, True, True, False)), (String ((Ascii (False, False, False,
      False, True, True, True, False)), (String ((Ascii (False, False, False,
      True, False, True, True, False)), (String ((Ascii (True, False, False,
      False, False, True, True, False)), EmptyString)))))))))) BImplicit
      (ESort u0)
  in
  let Pair (a, _) =
    q_local s (String ((Ascii (True, False, False, False, False, True, True,
      False)), EmptyString)) BDefault (local_expr alpha)
  in
  close_pi (Cons (alpha, (Cons (a, Nil))))
    (apply_exprs (EConst (q_eq_name, (Cons (u0, Nil)))) (Cons
      ((local_expr alpha), (Cons ((local_expr a), (Cons ((local_expr a),
      Nil)))))))

(** val quotient_check_eq : environment -> unit0 result **)

let quotient_check_eq env =
  match find_decl q_eq_name env with
  | Some d ->
    (match d.decl_kind_of with
     | DInductive info ->
       (match d.decl_params with
        | Nil -> Reject MalformedDeclaration
        | Cons (u0, l) ->
          (match l with
           | Nil ->
             bind
               (require (expr_eqb d.decl_type (quotient_eq_type (LParam u0)))
                 MalformedDeclaration)
               (fun _ ->
               match info.ind_ctors with
               | Nil -> Reject MalformedDeclaration
               | Cons (ctor, l0) ->
                 (match l0 with
                  | Nil ->
                    (match find_decl ctor env with
                     | Some c ->
                       (match c.decl_kind_of with
                        | DConstructor ci ->
                          (match c.decl_params with
                           | Nil -> Reject MalformedDeclaration
                           | Cons (v0, l1) ->
                             (match l1 with
                              | Nil ->
                                require
                                  (match name_eqb ci.ctor_induct q_eq_name with
                                   | True ->
                                     expr_eqb c.decl_type
                                       (quotient_eq_refl_type (LParam v0))
                                   | False -> False)
                                  MalformedDeclaration
                              | Cons (_, _) -> Reject MalformedDeclaration))
                        | _ -> Reject MalformedDeclaration)
                     | None -> Reject UnknownConstant)
                  | Cons (_, _) -> Reject MalformedDeclaration))
           | Cons (_, _) -> Reject MalformedDeclaration))
     | _ -> Reject MalformedDeclaration)
  | None -> Reject UnknownConstant

(** val canonical_quotient : quotient_kind -> declaration **)

let canonical_quotient kind =
  let un = NameStr (NameAnon, (String ((Ascii (True, False, True, False,
    True, True, True, False)), EmptyString)))
  in
  let vn = NameStr (NameAnon, (String ((Ascii (False, True, True, False,
    True, True, True, False)), EmptyString)))
  in
  let u0 = LParam un in
  let v0 = LParam vn in
  let Pair (alpha, s) =
    q_local initial_ind_state (String ((Ascii (True, False, False, False,
      False, True, True, False)), (String ((Ascii (False, False, True, True,
      False, True, True, False)), (String ((Ascii (False, False, False,
      False, True, True, True, False)), (String ((Ascii (False, False, False,
      True, False, True, True, False)), (String ((Ascii (True, False, False,
      False, False, True, True, False)), EmptyString)))))))))) BImplicit
      (ESort u0)
  in
  let av = local_expr alpha in
  let Pair (relation0, s0) =
    q_local s (String ((Ascii (False, True, False, False, True, True, True,
      False)), EmptyString))
      (match kind with
       | QType -> BDefault
       | QCtor -> BDefault
       | _ -> BImplicit)
      (q_arrow av (q_arrow av (ESort LZero)))
  in
  let rv = local_expr relation0 in
  let quot0 =
    apply_exprs (EConst (q_name, (Cons (u0, Nil)))) (Cons (av, (Cons (rv,
      Nil))))
  in
  let Pair (a, s1) =
    q_local s0 (String ((Ascii (True, False, False, False, False, True, True,
      False)), EmptyString)) BDefault av
  in
  let aa = local_expr a in
  let Pair (p0, ty0) =
    match kind with
    | QType ->
      Pair ((Pair (q_name, (Cons (un, Nil)))),
        (close_pi (Cons (alpha, (Cons (relation0, Nil)))) (ESort u0)))
    | QCtor ->
      Pair ((Pair (q_mk_name, (Cons (un, Nil)))),
        (close_pi (Cons (alpha, (Cons (relation0, (Cons (a, Nil)))))) quot0))
    | QLift ->
      let Pair (beta, s2) =
        q_local s1 (String ((Ascii (False, True, False, False, False, True,
          True, False)), (String ((Ascii (True, False, True, False, False,
          True, True, False)), (String ((Ascii (False, False, True, False,
          True, True, True, False)), (String ((Ascii (True, False, False,
          False, False, True, True, False)), EmptyString)))))))) BImplicit
          (ESort v0)
      in
      let bv = local_expr beta in
      let Pair (f, s3) =
        q_local s2 (String ((Ascii (False, True, True, False, False, True,
          True, False)), EmptyString)) BDefault (q_arrow av bv)
      in
      let fv = local_expr f in
      let Pair (b, _) =
        q_local s3 (String ((Ascii (False, True, False, False, False, True,
          True, False)), EmptyString)) BDefault av
      in
      let bb = local_expr b in
      let equality =
        apply_exprs (EConst (q_eq_name, (Cons (v0, Nil)))) (Cons (bv, (Cons
          ((EApp (fv, aa)), (Cons ((EApp (fv, bb)), Nil))))))
      in
      let sanity =
        close_pi (Cons (a, (Cons (b, Nil))))
          (q_arrow (apply_exprs rv (Cons (aa, (Cons (bb, Nil))))) equality)
      in
      Pair ((Pair (q_lift_name, (Cons (un, (Cons (vn, Nil)))))),
      (close_pi (Cons (alpha, (Cons (relation0, (Cons (beta, (Cons (f,
        Nil)))))))) (q_arrow sanity (q_arrow quot0 bv))))
    | QInd ->
      let Pair (beta, s2) =
        q_local s1 (String ((Ascii (False, True, False, False, False, True,
          True, False)), (String ((Ascii (True, False, True, False, False,
          True, True, False)), (String ((Ascii (False, False, True, False,
          True, True, True, False)), (String ((Ascii (True, False, False,
          False, False, True, True, False)), EmptyString)))))))) BImplicit
          (q_arrow quot0 (ESort LZero))
      in
      let bv = local_expr beta in
      let all_quot =
        close_pi (Cons (a, Nil)) (EApp (bv,
          (apply_exprs (EConst (q_mk_name, (Cons (u0, Nil)))) (Cons (av,
            (Cons (rv, (Cons (aa, Nil)))))))))
      in
      let Pair (q0, _) =
        q_local s2 (String ((Ascii (True, False, False, False, True, True,
          True, False)), EmptyString)) BImplicit quot0
      in
      Pair ((Pair (q_ind_name, (Cons (un, Nil)))),
      (close_pi (Cons (alpha, (Cons (relation0, Nil))))
        (close_pi (Cons (beta, Nil))
          (q_arrow all_quot
            (close_pi (Cons (q0, Nil)) (EApp (bv, (local_expr q0))))))))
  in
  let Pair (name0, params) = p0 in
  { decl_name = name0; decl_params = params; decl_type = ty0; decl_value =
  None; decl_kind_of = (DQuotient kind); decl_hints = HintOpaque }

(** val quotient_header_matches : quotient_kind -> declaration -> bool **)

let quotient_header_matches kind d =
  let generated = canonical_quotient kind in
  let same_kind =
    match kind with
    | QType ->
      (match d.decl_kind_of with
       | DQuotient q0 -> (match q0 with
                          | QType -> True
                          | _ -> False)
       | _ -> False)
    | QCtor ->
      (match d.decl_kind_of with
       | DQuotient q0 -> (match q0 with
                          | QCtor -> True
                          | _ -> False)
       | _ -> False)
    | QLift ->
      (match d.decl_kind_of with
       | DQuotient q0 -> (match q0 with
                          | QLift -> True
                          | _ -> False)
       | _ -> False)
    | QInd ->
      (match d.decl_kind_of with
       | DQuotient q0 -> (match q0 with
                          | QInd -> True
                          | _ -> False)
       | _ -> False)
  in
  (match match match match same_kind with
                     | True -> name_eqb d.decl_name generated.decl_name
                     | False -> False with
               | True -> names_unique d.decl_params
               | False -> False with
         | True -> eqb (length d.decl_params) (length generated.decl_params)
         | False -> False with
   | True ->
     (match d.decl_value with
      | Some _ -> False
      | None ->
        expr_eqb d.decl_type
          (subst_levels generated.decl_params
            (map (fun x0 -> LParam x0) d.decl_params) generated.decl_type))
   | False -> False)

(** val quotient_dependency : environment -> quotient_kind -> bool **)

let quotient_dependency env kind =
  match find_decl (canonical_quotient kind).decl_name env with
  | Some d -> quotient_header_matches kind d
  | None -> False

(** val quotient_dependencies : environment -> quotient_kind -> bool **)

let quotient_dependencies env = function
| QType -> True
| QInd ->
  (match quotient_dependency env QType with
   | True -> quotient_dependency env QCtor
   | False -> False)
| _ -> quotient_dependency env QType

(** val admit_quotient :
    nat -> environment -> name -> name list -> expr -> quotient_kind ->
    environment result **)

let admit_quotient fuel0 env n0 ps ty0 kind =
  bind (quotient_check_eq env) (fun _ ->
    bind (check_header fuel0 env n0 ps ty0) (fun _ ->
      let generated = canonical_quotient kind in
      bind
        (require
          (match name_eqb n0 generated.decl_name with
           | True -> eqb (length ps) (length generated.decl_params)
           | False -> False)
          MalformedDeclaration)
        (fun _ ->
        bind
          (require
            (expr_eqb
              (subst_levels ps
                (map (fun x0 -> LParam x0) generated.decl_params) ty0)
              generated.decl_type)
            MalformedDeclaration)
          (fun _ ->
          bind
            (require (quotient_dependencies env kind) MalformedDeclaration)
            (fun _ -> Accept (Cons (generated, env)))))))

type 'x compare0 =
| LT
| EQ
| GT

module type OrderedType =
 sig
  type t

  val compare : t -> t -> t compare0

  val eq_dec : t -> t -> sumbool
 end

module OrderedTypeFacts =
 functor (O:OrderedType) ->
 struct
  module TO =
   struct
    type t = O.t
   end

  module IsTO =
   struct
   end

  module OrderTac = MakeOrderTac(TO)(IsTO)

  (** val eq_dec : O.t -> O.t -> sumbool **)

  let eq_dec =
    O.eq_dec

  (** val lt_dec : O.t -> O.t -> sumbool **)

  let lt_dec x0 y =
    match O.compare x0 y with
    | LT -> Left
    | _ -> Right

  (** val eqb : O.t -> O.t -> bool **)

  let eqb x0 y =
    match eq_dec x0 y with
    | Left -> True
    | Right -> False
 end

module KeyOrderedType =
 functor (O:OrderedType) ->
 struct
  module MO = OrderedTypeFacts(O)
 end

module N_as_OT =
 struct
  type t = n

  (** val compare : n -> n -> n compare0 **)

  let compare x0 y =
    match N.compare x0 y with
    | Eq -> EQ
    | Lt -> LT
    | Gt -> GT

  (** val eq_dec : n -> n -> sumbool **)

  let eq_dec =
    N.eq_dec
 end

module PositiveMap =
 struct
  type key = positive

  type 'a tree =
  | Leaf
  | Node of 'a tree * 'a option * 'a tree

  type 'a t = 'a tree

  (** val empty : 'a1 t **)

  let empty =
    Leaf

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find i = function
  | Leaf -> None
  | Node (l, o, r) ->
    (match i with
     | XI ii -> find ii r
     | XO ii -> find ii l
     | XH -> o)

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add i v0 = function
  | Leaf ->
    (match i with
     | XI ii -> Node (Leaf, None, (add ii v0 Leaf))
     | XO ii -> Node ((add ii v0 Leaf), None, Leaf)
     | XH -> Node (Leaf, (Some v0), Leaf))
  | Node (l, o, r) ->
    (match i with
     | XI ii -> Node (l, o, (add ii v0 r))
     | XO ii -> Node ((add ii v0 l), o, r)
     | XH -> Node (l, (Some v0), r))
 end

type dag_node =
| DBVar of nat
| DFVar of name
| DMVar of name
| DSort of level
| DConst of name * level list
| DApp of positive * positive
| DLam of name * binder_info * positive * positive
| DPi of name * binder_info * positive * positive
| DLet of name * positive * positive * positive * bool
| DLit of literal
| DProj of name * nat * positive
| DMData of positive

type scope_entry = { scope_expr : expr; scope_need : n }

type scope_table = scope_entry PositiveMap.t

(** val scope_ref : scope_table -> positive -> scope_entry result **)

let scope_ref t0 id =
  match PositiveMap.find id t0 with
  | Some e -> Accept e
  | None -> Reject MalformedDeclaration

(** val scope_node : scope_table -> dag_node -> scope_entry result **)

let scope_node t0 = function
| DBVar i -> Accept { scope_expr = (EBVar i); scope_need = (N.of_nat (S i)) }
| DFVar n1 -> Accept { scope_expr = (EFVar n1); scope_need = N0 }
| DMVar n1 -> Accept { scope_expr = (EMVar n1); scope_need = N0 }
| DSort u0 -> Accept { scope_expr = (ESort u0); scope_need = N0 }
| DConst (n1, us) ->
  Accept { scope_expr = (EConst (n1, us)); scope_need = N0 }
| DApp (f, a) ->
  bind (scope_ref t0 f) (fun f0 ->
    bind (scope_ref t0 a) (fun a0 -> Accept { scope_expr = (EApp
      (f0.scope_expr, a0.scope_expr)); scope_need =
      (N.max f0.scope_need a0.scope_need) }))
| DLam (n1, bi, a, b) ->
  bind (scope_ref t0 a) (fun a0 ->
    bind (scope_ref t0 b) (fun b0 -> Accept { scope_expr = (ELam (n1, bi,
      a0.scope_expr, b0.scope_expr)); scope_need =
      (N.max a0.scope_need (N.pred b0.scope_need)) }))
| DPi (n1, bi, a, b) ->
  bind (scope_ref t0 a) (fun a0 ->
    bind (scope_ref t0 b) (fun b0 -> Accept { scope_expr = (EPi (n1, bi,
      a0.scope_expr, b0.scope_expr)); scope_need =
      (N.max a0.scope_need (N.pred b0.scope_need)) }))
| DLet (n1, a, v0, b, nd) ->
  bind (scope_ref t0 a) (fun a0 ->
    bind (scope_ref t0 v0) (fun v1 ->
      bind (scope_ref t0 b) (fun b0 -> Accept { scope_expr = (ELet (n1,
        a0.scope_expr, v1.scope_expr, b0.scope_expr, nd)); scope_need =
        (N.max (N.max a0.scope_need v1.scope_need) (N.pred b0.scope_need)) })))
| DLit l -> Accept { scope_expr = (ELit l); scope_need = N0 }
| DProj (n1, i, a) ->
  bind (scope_ref t0 a) (fun a0 -> Accept { scope_expr = (EProj (n1, i,
    a0.scope_expr)); scope_need = a0.scope_need })
| DMData a ->
  bind (scope_ref t0 a) (fun a0 -> Accept { scope_expr = (EMData
    a0.scope_expr); scope_need = a0.scope_need })

type dag_arena = { arena_scope : scope_table;
                   arena_nodes : dag_node PositiveMap.t }

(** val empty_arena : dag_arena **)

let empty_arena =
  { arena_scope = PositiveMap.empty; arena_nodes = PositiveMap.empty }

(** val arena_add :
    dag_arena -> PositiveMap.key -> dag_node -> dag_arena result **)

let arena_add arena id node0 =
  match PositiveMap.find id arena.arena_scope with
  | Some _ -> Reject DuplicateDeclaration
  | None ->
    bind (scope_node arena.arena_scope node0) (fun entry -> Accept
      { arena_scope = (PositiveMap.add id entry arena.arena_scope);
      arena_nodes = (PositiveMap.add id node0 arena.arena_nodes) })

(** val arena_build :
    dag_arena -> (PositiveMap.key, dag_node) prod list -> dag_arena result **)

let rec arena_build arena = function
| Nil -> Accept arena
| Cons (y, rows1) ->
  let Pair (id, node0) = y in
  bind (arena_add arena id node0) (fun next -> arena_build next rows1)

type context_path = (positive, positive option) prod list

(** val value_key_eqb : positive option -> positive option -> bool **)

let value_key_eqb a b =
  match a with
  | Some a0 -> (match b with
                | Some b0 -> Coq_Pos.eqb a0 b0
                | None -> False)
  | None -> (match b with
             | Some _ -> False
             | None -> True)

(** val path_eqb : context_path -> context_path -> bool **)

let rec path_eqb a b =
  match a with
  | Nil -> (match b with
            | Nil -> True
            | Cons (_, _) -> False)
  | Cons (p0, a0) ->
    let Pair (t0, v0) = p0 in
    (match b with
     | Nil -> False
     | Cons (p1, b0) ->
       let Pair (u0, w) = p1 in
       (match match Coq_Pos.eqb t0 u0 with
              | True -> value_key_eqb v0 w
              | False -> False with
        | True -> path_eqb a0 b0
        | False -> False))

type input_query = (positive, context_path) prod

(** val path_bucket : context_path -> positive **)

let path_bucket path =
  Coq_Pos.of_succ_nat (length path)

type path_entries = (context_path, expr result) prod list

type path_index = path_entries PositiveMap.t

type query_cache = path_index PositiveMap.t

(** val find_path :
    context_path -> (context_path, expr result) prod list -> expr result
    option **)

let rec find_path path = function
| Nil -> None
| Cons (p0, entries0) ->
  let Pair (key0, value) = p0 in
  (match path_eqb path key0 with
   | True -> Some value
   | False -> find_path path entries0)

(** val cache_find : input_query -> query_cache -> expr result option **)

let cache_find q0 cache =
  let Pair (id, path) = q0 in
  (match PositiveMap.find id cache with
   | Some index ->
     (match PositiveMap.find (path_bucket path) index with
      | Some entries -> find_path path entries
      | None -> None)
   | None -> None)

(** val cache_add :
    input_query -> expr result -> query_cache -> query_cache **)

let cache_add q0 value cache =
  let Pair (id, path) = q0 in
  let bucket = path_bucket path in
  let index =
    match PositiveMap.find id cache with
    | Some index -> index
    | None -> PositiveMap.empty
  in
  let entries =
    match PositiveMap.find bucket index with
    | Some xs -> xs
    | None -> Nil
  in
  PositiveMap.add id
    (PositiveMap.add bucket (Cons ((Pair (path, value)), entries)) index)
    cache

(** val path_from :
    context -> scope_table -> context_path -> context result **)

let rec path_from base arena = function
| Nil -> Accept base
| Cons (p0, path0) ->
  let Pair (ty0, value) = p0 in
  bind (path_from base arena path0) (fun g ->
    bind (scope_ref arena ty0) (fun t0 ->
      bind
        (match value with
         | Some id ->
           bind (scope_ref arena id) (fun e -> Accept (Some e.scope_expr))
         | None -> Accept None)
        (fun v0 -> Accept (push_binding g t0.scope_expr v0))))

(** val step_eval :
    methods -> nat -> environment -> name list -> context -> dag_arena ->
    bool -> input_query -> expr result **)

let step_eval rec0 fuel0 env ps base arena checking = function
| Pair (id, path) ->
  bind (path_from base arena.arena_scope path) (fun g ->
    bind (scope_ref arena.arena_scope id) (fun e ->
      infer_step rec0 fuel0 env ps checking g e.scope_expr))

type step_cache = { checked_cache : query_cache; unchecked_cache : query_cache }

(** val select_cache : bool -> step_cache -> query_cache **)

let select_cache checking cache =
  match checking with
  | True -> cache.checked_cache
  | False -> cache.unchecked_cache

(** val update_cache : bool -> query_cache -> step_cache -> step_cache **)

let update_cache checking entries cache =
  match checking with
  | True ->
    { checked_cache = entries; unchecked_cache = cache.unchecked_cache }
  | False ->
    { checked_cache = cache.checked_cache; unchecked_cache = entries }

(** val empty_step_cache : step_cache **)

let empty_step_cache =
  { checked_cache = PositiveMap.empty; unchecked_cache = PositiveMap.empty }

type 'a action = step_cache -> ('a result, step_cache) prod

(** val pure : 'a1 result -> 'a1 action **)

let pure value cache =
  Pair (value, cache)

(** val then_do : 'a1 action -> ('a1 -> 'a2 action) -> 'a2 action **)

let then_do a f cache =
  let Pair (value, next) = a cache in
  (match value with
   | Accept x0 -> f x0 next
   | Reject why -> Pair ((Reject why), next)
   | Decline why -> Pair ((Decline why), next))

(** val memo_action : bool -> input_query -> expr action -> expr action **)

let memo_action checking q0 work cache =
  match cache_find q0 (select_cache checking cache) with
  | Some value -> Pair (value, cache)
  | None ->
    let Pair (value, next) = work cache in
    Pair (value,
    (update_cache checking (cache_add q0 value (select_cache checking next))
      next))

(** val node_action :
    methods -> nat -> environment -> name list -> dag_arena -> (bool ->
    input_query -> expr action) -> bool -> context_path -> context ->
    dag_node -> expr action **)

let node_action rec0 fuel0 env ps arena call0 checking path g node0 = match node0 with
| DApp (f, a) ->
  then_do (pure (scope_ref arena.arena_scope a)) (fun ae ->
    then_do (call0 checking (Pair (f, path))) (fun ft ->
      then_do (pure (rec0.whnf_method g ft)) (fun ft0 ->
        match ft0 with
        | EPi (_, _, domain, body) ->
          then_do
            (match checking with
             | True ->
               then_do (call0 True (Pair (a, path))) (fun arg_type ->
                 then_do
                   (pure
                     (application_type_defeq rec0 g ae.scope_expr domain
                       arg_type))
                   (fun ok -> pure (require ok TypeMismatch)))
             | False -> pure (Accept Tt))
            (fun _ -> pure (Accept (instantiate body ae.scope_expr)))
        | _ -> pure (Reject ExpectedPi))))
| DLam (n0, bi, a, b) ->
  then_do (pure (scope_ref arena.arena_scope a)) (fun ae ->
    then_do
      (match checking with
       | True ->
         then_do (call0 True (Pair (a, path))) (fun dt ->
           then_do (pure (rec0.whnf_method g dt)) (fun dt0 ->
             pure
               (match dt0 with
                | EBVar _ -> Reject ExpectedSort
                | EFVar _ -> Reject ExpectedSort
                | EMVar _ -> Reject ExpectedSort
                | ESort _ -> Accept Tt
                | _ -> Reject ExpectedSort)))
       | False -> pure (Accept Tt))
      (fun _ ->
      then_do (call0 checking (Pair (b, (Cons ((Pair (a, None)), path)))))
        (fun bt0 -> pure (Accept (EPi (n0, bi, ae.scope_expr, bt0))))))
| DPi (_, _, a, b) ->
  then_do (pure (scope_ref arena.arena_scope a)) (fun ae ->
    then_do (call0 checking (Pair (a, path))) (fun dt ->
      then_do (pure (rec0.whnf_method g dt)) (fun dt0 ->
        then_do
          (pure
            (match dt0 with
             | ESort u0 -> Accept u0
             | _ -> Reject ExpectedSort))
          (fun u0 ->
          let gb = push_binding g ae.scope_expr None in
          then_do
            (call0 checking (Pair (b, (Cons ((Pair (a, None)), path)))))
            (fun bt0 ->
            then_do (pure (rec0.whnf_method gb bt0)) (fun bt1 ->
              then_do
                (pure
                  (match bt1 with
                   | ESort v0 -> Accept v0
                   | _ -> Reject ExpectedSort))
                (fun v0 -> pure (Accept (ESort (LIMax (u0, v0)))))))))))
| DLet (_, a, v0, b, _) ->
  then_do (pure (scope_ref arena.arena_scope a)) (fun ae ->
    then_do (pure (scope_ref arena.arena_scope v0)) (fun ve ->
      then_do
        (match checking with
         | True ->
           then_do (call0 True (Pair (a, path))) (fun dt ->
             then_do (pure (rec0.whnf_method g dt)) (fun dt0 ->
               then_do
                 (pure
                   (match dt0 with
                    | EBVar _ -> Reject ExpectedSort
                    | EFVar _ -> Reject ExpectedSort
                    | EMVar _ -> Reject ExpectedSort
                    | ESort _ -> Accept Tt
                    | _ -> Reject ExpectedSort))
                 (fun _ ->
                 then_do (call0 True (Pair (v0, path))) (fun vt ->
                   then_do (pure (rec0.defeq_method g vt ae.scope_expr))
                     (fun ok -> pure (require ok TypeMismatch))))))
         | False -> pure (Accept Tt))
        (fun _ ->
        then_do
          (call0 checking (Pair (b, (Cons ((Pair (a, (Some v0))), path)))))
          (fun bt0 -> pure (Accept (instantiate bt0 ve.scope_expr))))))
| DMData a -> call0 checking (Pair (a, path))
| _ ->
  then_do (pure (scope_node arena.arena_scope node0)) (fun e ->
    pure (infer_step rec0 fuel0 env ps checking g e.scope_expr))

(** val uncached_action :
    methods -> nat -> environment -> name list -> context -> dag_arena ->
    (bool -> input_query -> expr action) -> bool -> input_query -> expr action **)

let uncached_action rec0 fuel0 env ps base arena call0 checking = function
| Pair (id, path) ->
  then_do (pure (path_from base arena.arena_scope path)) (fun g ->
    then_do (pure (scope_ref arena.arena_scope id)) (fun e ->
      match PositiveMap.find id arena.arena_nodes with
      | Some node0 ->
        node_action rec0 fuel0 env ps arena call0 checking path g node0
      | None -> pure (infer_step rec0 fuel0 env ps checking g e.scope_expr)))

(** val memo_infer :
    methods -> nat -> environment -> name list -> context -> dag_arena -> nat
    -> bool -> input_query -> expr action **)

let rec memo_infer rec0 fuel0 env ps base arena budget checking q0 =
  memo_action checking q0 (fun cache ->
    match budget with
    | O -> pure (step_eval rec0 fuel0 env ps base arena checking q0) cache
    | S n0 ->
      uncached_action rec0 fuel0 env ps base arena
        (memo_infer rec0 fuel0 env ps base arena n0) checking q0 cache)

(** val run_memo_infer :
    methods -> nat -> environment -> name list -> context -> dag_arena -> nat
    -> bool -> input_query -> expr result **)

let run_memo_infer rec0 fuel0 env ps base arena budget checking q0 =
  fst
    (memo_infer rec0 fuel0 env ps base arena budget checking q0
      empty_step_cache)

(** val entry_scoped : nat -> scope_entry -> bool **)

let entry_scoped depth entry =
  N.leb entry.scope_need (N.of_nat depth)

(** val input_infer :
    nat -> nat -> environment -> name list -> dag_arena -> positive -> expr
    result **)

let input_infer budget fuel0 env ps arena root =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S n0 ->
    run_memo_infer (checker n0 env ps) n0 env ps empty_context arena budget
      True (Pair (root, Nil))

(** val input_header :
    nat -> nat -> environment -> name -> name list -> dag_arena -> positive
    -> scope_entry -> unit0 result **)

let input_header budget fuel0 env n0 ps arena root entry =
  match find_decl n0 env with
  | Some _ -> Reject DuplicateDeclaration
  | None ->
    (match negb (names_unique ps) with
     | True -> Reject DuplicateUniverse
     | False ->
       (match negb (entry_scoped O entry) with
        | True -> Reject MalformedDeclaration
        | False ->
          bind (input_infer budget fuel0 env ps arena root) (fun inferred ->
            bind (whnf fuel0 env ps empty_context inferred) (fun reduced ->
              match reduced with
              | ESort _ -> Accept Tt
              | _ -> Reject ExpectedSort))))

(** val input_check :
    nat -> nat -> environment -> name list -> dag_arena -> positive ->
    positive -> expr -> unit0 result **)

let input_check budget fuel0 env ps arena type_root body_root ty0 =
  bind (input_infer budget fuel0 env ps arena type_root) (fun type_type ->
    bind ((checker fuel0 env ps).whnf_method empty_context type_type)
      (fun type_type0 ->
      bind
        (match type_type0 with
         | EBVar _ -> Reject ExpectedSort
         | EFVar _ -> Reject ExpectedSort
         | EMVar _ -> Reject ExpectedSort
         | ESort u0 -> Accept u0
         | _ -> Reject ExpectedSort)
        (fun _ ->
        bind (input_infer budget fuel0 env ps arena body_root)
          (fun body_type ->
          bind (defeq fuel0 env ps empty_context body_type ty0) (fun ok ->
            require ok TypeMismatch)))))

(** val safe_definition_in_arena :
    reducibility_hints -> nat -> nat -> environment -> name -> name list ->
    dag_arena -> positive -> positive -> scope_entry -> scope_entry ->
    environment result **)

let safe_definition_in_arena hints budget fuel0 env n0 ps arena type_root body_root ty0 body =
  bind (input_header budget fuel0 env n0 ps arena type_root ty0) (fun _ ->
    bind (require (entry_scoped O body) MalformedDeclaration) (fun _ ->
      bind
        (input_check budget fuel0 env ps arena type_root body_root
          ty0.scope_expr)
        (fun _ ->
        bind
          (classify_primitive fuel0 env n0 ps ty0.scope_expr body.scope_expr)
          (fun primitive ->
          let kind =
            match primitive with
            | Some p0 -> DPrimitive p0
            | None -> DDefinition
          in
          Accept (Cons ({ decl_name = n0; decl_params = ps; decl_type =
          ty0.scope_expr; decl_value = (Some body.scope_expr); decl_kind_of =
          kind; decl_hints = hints }, env))))))

(** val admit_dag_definition :
    reducibility_hints -> nat -> nat -> environment -> name -> name list ->
    (PositiveMap.key, dag_node) prod list -> positive -> positive ->
    environment result **)

let admit_dag_definition hints budget fuel0 env n0 ps rows0 type_root body_root =
  bind (arena_build empty_arena rows0) (fun arena ->
    bind (scope_ref arena.arena_scope type_root) (fun ty0 ->
      bind (scope_ref arena.arena_scope body_root) (fun body ->
        safe_definition_in_arena hints budget fuel0 env n0 ps arena type_root
          body_root ty0 body)))

(** val input_proposition :
    nat -> nat -> environment -> name list -> dag_arena -> positive -> unit0
    result **)

let input_proposition budget fuel0 env ps arena root =
  bind (input_infer budget fuel0 env ps arena root) (fun inferred ->
    bind (whnf fuel0 env ps empty_context inferred) (fun reduced ->
      match reduced with
      | ESort u0 ->
        bind (level_equiv fuel0 u0 LZero) (fun is_zero ->
          match is_zero with
          | True -> Accept Tt
          | False -> Reject MalformedDeclaration)
      | _ -> Reject ExpectedSort))

(** val input_checked_constant :
    nat -> nat -> environment -> name -> name list -> dag_arena -> positive
    -> positive -> scope_entry -> scope_entry -> decl_kind -> environment
    result **)

let input_checked_constant budget fuel0 env n0 ps arena type_root body_root ty0 body kind =
  bind (input_header budget fuel0 env n0 ps arena type_root ty0) (fun _ ->
    bind
      (match entry_scoped O body with
       | True ->
         input_check budget fuel0 env ps arena type_root body_root
           ty0.scope_expr
       | False -> Reject MalformedDeclaration)
      (fun _ -> Accept (Cons ({ decl_name = n0; decl_params = ps; decl_type =
      ty0.scope_expr; decl_value = (Some body.scope_expr); decl_kind_of =
      kind; decl_hints = HintOpaque }, env))))

(** val theorem_in_arena :
    nat -> nat -> environment -> name -> name list -> dag_arena -> positive
    -> positive -> scope_entry -> scope_entry -> environment result **)

let theorem_in_arena budget fuel0 env n0 ps arena type_root body_root ty0 body =
  match name_mem n0 reserved_names with
  | True -> Reject MalformedDeclaration
  | False ->
    bind (input_header budget fuel0 env n0 ps arena type_root ty0) (fun _ ->
      bind (input_proposition budget fuel0 env ps arena type_root) (fun _ ->
        input_checked_constant budget fuel0 env n0 ps arena type_root
          body_root ty0 body DTheorem))

(** val safe_opaque_in_arena :
    nat -> nat -> environment -> name -> name list -> dag_arena -> positive
    -> positive -> scope_entry -> scope_entry -> environment result **)

let safe_opaque_in_arena budget fuel0 env n0 ps arena type_root body_root ty0 body =
  match name_mem n0 reserved_names with
  | True -> Reject MalformedDeclaration
  | False ->
    input_checked_constant budget fuel0 env n0 ps arena type_root body_root
      ty0 body DOpaque

(** val admit_dag_theorem :
    nat -> nat -> environment -> name -> name list -> (PositiveMap.key,
    dag_node) prod list -> positive -> positive -> environment result **)

let admit_dag_theorem budget fuel0 env n0 ps rows0 type_root body_root =
  bind (arena_build empty_arena rows0) (fun arena ->
    bind (scope_ref arena.arena_scope type_root) (fun ty0 ->
      bind (scope_ref arena.arena_scope body_root) (fun body ->
        theorem_in_arena budget fuel0 env n0 ps arena type_root body_root ty0
          body)))

(** val admit_dag_opaque :
    nat -> nat -> environment -> name -> name list -> (PositiveMap.key,
    dag_node) prod list -> positive -> positive -> environment result **)

let admit_dag_opaque budget fuel0 env n0 ps rows0 type_root body_root =
  bind (arena_build empty_arena rows0) (fun arena ->
    bind (scope_ref arena.arena_scope type_root) (fun ty0 ->
      bind (scope_ref arena.arena_scope body_root) (fun body ->
        safe_opaque_in_arena budget fuel0 env n0 ps arena type_root body_root
          ty0 body)))

module Raw =
 functor (X:OrderedType) ->
 struct
  module MX = OrderedTypeFacts(X)

  module PX = KeyOrderedType(X)

  type key = X.t

  type 'elt t = (X.t, 'elt) prod list

  (** val empty : 'a1 t **)

  let empty =
    Nil

  (** val is_empty : 'a1 t -> bool **)

  let is_empty = function
  | Nil -> True
  | Cons (_, _) -> False

  (** val mem : key -> 'a1 t -> bool **)

  let rec mem k = function
  | Nil -> False
  | Cons (p0, l) ->
    let Pair (k', _) = p0 in
    (match X.compare k k' with
     | LT -> False
     | EQ -> True
     | GT -> mem k l)

  (** val find : key -> 'a1 t -> 'a1 option **)

  let rec find k = function
  | Nil -> None
  | Cons (p0, s') ->
    let Pair (k', x0) = p0 in
    (match X.compare k k' with
     | LT -> None
     | EQ -> Some x0
     | GT -> find k s')

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let rec add k x0 s = match s with
  | Nil -> Cons ((Pair (k, x0)), Nil)
  | Cons (p0, l) ->
    let Pair (k', y) = p0 in
    (match X.compare k k' with
     | LT -> Cons ((Pair (k, x0)), s)
     | EQ -> Cons ((Pair (k, x0)), l)
     | GT -> Cons ((Pair (k', y)), (add k x0 l)))

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let rec remove k s = match s with
  | Nil -> Nil
  | Cons (p0, l) ->
    let Pair (k', x0) = p0 in
    (match X.compare k k' with
     | LT -> s
     | EQ -> l
     | GT -> Cons ((Pair (k', x0)), (remove k l)))

  (** val elements : 'a1 t -> 'a1 t **)

  let elements m =
    m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let rec fold f m acc =
    match m with
    | Nil -> acc
    | Cons (p0, m') -> let Pair (k, e) = p0 in fold f m' (f k e acc)

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let rec equal cmp m m' =
    match m with
    | Nil -> (match m' with
              | Nil -> True
              | Cons (_, _) -> False)
    | Cons (p0, l) ->
      let Pair (x0, e) = p0 in
      (match m' with
       | Nil -> False
       | Cons (p1, l') ->
         let Pair (x', e') = p1 in
         (match X.compare x0 x' with
          | EQ ->
            (match cmp e e' with
             | True -> equal cmp l l'
             | False -> False)
          | _ -> False))

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec map f = function
  | Nil -> Nil
  | Cons (p0, m') ->
    let Pair (k, e) = p0 in Cons ((Pair (k, (f e))), (map f m'))

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let rec mapi f = function
  | Nil -> Nil
  | Cons (p0, m') ->
    let Pair (k, e) = p0 in Cons ((Pair (k, (f k e))), (mapi f m'))

  (** val option_cons :
      key -> 'a1 option -> (key, 'a1) prod list -> (key, 'a1) prod list **)

  let option_cons k o l =
    match o with
    | Some e -> Cons ((Pair (k, e)), l)
    | None -> l

  (** val map2_l :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a3 t **)

  let rec map2_l f = function
  | Nil -> Nil
  | Cons (p0, l) ->
    let Pair (k, e) = p0 in option_cons k (f (Some e) None) (map2_l f l)

  (** val map2_r :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a2 t -> 'a3 t **)

  let rec map2_r f = function
  | Nil -> Nil
  | Cons (p0, l') ->
    let Pair (k, e') = p0 in option_cons k (f None (Some e')) (map2_r f l')

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let rec map2 f m = match m with
  | Nil -> map2_r f
  | Cons (p0, l) ->
    let Pair (k, e) = p0 in
    let rec map2_aux m' = match m' with
    | Nil -> map2_l f m
    | Cons (p1, l') ->
      let Pair (k', e') = p1 in
      (match X.compare k k' with
       | LT -> option_cons k (f (Some e) None) (map2 f l m')
       | EQ -> option_cons k (f (Some e) (Some e')) (map2 f l l')
       | GT -> option_cons k' (f None (Some e')) (map2_aux l'))
    in map2_aux

  (** val combine : 'a1 t -> 'a2 t -> ('a1 option, 'a2 option) prod t **)

  let rec combine m = match m with
  | Nil -> map (fun e' -> Pair (None, (Some e')))
  | Cons (p0, l) ->
    let Pair (k, e) = p0 in
    let rec combine_aux m' = match m' with
    | Nil -> map (fun e0 -> Pair ((Some e0), None)) m
    | Cons (p1, l') ->
      let Pair (k', e') = p1 in
      (match X.compare k k' with
       | LT -> Cons ((Pair (k, (Pair ((Some e), None)))), (combine l m'))
       | EQ -> Cons ((Pair (k, (Pair ((Some e), (Some e'))))), (combine l l'))
       | GT -> Cons ((Pair (k', (Pair (None, (Some e'))))), (combine_aux l')))
    in combine_aux

  (** val fold_right_pair :
      ('a1 -> 'a2 -> 'a3 -> 'a3) -> ('a1, 'a2) prod list -> 'a3 -> 'a3 **)

  let fold_right_pair f l i =
    fold_right (fun p0 -> f (fst p0) (snd p0)) i l

  (** val map2_alt :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> (key,
      'a3) prod list **)

  let map2_alt f m m' =
    let m0 = combine m m' in
    let m1 = map (fun p0 -> f (fst p0) (snd p0)) m0 in
    fold_right_pair option_cons m1 Nil

  (** val at_least_one :
      'a1 option -> 'a2 option -> ('a1 option, 'a2 option) prod option **)

  let at_least_one o o' =
    match o with
    | Some _ -> Some (Pair (o, o'))
    | None -> (match o' with
               | Some _ -> Some (Pair (o, o'))
               | None -> None)

  (** val at_least_one_then_f :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 option -> 'a2 option ->
      'a3 option **)

  let at_least_one_then_f f o o' =
    match o with
    | Some _ -> f o o'
    | None -> (match o' with
               | Some _ -> f o o'
               | None -> None)
 end

module type Int =
 sig
  type t

  val i2z : t -> z

  val _0 : t

  val _1 : t

  val _2 : t

  val _3 : t

  val add : t -> t -> t

  val opp : t -> t

  val sub : t -> t -> t

  val mul : t -> t -> t

  val max : t -> t -> t

  val eqb : t -> t -> bool

  val ltb : t -> t -> bool

  val leb : t -> t -> bool

  val gt_le_dec : t -> t -> sumbool

  val ge_lt_dec : t -> t -> sumbool

  val eq_dec : t -> t -> sumbool
 end

module Z_as_Int =
 struct
  type t = z

  (** val _0 : z **)

  let _0 =
    Z0

  (** val _1 : z **)

  let _1 =
    Zpos XH

  (** val _2 : z **)

  let _2 =
    Zpos (XO XH)

  (** val _3 : z **)

  let _3 =
    Zpos (XI XH)

  (** val add : z -> z -> z **)

  let add =
    Z.add

  (** val opp : z -> z **)

  let opp =
    Z.opp

  (** val sub : z -> z -> z **)

  let sub =
    Z.sub

  (** val mul : z -> z -> z **)

  let mul =
    Z.mul

  (** val max : z -> z -> z **)

  let max =
    Z.max

  (** val eqb : z -> z -> bool **)

  let eqb =
    Z.eqb

  (** val ltb : z -> z -> bool **)

  let ltb =
    Z.ltb

  (** val leb : z -> z -> bool **)

  let leb =
    Z.leb

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec =
    Z.eq_dec

  (** val gt_le_dec : z -> z -> sumbool **)

  let gt_le_dec i j =
    let b = Z.ltb j i in (match b with
                          | True -> Left
                          | False -> Right)

  (** val ge_lt_dec : z -> z -> sumbool **)

  let ge_lt_dec i j =
    let b = Z.ltb i j in (match b with
                          | True -> Right
                          | False -> Left)

  (** val i2z : t -> z **)

  let i2z n0 =
    n0
 end

module Coq_Raw =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  type key = X.t

  type 'elt tree =
  | Leaf
  | Node of 'elt tree * key * 'elt * 'elt tree * I.t

  (** val tree_rect :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rect leaf0 node0 = function
  | Leaf -> leaf0
  | Node (t1, k, e, t2, t3) ->
    node0 t1 (tree_rect leaf0 node0 t1) k e t2 (tree_rect leaf0 node0 t2) t3

  (** val tree_rec :
      'a2 -> ('a1 tree -> 'a2 -> key -> 'a1 -> 'a1 tree -> 'a2 -> I.t -> 'a2)
      -> 'a1 tree -> 'a2 **)

  let rec tree_rec leaf0 node0 = function
  | Leaf -> leaf0
  | Node (t1, k, e, t2, t3) ->
    node0 t1 (tree_rec leaf0 node0 t1) k e t2 (tree_rec leaf0 node0 t2) t3

  (** val height : 'a1 tree -> I.t **)

  let height = function
  | Leaf -> I._0
  | Node (_, _, _, _, h) -> h

  (** val cardinal : 'a1 tree -> nat **)

  let rec cardinal = function
  | Leaf -> O
  | Node (l, _, _, r, _) -> S (add (cardinal l) (cardinal r))

  (** val empty : 'a1 tree **)

  let empty =
    Leaf

  (** val is_empty : 'a1 tree -> bool **)

  let is_empty = function
  | Leaf -> True
  | Node (_, _, _, _, _) -> False

  (** val mem : X.t -> 'a1 tree -> bool **)

  let rec mem x0 = function
  | Leaf -> False
  | Node (l, y, _, r, _) ->
    (match X.compare x0 y with
     | LT -> mem x0 l
     | EQ -> True
     | GT -> mem x0 r)

  (** val find : X.t -> 'a1 tree -> 'a1 option **)

  let rec find x0 = function
  | Leaf -> None
  | Node (l, y, d, r, _) ->
    (match X.compare x0 y with
     | LT -> find x0 l
     | EQ -> Some d
     | GT -> find x0 r)

  (** val create : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let create l x0 e r =
    Node (l, x0, e, r, (I.add (I.max (height l) (height r)) I._1))

  (** val assert_false : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let assert_false =
    create

  (** val bal : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let bal l x0 d r =
    let hl = height l in
    let hr = height r in
    (match I.gt_le_dec hl (I.add hr I._2) with
     | Left ->
       (match l with
        | Leaf -> assert_false l x0 d r
        | Node (ll, lx, ld, lr, _) ->
          (match I.ge_lt_dec (height ll) (height lr) with
           | Left -> create ll lx ld (create lr x0 d r)
           | Right ->
             (match lr with
              | Leaf -> assert_false l x0 d r
              | Node (lrl, lrx, lrd, lrr, _) ->
                create (create ll lx ld lrl) lrx lrd (create lrr x0 d r))))
     | Right ->
       (match I.gt_le_dec hr (I.add hl I._2) with
        | Left ->
          (match r with
           | Leaf -> assert_false l x0 d r
           | Node (rl, rx, rd, rr, _) ->
             (match I.ge_lt_dec (height rr) (height rl) with
              | Left -> create (create l x0 d rl) rx rd rr
              | Right ->
                (match rl with
                 | Leaf -> assert_false l x0 d r
                 | Node (rll, rlx, rld, rlr, _) ->
                   create (create l x0 d rll) rlx rld (create rlr rx rd rr))))
        | Right -> create l x0 d r))

  (** val add : key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec add x0 d = function
  | Leaf -> Node (Leaf, x0, d, Leaf, I._1)
  | Node (l, y, d', r, h) ->
    (match X.compare x0 y with
     | LT -> bal (add x0 d l) y d' r
     | EQ -> Node (l, y, d, r, h)
     | GT -> bal l y d' (add x0 d r))

  (** val remove_min :
      'a1 tree -> key -> 'a1 -> 'a1 tree -> ('a1 tree, (key, 'a1) prod) prod **)

  let rec remove_min l x0 d r =
    match l with
    | Leaf -> Pair (r, (Pair (x0, d)))
    | Node (ll, lx, ld, lr, _) ->
      let Pair (l', m) = remove_min ll lx ld lr in Pair ((bal l' x0 d r), m)

  (** val merge : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let merge s1 s2 =
    match s1 with
    | Leaf -> s2
    | Node (_, _, _, _, _) ->
      (match s2 with
       | Leaf -> s1
       | Node (l2, x2, d2, r2, _) ->
         let Pair (s2', p0) = remove_min l2 x2 d2 r2 in
         let Pair (x0, d) = p0 in bal s1 x0 d s2')

  (** val remove : X.t -> 'a1 tree -> 'a1 tree **)

  let rec remove x0 = function
  | Leaf -> Leaf
  | Node (l, y, d, r, _) ->
    (match X.compare x0 y with
     | LT -> bal (remove x0 l) y d r
     | EQ -> merge l r
     | GT -> bal l y d (remove x0 r))

  (** val join : 'a1 tree -> key -> 'a1 -> 'a1 tree -> 'a1 tree **)

  let rec join l = match l with
  | Leaf -> add
  | Node (ll, lx, ld, lr, lh) ->
    (fun x0 d ->
      let rec join_aux r = match r with
      | Leaf -> add x0 d l
      | Node (rl, rx, rd, rr, rh) ->
        (match I.gt_le_dec lh (I.add rh I._2) with
         | Left -> bal ll lx ld (join lr x0 d r)
         | Right ->
           (match I.gt_le_dec rh (I.add lh I._2) with
            | Left -> bal (join_aux rl) rx rd rr
            | Right -> create l x0 d r))
      in join_aux)

  type 'elt triple = { t_left : 'elt tree; t_opt : 'elt option;
                       t_right : 'elt tree }

  (** val t_left : 'a1 triple -> 'a1 tree **)

  let t_left t0 =
    t0.t_left

  (** val t_opt : 'a1 triple -> 'a1 option **)

  let t_opt t0 =
    t0.t_opt

  (** val t_right : 'a1 triple -> 'a1 tree **)

  let t_right t0 =
    t0.t_right

  (** val split : X.t -> 'a1 tree -> 'a1 triple **)

  let rec split x0 = function
  | Leaf -> { t_left = Leaf; t_opt = None; t_right = Leaf }
  | Node (l, y, d, r, _) ->
    (match X.compare x0 y with
     | LT ->
       let { t_left = ll; t_opt = o; t_right = rl } = split x0 l in
       { t_left = ll; t_opt = o; t_right = (join rl y d r) }
     | EQ -> { t_left = l; t_opt = (Some d); t_right = r }
     | GT ->
       let { t_left = rl; t_opt = o; t_right = rr } = split x0 r in
       { t_left = (join l y d rl); t_opt = o; t_right = rr })

  (** val concat : 'a1 tree -> 'a1 tree -> 'a1 tree **)

  let concat m1 m2 =
    match m1 with
    | Leaf -> m2
    | Node (_, _, _, _, _) ->
      (match m2 with
       | Leaf -> m1
       | Node (l2, x2, d2, r2, _) ->
         let Pair (m2', xd) = remove_min l2 x2 d2 r2 in
         join m1 (fst xd) (snd xd) m2')

  (** val elements_aux :
      (key, 'a1) prod list -> 'a1 tree -> (key, 'a1) prod list **)

  let rec elements_aux acc = function
  | Leaf -> acc
  | Node (l, x0, d, r, _) ->
    elements_aux (Cons ((Pair (x0, d)), (elements_aux acc r))) l

  (** val elements : 'a1 tree -> (key, 'a1) prod list **)

  let elements m =
    elements_aux Nil m

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

  let rec fold f m a =
    match m with
    | Leaf -> a
    | Node (l, x0, d, r, _) -> fold f r (f x0 d (fold f l a))

  type 'elt enumeration =
  | End
  | More of key * 'elt * 'elt tree * 'elt enumeration

  (** val enumeration_rect :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rect end0 more = function
  | End -> end0
  | More (k, e0, t0, e1) -> more k e0 t0 e1 (enumeration_rect end0 more e1)

  (** val enumeration_rec :
      'a2 -> (key -> 'a1 -> 'a1 tree -> 'a1 enumeration -> 'a2 -> 'a2) -> 'a1
      enumeration -> 'a2 **)

  let rec enumeration_rec end0 more = function
  | End -> end0
  | More (k, e0, t0, e1) -> more k e0 t0 e1 (enumeration_rec end0 more e1)

  (** val cons : 'a1 tree -> 'a1 enumeration -> 'a1 enumeration **)

  let rec cons m e =
    match m with
    | Leaf -> e
    | Node (l, x0, d, r, _) -> cons l (More (x0, d, r, e))

  (** val equal_more :
      ('a1 -> 'a1 -> bool) -> X.t -> 'a1 -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let equal_more cmp x1 d1 cont = function
  | End -> False
  | More (x2, d2, r2, e3) ->
    (match X.compare x1 x2 with
     | EQ -> (match cmp d1 d2 with
              | True -> cont (cons r2 e3)
              | False -> False)
     | _ -> False)

  (** val equal_cont :
      ('a1 -> 'a1 -> bool) -> 'a1 tree -> ('a1 enumeration -> bool) -> 'a1
      enumeration -> bool **)

  let rec equal_cont cmp m1 cont e2 =
    match m1 with
    | Leaf -> cont e2
    | Node (l1, x1, d1, r1, _) ->
      equal_cont cmp l1 (equal_more cmp x1 d1 (equal_cont cmp r1 cont)) e2

  (** val equal_end : 'a1 enumeration -> bool **)

  let equal_end = function
  | End -> True
  | More (_, _, _, _) -> False

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 tree -> 'a1 tree -> bool **)

  let equal cmp m1 m2 =
    equal_cont cmp m1 equal_end (cons m2 End)

  (** val map : ('a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec map f = function
  | Leaf -> Leaf
  | Node (l, x0, d, r, h) -> Node ((map f l), x0, (f d), (map f r), h)

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 tree -> 'a2 tree **)

  let rec mapi f = function
  | Leaf -> Leaf
  | Node (l, x0, d, r, h) -> Node ((mapi f l), x0, (f x0 d), (mapi f r), h)

  (** val map_option : (key -> 'a1 -> 'a2 option) -> 'a1 tree -> 'a2 tree **)

  let rec map_option f = function
  | Leaf -> Leaf
  | Node (l, x0, d, r, _) ->
    (match f x0 d with
     | Some d' -> join (map_option f l) x0 d' (map_option f r)
     | None -> concat (map_option f l) (map_option f r))

  (** val map2_opt :
      (key -> 'a1 -> 'a2 option -> 'a3 option) -> ('a1 tree -> 'a3 tree) ->
      ('a2 tree -> 'a3 tree) -> 'a1 tree -> 'a2 tree -> 'a3 tree **)

  let rec map2_opt f mapl mapr m1 m2 =
    match m1 with
    | Leaf -> mapr m2
    | Node (l1, x1, d1, r1, _) ->
      (match m2 with
       | Leaf -> mapl m1
       | Node (_, _, _, _, _) ->
         let { t_left = l2'; t_opt = o2; t_right = r2' } = split x1 m2 in
         (match f x1 d1 o2 with
          | Some e ->
            join (map2_opt f mapl mapr l1 l2') x1 e
              (map2_opt f mapl mapr r1 r2')
          | None ->
            concat (map2_opt f mapl mapr l1 l2') (map2_opt f mapl mapr r1 r2')))

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 tree -> 'a2 tree -> 'a3
      tree **)

  let map2 f =
    map2_opt (fun _ d o -> f (Some d) o)
      (map_option (fun _ d -> f (Some d) None))
      (map_option (fun _ d' -> f None (Some d')))

  module Proofs =
   struct
    module MX = OrderedTypeFacts(X)

    module PX = KeyOrderedType(X)

    module L = Raw(X)

    (** val fold' : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 tree -> 'a2 -> 'a2 **)

    let fold' f s =
      L.fold f (elements s)

    (** val flatten_e : 'a1 enumeration -> (key, 'a1) prod list **)

    let rec flatten_e = function
    | End -> Nil
    | More (x0, e0, t0, r) ->
      Cons ((Pair (x0, e0)), (app (elements t0) (flatten_e r)))
   end
 end

module IntMake =
 functor (I:Int) ->
 functor (X:OrderedType) ->
 struct
  module E = X

  module Raw = Coq_Raw(I)(X)

  type 'elt bst =
    'elt Raw.tree
    (* singleton inductive, whose constructor was Bst *)

  (** val this : 'a1 bst -> 'a1 Raw.tree **)

  let this b =
    b

  type 'elt t = 'elt bst

  type key = E.t

  (** val empty : 'a1 t **)

  let empty =
    Raw.empty

  (** val is_empty : 'a1 t -> bool **)

  let is_empty =
    Raw.is_empty

  (** val add : key -> 'a1 -> 'a1 t -> 'a1 t **)

  let add =
    Raw.add

  (** val remove : key -> 'a1 t -> 'a1 t **)

  let remove =
    Raw.remove

  (** val mem : key -> 'a1 t -> bool **)

  let mem =
    Raw.mem

  (** val find : key -> 'a1 t -> 'a1 option **)

  let find =
    Raw.find

  (** val map : ('a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let map =
    Raw.map

  (** val mapi : (key -> 'a1 -> 'a2) -> 'a1 t -> 'a2 t **)

  let mapi =
    Raw.mapi

  (** val map2 :
      ('a1 option -> 'a2 option -> 'a3 option) -> 'a1 t -> 'a2 t -> 'a3 t **)

  let map2 =
    Raw.map2

  (** val elements : 'a1 t -> (key, 'a1) prod list **)

  let elements =
    Raw.elements

  (** val cardinal : 'a1 t -> nat **)

  let cardinal =
    Raw.cardinal

  (** val fold : (key -> 'a1 -> 'a2 -> 'a2) -> 'a1 t -> 'a2 -> 'a2 **)

  let fold =
    Raw.fold

  (** val equal : ('a1 -> 'a1 -> bool) -> 'a1 t -> 'a1 t -> bool **)

  let equal =
    Raw.equal
 end

module Make =
 functor (X:OrderedType) ->
 IntMake(Z_as_Int)(X)

module DeclarationBuckets = Make(N_as_OT)

type declaration_index = declaration list DeclarationBuckets.t

(** val declaration_bucket : n -> declaration_index -> environment **)

let declaration_bucket key0 index =
  match DeclarationBuckets.find key0 index with
  | Some bucket -> bucket
  | None -> Nil

(** val empty_declaration_index : declaration_index **)

let empty_declaration_index =
  DeclarationBuckets.empty

(** val index_declaration :
    (name -> n) -> declaration -> declaration_index -> declaration_index **)

let index_declaration hash d index =
  let key0 = hash d.decl_name in
  DeclarationBuckets.add key0 (Cons (d, (declaration_bucket key0 index)))
    index

(** val index_environment :
    (name -> n) -> environment -> declaration_index **)

let rec index_environment hash = function
| Nil -> empty_declaration_index
| Cons (d, rest) -> index_declaration hash d (index_environment hash rest)

(** val indexed_find_decl :
    (name -> n) -> name -> declaration_index -> declaration option **)

let indexed_find_decl hash n0 index =
  find_decl n0 (declaration_bucket (hash n0) index)

type declaration_lookup = name -> declaration option

(** val prepare_lookup : (name -> n) -> environment -> declaration_lookup **)

let prepare_lookup hash env =
  let index = index_environment hash env in
  (fun n0 -> indexed_find_decl hash n0 index)

(** val lookup_get_constant :
    declaration_lookup -> name list -> name -> level list -> declaration
    result **)

let lookup_get_constant lookup ps n0 us =
  match lookup n0 with
  | Some d ->
    (match d.decl_kind_of with
     | DUnsupported -> Decline UnsupportedDeclaration
     | DUnsafe _ -> Reject MalformedDeclaration
     | DPartial -> Reject MalformedDeclaration
     | _ ->
       bind (require (eqb (length d.decl_params) (length us)) UniverseArity)
         (fun _ -> bind (check_levels ps us) (fun _ -> Accept d)))
  | None -> Reject UnknownConstant

(** val lookup_ctor_shape :
    declaration_lookup -> name -> name -> nat -> nat -> expr -> bool **)

let lookup_ctor_shape lookup n0 parent index fields ty0 =
  match lookup n0 with
  | Some d ->
    (match d.decl_kind_of with
     | DConstructor c ->
       (match match match match match match name_eqb c.ctor_induct parent with
                                      | True -> eqb c.ctor_index index
                                      | False -> False with
                                | True -> eqb c.ctor_num_params O
                                | False -> False with
                          | True -> eqb c.ctor_num_fields fields
                          | False -> False with
                    | True -> negb c.ctor_is_unsafe
                    | False -> False with
              | True -> eqb (length d.decl_params) O
              | False -> False with
        | True -> expr_eqb d.decl_type ty0
        | False -> False)
     | _ -> False)
  | None -> False

(** val lookup_nat_ready : declaration_lookup -> bool **)

let lookup_nat_ready lookup =
  match lookup core_nat_name with
  | Some d ->
    (match d.decl_kind_of with
     | DInductive i ->
       (match match match match match match match eqb (length d.decl_params) O with
                                            | True ->
                                              expr_eqb d.decl_type (ESort
                                                (LSucc LZero))
                                            | False -> False with
                                      | True -> eqb i.ind_num_params O
                                      | False -> False with
                                | True -> eqb i.ind_num_indices O
                                | False -> False with
                          | True -> negb i.ind_is_unsafe
                          | False -> False with
                    | True ->
                      list_eqb name_eqb i.ind_ctors (Cons (core_zero_name,
                        (Cons (core_succ_name, Nil))))
                    | False -> False with
              | True ->
                lookup_ctor_shape lookup core_zero_name core_nat_name O O
                  core_nat
              | False -> False with
        | True ->
          lookup_ctor_shape lookup core_succ_name core_nat_name (S O) (S O)
            (EPi (NameAnon, BDefault, core_nat, core_nat))
        | False -> False)
     | _ -> False)
  | None -> False

module Accessor =
 struct
  (** val core_name : string -> name **)

  let core_name s =
    NameStr (NameAnon, s)

  (** val core_nat_name : name **)

  let core_nat_name =
    core_name (String ((Ascii (False, True, True, True, False, False, True,
      False)), (String ((Ascii (True, False, False, False, False, True, True,
      False)), (String ((Ascii (False, False, True, False, True, True, True,
      False)), EmptyString))))))

  (** val core_zero_name : name **)

  let core_zero_name =
    NameStr (core_nat_name, (String ((Ascii (False, True, False, True, True,
      True, True, False)), (String ((Ascii (True, False, True, False, False,
      True, True, False)), (String ((Ascii (False, True, False, False, True,
      True, True, False)), (String ((Ascii (True, True, True, True, False,
      True, True, False)), EmptyString)))))))))

  (** val core_succ_name : name **)

  let core_succ_name =
    NameStr (core_nat_name, (String ((Ascii (True, True, False, False, True,
      True, True, False)), (String ((Ascii (True, False, True, False, True,
      True, True, False)), (String ((Ascii (True, True, False, False, False,
      True, True, False)), (String ((Ascii (True, True, False, False, False,
      True, True, False)), EmptyString)))))))))

  (** val core_bool_name : name **)

  let core_bool_name =
    core_name (String ((Ascii (False, True, False, False, False, False, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, False, True, True, False, True, True,
      False)), EmptyString))))))))

  (** val core_false_name : name **)

  let core_false_name =
    NameStr (core_bool_name, (String ((Ascii (False, True, True, False,
      False, True, True, False)), (String ((Ascii (True, False, False, False,
      False, True, True, False)), (String ((Ascii (False, False, True, True,
      False, True, True, False)), (String ((Ascii (True, True, False, False,
      True, True, True, False)), (String ((Ascii (True, False, True, False,
      False, True, True, False)), EmptyString)))))))))))

  (** val core_true_name : name **)

  let core_true_name =
    NameStr (core_bool_name, (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (False, True, False, False,
      True, True, True, False)), (String ((Ascii (True, False, True, False,
      True, True, True, False)), (String ((Ascii (True, False, True, False,
      False, True, True, False)), EmptyString)))))))))

  (** val core_char_name : name **)

  let core_char_name =
    core_name (String ((Ascii (True, True, False, False, False, False, True,
      False)), (String ((Ascii (False, False, False, True, False, True, True,
      False)), (String ((Ascii (True, False, False, False, False, True, True,
      False)), (String ((Ascii (False, True, False, False, True, True, True,
      False)), EmptyString))))))))

  (** val core_char_of_nat : name **)

  let core_char_of_nat =
    NameStr (core_char_name, (String ((Ascii (True, True, True, True, False,
      True, True, False)), (String ((Ascii (False, True, True, False, False,
      True, True, False)), (String ((Ascii (False, True, True, True, False,
      False, True, False)), (String ((Ascii (True, False, False, False,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), EmptyString)))))))))))

  (** val core_string_name : name **)

  let core_string_name =
    core_name (String ((Ascii (True, True, False, False, True, False, True,
      False)), (String ((Ascii (False, False, True, False, True, True, True,
      False)), (String ((Ascii (False, True, False, False, True, True, True,
      False)), (String ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (False, True, True, True, False, True, True,
      False)), (String ((Ascii (True, True, True, False, False, True, True,
      False)), EmptyString))))))))))))

  (** val core_string_of_list : name **)

  let core_string_of_list =
    NameStr (core_string_name, (String ((Ascii (True, True, True, True,
      False, True, True, False)), (String ((Ascii (False, True, True, False,
      False, True, True, False)), (String ((Ascii (False, False, True, True,
      False, False, True, False)), (String ((Ascii (True, False, False, True,
      False, True, True, False)), (String ((Ascii (True, True, False, False,
      True, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), EmptyString)))))))))))))

  (** val core_list_name : name **)

  let core_list_name =
    core_name (String ((Ascii (False, False, True, True, False, False, True,
      False)), (String ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (True, True, False, False, True, True, True,
      False)), (String ((Ascii (False, False, True, False, True, True, True,
      False)), EmptyString))))))))

  (** val core_nat : expr **)

  let core_nat =
    EConst (core_nat_name, Nil)

  (** val core_spine : expr -> expr list -> (expr, expr list) prod **)

  let rec core_spine e args =
    match e with
    | EApp (f, a) -> core_spine f (Cons (a, args))
    | _ -> Pair (e, args)

  (** val core_apps : expr -> expr list -> expr **)

  let core_apps e args =
    fold_left (fun x0 x1 -> EApp (x0, x1)) args e

  (** val core_occurs : nat -> expr -> bool **)

  let rec core_occurs index = function
  | EBVar i -> Nat.eqb i index
  | EApp (a, b) ->
    (match core_occurs index a with
     | True -> True
     | False -> core_occurs index b)
  | ELam (_, _, a, b) ->
    (match core_occurs index a with
     | True -> True
     | False -> core_occurs (S index) b)
  | EPi (_, _, a, b) ->
    (match core_occurs index a with
     | True -> True
     | False -> core_occurs (S index) b)
  | ELet (_, a, v0, b, _) ->
    (match match core_occurs index a with
           | True -> True
           | False -> core_occurs index v0 with
     | True -> True
     | False -> core_occurs (S index) b)
  | EProj (_, _, a) -> core_occurs index a
  | EMData a -> core_occurs index a
  | _ -> False

  (** val core_level_positive : level -> bool **)

  let rec core_level_positive = function
  | LSucc _ -> True
  | LMax (a, b) ->
    (match core_level_positive a with
     | True -> True
     | False -> core_level_positive b)
  | LIMax (_, b) -> core_level_positive b
  | _ -> False

  (** val core_inductive :
      (name -> environment -> declaration option) -> environment -> name ->
      inductive_data option **)

  let core_inductive resolve env n0 =
    match resolve n0 env with
    | Some d -> (match d.decl_kind_of with
                 | DInductive i -> Some i
                 | _ -> None)
    | None -> None

  (** val core_constructor :
      (name -> environment -> declaration option) -> environment -> name ->
      constructor_data option **)

  let core_constructor resolve env n0 =
    match resolve n0 env with
    | Some d ->
      (match d.decl_kind_of with
       | DConstructor i -> Some i
       | _ -> None)
    | None -> None

  (** val core_structure :
      (name -> environment -> declaration option) -> environment -> name ->
      bool **)

  let core_structure resolve env n0 =
    match core_inductive resolve env n0 with
    | Some i ->
      (match match negb i.ind_is_rec with
             | True -> Nat.eqb i.ind_num_indices O
             | False -> False with
       | True -> Nat.eqb (length i.ind_ctors) (S O)
       | False -> False)
    | None -> False

  (** val core_ctor_shape :
      (name -> environment -> declaration option) -> environment -> name ->
      name -> nat -> nat -> expr -> bool **)

  let core_ctor_shape resolve env n0 parent index fields ty0 =
    match resolve n0 env with
    | Some d ->
      (match d.decl_kind_of with
       | DConstructor c ->
         (match match match match match match name_eqb c.ctor_induct parent with
                                        | True -> Nat.eqb c.ctor_index index
                                        | False -> False with
                                  | True -> Nat.eqb c.ctor_num_params O
                                  | False -> False with
                            | True -> Nat.eqb c.ctor_num_fields fields
                            | False -> False with
                      | True -> negb c.ctor_is_unsafe
                      | False -> False with
                | True -> Nat.eqb (length d.decl_params) O
                | False -> False with
          | True -> expr_eqb d.decl_type ty0
          | False -> False)
       | _ -> False)
    | None -> False

  (** val core_nat_ready :
      (name -> environment -> declaration option) -> environment -> bool **)

  let core_nat_ready resolve env =
    match resolve core_nat_name env with
    | Some d ->
      (match d.decl_kind_of with
       | DInductive i ->
         (match match match match match match match Nat.eqb
                                                      (length d.decl_params) O with
                                              | True ->
                                                expr_eqb d.decl_type (ESort
                                                  (LSucc LZero))
                                              | False -> False with
                                        | True -> Nat.eqb i.ind_num_params O
                                        | False -> False with
                                  | True -> Nat.eqb i.ind_num_indices O
                                  | False -> False with
                            | True -> negb i.ind_is_unsafe
                            | False -> False with
                      | True ->
                        list_eqb name_eqb i.ind_ctors (Cons (core_zero_name,
                          (Cons (core_succ_name, Nil))))
                      | False -> False with
                | True ->
                  core_ctor_shape resolve env core_zero_name core_nat_name O
                    O core_nat
                | False -> False with
          | True ->
            core_ctor_shape resolve env core_succ_name core_nat_name (S O) (S
              O) (EPi (NameAnon, BDefault, core_nat, core_nat))
          | False -> False)
       | _ -> False)
    | None -> False

  (** val core_bool_ready :
      (name -> environment -> declaration option) -> environment -> bool **)

  let core_bool_ready resolve env =
    match resolve core_bool_name env with
    | Some d ->
      (match d.decl_kind_of with
       | DInductive i ->
         (match match match match match match match Nat.eqb
                                                      (length d.decl_params) O with
                                              | True ->
                                                expr_eqb d.decl_type (ESort
                                                  (LSucc LZero))
                                              | False -> False with
                                        | True -> Nat.eqb i.ind_num_params O
                                        | False -> False with
                                  | True -> Nat.eqb i.ind_num_indices O
                                  | False -> False with
                            | True -> negb i.ind_is_unsafe
                            | False -> False with
                      | True ->
                        list_eqb name_eqb i.ind_ctors (Cons (core_false_name,
                          (Cons (core_true_name, Nil))))
                      | False -> False with
                | True ->
                  core_ctor_shape resolve env core_false_name core_bool_name
                    O O (EConst (core_bool_name, Nil))
                | False -> False with
          | True ->
            core_ctor_shape resolve env core_true_name core_bool_name (S O) O
              (EConst (core_bool_name, Nil))
          | False -> False)
       | _ -> False)
    | None -> False

  (** val core_string_ready :
      (name -> environment -> declaration option) -> environment -> bool **)

  let core_string_ready resolve env =
    match resolve core_char_of_nat env with
    | Some c ->
      (match resolve core_string_of_list env with
       | Some s ->
         (match c.decl_kind_of with
          | DPrimitive p0 ->
            (match p0 with
             | PCharOfNat ->
               (match s.decl_kind_of with
                | DPrimitive p1 ->
                  (match p1 with
                   | PStringOfList -> core_nat_ready resolve env
                   | _ -> False)
                | _ -> False)
             | _ -> False)
          | _ -> False)
       | None -> False)
    | None -> False

  (** val core_supported :
      (name -> environment -> declaration option) -> environment -> expr ->
      bool **)

  let rec core_supported resolve env = function
  | EApp (a, b) ->
    (match core_supported resolve env a with
     | True -> core_supported resolve env b
     | False -> False)
  | ELam (_, _, a, b) ->
    (match core_supported resolve env a with
     | True -> core_supported resolve env b
     | False -> False)
  | EPi (_, _, a, b) ->
    (match core_supported resolve env a with
     | True -> core_supported resolve env b
     | False -> False)
  | ELet (_, a, v0, b, _) ->
    (match match core_supported resolve env a with
           | True -> core_supported resolve env v0
           | False -> False with
     | True -> core_supported resolve env b
     | False -> False)
  | ELit l ->
    (match l with
     | LitNat _ -> core_nat_ready resolve env
     | LitString _ -> core_string_ready resolve env)
  | EProj (n0, _, a) ->
    (match core_inductive resolve env n0 with
     | Some _ -> core_supported resolve env a
     | None -> False)
  | EMData a -> core_supported resolve env a
  | _ -> True

  (** val check_level : name list -> level -> unit0 result **)

  let check_level ps u0 =
    match level_has_meta u0 with
    | True -> Reject MetaVariable
    | False -> require (level_wf ps u0) UnknownUniverse

  (** val check_levels : name list -> level list -> unit0 result **)

  let rec check_levels ps = function
  | Nil -> Accept Tt
  | Cons (u0, us0) -> bind (check_level ps u0) (fun _ -> check_levels ps us0)

  (** val get_constant :
      (name -> environment -> declaration option) -> environment -> name list
      -> name -> level list -> declaration result **)

  let get_constant resolve env ps n0 us =
    match resolve n0 env with
    | Some d ->
      (match d.decl_kind_of with
       | DUnsupported -> Decline UnsupportedDeclaration
       | DUnsafe _ -> Reject MalformedDeclaration
       | DPartial -> Reject MalformedDeclaration
       | _ ->
         bind
           (require (Nat.eqb (length d.decl_params) (length us))
             UniverseArity)
           (fun _ -> bind (check_levels ps us) (fun _ -> Accept d)))
    | None -> Reject UnknownConstant

  (** val inference_only : methods -> methods **)

  let inference_only rec0 =
    { infer_method = rec0.infer_type_method; infer_type_method =
      rec0.infer_type_method; whnf_method = rec0.whnf_method;
      whnf_core_method = rec0.whnf_core_method; defeq_method =
      rec0.defeq_method; method_mode = rec0.method_mode; eager_defeq_method =
      rec0.eager_defeq_method }

  (** val sort_of : methods -> context -> expr -> level result **)

  let sort_of rec0 g e =
    bind (rec0.infer_method g e) (fun t0 ->
      bind (rec0.whnf_method g t0) (fun t1 ->
        match t1 with
        | ESort u0 -> Accept u0
        | _ -> Reject ExpectedSort))

  (** val core_apply_type :
      methods -> context -> expr -> expr list -> expr result **)

  let rec core_apply_type rec0 g ty0 = function
  | Nil -> Accept ty0
  | Cons (a, args0) ->
    bind (rec0.whnf_method g ty0) (fun ty1 ->
      match ty1 with
      | EPi (_, _, _, body) ->
        core_apply_type rec0 g (instantiate body a) args0
      | _ -> Reject ExpectedPi)

  (** val core_projection_field :
      methods -> nat -> context -> name -> expr -> bool -> nat -> nat -> expr
      -> expr result **)

  let rec core_projection_field rec0 fuel0 g owner value maybe_prop skip index ty0 =
    bind (rec0.whnf_method g ty0) (fun reduced ->
      match reduced with
      | EPi (_, _, domain, body) ->
        let verify_prop = fun _ ->
          bind (sort_of rec0 g domain) (fun u0 ->
            bind (level_equiv fuel0 u0 LZero) (fun ok ->
              require ok TypeMismatch))
        in
        (match skip with
         | O ->
           bind
             (match maybe_prop with
              | True -> verify_prop Tt
              | False -> Accept Tt)
             (fun _ -> Accept domain)
         | S skip0 ->
           bind
             (match match maybe_prop with
                    | True -> core_occurs O body
                    | False -> False with
              | True -> verify_prop Tt
              | False -> Accept Tt)
             (fun _ ->
             core_projection_field rec0 fuel0 g owner value maybe_prop skip0
               (S index) (instantiate body (EProj (owner, index, value)))))
      | _ -> Reject ExpectedPi)

  (** val core_infer_projection :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> name -> nat -> expr -> expr result **)

  let core_infer_projection resolve rec0 fuel0 env g owner index value =
    bind (rec0.infer_method g value) (fun st ->
      bind (rec0.whnf_method g st) (fun st0 ->
        let Pair (head, args) = core_spine st0 Nil in
        (match head with
         | EConst (n0, us) ->
           (match core_inductive resolve env owner with
            | Some info ->
              bind
                (require
                  (match name_eqb n0 owner with
                   | True ->
                     Nat.eqb (length args)
                       (add info.ind_num_params info.ind_num_indices)
                   | False -> False)
                  TypeMismatch)
                (fun _ ->
                match info.ind_ctors with
                | Nil -> Reject TypeMismatch
                | Cons (ctor, l) ->
                  (match l with
                   | Nil ->
                     (match resolve ctor env with
                      | Some d ->
                        (match d.decl_kind_of with
                         | DConstructor c ->
                           bind
                             (require (Nat.ltb index c.ctor_num_fields)
                               TypeMismatch)
                             (fun _ ->
                             bind
                               (core_apply_type rec0 g
                                 (subst_levels d.decl_params us d.decl_type)
                                 (firstn info.ind_num_params args))
                               (fun ty0 ->
                               bind (sort_of rec0 g st0) (fun u0 ->
                                 core_projection_field rec0 fuel0 g owner
                                   value (negb (core_level_positive u0))
                                   index O ty0)))
                         | _ -> Reject MalformedDeclaration)
                      | None -> Reject UnknownConstant)
                   | Cons (_, _) -> Reject TypeMismatch))
            | None -> Reject TypeMismatch)
         | _ -> Reject TypeMismatch)))

  (** val core_nat_value : expr -> n option **)

  let core_nat_value = function
  | EConst (n0, l) ->
    (match l with
     | Nil ->
       (match name_eqb n0 core_zero_name with
        | True -> Some N0
        | False -> None)
     | Cons (_, _) -> None)
  | ELit l -> (match l with
               | LitNat n0 -> Some n0
               | LitString _ -> None)
  | _ -> None

  (** val core_nat_constructor : n -> expr **)

  let core_nat_constructor n0 = match n0 with
  | N0 -> EConst (core_zero_name, Nil)
  | Npos _ ->
    EApp ((EConst (core_succ_name, Nil)), (ELit (LitNat (N.pred n0))))

  (** val core_shiftr : nat -> n -> n -> n result **)

  let core_shiftr fuel0 a b =
    match N.ltb (N.log2 a) b with
    | True -> Accept N0
    | False ->
      (match N.leb b (N.of_nat fuel0) with
       | True -> Accept (N.shiftr a b)
       | False -> Decline OutOfFuel)

  (** val core_binary_nat :
      (name -> environment -> declaration option) -> nat -> environment ->
      primitive_kind -> n -> n -> expr option result **)

  let core_binary_nat resolve fuel0 env op a b =
    let numeric = fun n0 -> Accept (Some (ELit (LitNat n0))) in
    let bounded = fun operation ->
      match N.leb b (N.of_nat fuel0) with
      | True -> numeric (operation a b)
      | False -> Decline OutOfFuel
    in
    let boolean = fun b0 ->
      match core_bool_ready resolve env with
      | True ->
        Accept (Some (EConst
          ((match b0 with
            | True -> core_true_name
            | False -> core_false_name),
          Nil)))
      | False -> Decline UnsupportedExpression
    in
    (match op with
     | PNatAdd -> numeric (N.add a b)
     | PNatSub -> numeric (N.sub a b)
     | PNatMul -> numeric (N.mul a b)
     | PNatPow -> bounded N.pow
     | PNatGcd -> numeric (N.gcd a b)
     | PNatMod -> numeric (N.modulo a b)
     | PNatDiv -> numeric (N.div a b)
     | PNatBEq -> boolean (N.eqb a b)
     | PNatBLE -> boolean (N.leb a b)
     | PNatLAnd -> numeric (N.coq_land a b)
     | PNatLOr -> numeric (N.coq_lor a b)
     | PNatXor -> numeric (N.coq_lxor a b)
     | PNatShiftLeft -> bounded N.shiftl
     | PNatShiftRight -> bind (core_shiftr fuel0 a b) numeric
     | _ -> Accept None)

  (** val core_reduce_nat :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> expr -> expr option result **)

  let core_reduce_nat resolve rec0 fuel0 env g e =
    let Pair (head, args) = core_spine e Nil in
    (match head with
     | EConst (n0, l) ->
       (match l with
        | Nil ->
          (match args with
           | Nil -> Accept None
           | Cons (a, l0) ->
             (match l0 with
              | Nil ->
                let op =
                  match name_eqb n0 core_succ_name with
                  | True -> Some True
                  | False ->
                    (match resolve n0 env with
                     | Some d ->
                       (match d.decl_kind_of with
                        | DPrimitive p0 ->
                          (match p0 with
                           | PNatPred -> Some False
                           | _ -> None)
                        | _ -> None)
                     | None -> None)
                in
                (match op with
                 | Some successor ->
                   (match negb (core_nat_ready resolve env) with
                    | True -> Accept None
                    | False ->
                      bind (rec0.whnf_method g a) (fun a0 ->
                        match core_nat_value a0 with
                        | Some a1 ->
                          Accept (Some (ELit (LitNat
                            (match successor with
                             | True -> N.succ a1
                             | False -> N.pred a1))))
                        | None -> Accept None))
                 | None -> Accept None)
              | Cons (b, l1) ->
                (match l1 with
                 | Nil ->
                   (match resolve n0 env with
                    | Some d ->
                      (match d.decl_kind_of with
                       | DPrimitive op ->
                         (match op with
                          | PNatBitwise -> Accept None
                          | _ ->
                            (match negb (core_nat_ready resolve env) with
                             | True -> Accept None
                             | False ->
                               bind (rec0.whnf_method g a) (fun a0 ->
                                 bind (rec0.whnf_method g b) (fun b0 ->
                                   match core_nat_value a0 with
                                   | Some a1 ->
                                     (match core_nat_value b0 with
                                      | Some b1 ->
                                        core_binary_nat resolve fuel0 env op
                                          a1 b1
                                      | None -> Accept None)
                                   | None -> Accept None))))
                       | _ -> Accept None)
                    | None -> Accept None)
                 | Cons (_, _) -> Accept None)))
        | Cons (_, _) -> Accept None)
     | _ -> Accept None)

  (** val core_cont : ascii -> bool **)

  let core_cont b =
    match Nat.leb (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            (nat_of_ascii b) with
    | True ->
      Nat.ltb (nat_of_ascii b) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    | False -> False

  (** val core_digit : ascii -> n **)

  let core_digit b =
    N.modulo (N.of_nat (nat_of_ascii b)) (Npos (XO (XO (XO (XO (XO (XO
      XH)))))))

  (** val core_append_digit : n -> ascii -> n **)

  let core_append_digit n0 b =
    N.add (N.mul n0 (Npos (XO (XO (XO (XO (XO (XO XH)))))))) (core_digit b)

  (** val core_utf8 : string -> n list option **)

  let rec core_utf8 = function
  | EmptyString -> Some Nil
  | String (a, rest) ->
    let n0 = nat_of_ascii a in
    (match Nat.ltb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S
             O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
     | True ->
       option_map (fun x0 -> Cons ((N.of_nat n0), x0)) (core_utf8 rest)
     | False ->
       (match Nat.ltb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
        | True -> None
        | False ->
          (match Nat.ltb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                   O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
           | True ->
             (match rest with
              | EmptyString -> None
              | String (b, tail) ->
                (match core_cont b with
                 | True ->
                   option_map (fun x0 -> Cons
                     ((core_append_digit
                        (N.of_nat
                          (sub n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                            (S (S
                            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                        b),
                     x0)) (core_utf8 tail)
                 | False -> None))
           | False ->
             (match Nat.ltb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                      (S (S (S (S (S (S (S (S (S
                      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
              | True ->
                (match rest with
                 | EmptyString -> None
                 | String (b, s0) ->
                   (match s0 with
                    | EmptyString -> None
                    | String (c, tail) ->
                      (match match match match core_cont b with
                                         | True -> core_cont c
                                         | False -> False with
                                   | True ->
                                     (match negb
                                              (Nat.eqb n0 (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S
                                                O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
                                      | True -> True
                                      | False ->
                                        Nat.leb (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S
                                          O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                          (nat_of_ascii b))
                                   | False -> False with
                             | True ->
                               (match negb
                                        (Nat.eqb n0 (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S
                                          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
                                | True -> True
                                | False ->
                                  Nat.ltb (nat_of_ascii b) (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                             | False -> False with
                       | True ->
                         option_map (fun x0 -> Cons
                           ((core_append_digit
                              (core_append_digit
                                (N.of_nat
                                  (sub n0 (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                                    (S (S
                                    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                b)
                              c),
                           x0)) (core_utf8 tail)
                       | False -> None)))
              | False ->
                (match Nat.ltb n0 (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                         (S (S (S (S (S (S (S (S (S (S
                         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
                 | True ->
                   (match rest with
                    | EmptyString -> None
                    | String (b, s0) ->
                      (match s0 with
                       | EmptyString -> None
                       | String (c, s1) ->
                         (match s1 with
                          | EmptyString -> None
                          | String (d, tail) ->
                            (match match match match match core_cont b with
                                                     | True -> core_cont c
                                                     | False -> False with
                                               | True -> core_cont d
                                               | False -> False with
                                         | True ->
                                           (match negb
                                                    (Nat.eqb n0 (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S (S (S (S (S
                                                      (S (S (S (S
                                                      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
                                            | True -> True
                                            | False ->
                                              Nat.leb (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S
                                                O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                                (nat_of_ascii b))
                                         | False -> False with
                                   | True ->
                                     (match negb
                                              (Nat.eqb n0 (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S (S (S
                                                (S (S (S (S (S (S (S (S
                                                O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) with
                                      | True -> True
                                      | False ->
                                        Nat.ltb (nat_of_ascii b) (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S (S (S (S (S
                                          (S (S (S (S (S (S (S (S
                                          O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                   | False -> False with
                             | True ->
                               option_map (fun x0 -> Cons
                                 ((core_append_digit
                                    (core_append_digit
                                      (core_append_digit
                                        (N.of_nat
                                          (sub n0 (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            (S (S (S (S (S (S (S (S (S (S (S
                                            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
                                        b)
                                      c)
                                    d),
                                 x0)) (core_utf8 tail)
                             | False -> None))))
                 | False -> None)))))

  (** val core_char_list : n list -> expr **)

  let rec core_char_list cs =
    let char = EConst (core_char_name, Nil) in
    (match cs with
     | Nil ->
       EApp ((EConst ((NameStr (core_list_name, (String ((Ascii (False, True,
         True, True, False, True, True, False)), (String ((Ascii (True,
         False, False, True, False, True, True, False)), (String ((Ascii
         (False, False, True, True, False, True, True, False)),
         EmptyString)))))))), (Cons (LZero, Nil)))), char)
     | Cons (c, cs0) ->
       core_apps (EConst ((NameStr (core_list_name, (String ((Ascii (True,
         True, False, False, False, True, True, False)), (String ((Ascii
         (True, True, True, True, False, True, True, False)), (String ((Ascii
         (False, True, True, True, False, True, True, False)), (String
         ((Ascii (True, True, False, False, True, True, True, False)),
         EmptyString)))))))))), (Cons (LZero, Nil)))) (Cons (char, (Cons
         ((EApp ((EConst (core_char_of_nat, Nil)), (ELit (LitNat c)))), (Cons
         ((core_char_list cs0), Nil)))))))

  (** val core_expand_string : string -> expr result **)

  let core_expand_string s =
    match core_utf8 s with
    | Some cs ->
      Accept (EApp ((EConst (core_string_of_list, Nil)), (core_char_list cs)))
    | None -> Reject MalformedDeclaration

  (** val core_major_induct : nat -> expr -> name option **)

  let rec core_major_induct index = function
  | EPi (_, _, domain, body) ->
    (match index with
     | O ->
       (match fst (core_spine domain Nil) with
        | EConst (n0, _) -> Some n0
        | _ -> None)
     | S index0 -> core_major_induct index0 body)
  | _ -> None

  (** val core_make_structure :
      (name -> environment -> declaration option) -> environment -> name ->
      level list -> expr list -> expr -> expr option **)

  let core_make_structure resolve env owner us args value =
    match core_inductive resolve env owner with
    | Some info ->
      (match info.ind_ctors with
       | Nil -> None
       | Cons (ctor, l) ->
         (match l with
          | Nil ->
            (match core_constructor resolve env ctor with
             | Some c ->
               Some
                 (core_apps (EConst (ctor, us))
                   (app (firstn c.ctor_num_params args)
                     (map (fun i -> EProj (owner, i, value))
                       (seq O c.ctor_num_fields))))
             | None -> None)
          | Cons (_, _) -> None))
    | None -> None

  (** val core_to_constructor :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> name -> bool -> expr -> expr result **)

  let core_to_constructor resolve rec0 fuel0 env g owner k_rule value =
    bind (rec0.whnf_method g value) (fun reduced ->
      match reduced with
      | ELit l ->
        (match l with
         | LitNat n0 ->
           (match match name_eqb owner core_nat_name with
                  | True -> core_nat_ready resolve env
                  | False -> False with
            | True -> Accept (core_nat_constructor n0)
            | False -> Accept reduced)
         | LitString s ->
           bind (core_expand_string s) (fun expanded ->
             rec0.whnf_method g expanded))
      | _ ->
        (match fst (core_spine reduced Nil) with
         | EConst (n0, _) ->
           (match core_constructor resolve env n0 with
            | Some _ -> Accept reduced
            | None ->
              (match negb
                       (match k_rule with
                        | True -> True
                        | False -> core_structure resolve env owner) with
               | True -> Accept reduced
               | False ->
                 bind (rec0.infer_method g reduced) (fun ty0 ->
                   bind (rec0.whnf_method g ty0) (fun ty1 ->
                     let Pair (head, args) = core_spine ty1 Nil in
                     (match head with
                      | EConst (n1, us) ->
                        (match negb (name_eqb n1 owner) with
                         | True -> Accept reduced
                         | False ->
                           (match core_make_structure resolve env owner us
                                    args reduced with
                            | Some candidate ->
                              (match k_rule with
                               | True ->
                                 bind (sort_of rec0 g ty1) (fun sort ->
                                   bind (level_equiv fuel0 sort LZero)
                                     (fun prop0 ->
                                     match prop0 with
                                     | True ->
                                       bind (rec0.infer_method g candidate)
                                         (fun ct ->
                                         bind (rec0.defeq_method g ty1 ct)
                                           (fun ok ->
                                           match ok with
                                           | True -> Accept candidate
                                           | False -> Accept reduced))
                                     | False -> Accept reduced))
                               | False ->
                                 bind (sort_of rec0 g ty1) (fun sort ->
                                   match core_level_positive sort with
                                   | True -> Accept candidate
                                   | False -> Accept reduced))
                            | None -> Accept reduced))
                      | _ -> Accept reduced)))))
         | _ ->
           (match negb
                    (match k_rule with
                     | True -> True
                     | False -> core_structure resolve env owner) with
            | True -> Accept reduced
            | False ->
              bind (rec0.infer_method g reduced) (fun ty0 ->
                bind (rec0.whnf_method g ty0) (fun ty1 ->
                  let Pair (head, args) = core_spine ty1 Nil in
                  (match head with
                   | EConst (n0, us) ->
                     (match negb (name_eqb n0 owner) with
                      | True -> Accept reduced
                      | False ->
                        (match core_make_structure resolve env owner us args
                                 reduced with
                         | Some candidate ->
                           (match k_rule with
                            | True ->
                              bind (sort_of rec0 g ty1) (fun sort ->
                                bind (level_equiv fuel0 sort LZero)
                                  (fun prop0 ->
                                  match prop0 with
                                  | True ->
                                    bind (rec0.infer_method g candidate)
                                      (fun ct ->
                                      bind (rec0.defeq_method g ty1 ct)
                                        (fun ok ->
                                        match ok with
                                        | True -> Accept candidate
                                        | False -> Accept reduced))
                                  | False -> Accept reduced))
                            | False ->
                              bind (sort_of rec0 g ty1) (fun sort ->
                                match core_level_positive sort with
                                | True -> Accept candidate
                                | False -> Accept reduced))
                         | None -> Accept reduced))
                   | _ -> Accept reduced))))))

  (** val core_find_rule :
      name -> recursor_rule list -> recursor_rule option **)

  let rec core_find_rule n0 = function
  | Nil -> None
  | Cons (r, rules0) ->
    (match name_eqb n0 r.rule_ctor with
     | True -> Some r
     | False -> core_find_rule n0 rules0)

  (** val core_reduce_recursor :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> expr -> expr option result **)

  let core_reduce_recursor resolve rec0 fuel0 env g e =
    let Pair (head, args) = core_spine e Nil in
    (match head with
     | EConst (n0, us) ->
       (match resolve n0 env with
        | Some d ->
          (match d.decl_kind_of with
           | DRecursor info ->
             let first_index =
               add (add info.rec_num_params info.rec_num_motives)
                 info.rec_num_minors
             in
             let major_index = add first_index info.rec_num_indices in
             (match nth_error args major_index with
              | Some major ->
                (match core_major_induct major_index d.decl_type with
                 | Some owner ->
                   bind
                     (core_to_constructor resolve rec0 fuel0 env g owner
                       info.rec_k major)
                     (fun major0 ->
                     let Pair (ctor, fields) = core_spine major0 Nil in
                     (match ctor with
                      | EConst (cn, _) ->
                        (match core_find_rule cn info.rec_rules with
                         | Some rule ->
                           (match core_constructor resolve env cn with
                            | Some ci ->
                              (match negb
                                       (match match match name_eqb
                                                            ci.ctor_induct
                                                            owner with
                                                    | True ->
                                                      Nat.eqb (length fields)
                                                        (add
                                                          ci.ctor_num_params
                                                          ci.ctor_num_fields)
                                                    | False -> False with
                                              | True ->
                                                Nat.eqb rule.rule_nfields
                                                  ci.ctor_num_fields
                                              | False -> False with
                                        | True ->
                                          Nat.eqb (length us)
                                            (length d.decl_params)
                                        | False -> False) with
                               | True -> Accept None
                               | False ->
                                 Accept (Some
                                   (core_apps
                                     (subst_levels d.decl_params us
                                       rule.rule_rhs)
                                     (app (firstn first_index args)
                                       (app (skipn ci.ctor_num_params fields)
                                         (skipn (S major_index) args))))))
                            | None -> Accept None)
                         | None -> Accept None)
                      | _ -> Accept None))
                 | None -> Reject MalformedDeclaration)
              | None -> Accept None)
           | _ -> Accept None)
        | None -> Accept None)
     | _ -> Accept None)

  (** val core_reduce_projection_with :
      (name -> environment -> declaration option) -> methods -> (context ->
      expr -> expr result) -> environment -> context -> name -> nat -> expr
      -> expr option result **)

  let core_reduce_projection_with resolve rec0 reduce env g owner index value =
    bind (reduce g value) (fun reduced ->
      bind
        (match reduced with
         | ELit l ->
           (match l with
            | LitNat _ -> Accept reduced
            | LitString s ->
              bind (core_expand_string s) (fun expanded ->
                rec0.whnf_method g expanded))
         | _ -> Accept reduced)
        (fun reduced0 ->
        let Pair (head, args) = core_spine reduced0 Nil in
        (match head with
         | EConst (n0, _) ->
           (match core_constructor resolve env n0 with
            | Some ci ->
              (match match match name_eqb ci.ctor_induct owner with
                           | True -> Nat.ltb index ci.ctor_num_fields
                           | False -> False with
                     | True ->
                       Nat.eqb (length args)
                         (add ci.ctor_num_params ci.ctor_num_fields)
                     | False -> False with
               | True ->
                 Accept (nth_error args (add ci.ctor_num_params index))
               | False -> Accept None)
            | None -> Accept None)
         | _ -> Accept None)))

  (** val core_reduce_projection :
      (name -> environment -> declaration option) -> methods -> environment
      -> context -> name -> nat -> expr -> expr option result **)

  let core_reduce_projection resolve rec0 =
    core_reduce_projection_with resolve rec0 rec0.whnf_method

  (** val core_reduce_quotient :
      (name -> environment -> declaration option) -> methods -> environment
      -> context -> expr -> expr option result **)

  let core_reduce_quotient resolve rec0 env g e =
    let Pair (head, args) = core_spine e Nil in
    (match head with
     | EConst (n0, _) ->
       (match resolve n0 env with
        | Some d ->
          let major_pos =
            match d.decl_kind_of with
            | DAssumption -> None
            | DDefinition -> None
            | DTheorem -> None
            | DOpaque -> None
            | DUnsupported -> None
            | DInductive _ -> None
            | DConstructor _ -> None
            | DRecursor _ -> None
            | DPrimitive _ -> None
            | DQuotient q0 ->
              (match q0 with
               | QType -> None
               | QCtor -> None
               | QLift -> Some (S (S (S (S (S O)))))
               | QInd -> Some (S (S (S (S O)))))
            | _ -> None
          in
          (match major_pos with
           | Some index ->
             (match nth_error args index with
              | Some major ->
                (match nth_error args (S (S (S O))) with
                 | Some fn ->
                   bind (rec0.whnf_method g major) (fun major0 ->
                     let Pair (ctor, cargs) = core_spine major0 Nil in
                     (match ctor with
                      | EConst (cn, _) ->
                        (match cargs with
                         | Nil -> Accept None
                         | Cons (_, l0) ->
                           (match l0 with
                            | Nil -> Accept None
                            | Cons (_, l1) ->
                              (match l1 with
                               | Nil -> Accept None
                               | Cons (representative, l2) ->
                                 (match l2 with
                                  | Nil ->
                                    (match resolve cn env with
                                     | Some cd ->
                                       (match cd.decl_kind_of with
                                        | DQuotient q0 ->
                                          (match q0 with
                                           | QCtor ->
                                             Accept (Some
                                               (core_apps (EApp (fn,
                                                 representative))
                                                 (skipn (S index) args)))
                                           | _ -> Accept None)
                                        | _ -> Accept None)
                                     | None -> Accept None)
                                  | Cons (_, _) -> Accept None))))
                      | _ -> Accept None))
                 | None -> Accept None)
              | None -> Accept None)
           | None -> Accept None)
        | None -> Accept None)
     | _ -> Accept None)

  (** val infer_step :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> name list -> bool -> context -> expr -> expr result **)

  let rec infer_step resolve rec0 fuel0 env ps checking g = function
  | EBVar i ->
    (match nth_error g.bound_context i with
     | Some b -> Accept (lift (S i) O b.binding_type)
     | None -> Reject LooseBoundVariable)
  | EFVar n0 ->
    (match find_free n0 g.free_context with
     | Some b -> Accept b.binding_type
     | None -> Reject UnknownFreeVariable)
  | EMVar _ -> Reject MetaVariable
  | ESort u0 -> bind (check_level ps u0) (fun _ -> Accept (ESort (LSucc u0)))
  | EConst (n0, us) ->
    bind (get_constant resolve env ps n0 us) (fun d -> Accept
      (instantiate_levels d.decl_params us d.decl_type))
  | EApp (f, a) ->
    bind (infer_step resolve rec0 fuel0 env ps checking g f) (fun ft ->
      bind (rec0.whnf_method g ft) (fun ft0 ->
        match ft0 with
        | EPi (_, _, domain, body) ->
          bind
            (match checking with
             | True ->
               bind (infer_step resolve rec0 fuel0 env ps True g a)
                 (fun arg_type ->
                 bind (application_type_defeq rec0 g a domain arg_type)
                   (fun ok -> require ok TypeMismatch))
             | False -> Accept Tt)
            (fun _ -> Accept (instantiate body a))
        | _ -> Reject ExpectedPi))
  | ELam (n0, bi, domain, body) ->
    bind
      (match checking with
       | True ->
         bind (infer_step resolve rec0 fuel0 env ps True g domain) (fun dt ->
           bind (rec0.whnf_method g dt) (fun dt0 ->
             match dt0 with
             | EBVar _ -> Reject ExpectedSort
             | EFVar _ -> Reject ExpectedSort
             | EMVar _ -> Reject ExpectedSort
             | ESort _ -> Accept Tt
             | _ -> Reject ExpectedSort))
       | False -> Accept Tt)
      (fun _ ->
      bind
        (infer_step resolve rec0 fuel0 env ps checking
          (push_binding g domain None) body)
        (fun bt0 -> Accept (EPi (n0, bi, domain, bt0))))
  | EPi (_, _, domain, body) ->
    bind (infer_step resolve rec0 fuel0 env ps checking g domain) (fun dt ->
      bind (rec0.whnf_method g dt) (fun dt0 ->
        bind
          (match dt0 with
           | ESort u0 -> Accept u0
           | _ -> Reject ExpectedSort)
          (fun u0 ->
          let gb = push_binding g domain None in
          bind (infer_step resolve rec0 fuel0 env ps checking gb body)
            (fun bt0 ->
            bind (rec0.whnf_method gb bt0) (fun bt1 ->
              bind
                (match bt1 with
                 | ESort v0 -> Accept v0
                 | _ -> Reject ExpectedSort)
                (fun v0 -> Accept (ESort (LIMax (u0, v0)))))))))
  | ELet (_, ty0, value, body, _) ->
    bind
      (match checking with
       | True ->
         bind (infer_step resolve rec0 fuel0 env ps True g ty0)
           (fun sort_type ->
           bind (rec0.whnf_method g sort_type) (fun sort_type0 ->
             bind
               (match sort_type0 with
                | EBVar _ -> Reject ExpectedSort
                | EFVar _ -> Reject ExpectedSort
                | EMVar _ -> Reject ExpectedSort
                | ESort _ -> Accept Tt
                | _ -> Reject ExpectedSort)
               (fun _ ->
               bind (infer_step resolve rec0 fuel0 env ps True g value)
                 (fun vt ->
                 bind (rec0.defeq_method g vt ty0) (fun ok ->
                   require ok TypeMismatch)))))
       | False -> Accept Tt)
      (fun _ ->
      bind
        (infer_step resolve rec0 fuel0 env ps checking
          (push_binding g ty0 (Some value)) body)
        (fun bt0 -> Accept (instantiate bt0 value)))
  | ELit l ->
    (match l with
     | LitNat _ ->
       (match core_nat_ready resolve env with
        | True -> Accept core_nat
        | False -> Decline UnsupportedExpression)
     | LitString s ->
       (match core_string_ready resolve env with
        | True ->
          bind (core_expand_string s) (fun _ -> Accept (EConst
            (core_string_name, Nil)))
        | False -> Decline UnsupportedExpression))
  | EProj (owner, index, value) ->
    (match core_inductive resolve env owner with
     | Some _ ->
       core_infer_projection resolve
         (match checking with
          | True -> rec0
          | False -> inference_only rec0)
         fuel0 env g owner index value
     | None -> Decline UnsupportedExpression)
  | EMData body -> infer_step resolve rec0 fuel0 env ps checking g body

  (** val core_beta_collect : expr -> expr list -> expr list -> expr **)

  let rec core_beta_collect head args values =
    match args with
    | Nil -> instantiate_many head values
    | Cons (a, args0) ->
      (match head with
       | ELam (_, _, _, body) ->
         core_beta_collect body args0 (Cons (a, values))
       | _ -> core_apps (instantiate_many head values) (Cons (a, args0)))

  (** val core_beta : expr -> expr list -> expr **)

  let core_beta head args =
    core_beta_collect head args Nil

  (** val core_unfold :
      (name -> environment -> declaration option) -> environment -> name list
      -> expr -> expr option result **)

  let core_unfold resolve env ps e =
    let Pair (head, args) = core_spine e Nil in
    (match head with
     | EConst (n0, us) ->
       bind (get_constant resolve env ps n0 us) (fun d ->
         match d.decl_kind_of with
         | DDefinition ->
           (match d.decl_value with
            | Some value ->
              Accept (Some
                (core_apps (instantiate_levels d.decl_params us value) args))
            | None -> Reject MalformedDeclaration)
         | DTheorem ->
           (match d.decl_value with
            | Some value ->
              Accept (Some
                (core_apps (instantiate_levels d.decl_params us value) args))
            | None -> Reject MalformedDeclaration)
         | DPrimitive _ ->
           (match d.decl_value with
            | Some value ->
              Accept (Some
                (core_apps (instantiate_levels d.decl_params us value) args))
            | None -> Reject MalformedDeclaration)
         | _ -> Accept None)
     | _ -> Accept None)

  (** val whnf_core_step :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> name list -> bool -> context -> expr -> expr result **)

  let whnf_core_step resolve rec0 fuel0 env ps cheap g e = match e with
  | EBVar i ->
    (match nth_error g.bound_context i with
     | Some b ->
       (match b.binding_value with
        | Some v0 -> rec0.whnf_core_method cheap g (lift (S i) O v0)
        | None -> Accept e)
     | None -> Reject LooseBoundVariable)
  | EFVar n0 ->
    (match find_free n0 g.free_context with
     | Some b ->
       (match b.binding_value with
        | Some v0 -> rec0.whnf_core_method cheap g v0
        | None -> Accept e)
     | None -> Reject UnknownFreeVariable)
  | EMVar _ -> Reject MetaVariable
  | ESort u0 -> bind (check_level ps u0) (fun _ -> Accept e)
  | EConst (n0, us) ->
    bind (get_constant resolve env ps n0 us) (fun _ -> Accept e)
  | EApp (_, _) ->
    let Pair (head, args) = core_spine e Nil in
    bind (rec0.whnf_core_method cheap g head) (fun fn ->
      match fn with
      | EBVar _ ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot0 ->
          bind
            (match quot0 with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel0 env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | EFVar _ ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot0 ->
          bind
            (match quot0 with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel0 env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | EMVar _ ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot0 ->
          bind
            (match quot0 with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel0 env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | ESort _ ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot0 ->
          bind
            (match quot0 with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel0 env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | EConst (_, _) ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot0 ->
          bind
            (match quot0 with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel0 env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | EApp (_, _) ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot0 ->
          bind
            (match quot0 with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel0 env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | ELam (_, _, _, _) -> rec0.whnf_core_method cheap g (core_beta fn args)
      | EPi (_, _, _, _) ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot0 ->
          bind
            (match quot0 with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel0 env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | ELet (_, _, _, _, _) ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot0 ->
          bind
            (match quot0 with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel0 env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | ELit _ ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot0 ->
          bind
            (match quot0 with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel0 env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | EProj (_, _, _) ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot0 ->
          bind
            (match quot0 with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel0 env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | EMData _ ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot0 ->
          bind
            (match quot0 with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel0 env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt)))
  | ELet (_, _, value, body, _) ->
    rec0.whnf_core_method cheap g (instantiate body value)
  | ELit l ->
    (match l with
     | LitNat _ -> Accept e
     | LitString s -> bind (core_expand_string s) (fun _ -> Accept e))
  | EProj (owner, index, value) ->
    bind
      (core_reduce_projection_with resolve rec0
        (match cheap with
         | True -> rec0.whnf_core_method True
         | False -> rec0.whnf_method)
        env g owner index value)
      (fun step ->
      match step with
      | Some value0 -> rec0.whnf_core_method cheap g value0
      | None -> Accept e)
  | EMData body -> rec0.whnf_core_method cheap g body
  | _ -> Accept e

  (** val finish_whnf_unfold :
      (name -> environment -> declaration option) -> environment -> name list
      -> expr -> whnf_round result **)

  let finish_whnf_unfold resolve env ps e =
    bind (core_unfold resolve env ps e) (fun unfolded -> Accept
      (match unfolded with
       | Some value -> WhnfContinue value
       | None -> WhnfDone e))

  (** val whnf_round_step :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> name list -> context -> expr -> whnf_round result **)

  let whnf_round_step resolve rec0 fuel0 env ps g e =
    bind (whnf_core_step resolve rec0 fuel0 env ps False g e) (fun reduced ->
      match reduced with
      | EBVar _ ->
        bind (core_reduce_nat resolve rec0 fuel0 env g reduced)
          (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | EFVar _ ->
        bind (core_reduce_nat resolve rec0 fuel0 env g reduced)
          (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | EMVar _ ->
        bind (core_reduce_nat resolve rec0 fuel0 env g reduced)
          (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | ESort _ ->
        bind (core_reduce_nat resolve rec0 fuel0 env g reduced)
          (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | EConst (n0, _) ->
        (match match name_eqb n0 core_zero_name with
               | True -> core_nat_ready resolve env
               | False -> False with
         | True -> Accept (WhnfDone (ELit (LitNat N0)))
         | False -> finish_whnf_unfold resolve env ps reduced)
      | EApp (_, _) ->
        bind (core_reduce_nat resolve rec0 fuel0 env g reduced)
          (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | ELam (_, _, _, _) ->
        bind (core_reduce_nat resolve rec0 fuel0 env g reduced)
          (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | EPi (_, _, _, _) ->
        bind (core_reduce_nat resolve rec0 fuel0 env g reduced)
          (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | ELet (_, _, _, _, _) ->
        bind (core_reduce_nat resolve rec0 fuel0 env g reduced)
          (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | ELit _ ->
        bind (core_reduce_nat resolve rec0 fuel0 env g reduced)
          (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | EProj (_, _, _) ->
        bind (core_reduce_nat resolve rec0 fuel0 env g reduced)
          (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | EMData _ ->
        bind (core_reduce_nat resolve rec0 fuel0 env g reduced)
          (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced))

  (** val whnf_loop :
      (name -> environment -> declaration option) -> nat -> methods -> nat ->
      environment -> name list -> context -> expr -> expr result **)

  let whnf_loop resolve rounds rec0 fuel0 env ps g e =
    run_whnf_rounds rounds (whnf_round_step resolve rec0 fuel0 env ps g) e

  (** val eta_compare :
      methods -> context -> expr -> expr -> expr -> bool result **)

  let eta_compare rec0 g domain body other =
    bind (rec0.infer_method g other) (fun ty0 ->
      bind (rec0.whnf_method g ty0) (fun ty1 ->
        match ty1 with
        | EPi (_, _, domain', _) ->
          bind (rec0.defeq_method g domain domain') (fun ok ->
            match ok with
            | True ->
              rec0.defeq_method (push_binding g domain None) body (EApp
                ((lift (S O) O other), (EBVar O)))
            | False -> Accept False)
        | _ -> Accept False))

  (** val core_alpha : nat -> expr -> expr -> (bool, nat) prod **)

  let rec core_alpha budget t0 s =
    match budget with
    | O -> Pair (False, O)
    | S budget0 ->
      (match t0 with
       | EBVar i ->
         (match s with
          | EBVar j -> Pair ((Nat.eqb i j), budget0)
          | _ -> Pair (False, budget0))
       | EFVar n0 ->
         (match s with
          | EFVar m -> Pair ((name_eqb n0 m), budget0)
          | _ -> Pair (False, budget0))
       | EMVar n0 ->
         (match s with
          | EMVar m -> Pair ((name_eqb n0 m), budget0)
          | _ -> Pair (False, budget0))
       | ESort u0 ->
         (match s with
          | ESort v0 -> Pair ((level_eqb u0 v0), budget0)
          | _ -> Pair (False, budget0))
       | EConst (n0, us) ->
         (match s with
          | EConst (m, vs) ->
            Pair
              ((match name_eqb n0 m with
                | True -> list_eqb level_eqb us vs
                | False -> False),
              budget0)
          | _ -> Pair (False, budget0))
       | EApp (f, a) ->
         (match s with
          | EApp (h, b) ->
            let Pair (ok, remaining) = core_alpha budget0 f h in
            (match ok with
             | True -> core_alpha remaining a b
             | False -> Pair (False, remaining))
          | _ -> Pair (False, budget0))
       | ELam (_, _, f, a) ->
         (match s with
          | ELam (_, _, h, b) ->
            let Pair (ok, remaining) = core_alpha budget0 f h in
            (match ok with
             | True -> core_alpha remaining a b
             | False -> Pair (False, remaining))
          | _ -> Pair (False, budget0))
       | EPi (_, _, f, a) ->
         (match s with
          | EPi (_, _, h, b) ->
            let Pair (ok, remaining) = core_alpha budget0 f h in
            (match ok with
             | True -> core_alpha remaining a b
             | False -> Pair (False, remaining))
          | _ -> Pair (False, budget0))
       | ELet (_, a, v0, b, _) ->
         (match s with
          | ELet (_, c, w, d, _) ->
            let Pair (ok, remaining) = core_alpha budget0 a c in
            (match ok with
             | True ->
               let Pair (ok0, remaining0) = core_alpha remaining v0 w in
               (match ok0 with
                | True -> core_alpha remaining0 b d
                | False -> Pair (False, remaining0))
             | False -> Pair (False, remaining))
          | _ -> Pair (False, budget0))
       | ELit a ->
         (match s with
          | ELit b -> Pair ((literal_eqb a b), budget0)
          | _ -> Pair (False, budget0))
       | EProj (n0, i, a) ->
         (match s with
          | EProj (m, j, b) ->
            (match match name_eqb n0 m with
                   | True -> Nat.eqb i j
                   | False -> False with
             | True -> core_alpha budget0 a b
             | False -> Pair (False, budget0))
          | _ -> Pair (False, budget0))
       | EMData a ->
         (match s with
          | EMData b -> core_alpha budget0 a b
          | _ -> Pair (False, budget0)))

  (** val core_alpha_eq : expr -> expr -> bool **)

  let core_alpha_eq t0 s =
    fst
      (core_alpha (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        t0 s)

  (** val core_compare_args :
      methods -> context -> expr list -> expr list -> bool result **)

  let rec core_compare_args rec0 g xs ys =
    match xs with
    | Nil -> (match ys with
              | Nil -> Accept True
              | Cons (_, _) -> Accept False)
    | Cons (x0, xs0) ->
      (match ys with
       | Nil -> Accept False
       | Cons (y, ys0) ->
         bind (rec0.defeq_method g x0 y) (fun ok ->
           match ok with
           | True -> core_compare_args rec0 g xs0 ys0
           | False -> Accept False))

  (** val core_same_head : nat -> expr -> expr -> bool result **)

  let core_same_head fuel0 t0 s =
    match t0 with
    | EBVar i ->
      (match s with
       | EBVar j -> Accept (Nat.eqb i j)
       | _ -> Accept False)
    | EFVar n0 ->
      (match s with
       | EFVar m -> Accept (name_eqb n0 m)
       | _ -> Accept False)
    | EConst (n0, us) ->
      (match s with
       | EConst (m, vs) ->
         (match name_eqb n0 m with
          | True -> levels_equiv fuel0 us vs
          | False -> Accept False)
       | _ -> Accept False)
    | _ -> Accept False

  (** val core_congruent_apps :
      methods -> nat -> context -> expr -> expr -> bool result **)

  let core_congruent_apps rec0 fuel0 g t0 s =
    match t0 with
    | EApp (_, _) ->
      (match s with
       | EApp (_, _) ->
         let Pair (tf, ta) = core_spine t0 Nil in
         let Pair (sf, sa) = core_spine s Nil in
         bind (core_same_head fuel0 tf sf) (fun same ->
           match match same with
                 | True -> Nat.eqb (length ta) (length sa)
                 | False -> False with
           | True -> core_compare_args rec0 g (rev0 ta) (rev0 sa)
           | False -> Accept False)
       | _ -> Accept False)
    | _ -> Accept False

  (** val core_delta_info :
      (name -> environment -> declaration option) -> environment -> expr ->
      declaration option **)

  let core_delta_info resolve env e =
    match fst (core_spine e Nil) with
    | EConst (n0, us) ->
      (match resolve n0 env with
       | Some d ->
         (match d.decl_kind_of with
          | DDefinition ->
            (match d.decl_value with
             | Some _ ->
               (match Nat.eqb (length d.decl_params) (length us) with
                | True -> Some d
                | False -> None)
             | None -> None)
          | DTheorem ->
            (match d.decl_value with
             | Some _ ->
               (match Nat.eqb (length d.decl_params) (length us) with
                | True -> Some d
                | False -> None)
             | None -> None)
          | DPrimitive _ ->
            (match d.decl_value with
             | Some _ ->
               (match Nat.eqb (length d.decl_params) (length us) with
                | True -> Some d
                | False -> None)
             | None -> None)
          | _ -> None)
       | None -> None)
    | _ -> None

  (** val core_delta_sides :
      (name -> environment -> declaration option) -> environment -> expr ->
      expr -> (bool, bool) prod **)

  let core_delta_sides resolve env t0 s =
    match core_delta_info resolve env t0 with
    | Some dt ->
      (match core_delta_info resolve env s with
       | Some ds ->
         (match hints_lt (effective_hints dt) (effective_hints ds) with
          | True -> Pair (False, True)
          | False ->
            (match hints_lt (effective_hints ds) (effective_hints dt) with
             | True -> Pair (True, False)
             | False -> Pair (True, True)))
       | None -> Pair (True, True))
    | None -> Pair (True, True)

  (** val core_erasing_delta :
      (name -> environment -> declaration option) -> environment -> expr ->
      bool **)

  let core_erasing_delta resolve env e =
    let Pair (head, args) = core_spine e Nil in
    (match head with
     | EConst (n0, _) ->
       (match args with
        | Nil -> False
        | Cons (_, _) ->
          (match resolve n0 env with
           | Some d ->
             (match d.decl_value with
              | Some e0 ->
                (match e0 with
                 | ELam (_, _, _, body) -> negb (core_occurs O body)
                 | _ -> False)
              | None -> False)
           | None -> False))
     | _ -> False)

  (** val core_delta_congruent :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> expr -> expr -> bool result **)

  let core_delta_congruent resolve rec0 fuel0 env g t0 s =
    match core_delta_info resolve env t0 with
    | Some dt ->
      (match core_delta_info resolve env s with
       | Some ds ->
         (match effective_hints dt with
          | HintRegular ht ->
            (match effective_hints ds with
             | HintRegular hs ->
               (match match N.eqb ht hs with
                      | True ->
                        negb
                          (match core_erasing_delta resolve env t0 with
                           | True -> True
                           | False -> core_erasing_delta resolve env s)
                      | False -> False with
                | True -> core_congruent_apps rec0 fuel0 g t0 s
                | False -> Accept False)
             | _ -> Accept False)
          | _ -> Accept False)
       | None -> Accept False)
    | None -> Accept False

  (** val compare_heads :
      methods -> nat -> context -> expr -> expr -> bool result **)

  let compare_heads rec0 fuel0 g t0 s =
    match t0 with
    | EBVar n0 ->
      (match s with
       | EBVar m -> Accept (Nat.eqb n0 m)
       | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
       | _ -> Accept False)
    | EFVar n0 ->
      (match s with
       | EFVar m -> Accept (name_eqb n0 m)
       | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
       | _ -> Accept False)
    | EMVar _ ->
      (match s with
       | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
       | _ -> Accept False)
    | EConst (n0, us) ->
      (match s with
       | EConst (m, vs) ->
         (match name_eqb n0 m with
          | True -> levels_equiv fuel0 us vs
          | False -> Accept False)
       | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
       | _ -> Accept False)
    | EApp (_, _) ->
      (match s with
       | EApp (_, _) ->
         let Pair (tf, ta) = core_spine t0 Nil in
         let Pair (sf, sa) = core_spine s Nil in
         (match Nat.eqb (length ta) (length sa) with
          | True ->
            bind (rec0.defeq_method g tf sf) (fun ok ->
              match ok with
              | True -> core_compare_args rec0 g ta sa
              | False -> Accept False)
          | False -> Accept False)
       | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
       | _ -> Accept False)
    | ELam (_, _, domain, body) -> eta_compare rec0 g domain body s
    | EPi (_, _, _, _) ->
      (match s with
       | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
       | _ -> Accept False)
    | ELet (_, _, _, _, _) ->
      (match s with
       | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
       | _ -> Accept False)
    | EProj (n0, i, a) ->
      (match s with
       | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
       | EProj (m, j, b) ->
         (match match name_eqb n0 m with
                | True -> Nat.eqb i j
                | False -> False with
          | True -> rec0.defeq_method g a b
          | False -> Accept False)
       | _ -> Accept False)
    | _ ->
      (match s with
       | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t0
       | _ -> Accept False)

  (** val core_compare_fields :
      methods -> context -> name -> expr -> nat -> expr list -> bool result **)

  let rec core_compare_fields rec0 g owner value index = function
  | Nil -> Accept True
  | Cons (field, fields0) ->
    bind (rec0.defeq_method g (EProj (owner, index, value)) field) (fun ok ->
      match ok with
      | True -> core_compare_fields rec0 g owner value (S index) fields0
      | False -> Accept False)

  (** val core_structure_eta :
      (name -> environment -> declaration option) -> methods -> environment
      -> context -> expr -> expr -> bool result **)

  let core_structure_eta resolve rec0 env g value constructed =
    let Pair (head, args) = core_spine constructed Nil in
    (match head with
     | EConst (ctor, _) ->
       (match core_constructor resolve env ctor with
        | Some c ->
          (match match core_structure resolve env c.ctor_induct with
                 | True ->
                   Nat.eqb (length args)
                     (add c.ctor_num_params c.ctor_num_fields)
                 | False -> False with
           | True ->
             bind (rec0.infer_method g value) (fun vt ->
               bind (rec0.infer_method g constructed) (fun ct ->
                 bind (rec0.defeq_method g vt ct) (fun ok ->
                   match ok with
                   | True ->
                     core_compare_fields rec0 g c.ctor_induct value O
                       (skipn c.ctor_num_params args)
                   | False -> Accept False)))
           | False -> Accept False)
        | None -> Accept False)
     | _ -> Accept False)

  (** val core_unit_like :
      (name -> environment -> declaration option) -> methods -> environment
      -> context -> expr -> expr -> bool result **)

  let core_unit_like resolve rec0 env g t0 s =
    bind (rec0.infer_method g t0) (fun ty0 ->
      bind (rec0.whnf_method g ty0) (fun ty1 ->
        match fst (core_spine ty1 Nil) with
        | EConst (owner, _) ->
          (match core_structure resolve env owner with
           | True ->
             (match core_inductive resolve env owner with
              | Some i ->
                (match i.ind_ctors with
                 | Nil -> Accept False
                 | Cons (ctor, l) ->
                   (match l with
                    | Nil ->
                      (match core_constructor resolve env ctor with
                       | Some c ->
                         (match Nat.eqb c.ctor_num_fields O with
                          | True ->
                            bind (rec0.infer_method g s) (fun sty ->
                              rec0.defeq_method g ty1 sty)
                          | False -> Accept False)
                       | None -> Accept False)
                    | Cons (_, _) -> Accept False))
              | None -> Accept False)
           | False -> Accept False)
        | _ -> Accept False))

  (** val core_try_string_expansion :
      methods -> context -> expr -> expr -> bool option result **)

  let core_try_string_expansion rec0 g t0 s =
    let expand = fun text other ->
      bind (core_expand_string text) (fun expanded ->
        bind (rec0.defeq_method g expanded other) (fun ok -> Accept (Some ok)))
    in
    (match t0 with
     | EApp (e, _) ->
       (match e with
        | EConst (n0, l) ->
          (match l with
           | Nil ->
             (match s with
              | ELit l0 ->
                (match l0 with
                 | LitNat _ -> Accept None
                 | LitString text ->
                   (match name_eqb n0 core_string_of_list with
                    | True -> expand text t0
                    | False -> Accept None))
              | _ -> Accept None)
           | Cons (_, _) -> Accept None)
        | _ -> Accept None)
     | ELit l ->
       (match l with
        | LitNat _ -> Accept None
        | LitString text ->
          (match s with
           | EApp (e, _) ->
             (match e with
              | EConst (n0, l0) ->
                (match l0 with
                 | Nil ->
                   (match name_eqb n0 core_string_of_list with
                    | True -> expand text s
                    | False -> Accept None)
                 | Cons (_, _) -> Accept None)
              | _ -> Accept None)
           | _ -> Accept None))
     | _ -> Accept None)

  (** val core_compare_fallback :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> expr -> expr -> bool result **)

  let core_compare_fallback resolve rec0 fuel0 env g t0 s =
    bind (compare_heads rec0 fuel0 g t0 s) (fun ok ->
      match ok with
      | True -> Accept True
      | False ->
        bind (core_structure_eta resolve rec0 env g t0 s) (fun ok0 ->
          match ok0 with
          | True -> Accept True
          | False ->
            bind (core_structure_eta resolve rec0 env g s t0) (fun ok1 ->
              match ok1 with
              | True -> Accept True
              | False ->
                bind (core_try_string_expansion rec0 g t0 s) (fun expanded ->
                  match expanded with
                  | Some ok2 -> Accept ok2
                  | None -> core_unit_like resolve rec0 env g t0 s))))

  (** val compare_after_whnf :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> expr -> expr -> bool result **)

  let compare_after_whnf resolve rec0 fuel0 env g t0 s =
    match core_alpha_eq t0 s with
    | True -> Accept True
    | False ->
      (match t0 with
       | ESort u0 ->
         (match s with
          | ESort v0 -> level_equiv fuel0 u0 v0
          | _ ->
            bind (rec0.infer_method g t0) (fun tt0 ->
              bind (sort_of rec0 g tt0) (fun sort ->
                bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                  match is_prop with
                  | True ->
                    bind (rec0.infer_method g s) (fun st ->
                      rec0.defeq_method g tt0 st)
                  | False ->
                    core_compare_fallback resolve rec0 fuel0 env g t0 s))))
       | ELam (_, _, a, b) ->
         (match s with
          | ELam (_, _, c, d) ->
            bind (rec0.defeq_method g a c) (fun ok ->
              match ok with
              | True -> rec0.defeq_method (push_binding g a None) b d
              | False -> Accept False)
          | _ ->
            bind (rec0.infer_method g t0) (fun tt0 ->
              bind (sort_of rec0 g tt0) (fun sort ->
                bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                  match is_prop with
                  | True ->
                    bind (rec0.infer_method g s) (fun st ->
                      rec0.defeq_method g tt0 st)
                  | False ->
                    core_compare_fallback resolve rec0 fuel0 env g t0 s))))
       | EPi (_, _, a, b) ->
         (match s with
          | EPi (_, _, c, d) ->
            bind (rec0.defeq_method g a c) (fun ok ->
              match ok with
              | True -> rec0.defeq_method (push_binding g a None) b d
              | False -> Accept False)
          | _ ->
            bind (rec0.infer_method g t0) (fun tt0 ->
              bind (sort_of rec0 g tt0) (fun sort ->
                bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                  match is_prop with
                  | True ->
                    bind (rec0.infer_method g s) (fun st ->
                      rec0.defeq_method g tt0 st)
                  | False ->
                    core_compare_fallback resolve rec0 fuel0 env g t0 s))))
       | ELit l ->
         (match l with
          | LitNat n0 ->
            (match s with
             | ELit l0 ->
               (match l0 with
                | LitNat m -> Accept (N.eqb n0 m)
                | LitString _ ->
                  bind (rec0.infer_method g t0) (fun tt0 ->
                    bind (sort_of rec0 g tt0) (fun sort ->
                      bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                        match is_prop with
                        | True ->
                          bind (rec0.infer_method g s) (fun st ->
                            rec0.defeq_method g tt0 st)
                        | False ->
                          core_compare_fallback resolve rec0 fuel0 env g t0 s))))
             | _ ->
               bind (rec0.infer_method g t0) (fun tt0 ->
                 bind (sort_of rec0 g tt0) (fun sort ->
                   bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                     match is_prop with
                     | True ->
                       bind (rec0.infer_method g s) (fun st ->
                         rec0.defeq_method g tt0 st)
                     | False ->
                       core_compare_fallback resolve rec0 fuel0 env g t0 s))))
          | LitString a ->
            (match s with
             | ELit l0 ->
               (match l0 with
                | LitNat _ ->
                  bind (rec0.infer_method g t0) (fun tt0 ->
                    bind (sort_of rec0 g tt0) (fun sort ->
                      bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                        match is_prop with
                        | True ->
                          bind (rec0.infer_method g s) (fun st ->
                            rec0.defeq_method g tt0 st)
                        | False ->
                          core_compare_fallback resolve rec0 fuel0 env g t0 s)))
                | LitString b -> Accept (eqb2 a b))
             | _ ->
               bind (rec0.infer_method g t0) (fun tt0 ->
                 bind (sort_of rec0 g tt0) (fun sort ->
                   bind (level_equiv fuel0 sort LZero) (fun is_prop ->
                     match is_prop with
                     | True ->
                       bind (rec0.infer_method g s) (fun st ->
                         rec0.defeq_method g tt0 st)
                     | False ->
                       core_compare_fallback resolve rec0 fuel0 env g t0 s)))))
       | _ ->
         bind (rec0.infer_method g t0) (fun tt0 ->
           bind (sort_of rec0 g tt0) (fun sort ->
             bind (level_equiv fuel0 sort LZero) (fun is_prop ->
               match is_prop with
               | True ->
                 bind (rec0.infer_method g s) (fun st ->
                   rec0.defeq_method g tt0 st)
               | False -> core_compare_fallback resolve rec0 fuel0 env g t0 s))))

  (** val core_quick :
      methods -> nat -> context -> expr -> expr -> bool option result **)

  let core_quick rec0 fuel0 g t0 s =
    match core_alpha_eq t0 s with
    | True -> Accept (Some True)
    | False ->
      (match t0 with
       | ESort u0 ->
         (match s with
          | ESort v0 ->
            bind (level_equiv fuel0 u0 v0) (fun ok -> Accept (Some ok))
          | _ -> Accept None)
       | ELam (_, _, a, b) ->
         (match s with
          | ELam (_, _, c, d) ->
            bind (rec0.defeq_method g a c) (fun ok ->
              match ok with
              | True ->
                bind (rec0.defeq_method (push_binding g a None) b d)
                  (fun ok0 -> Accept (Some ok0))
              | False -> Accept (Some False))
          | _ -> Accept None)
       | EPi (_, _, a, b) ->
         (match s with
          | EPi (_, _, c, d) ->
            bind (rec0.defeq_method g a c) (fun ok ->
              match ok with
              | True ->
                bind (rec0.defeq_method (push_binding g a None) b d)
                  (fun ok0 -> Accept (Some ok0))
              | False -> Accept (Some False))
          | _ -> Accept None)
       | ELit a ->
         (match s with
          | ELit b -> Accept (Some (literal_eqb a b))
          | _ -> Accept None)
       | EMData a ->
         (match s with
          | EMData b ->
            bind (rec0.defeq_method g a b) (fun ok -> Accept (Some ok))
          | _ -> Accept None)
       | _ -> Accept None)

  (** val core_proof_irrel :
      methods -> nat -> context -> expr -> expr -> bool option result **)

  let core_proof_irrel rec0 fuel0 g t0 s =
    bind (rec0.infer_method g t0) (fun ty0 ->
      bind (sort_of rec0 g ty0) (fun sort ->
        bind (level_equiv fuel0 sort LZero) (fun is_prop ->
          match is_prop with
          | True ->
            bind (rec0.infer_method g s) (fun sty ->
              bind (rec0.defeq_method g ty0 sty) (fun ok -> Accept (Some ok)))
          | False -> Accept None)))

  (** val core_offset :
      (name -> environment -> declaration option) -> methods -> environment
      -> context -> expr -> expr -> bool option result **)

  let core_offset resolve rec0 env g t0 s =
    match core_nat_ready resolve env with
    | True ->
      let pred_of = fun e ->
        match e with
        | EBVar _ -> None
        | EFVar _ -> None
        | EMVar _ -> None
        | ESort _ -> None
        | EConst (_, _) -> None
        | EApp (e0, a) ->
          (match e0 with
           | EBVar _ -> None
           | EFVar _ -> None
           | EMVar _ -> None
           | ESort _ -> None
           | EConst (n0, l) ->
             (match l with
              | Nil ->
                (match name_eqb n0 core_succ_name with
                 | True -> Some a
                 | False -> None)
              | Cons (_, _) -> None)
           | _ -> None)
        | ELit l ->
          (match l with
           | LitNat n0 ->
             (match N.eqb n0 N0 with
              | True -> None
              | False -> Some (ELit (LitNat (N.pred n0))))
           | LitString _ -> None)
        | _ -> None
      in
      let zero0 = fun e ->
        match e with
        | EConst (n0, l) ->
          (match l with
           | Nil -> name_eqb n0 core_zero_name
           | Cons (_, _) -> False)
        | ELit l ->
          (match l with
           | LitNat n0 -> N.eqb n0 N0
           | LitString _ -> False)
        | _ -> False
      in
      (match match zero0 t0 with
             | True -> zero0 s
             | False -> False with
       | True -> Accept (Some True)
       | False ->
         (match pred_of t0 with
          | Some a ->
            (match pred_of s with
             | Some b ->
               bind (rec0.defeq_method g a b) (fun ok -> Accept (Some ok))
             | None -> Accept None)
          | None -> Accept None))
    | False -> Accept None

  (** val core_try_unfold_proj_app :
      methods -> context -> expr -> expr option result **)

  let core_try_unfold_proj_app rec0 g e =
    match fst (core_spine e Nil) with
    | EProj (_, _, _) ->
      bind (rec0.whnf_core_method False g e) (fun reduced -> Accept
        (match expr_eqb reduced e with
         | True -> None
         | False -> Some reduced))
    | _ -> Accept None

  (** val core_opposite_projection :
      (name -> environment -> declaration option) -> methods -> environment
      -> context -> expr -> expr -> (expr, expr) prod option result **)

  let core_opposite_projection resolve rec0 env g t0 s =
    match core_delta_info resolve env t0 with
    | Some _ ->
      (match core_delta_info resolve env s with
       | Some _ -> Accept None
       | None ->
         bind (core_try_unfold_proj_app rec0 g s) (fun reduced -> Accept
           (match reduced with
            | Some s' -> Some (Pair (t0, s'))
            | None -> None)))
    | None ->
      (match core_delta_info resolve env s with
       | Some _ ->
         bind (core_try_unfold_proj_app rec0 g t0) (fun reduced -> Accept
           (match reduced with
            | Some t' -> Some (Pair (t', s))
            | None -> None))
       | None -> Accept None)

  (** val core_lazy_delta :
      (name -> environment -> declaration option) -> nat -> methods -> nat ->
      environment -> name list -> context -> expr -> expr ->
      conversion_progress result **)

  let rec core_lazy_delta resolve rounds rec0 fuel0 env ps g t0 s =
    match rounds with
    | O -> Decline OutOfFuel
    | S rounds0 ->
      bind (core_quick rec0 fuel0 g t0 s) (fun quick ->
        match quick with
        | Some ok -> Accept (ConversionDone ok)
        | None ->
          bind (core_offset resolve rec0 env g t0 s) (fun offset ->
            match offset with
            | Some ok -> Accept (ConversionDone ok)
            | None ->
              let eligible =
                pair_probe_guard
                  (nat_probe_head resolve core_succ_name env
                    (core_spine t0 Nil))
                  (nat_probe_head resolve core_succ_name env
                    (core_spine s Nil))
                  (fun _ -> nat_probe_allowed rec0.method_mode t0 s)
              in
              bind
                (match eligible with
                 | True -> core_reduce_nat resolve rec0 fuel0 env g t0
                 | False -> Accept None)
                (fun tn ->
                match tn with
                | Some tn0 ->
                  bind (rec0.defeq_method g tn0 s) (fun ok -> Accept
                    (ConversionDone ok))
                | None ->
                  bind
                    (match eligible with
                     | True -> core_reduce_nat resolve rec0 fuel0 env g s
                     | False -> Accept None)
                    (fun sn ->
                    match sn with
                    | Some sn0 ->
                      bind (rec0.defeq_method g t0 sn0) (fun ok -> Accept
                        (ConversionDone ok))
                    | None ->
                      bind
                        (core_delta_congruent resolve rec0 fuel0 env g t0 s)
                        (fun same ->
                        match same with
                        | True -> Accept (ConversionDone True)
                        | False ->
                          bind
                            (core_opposite_projection resolve rec0 env g t0 s)
                            (fun projected ->
                            match projected with
                            | Some p0 ->
                              let Pair (tn0, sn0) = p0 in
                              core_lazy_delta resolve rounds0 rec0 fuel0 env
                                ps g tn0 sn0
                            | None ->
                              let Pair (unfold_left, unfold_right) =
                                core_delta_sides resolve env t0 s
                              in
                              bind
                                (match unfold_left with
                                 | True -> core_unfold resolve env ps t0
                                 | False -> Accept None)
                                (fun td ->
                                bind
                                  (match unfold_right with
                                   | True -> core_unfold resolve env ps s
                                   | False -> Accept None)
                                  (fun sd ->
                                  match td with
                                  | Some _ ->
                                    bind
                                      (match td with
                                       | Some e ->
                                         rec0.whnf_core_method True g e
                                       | None -> Accept t0)
                                      (fun tn0 ->
                                      bind
                                        (match sd with
                                         | Some e ->
                                           rec0.whnf_core_method True g e
                                         | None -> Accept s)
                                        (fun sn0 ->
                                        core_lazy_delta resolve rounds0 rec0
                                          fuel0 env ps g tn0 sn0))
                                  | None ->
                                    (match sd with
                                     | Some _ ->
                                       bind
                                         (match td with
                                          | Some e ->
                                            rec0.whnf_core_method True g e
                                          | None -> Accept t0)
                                         (fun tn0 ->
                                         bind
                                           (match sd with
                                            | Some e ->
                                              rec0.whnf_core_method True g e
                                            | None -> Accept s)
                                           (fun sn0 ->
                                           core_lazy_delta resolve rounds0
                                             rec0 fuel0 env ps g tn0 sn0))
                                     | None ->
                                       Accept (ConversionStuck (t0, s)))))))))))

  (** val core_finish_conversion :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> expr -> expr -> bool result **)

  let core_finish_conversion resolve rec0 fuel0 env g t0 s =
    let project = fun e ->
      let Pair (head, args) = core_spine e Nil in
      (match head with
       | EBVar _ -> Accept None
       | EFVar _ -> Accept None
       | EMVar _ -> Accept None
       | ESort _ -> Accept None
       | EConst (_, _) -> Accept None
       | EApp (_, _) -> Accept None
       | ELam (_, _, _, _) -> Accept None
       | EPi (_, _, _, _) -> Accept None
       | ELet (_, _, _, _, _) -> Accept None
       | ELit _ -> Accept None
       | EProj (owner, index, value) ->
         bind (core_reduce_projection resolve rec0 env g owner index value)
           (fun field -> Accept
           (option_map (fun f -> core_apps f args) field))
       | EMData _ -> Accept None)
    in
    bind (project t0) (fun tp ->
      bind (project s) (fun sp ->
        match tp with
        | Some t1 ->
          (match sp with
           | Some s0 -> rec0.defeq_method g t1 s0
           | None -> rec0.defeq_method g t1 s)
        | None ->
          (match sp with
           | Some s0 -> rec0.defeq_method g t0 s0
           | None -> compare_after_whnf resolve rec0 fuel0 env g t0 s)))

  (** val core_true_shortcut :
      (name -> environment -> declaration option) -> methods -> environment
      -> context -> expr -> expr -> bool result **)

  let core_true_shortcut resolve rec0 env g t0 s =
    match match match core_is_true s with
                | True -> true_probe_allowed rec0.method_mode t0
                | False -> False with
          | True -> core_bool_ready resolve env
          | False -> False with
    | True ->
      bind (rec0.whnf_method g t0) (fun tn -> Accept (core_is_true tn))
    | False -> Accept False

  (** val defeq_step :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> name list -> context -> expr -> expr -> bool result **)

  let defeq_step resolve rec0 fuel0 env ps g t0 s =
    let rec1 = inference_only rec0 in
    bind (core_quick rec1 fuel0 g t0 s) (fun quick ->
      match quick with
      | Some ok -> Accept ok
      | None ->
        bind (core_true_shortcut resolve rec1 env g t0 s) (fun shortcut ->
          match shortcut with
          | True -> Accept True
          | False ->
            bind (core_proof_irrel rec1 fuel0 g t0 s) (fun irrelevant ->
              match irrelevant with
              | Some ok -> Accept ok
              | None ->
                bind (rec1.whnf_core_method True g t0) (fun tn ->
                  bind (rec1.whnf_core_method True g s) (fun sn ->
                    bind
                      (core_lazy_delta resolve (S fuel0) rec1 fuel0 env ps g
                        tn sn)
                      (fun progress ->
                      match progress with
                      | ConversionDone ok -> Accept ok
                      | ConversionStuck (tn0, sn0) ->
                        core_finish_conversion resolve rec1 fuel0 env g tn0
                          sn0))))))

  (** val checker_mode :
      (name -> environment -> declaration option) -> reduction_mode -> nat ->
      environment -> name list -> methods **)

  let rec checker_mode resolve mode fuel0 env ps =
    match fuel0 with
    | O ->
      { infer_method = (fun _ _ -> Decline OutOfFuel); infer_type_method =
        (fun _ _ -> Decline OutOfFuel); whnf_method = (fun _ _ -> Decline
        OutOfFuel); whnf_core_method = (fun _ _ _ -> Decline OutOfFuel);
        defeq_method = (fun _ _ _ -> Decline OutOfFuel); method_mode = mode;
        eager_defeq_method = (fun _ _ _ -> Decline OutOfFuel) }
    | S n0 ->
      { infer_method = (fun g e ->
        let rec0 = checker_mode resolve mode n0 env ps in
        infer_step resolve rec0 n0 env ps True g e); infer_type_method =
        (fun g e ->
        let rec0 = checker_mode resolve mode n0 env ps in
        infer_step resolve rec0 n0 env ps False g e); whnf_method =
        (fun g e ->
        let rec0 = checker_mode resolve mode n0 env ps in
        whnf_loop resolve (whnf_round_limit mode) rec0 n0 env ps g e);
        whnf_core_method = (fun cheap g e ->
        let rec0 = checker_mode resolve mode n0 env ps in
        whnf_core_step resolve rec0 n0 env ps cheap g e); defeq_method =
        (fun g t0 s ->
        let rec0 = checker_mode resolve mode n0 env ps in
        defeq_step resolve rec0 n0 env ps g t0 s); method_mode = mode;
        eager_defeq_method = (fun g t0 s ->
        let rec0 = checker_mode resolve EagerReduction n0 env ps in
        defeq_step resolve rec0 n0 env ps g t0 s) }
 end

(** val checker_with_lookup_mode :
    reduction_mode -> nat -> environment -> declaration_lookup -> name list
    -> methods **)

let checker_with_lookup_mode mode fuel0 env lookup ps =
  Accessor.checker_mode (fun n0 _ -> lookup n0) mode fuel0 env ps

(** val checker_with_lookup :
    nat -> environment -> declaration_lookup -> name list -> methods **)

let checker_with_lookup =
  checker_with_lookup_mode NormalReduction

(** val supported_with_lookup :
    declaration_lookup -> environment -> expr -> bool **)

let supported_with_lookup lookup env e =
  Accessor.core_supported (fun n0 _ -> lookup n0) env e

(** val defeq_with_methods :
    declaration_lookup -> environment -> methods -> context -> expr -> expr
    -> bool result **)

let defeq_with_methods lookup env m g t0 s =
  match match supported_with_lookup lookup env t0 with
        | True -> supported_with_lookup lookup env s
        | False -> False with
  | True -> m.defeq_method g t0 s
  | False -> Decline UnsupportedExpression

(** val prepared_whnf :
    declaration_lookup -> nat -> environment -> name list -> context -> expr
    -> expr result **)

let prepared_whnf lookup fuel0 env ps g e =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S _ ->
    (match supported_with_lookup lookup env e with
     | True -> (checker_with_lookup fuel0 env lookup ps).whnf_method g e
     | False -> Decline UnsupportedExpression)

(** val prepared_defeq :
    declaration_lookup -> nat -> environment -> name list -> context -> expr
    -> expr -> bool result **)

let prepared_defeq lookup fuel0 env ps g t0 s =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S _ ->
    defeq_with_methods lookup env (checker_with_lookup fuel0 env lookup ps) g
      t0 s

(** val lookup_step :
    declaration_lookup -> methods -> nat -> environment -> name list -> bool
    -> context -> expr -> expr result **)

let lookup_step lookup rec0 fuel0 env ps checking g e =
  Accessor.infer_step (fun n0 _ -> lookup n0) rec0 fuel0 env ps checking g e

(** val lookup_eval :
    declaration_lookup -> methods -> nat -> environment -> name list ->
    context -> dag_arena -> bool -> input_query -> expr result **)

let lookup_eval lookup rec0 fuel0 env ps base arena checking = function
| Pair (id, path) ->
  bind (path_from base arena.arena_scope path) (fun g ->
    bind (scope_ref arena.arena_scope id) (fun e ->
      lookup_step lookup rec0 fuel0 env ps checking g e.scope_expr))

(** val node_action0 :
    declaration_lookup -> methods -> nat -> environment -> name list ->
    dag_arena -> (bool -> input_query -> expr action) -> bool -> context_path
    -> context -> dag_node -> expr action **)

let node_action0 lookup rec0 fuel0 env ps arena call0 checking path g node0 = match node0 with
| DApp (f, a) ->
  then_do (pure (scope_ref arena.arena_scope a)) (fun ae ->
    then_do (call0 checking (Pair (f, path))) (fun ft ->
      then_do (pure (rec0.whnf_method g ft)) (fun ft0 ->
        match ft0 with
        | EPi (_, _, domain, body) ->
          then_do
            (match checking with
             | True ->
               then_do (call0 True (Pair (a, path))) (fun arg_type ->
                 then_do
                   (pure
                     (application_type_defeq rec0 g ae.scope_expr domain
                       arg_type))
                   (fun ok -> pure (require ok TypeMismatch)))
             | False -> pure (Accept Tt))
            (fun _ -> pure (Accept (instantiate body ae.scope_expr)))
        | _ -> pure (Reject ExpectedPi))))
| DLam (n0, bi, a, b) ->
  then_do (pure (scope_ref arena.arena_scope a)) (fun ae ->
    then_do
      (match checking with
       | True ->
         then_do (call0 True (Pair (a, path))) (fun dt ->
           then_do (pure (rec0.whnf_method g dt)) (fun dt0 ->
             pure
               (match dt0 with
                | EBVar _ -> Reject ExpectedSort
                | EFVar _ -> Reject ExpectedSort
                | EMVar _ -> Reject ExpectedSort
                | ESort _ -> Accept Tt
                | _ -> Reject ExpectedSort)))
       | False -> pure (Accept Tt))
      (fun _ ->
      then_do (call0 checking (Pair (b, (Cons ((Pair (a, None)), path)))))
        (fun bt0 -> pure (Accept (EPi (n0, bi, ae.scope_expr, bt0))))))
| DPi (_, _, a, b) ->
  then_do (pure (scope_ref arena.arena_scope a)) (fun ae ->
    then_do (call0 checking (Pair (a, path))) (fun dt ->
      then_do (pure (rec0.whnf_method g dt)) (fun dt0 ->
        then_do
          (pure
            (match dt0 with
             | ESort u0 -> Accept u0
             | _ -> Reject ExpectedSort))
          (fun u0 ->
          let gb = push_binding g ae.scope_expr None in
          then_do
            (call0 checking (Pair (b, (Cons ((Pair (a, None)), path)))))
            (fun bt0 ->
            then_do (pure (rec0.whnf_method gb bt0)) (fun bt1 ->
              then_do
                (pure
                  (match bt1 with
                   | ESort v0 -> Accept v0
                   | _ -> Reject ExpectedSort))
                (fun v0 -> pure (Accept (ESort (LIMax (u0, v0)))))))))))
| DLet (_, a, v0, b, _) ->
  then_do (pure (scope_ref arena.arena_scope a)) (fun ae ->
    then_do (pure (scope_ref arena.arena_scope v0)) (fun ve ->
      then_do
        (match checking with
         | True ->
           then_do (call0 True (Pair (a, path))) (fun dt ->
             then_do (pure (rec0.whnf_method g dt)) (fun dt0 ->
               then_do
                 (pure
                   (match dt0 with
                    | EBVar _ -> Reject ExpectedSort
                    | EFVar _ -> Reject ExpectedSort
                    | EMVar _ -> Reject ExpectedSort
                    | ESort _ -> Accept Tt
                    | _ -> Reject ExpectedSort))
                 (fun _ ->
                 then_do (call0 True (Pair (v0, path))) (fun vt ->
                   then_do (pure (rec0.defeq_method g vt ae.scope_expr))
                     (fun ok -> pure (require ok TypeMismatch))))))
         | False -> pure (Accept Tt))
        (fun _ ->
        then_do
          (call0 checking (Pair (b, (Cons ((Pair (a, (Some v0))), path)))))
          (fun bt0 -> pure (Accept (instantiate bt0 ve.scope_expr))))))
| DMData a -> call0 checking (Pair (a, path))
| _ ->
  then_do (pure (scope_node arena.arena_scope node0)) (fun e ->
    pure (lookup_step lookup rec0 fuel0 env ps checking g e.scope_expr))

(** val uncached_action0 :
    declaration_lookup -> methods -> nat -> environment -> name list ->
    context -> dag_arena -> (bool -> input_query -> expr action) -> bool ->
    input_query -> expr action **)

let uncached_action0 lookup rec0 fuel0 env ps base arena call0 checking = function
| Pair (id, path) ->
  then_do (pure (path_from base arena.arena_scope path)) (fun g ->
    then_do (pure (scope_ref arena.arena_scope id)) (fun e ->
      match PositiveMap.find id arena.arena_nodes with
      | Some node0 ->
        node_action0 lookup rec0 fuel0 env ps arena call0 checking path g
          node0
      | None ->
        pure (lookup_step lookup rec0 fuel0 env ps checking g e.scope_expr)))

(** val memo_infer0 :
    declaration_lookup -> methods -> nat -> environment -> name list ->
    context -> dag_arena -> nat -> bool -> input_query -> expr action **)

let rec memo_infer0 lookup rec0 fuel0 env ps base arena budget checking q0 =
  memo_action checking q0 (fun cache ->
    match budget with
    | O ->
      pure (lookup_eval lookup rec0 fuel0 env ps base arena checking q0) cache
    | S n0 ->
      uncached_action0 lookup rec0 fuel0 env ps base arena
        (memo_infer0 lookup rec0 fuel0 env ps base arena n0) checking q0 cache)

(** val run_memo_infer0 :
    declaration_lookup -> methods -> nat -> environment -> name list ->
    context -> dag_arena -> nat -> bool -> input_query -> expr result **)

let run_memo_infer0 lookup rec0 fuel0 env ps base arena budget checking q0 =
  fst
    (memo_infer0 lookup rec0 fuel0 env ps base arena budget checking q0
      empty_step_cache)

(** val suffix_zero : ascii **)

let suffix_zero =
  Ascii (False, False, False, False, False, False, False, False)

(** val suffix_bit : bool -> positive -> positive **)

let suffix_bit b p0 =
  match b with
  | True -> XI p0
  | False -> XO p0

(** val suffix_byte : ascii -> positive -> positive **)

let suffix_byte c p0 =
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = c in
  suffix_bit b0
    (suffix_bit b1
      (suffix_bit b2
        (suffix_bit b3
          (suffix_bit b4 (suffix_bit b5 (suffix_bit b6 (suffix_bit b7 p0)))))))

(** val suffix_xor_rotate : ascii -> ascii -> ascii **)

let suffix_xor_rotate a c =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (c0, c1, c2, c3, c4, c5, c6, c7) = c in
  Ascii ((xorb a7 c0), (xorb a0 c1), (xorb a1 c2), (xorb a2 c3),
  (xorb a3 c4), (xorb a4 c5), (xorb a5 c6), (xorb a6 c7))

(** val suffix_fold8 : ascii -> string -> positive **)

let rec suffix_fold8 a = function
| EmptyString -> suffix_byte a XH
| String (c, rest) -> suffix_fold8 (suffix_xor_rotate a c) rest

(** val suffix_lift : (string -> positive) -> name -> n **)

let suffix_lift f = function
| NameAnon -> N0
| NameStr (_, s) -> Npos (f s)
| NameNum (_, value) ->
  N.coq_land value (Npos (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI (XI
    (XI (XI XH))))))))))))))))

(** val suffix_bitfold8 : name -> n **)

let suffix_bitfold8 =
  suffix_lift (suffix_fold8 suffix_zero)

(** val at_least : nat -> environment -> bool **)

let rec at_least count env =
  match count with
  | O -> True
  | S count0 ->
    (match env with
     | Nil -> False
     | Cons (_, rest) -> at_least count0 rest)

(** val use_index : nat -> environment -> bool **)

let use_index fuel0 env =
  match fuel0 with
  | O -> False
  | S _ ->
    at_least (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) env

type dag_admission_kind =
| DagDefinition of reducibility_hints
| DagTheorem
| DagOpaque

(** val linear_env_admit :
    dag_admission_kind -> nat -> nat -> environment -> name -> name list ->
    (PositiveMap.key, dag_node) prod list -> positive -> positive ->
    environment result **)

let linear_env_admit kind budget fuel0 env n0 ps rows0 tr br =
  match kind with
  | DagDefinition hints ->
    admit_dag_definition hints budget fuel0 env n0 ps rows0 tr br
  | DagTheorem -> admit_dag_theorem budget fuel0 env n0 ps rows0 tr br
  | DagOpaque -> admit_dag_opaque budget fuel0 env n0 ps rows0 tr br

module PreparedDag =
 struct
  (** val input_infer :
      declaration_lookup -> environment -> nat -> nat -> name list ->
      dag_arena -> positive -> expr result **)

  let input_infer lookup env budget fuel0 ps arena root =
    match fuel0 with
    | O -> Decline OutOfFuel
    | S n0 ->
      run_memo_infer0 lookup (checker_with_lookup n0 env lookup ps) n0 env ps
        empty_context arena budget True (Pair (root, Nil))

  (** val input_header :
      declaration_lookup -> environment -> nat -> nat -> name -> name list ->
      dag_arena -> positive -> scope_entry -> unit0 result **)

  let input_header lookup env budget fuel0 n0 ps arena root entry =
    match lookup n0 with
    | Some _ -> Reject DuplicateDeclaration
    | None ->
      (match negb (names_unique ps) with
       | True -> Reject DuplicateUniverse
       | False ->
         (match negb (entry_scoped O entry) with
          | True -> Reject MalformedDeclaration
          | False ->
            bind (input_infer lookup env budget fuel0 ps arena root)
              (fun inferred ->
              bind (prepared_whnf lookup fuel0 env ps empty_context inferred)
                (fun reduced ->
                match reduced with
                | ESort _ -> Accept Tt
                | _ -> Reject ExpectedSort))))

  (** val input_check :
      declaration_lookup -> environment -> nat -> nat -> name list ->
      dag_arena -> positive -> positive -> expr -> unit0 result **)

  let input_check lookup env budget fuel0 ps arena tr br ty0 =
    bind (input_infer lookup env budget fuel0 ps arena tr) (fun type_type ->
      bind
        ((checker_with_lookup fuel0 env lookup ps).whnf_method empty_context
          type_type)
        (fun type_type0 ->
        bind
          (match type_type0 with
           | EBVar _ -> Reject ExpectedSort
           | EFVar _ -> Reject ExpectedSort
           | EMVar _ -> Reject ExpectedSort
           | ESort u0 -> Accept u0
           | _ -> Reject ExpectedSort)
          (fun _ ->
          bind (input_infer lookup env budget fuel0 ps arena br)
            (fun body_type ->
            bind
              (prepared_defeq lookup fuel0 env ps empty_context body_type ty0)
              (fun ok -> require ok TypeMismatch)))))

  (** val input_proposition :
      declaration_lookup -> environment -> nat -> nat -> name list ->
      dag_arena -> positive -> unit0 result **)

  let input_proposition lookup env budget fuel0 ps arena root =
    bind (input_infer lookup env budget fuel0 ps arena root) (fun inferred ->
      bind (prepared_whnf lookup fuel0 env ps empty_context inferred)
        (fun reduced ->
        match reduced with
        | ESort u0 ->
          bind (level_equiv fuel0 u0 LZero) (fun is_zero ->
            match is_zero with
            | True -> Accept Tt
            | False -> Reject MalformedDeclaration)
        | _ -> Reject ExpectedSort))

  (** val checked_constant :
      declaration_lookup -> environment -> nat -> nat -> name -> name list ->
      dag_arena -> positive -> positive -> scope_entry -> scope_entry ->
      decl_kind -> declaration list result **)

  let checked_constant lookup env budget fuel0 n0 ps arena tr br ty0 body kind =
    bind (input_header lookup env budget fuel0 n0 ps arena tr ty0) (fun _ ->
      bind
        (match entry_scoped O body with
         | True ->
           input_check lookup env budget fuel0 ps arena tr br ty0.scope_expr
         | False -> Reject MalformedDeclaration)
        (fun _ -> Accept (Cons ({ decl_name = n0; decl_params = ps;
        decl_type = ty0.scope_expr; decl_value = (Some body.scope_expr);
        decl_kind_of = kind; decl_hints = HintOpaque }, env))))

  (** val in_arena :
      declaration_lookup -> environment -> dag_admission_kind -> nat -> nat
      -> name -> name list -> dag_arena -> positive -> positive ->
      scope_entry -> scope_entry -> declaration list result **)

  let in_arena lookup env kind budget fuel0 n0 ps arena tr br ty0 body =
    match kind with
    | DagDefinition hints ->
      bind (input_header lookup env budget fuel0 n0 ps arena tr ty0)
        (fun _ ->
        bind (require (entry_scoped O body) MalformedDeclaration) (fun _ ->
          bind
            (input_check lookup env budget fuel0 ps arena tr br
              ty0.scope_expr)
            (fun _ ->
            bind
              (classify_primitive fuel0 env n0 ps ty0.scope_expr
                body.scope_expr)
              (fun primitive ->
              let kind0 =
                match primitive with
                | Some p0 -> DPrimitive p0
                | None -> DDefinition
              in
              Accept (Cons ({ decl_name = n0; decl_params = ps; decl_type =
              ty0.scope_expr; decl_value = (Some body.scope_expr);
              decl_kind_of = kind0; decl_hints = hints }, env))))))
    | DagTheorem ->
      (match name_mem n0 reserved_names with
       | True -> Reject MalformedDeclaration
       | False ->
         bind (input_header lookup env budget fuel0 n0 ps arena tr ty0)
           (fun _ ->
           bind (input_proposition lookup env budget fuel0 ps arena tr)
             (fun _ ->
             checked_constant lookup env budget fuel0 n0 ps arena tr br ty0
               body DTheorem)))
    | DagOpaque ->
      (match name_mem n0 reserved_names with
       | True -> Reject MalformedDeclaration
       | False ->
         checked_constant lookup env budget fuel0 n0 ps arena tr br ty0 body
           DOpaque)
 end

(** val cheap_header_error :
    environment -> name -> name list -> scope_entry -> reject_reason option **)

let cheap_header_error env n0 ps ty0 =
  let defect =
    match negb (names_unique ps) with
    | True -> Some DuplicateUniverse
    | False ->
      (match negb (entry_scoped O ty0) with
       | True -> Some MalformedDeclaration
       | False -> None)
  in
  (match defect with
   | Some reason ->
     (match find_decl n0 env with
      | Some _ -> Some DuplicateDeclaration
      | None -> Some reason)
   | None -> None)

(** val early_header_error :
    dag_admission_kind -> environment -> name -> name list -> scope_entry ->
    reject_reason option **)

let early_header_error kind env n0 ps ty0 =
  match kind with
  | DagDefinition _ -> cheap_header_error env n0 ps ty0
  | _ ->
    (match name_mem n0 reserved_names with
     | True -> Some MalformedDeclaration
     | False -> cheap_header_error env n0 ps ty0)

(** val admit_with_preparation :
    (unit0 -> declaration_lookup) -> dag_admission_kind -> nat -> nat ->
    environment -> name -> name list -> (PositiveMap.key, dag_node) prod list
    -> positive -> positive -> environment result **)

let admit_with_preparation prepare kind budget fuel0 env n0 ps rows0 tr br =
  bind (arena_build empty_arena rows0) (fun arena ->
    bind (scope_ref arena.arena_scope tr) (fun ty0 ->
      bind (scope_ref arena.arena_scope br) (fun body ->
        match early_header_error kind env n0 ps ty0 with
        | Some reason -> Reject reason
        | None ->
          let lookup = prepare Tt in
          PreparedDag.in_arena lookup env kind budget fuel0 n0 ps arena tr br
            ty0 body)))

(** val indexed_admit :
    (name -> n) -> dag_admission_kind -> nat -> nat -> environment -> name ->
    name list -> (PositiveMap.key, dag_node) prod list -> positive ->
    positive -> environment result **)

let indexed_admit hash kind budget fuel0 env n0 ps rows0 tr br =
  admit_with_preparation (fun _ -> prepare_lookup hash env) kind budget fuel0
    env n0 ps rows0 tr br

(** val indexed_dag_admit :
    dag_admission_kind -> nat -> nat -> environment -> name -> name list ->
    (PositiveMap.key, dag_node) prod list -> positive -> positive ->
    environment result **)

let indexed_dag_admit kind budget fuel0 env n0 ps rows0 tr br =
  match use_index fuel0 env with
  | True ->
    indexed_admit suffix_bitfold8 kind budget fuel0 env n0 ps rows0 tr br
  | False -> linear_env_admit kind budget fuel0 env n0 ps rows0 tr br

module Metadata =
 struct
  (** val fuel : nat **)

  let fuel =
    S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val label : string -> name **)

  let label s =
    NameStr ((NameStr (NameAnon, (String ((Ascii (True, False, True, True,
      False, False, True, False)), (String ((Ascii (True, False, True, False,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (True, False, False, False,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      False, True, True, False)), (String ((Ascii (True, False, False, False,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), (String ((Ascii (True, False, False, False,
      False, True, True, False)), (String ((Ascii (False, False, True, False,
      True, False, True, False)), (String ((Ascii (True, False, True, False,
      False, True, True, False)), (String ((Ascii (True, True, False, False,
      True, True, True, False)), (String ((Ascii (False, False, True, False,
      True, True, True, False)), EmptyString)))))))))))))))))))))))))), s)

  (** val pi : expr -> expr -> expr **)

  let pi a b =
    EPi (NameAnon, BDefault, a, b)

  (** val lam : expr -> expr -> expr **)

  let lam a b =
    ELam (NameAnon, BDefault, a, b)

  (** val type0 : expr **)

  let type0 =
    ESort (LSucc LZero)

  (** val type1 : expr **)

  let type1 =
    ESort (LSucc (LSucc LZero))

  (** val decl : name -> name list -> expr -> decl_kind -> declaration **)

  let decl n0 ps ty0 kind =
    { decl_name = n0; decl_params = ps; decl_type = ty0; decl_value = None;
      decl_kind_of = kind; decl_hints = HintOpaque }

  (** val seed_ind :
      name -> name list -> expr -> nat -> name list -> declaration **)

  let seed_ind n0 ps ty0 np ctors =
    decl n0 ps ty0 (DInductive { ind_num_params = np; ind_num_indices = O;
      ind_all = (Cons (n0, Nil)); ind_ctors = ctors; ind_num_nested = O;
      ind_is_rec = False; ind_is_reflexive = False; ind_is_unsafe = False })

  (** val seed_ctor :
      name -> name -> name list -> expr -> nat -> nat -> nat -> declaration **)

  let seed_ctor n0 owner ps ty0 np i fields =
    decl n0 ps ty0 (DConstructor { ctor_induct = owner; ctor_index = i;
      ctor_num_params = np; ctor_num_fields = fields; ctor_is_unsafe =
      False })

  (** val is_ind : declaration -> bool **)

  let is_ind d =
    match d.decl_kind_of with
    | DInductive _ -> True
    | _ -> False

  (** val is_ctor : declaration -> bool **)

  let is_ctor d =
    match d.decl_kind_of with
    | DConstructor _ -> True
    | _ -> False

  (** val is_rec : declaration -> bool **)

  let is_rec d =
    match d.decl_kind_of with
    | DRecursor _ -> True
    | _ -> False

  (** val admit_generated :
      environment -> declaration list -> environment result **)

  let admit_generated env ds =
    admit_inductive fuel env (filter is_ind ds) (filter is_ctor ds)
      (filter is_rec ds)

  (** val checked_block :
      environment -> name list -> nat -> ind_spec list -> environment result **)

  let checked_block env ps np specs =
    bind (derive_inductive fuel env ps np specs) (fun generated ->
      admit_generated env generated)

  (** val padding : nat -> environment result **)

  let rec padding = function
  | O -> Accept Nil
  | S n0 ->
    bind (padding n0) (fun env ->
      admit fuel env (InputAxiom ((NameNum
        ((label (String ((Ascii (False, False, False, False, True, True,
           True, False)), (String ((Ascii (True, False, False, False, False,
           True, True, False)), (String ((Ascii (False, False, True, False,
           False, True, True, False)), EmptyString))))))),
        (N.of_nat n0))), Nil, (ESort LZero), False)))

  (** val nat_spec : ind_spec **)

  let nat_spec =
    { spec_decl =
      (seed_ind core_nat_name Nil type0 O (Cons (core_zero_name, (Cons
        (core_succ_name, Nil)))));
      spec_ctors = (Cons
      ((seed_ctor core_zero_name core_nat_name Nil core_nat O O O), (Cons
      ((seed_ctor core_succ_name core_nat_name Nil (pi core_nat core_nat) O
         (S O) (S O)),
      Nil)))) }

  (** val u_name : name **)

  let u_name =
    NameStr (NameAnon, (String ((Ascii (True, False, True, False, True, True,
      True, False)), EmptyString)))

  (** val u : level **)

  let u =
    LParam u_name

  (** val refl_name : name **)

  let refl_name =
    NameStr (q_eq_name, (String ((Ascii (False, True, False, False, True,
      True, True, False)), (String ((Ascii (True, False, True, False, False,
      True, True, False)), (String ((Ascii (False, True, True, False, False,
      True, True, False)), (String ((Ascii (False, False, True, True, False,
      True, True, False)), EmptyString)))))))))

  (** val eq_spec : ind_spec **)

  let eq_spec =
    { spec_decl =
      (seed_ind q_eq_name (Cons (u_name, Nil)) (quotient_eq_type u) (S (S O))
        (Cons (refl_name, Nil)));
      spec_ctors = (Cons
      ((seed_ctor refl_name q_eq_name (Cons (u_name, Nil))
         (quotient_eq_refl_type u) (S (S O)) O O),
      Nil)) }

  (** val box_name : name **)

  let box_name =
    label (String ((Ascii (False, True, False, False, False, False, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, False, False, True, True, True, True,
      False)), EmptyString))))))

  (** val box_mk : name **)

  let box_mk =
    NameStr (box_name, (String ((Ascii (True, False, True, True, False, True,
      True, False)), (String ((Ascii (True, True, False, True, False, True,
      True, False)), EmptyString)))))

  (** val box : expr **)

  let box =
    EConst (box_name, Nil)

  (** val box_spec : ind_spec **)

  let box_spec =
    { spec_decl = (seed_ind box_name Nil type0 O (Cons (box_mk, Nil)));
      spec_ctors = (Cons
      ((seed_ctor box_mk box_name Nil (pi core_nat box) O O (S O)), Nil)) }

  (** val dep_name : name **)

  let dep_name =
    label (String ((Ascii (False, False, True, False, False, False, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (False, False, False, False, True, True, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (False, True, True, True, False, True, True,
      False)), (String ((Ascii (False, False, True, False, False, True, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (False, True, True, True, False, True, True,
      False)), (String ((Ascii (False, False, True, False, True, True, True,
      False)), EmptyString))))))))))))))))))

  (** val dep_mk : name **)

  let dep_mk =
    NameStr (dep_name, (String ((Ascii (True, False, True, True, False, True,
      True, False)), (String ((Ascii (True, True, False, True, False, True,
      True, False)), EmptyString)))))

  (** val dep : expr **)

  let dep =
    EConst (dep_name, Nil)

  (** val dep_spec : ind_spec **)

  let dep_spec =
    { spec_decl = (seed_ind dep_name Nil type1 O (Cons (dep_mk, Nil)));
      spec_ctors = (Cons
      ((seed_ctor dep_mk dep_name Nil (pi type0 (pi (EBVar O) dep)) O O (S (S
         O))),
      Nil)) }

  (** val padded_env : environment result **)

  let padded_env =
    padding (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

  (** val nat_env : environment result **)

  let nat_env =
    bind padded_env (fun env ->
      checked_block env Nil O (Cons (nat_spec, Nil)))

  (** val eq_env : environment result **)

  let eq_env =
    bind nat_env (fun env ->
      checked_block env (Cons (u_name, Nil)) (S (S O)) (Cons (eq_spec, Nil)))

  (** val structure_env : environment result **)

  let structure_env =
    bind eq_env (fun env ->
      bind (checked_block env Nil O (Cons (box_spec, Nil))) (fun env0 ->
        checked_block env0 Nil O (Cons (dep_spec, Nil))))

  (** val add_quot : environment -> quotient_kind -> environment result **)

  let add_quot env k =
    let d = canonical_quotient k in
    admit_quotient fuel env d.decl_name d.decl_params d.decl_type k

  (** val base_env : environment result **)

  let base_env =
    bind structure_env (fun env ->
      bind (add_quot env QType) (fun env0 ->
        bind (add_quot env0 QCtor) (fun env1 ->
          bind (add_quot env1 QLift) (fun env2 -> add_quot env2 QInd))))

  (** val fold : expr -> expr -> expr -> expr -> expr **)

  let fold ty0 z0 step n0 =
    core_apps (EConst ((rec_name core_nat_name), (Cons ((LSucc LZero),
      Nil)))) (Cons ((lam core_nat ty0), (Cons (z0, (Cons (step, (Cons (n0,
      Nil))))))))

  (** val add_body : expr **)

  let add_body =
    lam core_nat
      (lam core_nat
        (fold core_nat (EBVar (S O))
          (lam core_nat (lam core_nat (primitive_succ (EBVar O)))) (EBVar O)))

  (** val false_add : expr **)

  let false_add =
    lam core_nat (lam core_nat (EBVar (S O)))

  (** val rec_value : expr **)

  let rec_value =
    fold core_nat primitive_one (lam core_nat (lam core_nat (EBVar O)))
      primitive_two

  (** val eq_nat : expr -> expr -> expr **)

  let eq_nat a b =
    core_apps (EConst (q_eq_name, (Cons ((LSucc LZero), Nil)))) (Cons
      (core_nat, (Cons (a, (Cons (b, Nil))))))

  (** val refl_nat : expr -> expr **)

  let refl_nat a =
    core_apps (EConst (refl_name, (Cons ((LSucc LZero), Nil)))) (Cons
      (core_nat, (Cons (a, Nil))))

  (** val indexed_rec_value : expr **)

  let indexed_rec_value =
    core_apps (EConst ((rec_name q_eq_name), (Cons ((LSucc LZero), (Cons
      ((LSucc LZero), Nil)))))) (Cons (core_nat, (Cons (primitive_one, (Cons
      ((lam core_nat (lam (eq_nat primitive_one (EBVar O)) core_nat)), (Cons
      (primitive_one, (Cons (primitive_one, (Cons ((refl_nat primitive_one),
      Nil))))))))))))

  (** val box_value : expr **)

  let box_value =
    EApp ((EConst (box_mk, Nil)), primitive_one)

  (** val dep_value : expr **)

  let dep_value =
    core_apps (EConst (dep_mk, Nil)) (Cons (core_nat, (Cons (primitive_one,
      Nil))))

  (** val project_box : expr **)

  let project_box =
    EProj (box_name, O, box_value)

  (** val project_dep : expr **)

  let project_dep =
    EProj (dep_name, (S O), dep_value)

  (** val project_dep_fn : expr **)

  let project_dep_fn =
    lam dep (EProj (dep_name, (S O), (EBVar O)))

  (** val project_dep_type : expr **)

  let project_dep_type =
    pi dep (EProj (dep_name, O, (EBVar O)))

  (** val relation : expr **)

  let relation =
    lam core_nat (lam core_nat (eq_nat (EBVar (S O)) (EBVar O)))

  (** val identity : expr **)

  let identity =
    lam core_nat (EBVar O)

  (** val respect : expr **)

  let respect =
    lam core_nat
      (lam core_nat (lam (eq_nat (EBVar (S O)) (EBVar O)) (EBVar O)))

  (** val quot : expr **)

  let quot =
    core_apps (EConst (q_name, (Cons ((LSucc LZero), Nil)))) (Cons (core_nat,
      (Cons (relation, Nil))))

  (** val quot_value : expr **)

  let quot_value =
    core_apps (EConst (q_mk_name, (Cons ((LSucc LZero), Nil)))) (Cons
      (core_nat, (Cons (relation, (Cons (primitive_one, Nil))))))

  (** val lift_value : expr **)

  let lift_value =
    core_apps (EConst (q_lift_name, (Cons ((LSucc LZero), (Cons ((LSucc
      LZero), Nil)))))) (Cons (core_nat, (Cons (relation, (Cons (core_nat,
      (Cons (identity, (Cons (respect, (Cons (quot_value, Nil))))))))))))

  (** val ind_value : expr **)

  let ind_value =
    core_apps (EConst (q_ind_name, (Cons ((LSucc LZero), Nil)))) (Cons
      (core_nat, (Cons (relation, (Cons
      ((lam quot (eq_nat primitive_one primitive_one)), (Cons
      ((lam core_nat (refl_nat primitive_one)), (Cons (quot_value,
      Nil))))))))))

  (** val add_value : expr **)

  let add_value =
    primitive_call PNatAdd (Cons (primitive_one, (Cons (primitive_one, Nil))))

  (** val with_add : environment result **)

  let with_add =
    bind base_env (fun env ->
      admit fuel env (InputDefinition (HintOpaque, (primitive_name PNatAdd),
        Nil, (primitive_signature PNatAdd), add_body, InputSafe)))

  (** val fixture_shape_checks : bool result **)

  let fixture_shape_checks =
    bind base_env (fun env -> Accept
      (match core_nat_ready env with
       | True ->
         (match find_decl (rec_name q_eq_name) env with
          | Some r ->
            (match find_decl dep_mk env with
             | Some c ->
               (match r.decl_kind_of with
                | DRecursor r0 ->
                  (match c.decl_kind_of with
                   | DConstructor c0 ->
                     (match match eqb r0.rec_num_indices (S O) with
                            | True -> eqb r0.rec_num_params (S (S O))
                            | False -> False with
                      | True -> eqb c0.ctor_num_fields (S (S O))
                      | False -> False)
                   | _ -> False)
                | _ -> False)
             | None -> False)
          | None -> False)
       | False -> False))

  (** val without : name -> declaration list -> declaration list **)

  let without n0 env =
    filter (fun d -> negb (name_eqb n0 d.decl_name)) env

  (** val unsafe_shadow : name -> environment -> declaration list **)

  let unsafe_shadow n0 env =
    match find_decl n0 env with
    | Some d ->
      Cons ({ decl_name = d.decl_name; decl_params = d.decl_params;
        decl_type = d.decl_type; decl_value = d.decl_value; decl_kind_of =
        (DUnsafe d.decl_kind_of); decl_hints = d.decl_hints }, env)
    | None -> env

  (** val corrupt_fields : declaration -> declaration **)

  let corrupt_fields d =
    match d.decl_kind_of with
    | DConstructor c ->
      { decl_name = d.decl_name; decl_params = d.decl_params; decl_type =
        d.decl_type; decl_value = d.decl_value; decl_kind_of = (DConstructor
        { ctor_induct = c.ctor_induct; ctor_index = c.ctor_index;
        ctor_num_params = c.ctor_num_params; ctor_num_fields = (S
        c.ctor_num_fields); ctor_is_unsafe = c.ctor_is_unsafe });
        decl_hints = d.decl_hints }
    | _ -> d

  (** val corrupt_rule : declaration -> declaration **)

  let corrupt_rule d =
    match d.decl_kind_of with
    | DRecursor r ->
      { decl_name = d.decl_name; decl_params = d.decl_params; decl_type =
        d.decl_type; decl_value = d.decl_value; decl_kind_of = (DRecursor
        { rec_all = r.rec_all; rec_num_params = r.rec_num_params;
        rec_num_indices = r.rec_num_indices; rec_num_motives =
        r.rec_num_motives; rec_num_minors = r.rec_num_minors; rec_rules =
        Nil; rec_k = r.rec_k; rec_is_unsafe = r.rec_is_unsafe });
        decl_hints = d.decl_hints }
    | _ -> d

  (** val rejected_ctor_metadata : environment result **)

  let rejected_ctor_metadata =
    bind padded_env (fun env ->
      bind (derive_inductive fuel env Nil O (Cons (nat_spec, Nil)))
        (fun ds -> admit_generated env (map corrupt_fields ds)))

  (** val rejected_rec_metadata : environment result **)

  let rejected_rec_metadata =
    bind padded_env (fun env ->
      bind (derive_inductive fuel env Nil O (Cons (nat_spec, Nil)))
        (fun ds -> admit_generated env (map corrupt_rule ds)))

  (** val rejected_quot_signature : environment result **)

  let rejected_quot_signature =
    bind structure_env (fun env ->
      admit_quotient fuel env q_name (Cons (u_name, Nil)) type0 QType)

  (** val missing_eq_quot : environment result **)

  let missing_eq_quot =
    bind nat_env (fun env -> add_quot env QType)

  (** val accepted : 'a1 result -> bool **)

  let accepted = function
  | Accept _ -> True
  | _ -> False

  (** val reject_reason_of : 'a1 result -> reject_reason option **)

  let reject_reason_of = function
  | Reject r -> Some r
  | _ -> None
 end

module MetadataCases =
 struct
  module M = Metadata

  type rows = (positive, dag_node) prod list

  (** val emit :
      positive -> rows -> dag_node -> ((positive, positive) prod, (positive,
      dag_node) prod list) prod **)

  let emit next prior node0 =
    Pair ((Pair (next, (Coq_Pos.succ next))),
      (app prior (Cons ((Pair (next, node0)), Nil))))

  (** val quote :
      expr -> positive -> ((positive, positive) prod, rows) prod **)

  let rec quote e next =
    match e with
    | EBVar n0 -> emit next Nil (DBVar n0)
    | EFVar n0 -> emit next Nil (DFVar n0)
    | EMVar n0 -> emit next Nil (DMVar n0)
    | ESort u0 -> emit next Nil (DSort u0)
    | EConst (n0, us) -> emit next Nil (DConst (n0, us))
    | EApp (f, a) ->
      let Pair (p0, fs) = quote f next in
      let Pair (fi, next0) = p0 in
      let Pair (p1, ars) = quote a next0 in
      let Pair (ai, next1) = p1 in emit next1 (app fs ars) (DApp (fi, ai))
    | ELam (n0, bi, a, b) ->
      let Pair (p0, ars) = quote a next in
      let Pair (ai, next0) = p0 in
      let Pair (p1, bs) = quote b next0 in
      let Pair (bi0, next1) = p1 in
      emit next1 (app ars bs) (DLam (n0, bi, ai, bi0))
    | EPi (n0, bi, a, b) ->
      let Pair (p0, ars) = quote a next in
      let Pair (ai, next0) = p0 in
      let Pair (p1, bs) = quote b next0 in
      let Pair (bi0, next1) = p1 in
      emit next1 (app ars bs) (DPi (n0, bi, ai, bi0))
    | ELet (n0, a, v0, b, nd) ->
      let Pair (p0, ars) = quote a next in
      let Pair (ai, next0) = p0 in
      let Pair (p1, vs) = quote v0 next0 in
      let Pair (vi, next1) = p1 in
      let Pair (p2, bs) = quote b next1 in
      let Pair (bi, next2) = p2 in
      emit next2 (app ars (app vs bs)) (DLet (n0, ai, vi, bi, nd))
    | ELit l -> emit next Nil (DLit l)
    | EProj (n0, i, a) ->
      let Pair (p0, ars) = quote a next in
      let Pair (ai, next0) = p0 in emit next0 ars (DProj (n0, i, ai))
    | EMData a ->
      let Pair (p0, ars) = quote a next in
      let Pair (ai, next0) = p0 in emit next0 ars (DMData ai)

  (** val quote_pair :
      expr -> expr -> ((positive, positive) prod, (positive, dag_node) prod
      list) prod **)

  let quote_pair ty0 body =
    let Pair (p0, ts) = quote ty0 XH in
    let Pair (tr, next) = p0 in
    let Pair (p1, bs) = quote body next in
    let Pair (br, _) = p1 in Pair ((Pair (tr, br)), (app ts bs))

  type test_case = { case_label : string; case_kind : dag_admission_kind;
                     case_env : environment result; case_name : name;
                     case_type : expr; case_body : expr; case_positive : 
                     bool }

  (** val case_kind : test_case -> dag_admission_kind **)

  let case_kind t0 =
    t0.case_kind

  (** val case_name : test_case -> name **)

  let case_name t0 =
    t0.case_name

  (** val case_type : test_case -> expr **)

  let case_type t0 =
    t0.case_type

  (** val case_body : test_case -> expr **)

  let case_body t0 =
    t0.case_body

  (** val positive :
      string -> dag_admission_kind -> environment result -> name -> expr ->
      expr -> test_case **)

  let positive s k env n0 ty0 body =
    { case_label = s; case_kind = k; case_env = env; case_name = n0;
      case_type = ty0; case_body = body; case_positive = True }

  (** val equality_case : string -> expr -> test_case **)

  let equality_case s value =
    positive s DagTheorem M.base_env (M.label s)
      (M.eq_nat value primitive_one) (M.refl_nat primitive_one)

  (** val positives : test_case list **)

  let positives =
    Cons
      ((positive (String ((Ascii (True, False, False, False, False, True,
         True, False)), (String ((Ascii (True, False, True, False, True,
         True, True, False)), (String ((Ascii (False, False, True, False,
         True, True, True, False)), (String ((Ascii (False, False, False,
         True, False, True, True, False)), (String ((Ascii (True, False,
         True, False, False, True, True, False)), (String ((Ascii (False,
         True, True, True, False, True, True, False)), (String ((Ascii
         (False, False, True, False, True, True, True, False)), (String
         ((Ascii (True, False, False, True, False, True, True, False)),
         (String ((Ascii (True, True, False, False, False, True, True,
         False)), (String ((Ascii (True, False, False, False, False, True,
         True, False)), (String ((Ascii (False, False, True, False, True,
         True, True, False)), (String ((Ascii (True, False, True, False,
         False, True, True, False)), (String ((Ascii (False, False, True,
         False, False, True, True, False)), (String ((Ascii (True, False,
         True, True, False, True, False, False)), (String ((Ascii (True,
         False, False, False, False, True, True, False)), (String ((Ascii
         (False, False, True, False, False, True, True, False)), (String
         ((Ascii (False, False, True, False, False, True, True, False)),
         EmptyString)))))))))))))))))))))))))))))))))) (DagDefinition
         HintOpaque) M.base_env (primitive_name PNatAdd)
         (primitive_signature PNatAdd) M.add_body),
      (Cons
      ((equality_case (String ((Ascii (False, True, True, True, False, True,
         True, False)), (String ((Ascii (True, False, False, False, False,
         True, True, False)), (String ((Ascii (False, False, True, False,
         True, True, True, False)), (String ((Ascii (True, False, True, True,
         False, True, False, False)), (String ((Ascii (False, True, False,
         False, True, True, True, False)), (String ((Ascii (True, False,
         True, False, False, True, True, False)), (String ((Ascii (True,
         True, False, False, False, True, True, False)), (String ((Ascii
         (True, False, True, False, True, True, True, False)), (String
         ((Ascii (False, True, False, False, True, True, True, False)),
         (String ((Ascii (True, True, False, False, True, True, True,
         False)), (String ((Ascii (True, True, True, True, False, True, True,
         False)), (String ((Ascii (False, True, False, False, True, True,
         True, False)), EmptyString)))))))))))))))))))))))) M.rec_value),
      (Cons
      ((equality_case (String ((Ascii (True, False, False, True, False, True,
         True, False)), (String ((Ascii (False, True, True, True, False,
         True, True, False)), (String ((Ascii (False, False, True, False,
         False, True, True, False)), (String ((Ascii (True, False, True,
         False, False, True, True, False)), (String ((Ascii (False, False,
         False, True, True, True, True, False)), (String ((Ascii (True,
         False, True, False, False, True, True, False)), (String ((Ascii
         (False, False, True, False, False, True, True, False)), (String
         ((Ascii (True, False, True, True, False, True, False, False)),
         (String ((Ascii (True, False, True, False, False, True, True,
         False)), (String ((Ascii (True, False, False, False, True, True,
         True, False)), (String ((Ascii (True, False, True, False, True,
         True, True, False)), (String ((Ascii (True, False, False, False,
         False, True, True, False)), (String ((Ascii (False, False, True,
         True, False, True, True, False)), (String ((Ascii (True, False,
         False, True, False, True, True, False)), (String ((Ascii (False,
         False, True, False, True, True, True, False)), (String ((Ascii
         (True, False, False, True, True, True, True, False)), (String
         ((Ascii (True, False, True, True, False, True, False, False)),
         (String ((Ascii (False, True, False, False, True, True, True,
         False)), (String ((Ascii (True, False, True, False, False, True,
         True, False)), (String ((Ascii (True, True, False, False, False,
         True, True, False)), (String ((Ascii (True, False, True, False,
         True, True, True, False)), (String ((Ascii (False, True, False,
         False, True, True, True, False)), (String ((Ascii (True, True,
         False, False, True, True, True, False)), (String ((Ascii (True,
         True, True, True, False, True, True, False)), (String ((Ascii
         (False, True, False, False, True, True, True, False)),
         EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))
         M.indexed_rec_value),
      (Cons
      ((equality_case (String ((Ascii (True, False, False, False, True, True,
         True, False)), (String ((Ascii (True, False, True, False, True,
         True, True, False)), (String ((Ascii (True, True, True, True, False,
         True, True, False)), (String ((Ascii (False, False, True, False,
         True, True, True, False)), (String ((Ascii (True, False, True, True,
         False, True, False, False)), (String ((Ascii (False, False, True,
         True, False, True, True, False)), (String ((Ascii (True, False,
         False, True, False, True, True, False)), (String ((Ascii (False,
         True, True, False, False, True, True, False)), (String ((Ascii
         (False, False, True, False, True, True, True, False)),
         EmptyString)))))))))))))))))) M.lift_value),
      (Cons
      ((equality_case (String ((Ascii (True, True, True, True, False, True,
         True, False)), (String ((Ascii (False, True, False, False, True,
         True, True, False)), (String ((Ascii (False, False, True, False,
         False, True, True, False)), (String ((Ascii (True, False, False,
         True, False, True, True, False)), (String ((Ascii (False, True,
         True, True, False, True, True, False)), (String ((Ascii (True,
         False, False, False, False, True, True, False)), (String ((Ascii
         (False, True, False, False, True, True, True, False)), (String
         ((Ascii (True, False, False, True, True, True, True, False)),
         (String ((Ascii (True, False, True, True, False, True, False,
         False)), (String ((Ascii (False, False, False, False, True, True,
         True, False)), (String ((Ascii (False, True, False, False, True,
         True, True, False)), (String ((Ascii (True, True, True, True, False,
         True, True, False)), (String ((Ascii (False, True, False, True,
         False, True, True, False)), (String ((Ascii (True, False, True,
         False, False, True, True, False)), (String ((Ascii (True, True,
         False, False, False, True, True, False)), (String ((Ascii (False,
         False, True, False, True, True, True, False)), (String ((Ascii
         (True, False, False, True, False, True, True, False)), (String
         ((Ascii (True, True, True, True, False, True, True, False)), (String
         ((Ascii (False, True, True, True, False, True, True, False)),
         EmptyString)))))))))))))))))))))))))))))))))))))) M.project_box),
      (Cons
      ((equality_case (String ((Ascii (False, False, True, False, False,
         True, True, False)), (String ((Ascii (True, False, True, False,
         False, True, True, False)), (String ((Ascii (False, False, False,
         False, True, True, True, False)), (String ((Ascii (True, False,
         True, False, False, True, True, False)), (String ((Ascii (False,
         True, True, True, False, True, True, False)), (String ((Ascii
         (False, False, True, False, False, True, True, False)), (String
         ((Ascii (True, False, True, False, False, True, True, False)),
         (String ((Ascii (False, True, True, True, False, True, True,
         False)), (String ((Ascii (False, False, True, False, True, True,
         True, False)), (String ((Ascii (True, False, True, True, False,
         True, False, False)), (String ((Ascii (False, False, False, False,
         True, True, True, False)), (String ((Ascii (False, True, False,
         False, True, True, True, False)), (String ((Ascii (True, True, True,
         True, False, True, True, False)), (String ((Ascii (False, True,
         False, True, False, True, True, False)), (String ((Ascii (True,
         False, True, False, False, True, True, False)), (String ((Ascii
         (True, True, False, False, False, True, True, False)), (String
         ((Ascii (False, False, True, False, True, True, True, False)),
         (String ((Ascii (True, False, False, True, False, True, True,
         False)), (String ((Ascii (True, True, True, True, False, True, True,
         False)), (String ((Ascii (False, True, True, True, False, True,
         True, False)), EmptyString))))))))))))))))))))))))))))))))))))))))
         M.project_dep),
      (Cons
      ((positive (String ((Ascii (False, False, True, False, False, True,
         True, False)), (String ((Ascii (True, False, True, False, False,
         True, True, False)), (String ((Ascii (False, False, False, False,
         True, True, True, False)), (String ((Ascii (True, False, True,
         False, False, True, True, False)), (String ((Ascii (False, True,
         True, True, False, True, True, False)), (String ((Ascii (False,
         False, True, False, False, True, True, False)), (String ((Ascii
         (True, False, True, False, False, True, True, False)), (String
         ((Ascii (False, True, True, True, False, True, True, False)),
         (String ((Ascii (False, False, True, False, True, True, True,
         False)), (String ((Ascii (True, False, True, True, False, True,
         False, False)), (String ((Ascii (False, True, True, False, False,
         True, True, False)), (String ((Ascii (True, False, True, False,
         True, True, True, False)), (String ((Ascii (False, True, True, True,
         False, True, True, False)), (String ((Ascii (True, True, False,
         False, False, True, True, False)), (String ((Ascii (False, False,
         True, False, True, True, True, False)), (String ((Ascii (True,
         False, False, True, False, True, True, False)), (String ((Ascii
         (True, True, True, True, False, True, True, False)), (String ((Ascii
         (False, True, True, True, False, True, True, False)),
         EmptyString)))))))))))))))))))))))))))))))))))) (DagDefinition
         HintOpaque) M.base_env
         (M.label (String ((Ascii (False, False, True, False, False, True,
           True, False)), (String ((Ascii (True, False, True, False, False,
           True, True, False)), (String ((Ascii (False, False, False, False,
           True, True, True, False)), (String ((Ascii (True, False, True,
           False, False, True, True, False)), (String ((Ascii (False, True,
           True, True, False, True, True, False)), (String ((Ascii (False,
           False, True, False, False, True, True, False)), (String ((Ascii
           (True, False, True, False, False, True, True, False)), (String
           ((Ascii (False, True, True, True, False, True, True, False)),
           (String ((Ascii (False, False, True, False, True, True, True,
           False)), (String ((Ascii (True, False, True, True, False, True,
           False, False)), (String ((Ascii (False, True, True, False, False,
           True, True, False)), (String ((Ascii (True, False, True, False,
           True, True, True, False)), (String ((Ascii (False, True, True,
           True, False, True, True, False)), (String ((Ascii (True, True,
           False, False, False, True, True, False)), (String ((Ascii (False,
           False, True, False, True, True, True, False)), (String ((Ascii
           (True, False, False, True, False, True, True, False)), (String
           ((Ascii (True, True, True, True, False, True, True, False)),
           (String ((Ascii (False, True, True, True, False, True, True,
           False)), EmptyString)))))))))))))))))))))))))))))))))))))
         M.project_dep_type M.project_dep_fn),
      (Cons
      ((positive (String ((Ascii (True, False, False, False, True, True,
         True, False)), (String ((Ascii (True, False, True, False, True,
         True, True, False)), (String ((Ascii (True, True, True, True, False,
         True, True, False)), (String ((Ascii (False, False, True, False,
         True, True, True, False)), (String ((Ascii (True, False, True, True,
         False, True, False, False)), (String ((Ascii (True, False, False,
         True, False, True, True, False)), (String ((Ascii (False, True,
         True, True, False, True, True, False)), (String ((Ascii (False,
         False, True, False, False, True, True, False)),
         EmptyString)))))))))))))))) DagTheorem M.base_env
         (M.label (String ((Ascii (True, False, False, False, True, True,
           True, False)), (String ((Ascii (True, False, True, False, True,
           True, True, False)), (String ((Ascii (True, True, True, True,
           False, True, True, False)), (String ((Ascii (False, False, True,
           False, True, True, True, False)), (String ((Ascii (True, False,
           True, True, False, True, False, False)), (String ((Ascii (True,
           False, False, True, False, True, True, False)), (String ((Ascii
           (False, True, True, True, False, True, True, False)), (String
           ((Ascii (False, False, True, False, False, True, True, False)),
           EmptyString)))))))))))))))))
         (M.eq_nat primitive_one primitive_one) M.ind_value),
      (Cons
      ((positive (String ((Ascii (True, False, False, False, False, True,
         True, False)), (String ((Ascii (True, False, True, False, True,
         True, True, False)), (String ((Ascii (False, False, True, False,
         True, True, True, False)), (String ((Ascii (False, False, False,
         True, False, True, True, False)), (String ((Ascii (True, False,
         True, False, False, True, True, False)), (String ((Ascii (False,
         True, True, True, False, True, True, False)), (String ((Ascii
         (False, False, True, False, True, True, True, False)), (String
         ((Ascii (True, False, False, True, False, True, True, False)),
         (String ((Ascii (True, True, False, False, False, True, True,
         False)), (String ((Ascii (True, False, False, False, False, True,
         True, False)), (String ((Ascii (False, False, True, False, True,
         True, True, False)), (String ((Ascii (True, False, True, False,
         False, True, True, False)), (String ((Ascii (False, False, True,
         False, False, True, True, False)), (String ((Ascii (True, False,
         True, True, False, True, False, False)), (String ((Ascii (True,
         False, False, False, False, True, True, False)), (String ((Ascii
         (False, False, True, False, False, True, True, False)), (String
         ((Ascii (False, False, True, False, False, True, True, False)),
         (String ((Ascii (True, False, True, True, False, True, False,
         False)), (String ((Ascii (False, True, False, False, True, True,
         True, False)), (String ((Ascii (True, False, True, False, False,
         True, True, False)), (String ((Ascii (False, False, True, False,
         False, True, True, False)), (String ((Ascii (True, False, True,
         False, True, True, True, False)), (String ((Ascii (True, True,
         False, False, False, True, True, False)), (String ((Ascii (False,
         False, True, False, True, True, True, False)), (String ((Ascii
         (True, False, False, True, False, True, True, False)), (String
         ((Ascii (True, True, True, True, False, True, True, False)), (String
         ((Ascii (False, True, True, True, False, True, True, False)),
         EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))))))
         DagTheorem M.with_add
         (M.label (String ((Ascii (True, False, False, False, False, True,
           True, False)), (String ((Ascii (False, False, True, False, False,
           True, True, False)), (String ((Ascii (False, False, True, False,
           False, True, True, False)), (String ((Ascii (True, False, True,
           True, False, True, False, False)), (String ((Ascii (False, True,
           False, False, True, True, True, False)), (String ((Ascii (True,
           False, True, False, False, True, True, False)), (String ((Ascii
           (False, False, True, False, False, True, True, False)), (String
           ((Ascii (True, False, True, False, True, True, True, False)),
           (String ((Ascii (True, True, False, False, False, True, True,
           False)), (String ((Ascii (False, False, True, False, True, True,
           True, False)), (String ((Ascii (True, False, False, True, False,
           True, True, False)), (String ((Ascii (True, True, True, True,
           False, True, True, False)), (String ((Ascii (False, True, True,
           True, False, True, True, False)),
           EmptyString)))))))))))))))))))))))))))
         (M.eq_nat M.add_value primitive_two) (M.refl_nat primitive_two)),
      Nil)))))))))))))))))

  (** val change :
      string -> environment result -> expr -> expr -> test_case -> test_case **)

  let change s env ty0 body c =
    { case_label = s; case_kind = c.case_kind; case_env = env; case_name =
      c.case_name; case_type = ty0; case_body = body; case_positive = False }

  (** val alter_env : (environment -> environment) -> environment result **)

  let alter_env f =
    bind M.base_env (fun env -> Accept (f env))

  (** val negative_cases : test_case list **)

  let negative_cases =
    let add0 =
      positive (String ((Ascii (True, False, False, False, False, True, True,
        False)), (String ((Ascii (False, False, True, False, False, True,
        True, False)), (String ((Ascii (False, False, True, False, False,
        True, True, False)), EmptyString)))))) (DagDefinition HintOpaque)
        M.base_env (primitive_name PNatAdd) (primitive_signature PNatAdd)
        M.add_body
    in
    let rec0 =
      equality_case (String ((Ascii (False, True, False, False, True, True,
        True, False)), (String ((Ascii (True, False, True, False, False,
        True, True, False)), (String ((Ascii (True, True, False, False,
        False, True, True, False)), EmptyString)))))) M.rec_value
    in
    let q0 =
      equality_case (String ((Ascii (True, False, False, False, True, True,
        True, False)), (String ((Ascii (True, False, True, False, True, True,
        True, False)), (String ((Ascii (True, True, True, True, False, True,
        True, False)), (String ((Ascii (False, False, True, False, True,
        True, True, False)), EmptyString)))))))) M.lift_value
    in
    let proj =
      equality_case (String ((Ascii (False, False, False, False, True, True,
        True, False)), (String ((Ascii (False, True, False, False, True,
        True, True, False)), (String ((Ascii (True, True, True, True, False,
        True, True, False)), (String ((Ascii (False, True, False, True,
        False, True, True, False)), EmptyString)))))))) M.project_box
    in
    Cons
    ((change (String ((Ascii (False, True, True, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, False, True,
       True, False)), (String ((Ascii (False, False, True, True, False, True,
       True, False)), (String ((Ascii (True, True, False, False, True, True,
       True, False)), (String ((Ascii (True, False, True, False, False, True,
       True, False)), (String ((Ascii (True, False, True, True, False, True,
       False, False)), (String ((Ascii (True, False, False, False, False,
       True, True, False)), (String ((Ascii (False, False, True, False,
       False, True, True, False)), (String ((Ascii (False, False, True,
       False, False, True, True, False)), (String ((Ascii (True, False, True,
       True, False, True, False, False)), (String ((Ascii (True, False, True,
       False, False, True, True, False)), (String ((Ascii (True, False,
       False, False, True, True, True, False)), (String ((Ascii (True, False,
       True, False, True, True, True, False)), (String ((Ascii (True, False,
       False, False, False, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, True, False)), (String ((Ascii (True,
       False, False, True, False, True, True, False)), (String ((Ascii (True,
       True, True, True, False, True, True, False)), (String ((Ascii (False,
       True, True, True, False, True, True, False)), (String ((Ascii (True,
       True, False, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))))))))))) M.base_env
       add0.case_type M.false_add add0),
    (Cons
    ((change (String ((Ascii (True, False, True, True, False, True, True,
       False)), (String ((Ascii (True, False, False, True, False, True, True,
       False)), (String ((Ascii (True, True, False, False, True, True, True,
       False)), (String ((Ascii (True, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, False, True, False, True, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (True, True, True, False, False, True, True,
       False)), (String ((Ascii (True, False, True, True, False, True, False,
       False)), (String ((Ascii (False, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, True, False, False, True, True,
       False)), (String ((Ascii (True, True, False, False, False, True, True,
       False)), EmptyString))))))))))))))))))))))
       (alter_env (M.without (rec_name core_nat_name))) add0.case_type
       add0.case_body add0),
    (Cons
    ((change (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (True, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, False, False, False, True,
       True, False)), (String ((Ascii (False, True, True, False, False, True,
       True, False)), (String ((Ascii (True, False, True, False, False, True,
       True, False)), (String ((Ascii (True, False, True, True, False, True,
       False, False)), (String ((Ascii (False, True, False, False, True,
       True, True, False)), (String ((Ascii (True, False, True, False, False,
       True, True, False)), (String ((Ascii (True, True, False, False, False,
       True, True, False)), (String ((Ascii (True, False, True, True, False,
       True, False, False)), (String ((Ascii (True, True, False, False, True,
       True, True, False)), (String ((Ascii (False, False, False, True,
       False, True, True, False)), (String ((Ascii (True, False, False,
       False, False, True, True, False)), (String ((Ascii (False, False,
       True, False, False, True, True, False)), (String ((Ascii (True, True,
       True, True, False, True, True, False)), (String ((Ascii (True, True,
       True, False, True, True, True, False)),
       EmptyString))))))))))))))))))))))))))))))))))
       (alter_env (M.unsafe_shadow (rec_name core_nat_name))) rec0.case_type
       rec0.case_body rec0),
    (Cons
    ((change (String ((Ascii (True, False, True, True, False, True, True,
       False)), (String ((Ascii (True, False, False, True, False, True, True,
       False)), (String ((Ascii (True, True, False, False, True, True, True,
       False)), (String ((Ascii (True, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, False, True, False, True, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (True, True, True, False, False, True, True,
       False)), (String ((Ascii (True, False, True, True, False, True, False,
       False)), (String ((Ascii (True, False, False, False, True, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), (String ((Ascii (True, False, True, True, False, True, False,
       False)), (String ((Ascii (True, False, True, True, False, True, True,
       False)), (String ((Ascii (True, True, False, True, False, True, True,
       False)), EmptyString))))))))))))))))))))))))))))))
       (alter_env (M.without q_mk_name)) q0.case_type q0.case_body q0),
    (Cons
    ((change (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (True, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, False, False, False, True,
       True, False)), (String ((Ascii (False, True, True, False, False, True,
       True, False)), (String ((Ascii (True, False, True, False, False, True,
       True, False)), (String ((Ascii (True, False, True, True, False, True,
       False, False)), (String ((Ascii (True, False, False, False, True,
       True, True, False)), (String ((Ascii (True, False, True, False, True,
       True, True, False)), (String ((Ascii (True, True, True, True, False,
       True, True, False)), (String ((Ascii (False, False, True, False, True,
       True, True, False)), (String ((Ascii (True, False, True, True, False,
       True, False, False)), (String ((Ascii (True, True, False, False, True,
       True, True, False)), (String ((Ascii (False, False, False, True,
       False, True, True, False)), (String ((Ascii (True, False, False,
       False, False, True, True, False)), (String ((Ascii (False, False,
       True, False, False, True, True, False)), (String ((Ascii (True, True,
       True, True, False, True, True, False)), (String ((Ascii (True, True,
       True, False, True, True, True, False)),
       EmptyString))))))))))))))))))))))))))))))))))))
       (alter_env (M.unsafe_shadow q_lift_name)) q0.case_type q0.case_body q0),
    (Cons
    ((change (String ((Ascii (True, False, True, True, False, True, True,
       False)), (String ((Ascii (True, False, False, True, False, True, True,
       False)), (String ((Ascii (True, True, False, False, True, True, True,
       False)), (String ((Ascii (True, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, False, True, False, True, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (True, True, True, False, False, True, True,
       False)), (String ((Ascii (True, False, True, True, False, True, False,
       False)), (String ((Ascii (False, False, False, False, True, True,
       True, False)), (String ((Ascii (False, True, False, False, True, True,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (False, True, False, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, False, True,
       True, False)), (String ((Ascii (True, True, False, False, False, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), (String ((Ascii (True, False, False, True, False, True,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (False, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, True, False, True,
       False, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, True, True, False, True, True,
       True, False)), (String ((Ascii (False, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, False, True,
       True, False)), (String ((Ascii (False, True, False, False, True, True,
       True, False)),
       EmptyString))))))))))))))))))))))))))))))))))))))))))))))))
       (alter_env (M.without M.box_name)) proj.case_type proj.case_body proj),
    (Cons
    ((change (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (True, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, False, False, False, True,
       True, False)), (String ((Ascii (False, True, True, False, False, True,
       True, False)), (String ((Ascii (True, False, True, False, False, True,
       True, False)), (String ((Ascii (True, False, True, True, False, True,
       False, False)), (String ((Ascii (True, True, False, False, False,
       True, True, False)), (String ((Ascii (True, True, True, True, False,
       True, True, False)), (String ((Ascii (False, True, True, True, False,
       True, True, False)), (String ((Ascii (True, True, False, False, True,
       True, True, False)), (String ((Ascii (False, False, True, False, True,
       True, True, False)), (String ((Ascii (False, True, False, False, True,
       True, True, False)), (String ((Ascii (True, False, True, False, True,
       True, True, False)), (String ((Ascii (True, True, False, False, False,
       True, True, False)), (String ((Ascii (False, False, True, False, True,
       True, True, False)), (String ((Ascii (True, True, True, True, False,
       True, True, False)), (String ((Ascii (False, True, False, False, True,
       True, True, False)), (String ((Ascii (True, False, True, True, False,
       True, False, False)), (String ((Ascii (True, True, False, False, True,
       True, True, False)), (String ((Ascii (False, False, False, True,
       False, True, True, False)), (String ((Ascii (True, False, False,
       False, False, True, True, False)), (String ((Ascii (False, False,
       True, False, False, True, True, False)), (String ((Ascii (True, True,
       True, True, False, True, True, False)), (String ((Ascii (True, True,
       True, False, True, True, True, False)),
       EmptyString))))))))))))))))))))))))))))))))))))))))))))))))))
       (alter_env (M.unsafe_shadow M.box_mk)) proj.case_type proj.case_body
       proj),
    (Cons
    ((change (String ((Ascii (False, False, False, False, True, True, True,
       False)), (String ((Ascii (False, True, False, False, True, True, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (False, True, False, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, False, True, True,
       False)), (String ((Ascii (True, True, False, False, False, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), (String ((Ascii (True, False, False, True, False, True, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, True, False, True, False,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), (String ((Ascii (True, False, True, True, False, True, False,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (False, True, True, False, False, True, True,
       False)), (String ((Ascii (True, False, True, True, False, True, False,
       False)), (String ((Ascii (False, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, False, False, False, True,
       True, False)), (String ((Ascii (False, True, True, True, False, True,
       True, False)), (String ((Ascii (True, True, True, False, False, True,
       True, False)), (String ((Ascii (True, False, True, False, False, True,
       True, False)),
       EmptyString)))))))))))))))))))))))))))))))))))))))))))))) M.base_env
       (M.eq_nat (EProj (M.box_name, (S O), M.box_value)) primitive_one)
       proj.case_body proj),
    (Cons
    ((change (String ((Ascii (True, True, True, False, True, True, True,
       False)), (String ((Ascii (False, True, False, False, True, True, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (True, True, True, False, False, True, True,
       False)), (String ((Ascii (True, False, True, True, False, True, False,
       False)), (String ((Ascii (False, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, True, False, False, True, True,
       False)), (String ((Ascii (True, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, True, False, False, True, True, True,
       False)), (String ((Ascii (True, True, False, False, True, True, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (False, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, True, True, False, True, False,
       False)), (String ((Ascii (False, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, True, False, False, True, True,
       False)), (String ((Ascii (True, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, False, True, True, False, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), EmptyString))))))))))))))))))))))))))))))))))))))))))
       M.base_env (M.eq_nat M.rec_value primitive_zero)
       (M.refl_nat primitive_zero) rec0),
    (Cons
    ((change (String ((Ascii (True, True, True, False, True, True, True,
       False)), (String ((Ascii (False, True, False, False, True, True, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (True, True, True, False, False, True, True,
       False)), (String ((Ascii (True, False, True, True, False, True, False,
       False)), (String ((Ascii (False, False, True, False, False, True,
       True, False)), (String ((Ascii (True, False, True, False, False, True,
       True, False)), (String ((Ascii (False, False, False, False, True,
       True, True, False)), (String ((Ascii (True, False, True, False, False,
       True, True, False)), (String ((Ascii (False, True, True, True, False,
       True, True, False)), (String ((Ascii (False, False, True, False,
       False, True, True, False)), (String ((Ascii (True, False, True, False,
       False, True, True, False)), (String ((Ascii (False, True, True, True,
       False, True, True, False)), (String ((Ascii (False, False, True,
       False, True, True, True, False)), (String ((Ascii (True, False, True,
       True, False, True, False, False)), (String ((Ascii (False, True,
       False, False, True, True, True, False)), (String ((Ascii (True, False,
       True, False, False, True, True, False)), (String ((Ascii (True, True,
       False, False, True, True, True, False)), (String ((Ascii (True, False,
       True, False, True, True, True, False)), (String ((Ascii (False, False,
       True, True, False, True, True, False)), (String ((Ascii (False, False,
       True, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))))))))))))))))) M.base_env
       (M.eq_nat M.project_dep primitive_zero) (M.refl_nat primitive_zero)
       proj),
    (Cons
    ((change (String ((Ascii (False, True, True, False, False, True, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (False, True, False, False, True, True, True,
       False)), (String ((Ascii (True, True, True, False, False, True, True,
       False)), (String ((Ascii (True, False, True, False, False, True, True,
       False)), (String ((Ascii (False, False, True, False, False, True,
       True, False)), (String ((Ascii (True, False, True, True, False, True,
       False, False)), (String ((Ascii (False, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, False, False, False,
       True, True, False)), (String ((Ascii (False, False, True, False, True,
       True, True, False)), (String ((Ascii (True, False, True, True, False,
       True, False, False)), (String ((Ascii (False, True, True, False,
       False, True, True, False)), (String ((Ascii (True, False, False, True,
       False, True, True, False)), (String ((Ascii (True, False, True, False,
       False, True, True, False)), (String ((Ascii (False, False, True, True,
       False, True, True, False)), (String ((Ascii (False, False, True,
       False, False, True, True, False)), (String ((Ascii (True, True, False,
       False, True, True, True, False)),
       EmptyString))))))))))))))))))))))))))))))))))
       (alter_env
         (map (fun d ->
           match name_eqb d.decl_name core_succ_name with
           | True -> M.corrupt_fields d
           | False -> d)))
       (primitive_signature PNatAdd) M.add_body add0),
    Nil)))))))))))))))))))))

  (** val cases : test_case list **)

  let cases =
    app positives negative_cases

  (** val expected :
      declaration list -> test_case -> declaration list result **)

  let expected env c =
    Accept (Cons ({ decl_name = c.case_name; decl_params = Nil; decl_type =
      c.case_type; decl_value = (Some c.case_body); decl_kind_of =
      (match name_eqb c.case_name (primitive_name PNatAdd) with
       | True -> DPrimitive PNatAdd
       | False ->
         (match c.case_kind with
          | DagDefinition _ -> DDefinition
          | DagTheorem -> DTheorem
          | DagOpaque -> DOpaque));
      decl_hints =
      (match c.case_kind with
       | DagDefinition h -> h
       | _ -> HintOpaque) },
      env))

  (** val reductions : ((string, expr) prod, expr) prod list **)

  let reductions =
    Cons ((Pair ((Pair ((String ((Ascii (False, True, True, True, False,
      True, True, False)), (String ((Ascii (True, False, False, False, False,
      True, True, False)), (String ((Ascii (False, False, True, False, True,
      True, True, False)), (String ((Ascii (True, False, True, True, False,
      True, False, False)), (String ((Ascii (False, True, False, False, True,
      True, True, False)), (String ((Ascii (True, False, True, False, False,
      True, True, False)), (String ((Ascii (True, True, False, False, False,
      True, True, False)), (String ((Ascii (True, False, True, False, True,
      True, True, False)), (String ((Ascii (False, True, False, False, True,
      True, True, False)), (String ((Ascii (True, True, False, False, True,
      True, True, False)), (String ((Ascii (True, True, True, True, False,
      True, True, False)), (String ((Ascii (False, True, False, False, True,
      True, True, False)), EmptyString)))))))))))))))))))))))),
      M.rec_value)), (ELit (LitNat (Npos XH))))), (Cons ((Pair ((Pair
      ((String ((Ascii (True, False, False, True, False, True, True, False)),
      (String ((Ascii (False, True, True, True, False, True, True, False)),
      (String ((Ascii (False, False, True, False, False, True, True, False)),
      (String ((Ascii (True, False, True, False, False, True, True, False)),
      (String ((Ascii (False, False, False, True, True, True, True, False)),
      (String ((Ascii (True, False, True, False, False, True, True, False)),
      (String ((Ascii (False, False, True, False, False, True, True, False)),
      (String ((Ascii (True, False, True, True, False, True, False, False)),
      (String ((Ascii (True, False, True, False, False, True, True, False)),
      (String ((Ascii (True, False, False, False, True, True, True, False)),
      (String ((Ascii (True, False, True, False, True, True, True, False)),
      (String ((Ascii (True, False, False, False, False, True, True, False)),
      (String ((Ascii (False, False, True, True, False, True, True, False)),
      (String ((Ascii (True, False, False, True, False, True, True, False)),
      (String ((Ascii (False, False, True, False, True, True, True, False)),
      (String ((Ascii (True, False, False, True, True, True, True, False)),
      (String ((Ascii (True, False, True, True, False, True, False, False)),
      (String ((Ascii (False, True, False, False, True, True, True, False)),
      (String ((Ascii (True, False, True, False, False, True, True, False)),
      (String ((Ascii (True, True, False, False, False, True, True, False)),
      (String ((Ascii (True, False, True, False, True, True, True, False)),
      (String ((Ascii (False, True, False, False, True, True, True, False)),
      (String ((Ascii (True, True, False, False, True, True, True, False)),
      (String ((Ascii (True, True, True, True, False, True, True, False)),
      (String ((Ascii (False, True, False, False, True, True, True, False)),
      EmptyString)))))))))))))))))))))))))))))))))))))))))))))))))),
      M.indexed_rec_value)), (ELit (LitNat (Npos XH))))), (Cons ((Pair ((Pair
      ((String ((Ascii (True, False, False, False, True, True, True, False)),
      (String ((Ascii (True, False, True, False, True, True, True, False)),
      (String ((Ascii (True, True, True, True, False, True, True, False)),
      (String ((Ascii (False, False, True, False, True, True, True, False)),
      (String ((Ascii (True, False, True, True, False, True, False, False)),
      (String ((Ascii (False, False, True, True, False, True, True, False)),
      (String ((Ascii (True, False, False, True, False, True, True, False)),
      (String ((Ascii (False, True, True, False, False, True, True, False)),
      (String ((Ascii (False, False, True, False, True, True, True, False)),
      EmptyString)))))))))))))))))), M.lift_value)), (ELit (LitNat (Npos
      XH))))), (Cons ((Pair ((Pair ((String ((Ascii (True, False, False,
      False, True, True, True, False)), (String ((Ascii (True, False, True,
      False, True, True, True, False)), (String ((Ascii (True, True, True,
      True, False, True, True, False)), (String ((Ascii (False, False, True,
      False, True, True, True, False)), (String ((Ascii (True, False, True,
      True, False, True, False, False)), (String ((Ascii (True, False, False,
      True, False, True, True, False)), (String ((Ascii (False, True, True,
      True, False, True, True, False)), (String ((Ascii (False, False, True,
      False, False, True, True, False)), EmptyString)))))))))))))))),
      M.ind_value)), (M.refl_nat primitive_one))), (Cons ((Pair ((Pair
      ((String ((Ascii (True, True, True, True, False, True, True, False)),
      (String ((Ascii (False, True, False, False, True, True, True, False)),
      (String ((Ascii (False, False, True, False, False, True, True, False)),
      (String ((Ascii (True, False, False, True, False, True, True, False)),
      (String ((Ascii (False, True, True, True, False, True, True, False)),
      (String ((Ascii (True, False, False, False, False, True, True, False)),
      (String ((Ascii (False, True, False, False, True, True, True, False)),
      (String ((Ascii (True, False, False, True, True, True, True, False)),
      (String ((Ascii (True, False, True, True, False, True, False, False)),
      (String ((Ascii (False, False, False, False, True, True, True, False)),
      (String ((Ascii (False, True, False, False, True, True, True, False)),
      (String ((Ascii (True, True, True, True, False, True, True, False)),
      (String ((Ascii (False, True, False, True, False, True, True, False)),
      (String ((Ascii (True, False, True, False, False, True, True, False)),
      (String ((Ascii (True, True, False, False, False, True, True, False)),
      (String ((Ascii (False, False, True, False, True, True, True, False)),
      (String ((Ascii (True, False, False, True, False, True, True, False)),
      (String ((Ascii (True, True, True, True, False, True, True, False)),
      (String ((Ascii (False, True, True, True, False, True, True, False)),
      EmptyString)))))))))))))))))))))))))))))))))))))), M.project_box)),
      (ELit (LitNat (Npos XH))))), (Cons ((Pair ((Pair ((String ((Ascii
      (False, False, True, False, False, True, True, False)), (String ((Ascii
      (True, False, True, False, False, True, True, False)), (String ((Ascii
      (False, False, False, False, True, True, True, False)), (String ((Ascii
      (True, False, True, False, False, True, True, False)), (String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, False, True, True, False)), (String ((Ascii
      (True, False, True, False, False, True, True, False)), (String ((Ascii
      (False, True, True, True, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (True, False, True, True, False, True, False, False)), (String ((Ascii
      (False, False, False, False, True, True, True, False)), (String ((Ascii
      (False, True, False, False, True, True, True, False)), (String ((Ascii
      (True, True, True, True, False, True, True, False)), (String ((Ascii
      (False, True, False, True, False, True, True, False)), (String ((Ascii
      (True, False, True, False, False, True, True, False)), (String ((Ascii
      (True, True, False, False, False, True, True, False)), (String ((Ascii
      (False, False, True, False, True, True, True, False)), (String ((Ascii
      (True, False, False, True, False, True, True, False)), (String ((Ascii
      (True, True, True, True, False, True, True, False)), (String ((Ascii
      (False, True, True, True, False, True, True, False)),
      EmptyString)))))))))))))))))))))))))))))))))))))))), M.project_dep)),
      (ELit (LitNat (Npos XH))))), Nil)))))))))))
 end

type indexed_state = { state_environment : environment;
                       state_index : declaration_index }

(** val state_environment : (name -> n) -> indexed_state -> environment **)

let state_environment _ i =
  i.state_environment

(** val seed_state : (name -> n) -> environment -> indexed_state **)

let seed_state hash env =
  { state_environment = env; state_index = (index_environment hash env) }

(** val prepend_index :
    (name -> n) -> declaration list -> declaration_index -> declaration_index **)

let rec prepend_index hash added index =
  match added with
  | Nil -> index
  | Cons (d, rest) -> index_declaration hash d (prepend_index hash rest index)

(** val extend_state :
    (name -> n) -> indexed_state -> declaration list -> indexed_state **)

let extend_state hash s added =
  { state_environment = (app added s.state_environment); state_index =
    (prepend_index hash added s.state_index) }

(** val state_lookup :
    (name -> n) -> indexed_state -> name -> declaration option **)

let state_lookup hash s n0 =
  indexed_find_decl hash n0 s.state_index

(** val safety_eqb : input_safety -> input_safety -> bool **)

let safety_eqb a b =
  match a with
  | InputSafe -> (match b with
                  | InputSafe -> True
                  | _ -> False)
  | InputPartial -> (match b with
                     | InputPartial -> True
                     | _ -> False)
  | InputUnsafe -> (match b with
                    | InputUnsafe -> True
                    | _ -> False)

(** val checking_view : input_safety -> declaration -> declaration **)

let checking_view mode d =
  let kind =
    match d.decl_kind_of with
    | DUnsafe inner ->
      let k = DUnsafe inner in (match mode with
                                | InputUnsafe -> inner
                                | _ -> k)
    | DPartial -> (match mode with
                   | InputSafe -> DPartial
                   | _ -> DDefinition)
    | x0 -> x0
  in
  { decl_name = d.decl_name; decl_params = d.decl_params; decl_type =
  d.decl_type; decl_value = d.decl_value; decl_kind_of = kind; decl_hints =
  d.decl_hints }

(** val safety_environment :
    input_safety -> declaration list -> declaration list **)

let safety_environment mode env =
  map (checking_view mode) env

(** val safety_kind : input_safety -> decl_kind **)

let safety_kind = function
| InputSafe -> DDefinition
| InputPartial -> DPartial
| InputUnsafe -> DUnsafe DDefinition

(** val safe_name : name -> unit0 result **)

let safe_name n0 =
  require (negb (name_mem n0 reserved_names)) MalformedDeclaration

(** val check_value :
    nat -> environment -> name list -> expr -> expr -> unit0 result **)

let check_value fuel0 env ps ty0 value =
  bind (require (scoped O value) MalformedDeclaration) (fun _ ->
    check fuel0 env ps empty_context value ty0)

(** val restricted_constant :
    name -> name list -> expr -> expr option -> decl_kind -> declaration **)

let restricted_constant n0 ps ty0 body kind =
  { decl_name = n0; decl_params = ps; decl_type = ty0; decl_value = body;
    decl_kind_of = kind; decl_hints = HintOpaque }

(** val restricted_definition :
    reducibility_hints -> name -> name list -> expr -> expr -> decl_kind ->
    declaration **)

let restricted_definition hints n0 ps ty0 value kind =
  { decl_name = n0; decl_params = ps; decl_type = ty0; decl_value = (Some
    value); decl_kind_of = kind; decl_hints = hints }

(** val admit_extended :
    nat -> environment -> input_decl -> environment result **)

let admit_extended fuel0 env input = match input with
| InputAxiom (n0, ps, ty0, b) ->
  (match b with
   | True ->
     bind (safe_name n0) (fun _ ->
       let view = safety_environment InputUnsafe env in
       bind (check_header fuel0 view n0 ps ty0) (fun _ -> Accept (Cons
         ((restricted_constant n0 ps ty0 None (DUnsafe DAssumption)), env))))
   | False -> admit fuel0 env input)
| InputDefinition (hints, n0, ps, ty0, value, i) ->
  (match i with
   | InputSafe -> admit fuel0 env input
   | InputPartial ->
     bind (safe_name n0) (fun _ ->
       bind (check_header fuel0 env n0 ps ty0) (fun _ ->
         bind (check_value fuel0 env ps ty0 value) (fun _ -> Accept (Cons
           ((restricted_definition hints n0 ps ty0 value DPartial), env)))))
   | InputUnsafe ->
     bind (safe_name n0) (fun _ ->
       let view = safety_environment InputUnsafe env in
       bind (check_header fuel0 view n0 ps ty0) (fun _ ->
         let self = restricted_constant n0 ps ty0 None DAssumption in
         bind (check_value fuel0 (Cons (self, view)) ps ty0 value) (fun _ ->
           Accept (Cons
           ((restricted_definition hints n0 ps ty0 value (DUnsafe
              DDefinition)),
           env))))))
| InputOpaque (n0, ps, ty0, value, b) ->
  (match b with
   | True ->
     bind (safe_name n0) (fun _ ->
       bind (check_header fuel0 env n0 ps ty0) (fun _ ->
         bind (check_value fuel0 env ps ty0 value) (fun _ -> Accept (Cons
           ((restricted_constant n0 ps ty0 (Some value) (DUnsafe DOpaque)),
           env)))))
   | False -> admit fuel0 env input)
| _ -> admit fuel0 env input

(** val mutual_name : input_decl -> name **)

let mutual_name = function
| InputDefinition (_, n0, _, _, _, _) -> n0
| _ -> NameAnon

(** val check_mutual_headers :
    nat -> environment -> name list -> input_safety -> input_decl list ->
    declaration list result **)

let rec check_mutual_headers fuel0 view ps mode = function
| Nil -> Accept Nil
| Cons (i, inputs0) ->
  (match i with
   | InputDefinition (_, n0, qs, ty0, _, safety) ->
     bind
       (require
         (match safety_eqb safety mode with
          | True -> list_eqb name_eqb qs ps
          | False -> False)
         MalformedDeclaration)
       (fun _ ->
       bind (safe_name n0) (fun _ ->
         bind (check_header fuel0 view n0 ps ty0) (fun _ ->
           bind (check_mutual_headers fuel0 view ps mode inputs0)
             (fun rest -> Accept (Cons
             ((restricted_constant n0 ps ty0 None DAssumption), rest))))))
   | _ -> Reject MalformedDeclaration)

(** val check_mutual_values :
    nat -> environment -> input_decl list -> declaration list result **)

let rec check_mutual_values fuel0 view = function
| Nil -> Accept Nil
| Cons (i, inputs0) ->
  (match i with
   | InputDefinition (hints, n0, ps, ty0, value, safety) ->
     bind (check_value fuel0 view ps ty0 value) (fun _ ->
       bind (check_mutual_values fuel0 view inputs0) (fun rest -> Accept
         (Cons
         ((restricted_definition hints n0 ps ty0 value (safety_kind safety)),
         rest))))
   | _ -> Reject MalformedDeclaration)

(** val admit_mutual :
    nat -> environment -> input_decl list -> environment result **)

let admit_mutual fuel0 env inputs = match inputs with
| Nil -> Reject MalformedDeclaration
| Cons (i, _) ->
  (match i with
   | InputDefinition (_, _, ps, _, _, mode) ->
     bind (require (negb (safety_eqb mode InputSafe)) MalformedDeclaration)
       (fun _ ->
       bind
         (require (names_unique (map mutual_name inputs))
           DuplicateDeclaration)
         (fun _ ->
         let view = safety_environment mode env in
         bind (check_mutual_headers fuel0 view ps mode inputs)
           (fun placeholders ->
           bind (check_mutual_values fuel0 (app placeholders view) inputs)
             (fun generated -> Accept (app generated env)))))
   | _ -> Reject MalformedDeclaration)

type nested_elimination = { nested_params : ind_local list;
                            nested_context : context;
                            nested_specs : ind_spec list;
                            nested_mapping : (expr, name) prod list;
                            nested_aux_names : name list;
                            nested_aux_count : nat }

type nested_work = { nw_specs : ind_spec list;
                     nw_mapping : (expr, name) prod list; nw_next_aux : 
                     nat; nw_next_local : nat }

(** val nested_set_specs : nested_work -> ind_spec list -> nested_work **)

let nested_set_specs w specs =
  { nw_specs = specs; nw_mapping = w.nw_mapping; nw_next_aux = w.nw_next_aux;
    nw_next_local = w.nw_next_local }

(** val nested_set_local : nested_work -> nat -> nested_work **)

let nested_set_local w next =
  { nw_specs = w.nw_specs; nw_mapping = w.nw_mapping; nw_next_aux =
    w.nw_next_aux; nw_next_local = next }

(** val nested_open_params :
    nat -> nat -> ind_state -> expr -> ((ind_local list, expr) prod,
    ind_state) prod result **)

let rec nested_open_params fuel0 count s ty0 =
  match count with
  | O -> Accept (Pair ((Pair (Nil, ty0)), s))
  | S count0 ->
    (match fuel0 with
     | O -> Decline OutOfFuel
     | S fuel1 ->
       (match ty0 with
        | EPi (n0, bi, a, b) ->
          let Pair (x0, s0) = ind_fresh s n0 bi a in
          bind
            (nested_open_params fuel1 count0 s0
              (instantiate b (local_expr x0)))
            (fun rest ->
            let Pair (p0, s1) = rest in
            let Pair (xs, body) = p0 in
            Accept (Pair ((Pair ((Cons (x0, xs)), body)), s1)))
        | _ -> Reject MalformedDeclaration))

(** val nested_instantiate_params :
    nat -> expr list -> expr -> expr result **)

let rec nested_instantiate_params fuel0 args ty0 =
  match args with
  | Nil -> Accept ty0
  | Cons (a, args0) ->
    (match fuel0 with
     | O -> Decline OutOfFuel
     | S fuel1 ->
       (match ty0 with
        | EPi (_, _, _, body) ->
          nested_instantiate_params fuel1 args0 (instantiate body a)
        | _ -> Decline UnsupportedDeclaration))

(** val nested_lookup_local :
    nat -> name -> ind_local list -> ind_local list -> expr result **)

let rec nested_lookup_local fuel0 n0 xs ys =
  match xs with
  | Nil ->
    (match ys with
     | Nil -> Accept (EFVar n0)
     | Cons (_, _) -> Decline UnsupportedDeclaration)
  | Cons (x0, xs0) ->
    (match ys with
     | Nil -> Decline UnsupportedDeclaration
     | Cons (y, ys0) ->
       (match fuel0 with
        | O -> Decline OutOfFuel
        | S fuel1 ->
          (match name_eqb n0 x0.il_id with
           | True -> Accept (local_expr y)
           | False -> nested_lookup_local fuel1 n0 xs0 ys0)))

(** val nested_rebase :
    nat -> ind_local list -> ind_local list -> expr -> expr result **)

let rec nested_rebase fuel0 from to0 e =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    (match e with
     | EFVar n0 -> nested_lookup_local fuel1 n0 from to0
     | EApp (a, b) ->
       bind (nested_rebase fuel1 from to0 a) (fun a0 ->
         bind (nested_rebase fuel1 from to0 b) (fun b0 -> Accept (EApp (a0,
           b0))))
     | ELam (n0, bi, a, b) ->
       bind (nested_rebase fuel1 from to0 a) (fun a0 ->
         bind (nested_rebase fuel1 from to0 b) (fun b0 -> Accept (ELam (n0,
           bi, a0, b0))))
     | EPi (n0, bi, a, b) ->
       bind (nested_rebase fuel1 from to0 a) (fun a0 ->
         bind (nested_rebase fuel1 from to0 b) (fun b0 -> Accept (EPi (n0,
           bi, a0, b0))))
     | ELet (n0, a, v0, b, nd) ->
       bind (nested_rebase fuel1 from to0 a) (fun a0 ->
         bind (nested_rebase fuel1 from to0 v0) (fun v1 ->
           bind (nested_rebase fuel1 from to0 b) (fun b0 -> Accept (ELet (n0,
             a0, v1, b0, nd)))))
     | EProj (n0, i, a) ->
       bind (nested_rebase fuel1 from to0 a) (fun a0 -> Accept (EProj (n0, i,
         a0)))
     | EMData a ->
       bind (nested_rebase fuel1 from to0 a) (fun a0 -> Accept (EMData a0))
     | _ -> Accept e)

(** val nested_has_new : nat -> name list -> expr -> bool result **)

let rec nested_has_new fuel0 names e =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    (match e with
     | EConst (n0, _) -> Accept (name_mem n0 names)
     | EApp (a, b) ->
       bind (nested_has_new fuel1 names a) (fun a0 ->
         match a0 with
         | True -> Accept True
         | False -> nested_has_new fuel1 names b)
     | ELam (_, _, a, b) ->
       bind (nested_has_new fuel1 names a) (fun a0 ->
         match a0 with
         | True -> Accept True
         | False -> nested_has_new fuel1 names b)
     | EPi (_, _, a, b) ->
       bind (nested_has_new fuel1 names a) (fun a0 ->
         match a0 with
         | True -> Accept True
         | False -> nested_has_new fuel1 names b)
     | ELet (_, a, v0, b, _) ->
       bind (nested_has_new fuel1 names a) (fun a0 ->
         match a0 with
         | True -> Accept True
         | False ->
           bind (nested_has_new fuel1 names v0) (fun v1 ->
             match v1 with
             | True -> Accept True
             | False -> nested_has_new fuel1 names b))
     | EProj (_, _, a) -> nested_has_new fuel1 names a
     | EMData a -> nested_has_new fuel1 names a
     | _ -> Accept False)

(** val nested_any_new : nat -> name list -> expr list -> bool result **)

let rec nested_any_new fuel0 names = function
| Nil -> Accept False
| Cons (a, args0) ->
  (match fuel0 with
   | O -> Decline OutOfFuel
   | S fuel1 ->
     bind (nested_has_new fuel1 names a) (fun found ->
       match found with
       | True -> Accept True
       | False -> nested_any_new fuel1 names args0))

(** val nested_candidate :
    nat -> environment -> nested_work -> expr -> (((declaration,
    inductive_data) prod, level list) prod, expr list) prod option result **)

let nested_candidate fuel0 env w e =
  let Pair (head, args) = split_app e in
  (match args with
   | Nil -> Accept None
   | Cons (_, _) ->
     (match head with
      | EConst (n0, us) ->
        (match find_decl n0 env with
         | Some d ->
           (match d.decl_kind_of with
            | DInductive data ->
              (match Nat.leb data.ind_num_params (length args) with
               | True ->
                 let params = firstn data.ind_num_params args in
                 bind
                   (nested_any_new fuel0
                     (map (fun s -> s.spec_decl.decl_name) w.nw_specs) params)
                   (fun found ->
                   match found with
                   | True ->
                     (match forallb (scoped O) params with
                      | True ->
                        Accept (Some (Pair ((Pair ((Pair (d, data)), us)),
                          args)))
                      | False -> Reject MalformedDeclaration)
                   | False -> Accept None)
               | False -> Accept None)
            | _ -> Accept None)
         | None -> Accept None)
      | _ -> Accept None))

(** val nested_same_flags : nat -> expr -> expr -> bool result **)

let rec nested_same_flags fuel0 a b =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    (match a with
     | EApp (a0, b0) ->
       (match b with
        | EApp (c, d) ->
          bind (nested_same_flags fuel1 a0 c) (fun same ->
            match same with
            | True -> nested_same_flags fuel1 b0 d
            | False -> Accept False)
        | _ -> Accept True)
     | ELam (_, _, a0, b0) ->
       (match b with
        | ELam (_, _, c, d) ->
          bind (nested_same_flags fuel1 a0 c) (fun same ->
            match same with
            | True -> nested_same_flags fuel1 b0 d
            | False -> Accept False)
        | _ -> Accept True)
     | EPi (_, _, a0, b0) ->
       (match b with
        | EPi (_, _, c, d) ->
          bind (nested_same_flags fuel1 a0 c) (fun same ->
            match same with
            | True -> nested_same_flags fuel1 b0 d
            | False -> Accept False)
        | _ -> Accept True)
     | ELet (_, a0, v0, b0, nd) ->
       (match b with
        | ELet (_, c, w, d, md) ->
          (match eqb0 nd md with
           | True ->
             bind (nested_same_flags fuel1 a0 c) (fun same ->
               match same with
               | True ->
                 bind (nested_same_flags fuel1 v0 w) (fun same0 ->
                   match same0 with
                   | True -> nested_same_flags fuel1 b0 d
                   | False -> Accept False)
               | False -> Accept False)
           | False -> Accept False)
        | _ -> Accept True)
     | EProj (_, _, a0) ->
       (match b with
        | EProj (_, _, b0) -> nested_same_flags fuel1 a0 b0
        | _ -> Accept True)
     | EMData a0 ->
       (match b with
        | EMData b0 -> nested_same_flags fuel1 a0 b0
        | _ -> Accept True)
     | _ -> Accept True)

(** val nested_key_eq : nat -> expr -> expr -> bool result **)

let nested_key_eq fuel0 a b =
  match expr_eqb a b with
  | True -> nested_same_flags fuel0 a b
  | False -> Accept False

(** val nested_find_mapping :
    nat -> expr -> (expr, name) prod list -> name option result **)

let rec nested_find_mapping fuel0 e = function
| Nil -> Accept None
| Cons (p0, mapping0) ->
  let Pair (key0, n0) = p0 in
  (match fuel0 with
   | O -> Decline OutOfFuel
   | S fuel1 ->
     bind (nested_key_eq fuel1 key0 e) (fun same ->
       match same with
       | True -> Accept (Some n0)
       | False -> nested_find_mapping fuel1 e mapping0))

(** val nested_replace_prefix : nat -> name -> name -> name -> name result **)

let rec nested_replace_prefix fuel0 old0 new0 n0 =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    (match name_eqb n0 old0 with
     | True -> Accept new0
     | False ->
       (match n0 with
        | NameAnon -> Decline UnsupportedDeclaration
        | NameStr (p0, s) ->
          bind (nested_replace_prefix fuel1 old0 new0 p0) (fun p1 -> Accept
            (NameStr (p1, s)))
        | NameNum (p0, i) ->
          bind (nested_replace_prefix fuel1 old0 new0 p0) (fun p1 -> Accept
            (NameNum (p1, i)))))

(** val nested_aux_name : nat -> name **)

let nested_aux_name i =
  NameNum ((NameStr (NameAnon, (String ((Ascii (True, True, True, True, True,
    False, True, False)), (String ((Ascii (False, True, False, False, True,
    True, True, False)), (String ((Ascii (True, True, True, True, False,
    True, True, False)), (String ((Ascii (True, True, False, False, False,
    True, True, False)), (String ((Ascii (True, False, False, False, True,
    True, True, False)), (String ((Ascii (True, True, True, True, True,
    False, True, False)), (String ((Ascii (False, True, True, True, False,
    True, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), (String ((Ascii (True, True, False, False, True,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, False,
    True, True, False)), EmptyString)))))))))))))))))))))))))), (N.of_nat i))

(** val nested_unique_aux :
    nat -> name list -> name -> name list -> nat -> ((name, name list) prod,
    nat) prod result **)

let rec nested_unique_aux fuel0 used old0 ctors index =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    let aux0 = nested_aux_name index in
    bind (map_result (nested_replace_prefix fuel1 old0 aux0) ctors)
      (fun renamed ->
      let reserved0 = Cons (aux0, (Cons ((rec_name aux0), renamed))) in
      (match match existsb (fun n0 -> name_mem n0 used) reserved0 with
             | True -> True
             | False -> negb (names_unique reserved0) with
       | True -> nested_unique_aux fuel1 used old0 ctors (S index)
       | False -> Accept (Pair ((Pair (aux0, renamed)), (S index)))))

(** val nested_used_names : environment -> nested_work -> name list **)

let nested_used_names env w =
  app (map (fun d -> d.decl_name) env)
    (app (map (fun s -> s.spec_decl.decl_name) w.nw_specs)
      (app (map (fun s -> rec_name s.spec_decl.decl_name) w.nw_specs)
        (all_ctor_names w.nw_specs)))

(** val nested_make_ctors :
    nat -> environment -> name list -> ind_local list -> level list -> expr
    list -> name -> name list -> name list -> nat -> declaration list result **)

let rec nested_make_ctors fuel0 env ps as0 us params owner old_names new_names index =
  match old_names with
  | Nil ->
    (match new_names with
     | Nil -> Accept Nil
     | Cons (_, _) -> Decline UnsupportedDeclaration)
  | Cons (old0, olds) ->
    (match new_names with
     | Nil -> Decline UnsupportedDeclaration
     | Cons (new0, news) ->
       (match fuel0 with
        | O -> Decline OutOfFuel
        | S fuel1 ->
          (match find_decl old0 env with
           | Some d ->
             (match d.decl_kind_of with
              | DConstructor _ ->
                bind
                  (require (Nat.eqb (length d.decl_params) (length us))
                    UniverseArity)
                  (fun _ ->
                  bind
                    (nested_instantiate_params fuel1 params
                      (subst_levels d.decl_params us d.decl_type))
                    (fun ty0 ->
                    bind
                      (nested_make_ctors fuel1 env ps as0 us params owner
                        olds news (S index))
                      (fun rest -> Accept (Cons ({ decl_name = new0;
                      decl_params = ps; decl_type = (close_pi as0 ty0);
                      decl_value = None; decl_kind_of = (DConstructor
                      { ctor_induct = owner; ctor_index = index;
                      ctor_num_params = (length as0); ctor_num_fields = O;
                      ctor_is_unsafe = False }); decl_hints = HintOpaque },
                      rest)))))
              | _ -> Decline UnsupportedDeclaration)
           | None -> Decline UnsupportedDeclaration)))

(** val nested_expand_family :
    nat -> environment -> name list -> ind_local list -> ind_local list ->
    level list -> expr list -> name list -> nested_work -> nested_work result **)

let rec nested_expand_family fuel0 env ps params as0 us old_params family w =
  match family with
  | Nil -> Accept w
  | Cons (old0, family0) ->
    (match fuel0 with
     | O -> Decline OutOfFuel
     | S fuel1 ->
       (match find_decl old0 env with
        | Some d ->
          (match d.decl_kind_of with
           | DInductive data ->
             bind
               (require (Nat.eqb (length d.decl_params) (length us))
                 UniverseArity)
               (fun _ ->
               match negb (Nat.eqb data.ind_num_params (length old_params)) with
               | True -> Decline UnsupportedDeclaration
               | False ->
                 bind
                   (nested_unique_aux fuel1 (nested_used_names env w) old0
                     data.ind_ctors w.nw_next_aux)
                   (fun fresh ->
                   let Pair (p0, next) = fresh in
                   let Pair (aux0, ctor_names) = p0 in
                   bind
                     (nested_instantiate_params fuel1 old_params
                       (subst_levels d.decl_params us d.decl_type))
                     (fun ty0 ->
                     bind
                       (nested_rebase fuel1 as0 params
                         (apply_exprs (EConst (old0, us)) old_params))
                       (fun key0 ->
                       bind
                         (nested_make_ctors fuel1 env ps as0 us old_params
                           aux0 data.ind_ctors ctor_names O)
                         (fun ctors ->
                         let spec = { spec_decl = { decl_name = aux0;
                           decl_params = ps; decl_type = (close_pi as0 ty0);
                           decl_value = None; decl_kind_of = (DInductive
                           { ind_num_params = (length as0); ind_num_indices =
                           O; ind_all = Nil; ind_ctors = ctor_names;
                           ind_num_nested = O; ind_is_rec = False;
                           ind_is_reflexive = False; ind_is_unsafe =
                           False }); decl_hints = HintOpaque }; spec_ctors =
                           ctors }
                         in
                         nested_expand_family fuel1 env ps params as0 us
                           old_params family0 { nw_specs =
                           (app w.nw_specs (Cons (spec, Nil))); nw_mapping =
                           (app w.nw_mapping (Cons ((Pair (key0, aux0)),
                             Nil)));
                           nw_next_aux = next; nw_next_local =
                           w.nw_next_local })))))
           | _ -> Decline UnsupportedDeclaration)
        | None -> Decline UnsupportedDeclaration))

(** val nested_replace_root :
    nat -> environment -> name list -> ind_local list -> ind_local list ->
    expr -> nested_work -> (expr option, nested_work) prod result **)

let nested_replace_root fuel0 env ps params as0 e w =
  bind (nested_candidate fuel0 env w e) (fun candidate ->
    match candidate with
    | Some p0 ->
      let Pair (p1, args) = p0 in
      let Pair (p2, us) = p1 in
      let Pair (d, data) = p2 in
      let old_params = firstn data.ind_num_params args in
      bind
        (nested_rebase fuel0 as0 params
          (apply_exprs (EConst (d.decl_name, us)) old_params))
        (fun key0 ->
        bind (nested_find_mapping fuel0 key0 w.nw_mapping) (fun found ->
          bind
            (match found with
             | Some _ -> Accept w
             | None ->
               nested_expand_family fuel0 env ps params as0 us old_params
                 data.ind_all w)
            (fun w0 ->
            bind (nested_find_mapping fuel0 key0 w0.nw_mapping)
              (fun found0 ->
              match found0 with
              | Some aux0 ->
                Accept (Pair ((Some
                  (apply_exprs
                    (apply_locals (EConst (aux0,
                      (map (fun x0 -> LParam x0) ps))) as0)
                    (skipn data.ind_num_params args))),
                  w0))
              | None -> Decline UnsupportedDeclaration))))
    | None -> Accept (Pair (None, w)))

(** val nested_rewrite :
    nat -> environment -> name list -> ind_local list -> ind_local list ->
    expr -> nested_work -> (expr, nested_work) prod result **)

let rec nested_rewrite fuel0 env ps params as0 e w =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    bind (nested_replace_root fuel1 env ps params as0 e w) (fun replaced ->
      let Pair (replacement, w0) = replaced in
      (match replacement with
       | Some e0 -> Accept (Pair (e0, w0))
       | None ->
         (match e with
          | EApp (a, b) ->
            bind (nested_rewrite fuel1 env ps params as0 a w0) (fun first ->
              let Pair (a0, w1) = first in
              bind (nested_rewrite fuel1 env ps params as0 b w1)
                (fun second ->
                let Pair (b0, w2) = second in
                Accept (Pair ((EApp (a0, b0)), w2))))
          | ELam (n0, bi, a, b) ->
            bind (nested_rewrite fuel1 env ps params as0 a w0) (fun first ->
              let Pair (a0, w1) = first in
              bind (nested_rewrite fuel1 env ps params as0 b w1)
                (fun second ->
                let Pair (b0, w2) = second in
                Accept (Pair ((ELam (n0, bi, a0, b0)), w2))))
          | EPi (n0, bi, a, b) ->
            bind (nested_rewrite fuel1 env ps params as0 a w0) (fun first ->
              let Pair (a0, w1) = first in
              bind (nested_rewrite fuel1 env ps params as0 b w1)
                (fun second ->
                let Pair (b0, w2) = second in
                Accept (Pair ((EPi (n0, bi, a0, b0)), w2))))
          | ELet (n0, a, v0, b, nd) ->
            bind (nested_rewrite fuel1 env ps params as0 a w0) (fun first ->
              let Pair (a0, w1) = first in
              bind (nested_rewrite fuel1 env ps params as0 v0 w1)
                (fun second ->
                let Pair (v1, w2) = second in
                bind (nested_rewrite fuel1 env ps params as0 b w2)
                  (fun third ->
                  let Pair (b0, w3) = third in
                  Accept (Pair ((ELet (n0, a0, v1, b0, nd)), w3)))))
          | EProj (n0, i, a) ->
            bind (nested_rewrite fuel1 env ps params as0 a w0) (fun first ->
              let Pair (a0, w1) = first in
              Accept (Pair ((EProj (n0, i, a0)), w1)))
          | EMData a ->
            bind (nested_rewrite fuel1 env ps params as0 a w0) (fun first ->
              let Pair (a0, w1) = first in Accept (Pair ((EMData a0), w1)))
          | _ -> Accept (Pair (e, w0)))))

(** val nested_rewrite_ctors :
    nat -> environment -> name list -> nat -> ind_local list -> declaration
    list -> nested_work -> (declaration list, nested_work) prod result **)

let rec nested_rewrite_ctors fuel0 env ps nparams params ctors w =
  match ctors with
  | Nil -> Accept (Pair (Nil, w))
  | Cons (d, ctors0) ->
    (match fuel0 with
     | O -> Decline OutOfFuel
     | S fuel1 ->
       bind
         (nested_open_params fuel1 nparams { ist_next = w.nw_next_local;
           ist_context = empty_context } d.decl_type)
         (fun opened ->
         let Pair (p0, s) = opened in
         let Pair (as0, body) = p0 in
         bind
           (nested_rewrite fuel1 env ps params as0 body
             (nested_set_local w s.ist_next))
           (fun rewritten ->
           let Pair (body0, w0) = rewritten in
           bind (nested_rewrite_ctors fuel1 env ps nparams params ctors0 w0)
             (fun tail ->
             let Pair (rest, w1) = tail in
             Accept (Pair ((Cons ({ decl_name = d.decl_name; decl_params =
             d.decl_params; decl_type = (close_pi as0 body0); decl_value =
             d.decl_value; decl_kind_of = d.decl_kind_of; decl_hints =
             d.decl_hints }, rest)), w1))))))

(** val nested_replace_spec :
    nat -> nat -> ind_spec -> ind_spec list -> ind_spec list result **)

let rec nested_replace_spec fuel0 index spec specs =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    (match index with
     | O ->
       (match specs with
        | Nil -> Decline UnsupportedDeclaration
        | Cons (_, rest) -> Accept (Cons (spec, rest)))
     | S index0 ->
       (match specs with
        | Nil -> Decline UnsupportedDeclaration
        | Cons (head, rest) ->
          bind (nested_replace_spec fuel1 index0 spec rest) (fun rest0 ->
            Accept (Cons (head, rest0)))))

(** val nested_worklist :
    nat -> nat -> environment -> name list -> nat -> ind_local list ->
    nested_work -> nested_work result **)

let rec nested_worklist fuel0 index env ps nparams params w =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    (match nth_error w.nw_specs index with
     | Some spec ->
       bind
         (nested_rewrite_ctors fuel1 env ps nparams params spec.spec_ctors w)
         (fun rewritten ->
         let Pair (ctors, w0) = rewritten in
         bind
           (nested_replace_spec fuel1 index { spec_decl = spec.spec_decl;
             spec_ctors = ctors } w0.nw_specs)
           (fun specs ->
           nested_worklist fuel1 (S index) env ps nparams params
             (nested_set_specs w0 specs)))
     | None -> Accept w)

(** val eliminate_nested :
    nat -> environment -> name list -> nat -> ind_spec list ->
    nested_elimination result **)

let eliminate_nested fuel0 env ps nparams specs =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S remaining ->
    (match specs with
     | Nil -> Reject MalformedDeclaration
     | Cons (first, _) ->
       bind
         (nested_open_params remaining nparams initial_ind_state
           first.spec_decl.decl_type)
         (fun opened ->
         let Pair (p0, s) = opened in
         let Pair (params, _) = p0 in
         bind
           (nested_worklist remaining O env ps nparams params { nw_specs =
             specs; nw_mapping = Nil; nw_next_aux = (S O); nw_next_local =
             s.ist_next })
           (fun w ->
           let aux_names = map snd w.nw_mapping in
           Accept { nested_params = params; nested_context = s.ist_context;
           nested_specs = w.nw_specs; nested_mapping = w.nw_mapping;
           nested_aux_names = aux_names; nested_aux_count =
           (length aux_names) })))

module NilEmpty =
 struct
  (** val string_of_uint : uint -> string **)

  let rec string_of_uint = function
  | Nil0 -> EmptyString
  | D0 d0 ->
    String ((Ascii (False, False, False, False, True, True, False, False)),
      (string_of_uint d0))
  | D1 d0 ->
    String ((Ascii (True, False, False, False, True, True, False, False)),
      (string_of_uint d0))
  | D2 d0 ->
    String ((Ascii (False, True, False, False, True, True, False, False)),
      (string_of_uint d0))
  | D3 d0 ->
    String ((Ascii (True, True, False, False, True, True, False, False)),
      (string_of_uint d0))
  | D4 d0 ->
    String ((Ascii (False, False, True, False, True, True, False, False)),
      (string_of_uint d0))
  | D5 d0 ->
    String ((Ascii (True, False, True, False, True, True, False, False)),
      (string_of_uint d0))
  | D6 d0 ->
    String ((Ascii (False, True, True, False, True, True, False, False)),
      (string_of_uint d0))
  | D7 d0 ->
    String ((Ascii (True, True, True, False, True, True, False, False)),
      (string_of_uint d0))
  | D8 d0 ->
    String ((Ascii (False, False, False, True, True, True, False, False)),
      (string_of_uint d0))
  | D9 d0 ->
    String ((Ascii (True, False, False, True, True, True, False, False)),
      (string_of_uint d0))
 end

module NilZero =
 struct
  (** val string_of_uint : uint -> string **)

  let string_of_uint d = match d with
  | Nil0 ->
    String ((Ascii (False, False, False, False, True, True, False, False)),
      EmptyString)
  | _ -> NilEmpty.string_of_uint d
 end

(** val restore_lookup : name -> (expr, name) prod list -> expr option **)

let rec restore_lookup n0 = function
| Nil -> None
| Cons (p0, mapping0) ->
  let Pair (e, m) = p0 in
  (match name_eqb n0 m with
   | True -> Some e
   | False -> restore_lookup n0 mapping0)

(** val restore_name : name -> (name, name) prod list -> name **)

let rec restore_name n0 = function
| Nil -> n0
| Cons (p0, mapping0) ->
  let Pair (old0, new0) = p0 in
  (match name_eqb old0 n0 with
   | True -> new0
   | False -> restore_name n0 mapping0)

(** val local_replacement :
    name -> ind_local list -> expr list -> expr option **)

let rec local_replacement n0 ps values =
  match ps with
  | Nil -> None
  | Cons (p0, ps0) ->
    (match values with
     | Nil -> None
     | Cons (v0, vs) ->
       (match name_eqb n0 p0.il_id with
        | True -> Some v0
        | False -> local_replacement n0 ps0 vs))

(** val instantiate_locals :
    ind_local list -> expr list -> nat -> expr -> expr **)

let rec instantiate_locals ps values depth e = match e with
| EFVar n0 ->
  (match local_replacement n0 ps values with
   | Some v0 -> lift depth O v0
   | None -> e)
| EApp (f, a) ->
  EApp ((instantiate_locals ps values depth f),
    (instantiate_locals ps values depth a))
| ELam (n0, bi, a, b) ->
  ELam (n0, bi, (instantiate_locals ps values depth a),
    (instantiate_locals ps values (S depth) b))
| EPi (n0, bi, a, b) ->
  EPi (n0, bi, (instantiate_locals ps values depth a),
    (instantiate_locals ps values (S depth) b))
| ELet (n0, a, v0, b, nd) ->
  ELet (n0, (instantiate_locals ps values depth a),
    (instantiate_locals ps values depth v0),
    (instantiate_locals ps values (S depth) b), nd)
| EProj (n0, i, a) -> EProj (n0, i, (instantiate_locals ps values depth a))
| EMData a -> EMData (instantiate_locals ps values depth a)
| _ -> e

(** val nested_ctor_pattern :
    environment -> nested_elimination -> name -> (expr, name) prod option **)

let nested_ctor_pattern generated res n0 =
  match find_decl n0 generated with
  | Some d ->
    (match d.decl_kind_of with
     | DConstructor c ->
       (match restore_lookup c.ctor_induct res.nested_mapping with
        | Some pattern -> Some (Pair (pattern, c.ctor_induct))
        | None -> None)
     | _ -> None)
  | None -> None

(** val restore_ctor_name :
    nat -> environment -> nested_elimination -> name -> name result **)

let restore_ctor_name fuel0 generated res n0 =
  match nested_ctor_pattern generated res n0 with
  | Some p0 ->
    let Pair (pattern, aux0) = p0 in
    (match fst (split_app pattern) with
     | EConst (original, _) -> nested_replace_prefix fuel0 aux0 original n0
     | _ -> Reject MalformedDeclaration)
  | None -> Accept n0

(** val rewrite_nested_head :
    nat -> environment -> nested_elimination -> (name, name) prod list ->
    name -> level list -> expr list -> expr result **)

let rewrite_nested_head fuel0 generated res rec_map0 n0 us args =
  let np = length res.nested_params in
  (match restore_lookup n0 res.nested_mapping with
   | Some pattern ->
     bind (require (Nat.leb np (length args)) MalformedDeclaration) (fun _ ->
       Accept
       (apply_exprs
         (instantiate_locals res.nested_params (firstn np args) O pattern)
         (skipn np args)))
   | None ->
     (match nested_ctor_pattern generated res n0 with
      | Some p0 ->
        let Pair (pattern, aux0) = p0 in
        bind (require (Nat.leb np (length args)) MalformedDeclaration)
          (fun _ ->
          let pattern0 =
            instantiate_locals res.nested_params (firstn np args) O pattern
          in
          let Pair (head, parameters0) = split_app pattern0 in
          (match head with
           | EConst (original, levels) ->
             bind (nested_replace_prefix fuel0 aux0 original n0) (fun ctor ->
               Accept
               (apply_exprs (EConst (ctor, levels))
                 (app parameters0 (skipn np args))))
           | _ -> Reject MalformedDeclaration))
      | None ->
        Accept (apply_exprs (EConst ((restore_name n0 rec_map0), us)) args)))

(** val restore_nested_expr :
    nat -> environment -> nested_elimination -> (name, name) prod list ->
    expr -> expr result **)

let rec restore_nested_expr fuel0 generated res rec_map0 e =
  match fuel0 with
  | O -> Decline OutOfFuel
  | S fuel1 ->
    (match e with
     | EConst (n0, us) ->
       rewrite_nested_head fuel1 generated res rec_map0 n0 us Nil
     | EApp (_, _) ->
       let Pair (head, args) = split_app e in
       bind
         (map_result (restore_nested_expr fuel1 generated res rec_map0) args)
         (fun args0 ->
         match head with
         | EConst (n0, us) ->
           rewrite_nested_head fuel1 generated res rec_map0 n0 us args0
         | _ ->
           bind (restore_nested_expr fuel1 generated res rec_map0 head)
             (fun head0 -> Accept (apply_exprs head0 args0)))
     | ELam (n0, bi, a, b) ->
       bind (restore_nested_expr fuel1 generated res rec_map0 a) (fun a0 ->
         bind (restore_nested_expr fuel1 generated res rec_map0 b) (fun b0 ->
           Accept (ELam (n0, bi, a0, b0))))
     | EPi (n0, bi, a, b) ->
       bind (restore_nested_expr fuel1 generated res rec_map0 a) (fun a0 ->
         bind (restore_nested_expr fuel1 generated res rec_map0 b) (fun b0 ->
           Accept (EPi (n0, bi, a0, b0))))
     | ELet (n0, a, v0, b, nd) ->
       bind (restore_nested_expr fuel1 generated res rec_map0 a) (fun a0 ->
         bind (restore_nested_expr fuel1 generated res rec_map0 v0)
           (fun v1 ->
           bind (restore_nested_expr fuel1 generated res rec_map0 b)
             (fun b0 -> Accept (ELet (n0, a0, v1, b0, nd)))))
     | EProj (n0, i, a) ->
       bind (restore_nested_expr fuel1 generated res rec_map0 a) (fun a0 ->
         Accept (EProj (n0, i, a0)))
     | EMData a ->
       bind (restore_nested_expr fuel1 generated res rec_map0 a) (fun a0 ->
         Accept (EMData a0))
     | _ -> Accept e)

(** val restore_open :
    nat -> ind_state -> expr -> (ind_local list, expr) prod result **)

let rec restore_open count s e =
  match count with
  | O -> Accept (Pair (Nil, e))
  | S count0 ->
    (match e with
     | ELam (n0, bi, a, b) ->
       let Pair (x0, s0) = ind_fresh s n0 bi a in
       bind (restore_open count0 s0 (instantiate b (local_expr x0)))
         (fun rest ->
         let Pair (xs, body) = rest in Accept (Pair ((Cons (x0, xs)), body)))
     | EPi (n0, bi, a, b) ->
       let Pair (x0, s0) = ind_fresh s n0 bi a in
       bind (restore_open count0 s0 (instantiate b (local_expr x0)))
         (fun rest ->
         let Pair (xs, body) = rest in Accept (Pair ((Cons (x0, xs)), body)))
     | _ -> Reject MalformedDeclaration)

(** val restore_nested_type :
    nat -> environment -> nested_elimination -> (name, name) prod list ->
    expr -> expr result **)

let restore_nested_type fuel0 generated res rec_map0 e =
  bind (restore_open (length res.nested_params) initial_ind_state e)
    (fun opened ->
    let Pair (params, body) = opened in
    let mapping =
      map (fun entry ->
        let Pair (pattern, n0) = entry in
        Pair
        ((instantiate_locals res.nested_params (local_exprs params) O pattern),
        n0)) res.nested_mapping
    in
    let rebased = { nested_params = params; nested_context =
      res.nested_context; nested_specs = res.nested_specs; nested_mapping =
      mapping; nested_aux_names = res.nested_aux_names; nested_aux_count =
      res.nested_aux_count }
    in
    bind (restore_nested_expr fuel0 generated rebased rec_map0 body)
      (fun body0 ->
      match e with
      | EPi (_, _, _, _) -> Accept (close_pi params body0)
      | _ -> Accept (close_lam params body0)))

(** val indexed_rec_name : name -> nat -> name **)

let indexed_rec_name main i =
  NameStr (main,
    (append (String ((Ascii (False, True, False, False, True, True, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (True, True, False, False, False, True, True,
      False)), (String ((Ascii (True, True, True, True, True, False, True,
      False)), EmptyString)))))))) (NilZero.string_of_uint (Nat.to_uint i))))

(** val auxiliary_rec_names :
    name -> name list -> nat -> (name, name) prod list **)

let rec auxiliary_rec_names main names i =
  match names with
  | Nil -> Nil
  | Cons (n0, names0) ->
    Cons ((Pair ((rec_name n0), (indexed_rec_name main i))),
      (auxiliary_rec_names main names0 (S i)))

(** val restore_rule :
    nat -> environment -> nested_elimination -> (name, name) prod list ->
    recursor_rule -> recursor_rule result **)

let restore_rule fuel0 generated res rec_map0 r =
  bind (restore_ctor_name fuel0 generated res r.rule_ctor) (fun ctor ->
    bind (restore_nested_type fuel0 generated res rec_map0 r.rule_rhs)
      (fun rhs -> Accept { rule_ctor = ctor; rule_nfields = r.rule_nfields;
      rule_rhs = rhs }))

(** val restore_recursor :
    nat -> environment -> nested_elimination -> (name, name) prod list ->
    name list -> name -> declaration result **)

let restore_recursor fuel0 generated res rec_map0 all old0 =
  match find_decl old0 generated with
  | Some d ->
    (match d.decl_kind_of with
     | DRecursor info ->
       bind (restore_nested_type fuel0 generated res rec_map0 d.decl_type)
         (fun ty0 ->
         bind
           (map_result (restore_rule fuel0 generated res rec_map0)
             info.rec_rules)
           (fun rules -> Accept { decl_name = (restore_name old0 rec_map0);
           decl_params = d.decl_params; decl_type = ty0; decl_value = None;
           decl_kind_of = (DRecursor { rec_all = all; rec_num_params =
           info.rec_num_params; rec_num_indices = info.rec_num_indices;
           rec_num_motives = info.rec_num_motives; rec_num_minors =
           info.rec_num_minors; rec_rules = rules; rec_k = info.rec_k;
           rec_is_unsafe = info.rec_is_unsafe }); decl_hints = HintOpaque }))
     | _ -> Reject MalformedDeclaration)
  | None -> Reject UnknownConstant

(** val restore_constructor :
    nat -> environment -> nested_elimination -> name -> declaration result **)

let restore_constructor fuel0 generated res n0 =
  match find_decl n0 generated with
  | Some d ->
    (match d.decl_kind_of with
     | DConstructor info ->
       bind (restore_nested_type fuel0 generated res Nil d.decl_type)
         (fun ty0 -> Accept { decl_name = n0; decl_params = d.decl_params;
         decl_type = ty0; decl_value = None; decl_kind_of = (DConstructor
         info); decl_hints = HintOpaque })
     | _ -> Reject MalformedDeclaration)
  | None -> Reject UnknownConstant

(** val restore_inductive :
    environment -> nested_elimination -> name list -> name -> declaration
    result **)

let restore_inductive generated res all n0 =
  match find_decl n0 generated with
  | Some d ->
    (match d.decl_kind_of with
     | DInductive info ->
       Accept { decl_name = n0; decl_params = d.decl_params; decl_type =
         d.decl_type; decl_value = None; decl_kind_of = (DInductive
         { ind_num_params = info.ind_num_params; ind_num_indices =
         info.ind_num_indices; ind_all = all; ind_ctors = info.ind_ctors;
         ind_num_nested = res.nested_aux_count; ind_is_rec = info.ind_is_rec;
         ind_is_reflexive = info.ind_is_reflexive; ind_is_unsafe =
         info.ind_is_unsafe }); decl_hints = HintOpaque }
     | _ -> Reject MalformedDeclaration)
  | None -> Reject UnknownConstant

(** val name_prefix : name -> name -> bool **)

let rec name_prefix prefix0 n0 =
  match name_eqb prefix0 n0 with
  | True -> True
  | False ->
    (match n0 with
     | NameAnon -> False
     | NameStr (p0, _) -> name_prefix prefix0 p0
     | NameNum (p0, _) -> name_prefix prefix0 p0)

(** val uses_reserved_nested : expr -> bool **)

let rec uses_reserved_nested = function
| EConst (n0, _) ->
  name_prefix (NameStr (NameAnon, (String ((Ascii (True, True, True, True,
    True, False, True, False)), (String ((Ascii (False, True, True, True,
    False, True, True, False)), (String ((Ascii (True, False, True, False,
    False, True, True, False)), (String ((Ascii (True, True, False, False,
    True, True, True, False)), (String ((Ascii (False, False, True, False,
    True, True, True, False)), (String ((Ascii (True, False, True, False,
    False, True, True, False)), (String ((Ascii (False, False, True, False,
    False, True, True, False)), EmptyString)))))))))))))))) n0
| EApp (a, b) ->
  (match uses_reserved_nested a with
   | True -> True
   | False -> uses_reserved_nested b)
| ELam (_, _, a, b) ->
  (match uses_reserved_nested a with
   | True -> True
   | False -> uses_reserved_nested b)
| EPi (_, _, a, b) ->
  (match uses_reserved_nested a with
   | True -> True
   | False -> uses_reserved_nested b)
| ELet (_, a, v0, b, _) ->
  (match match uses_reserved_nested a with
         | True -> True
         | False -> uses_reserved_nested v0 with
   | True -> True
   | False -> uses_reserved_nested b)
| EProj (n0, _, a) ->
  (match name_prefix (NameStr (NameAnon, (String ((Ascii (True, True, True,
           True, True, False, True, False)), (String ((Ascii (False, True,
           True, True, False, True, True, False)), (String ((Ascii (True,
           False, True, False, False, True, True, False)), (String ((Ascii
           (True, True, False, False, True, True, True, False)), (String
           ((Ascii (False, False, True, False, True, True, True, False)),
           (String ((Ascii (True, False, True, False, False, True, True,
           False)), (String ((Ascii (False, False, True, False, False, True,
           True, False)), EmptyString)))))))))))))))) n0 with
   | True -> True
   | False -> uses_reserved_nested a)
| EMData a -> uses_reserved_nested a
| _ -> False

(** val admit_inductive_nested :
    nat -> environment -> declaration list -> declaration list -> declaration
    list -> environment result **)

let admit_inductive_nested fuel0 env types ctors recs =
  bind (prepare_inductive env types ctors recs) (fun prepared ->
    let Pair (p0, specs) = prepared in
    let Pair (ps, np) = p0 in
    bind
      (require
        (negb (existsb (fun d -> uses_reserved_nested d.decl_type) ctors))
        MalformedDeclaration)
      (fun _ ->
      bind (eliminate_nested fuel0 env ps np specs) (fun transformed ->
        bind (derive_inductive fuel0 env ps np transformed.nested_specs)
          (fun generated ->
          match Nat.eqb transformed.nested_aux_count O with
          | True ->
            bind (verify_members (app types (app ctors recs)) generated)
              (fun _ -> Accept (app generated env))
          | False ->
            (match types with
             | Nil -> Reject MalformedDeclaration
             | Cons (main, _) ->
               let all = ind_names types in
               let auxiliary =
                 skipn (length types)
                   (map (fun s -> s.spec_decl.decl_name)
                     transformed.nested_specs)
               in
               let rec_map0 =
                 auxiliary_rec_names main.decl_name auxiliary (S O)
               in
               bind
                 (map_result (restore_inductive generated transformed all)
                   all)
                 (fun restored_inds ->
                 bind
                   (map_result
                     (restore_constructor fuel0 generated transformed)
                     (ind_names ctors))
                   (fun restored_ctors ->
                   bind
                     (map_result
                       (restore_recursor fuel0 generated transformed rec_map0
                         all)
                       (map rec_name (app all auxiliary)))
                     (fun restored_recs ->
                     let restored =
                       app restored_recs (app restored_ctors restored_inds)
                     in
                     bind
                       (verify_members (app types (app ctors recs)) restored)
                       (fun _ ->
                       let final_env = app restored env in
                       bind
                         (map_result (fun entry ->
                           bind
                             (infer fuel0 final_env ps
                               transformed.nested_context (fst entry))
                             (fun _ -> Accept Tt))
                           transformed.nested_mapping)
                         (fun _ -> Accept final_env))))))))))

(** val mark_unsafe_inductive : declaration -> declaration **)

let mark_unsafe_inductive d =
  { decl_name = d.decl_name; decl_params = d.decl_params; decl_type =
    d.decl_type; decl_value = d.decl_value; decl_kind_of = (DUnsafe
    d.decl_kind_of); decl_hints = d.decl_hints }

(** val inductive_input_unsafe : declaration list -> bool **)

let inductive_input_unsafe = function
| Nil -> False
| Cons (d, _) ->
  (match d.decl_kind_of with
   | DInductive i -> i.ind_is_unsafe
   | _ -> False)

(** val admit_inductive_extended :
    nat -> environment -> declaration list -> declaration list -> declaration
    list -> environment result **)

let admit_inductive_extended fuel0 env types ctors recs =
  match inductive_input_unsafe types with
  | True ->
    let view = safety_environment InputUnsafe env in
    bind (admit_inductive_nested fuel0 view types ctors recs) (fun next ->
      let generated =
        filter (fun d ->
          match find_decl d.decl_name env with
          | Some _ -> False
          | None -> True) next
      in
      Accept (app (map mark_unsafe_inductive generated) env))
  | False -> admit_inductive_nested fuel0 env types ctors recs

(** val result_map : ('a1 -> 'a2) -> 'a1 result -> 'a2 result **)

let result_map f r =
  bind r (fun x0 -> Accept (f x0))

(** val single_delta : environment result -> declaration list result **)

let single_delta r =
  result_map (firstn (S O)) r

(** val mutual_delta :
    nat -> declaration list -> input_decl list -> environment result **)

let mutual_delta fuel0 env inputs = match inputs with
| Nil -> Reject MalformedDeclaration
| Cons (y, _) ->
  (match y with
   | InputDefinition (_, _, ps, _, _, mode) ->
     bind (require (negb (safety_eqb mode InputSafe)) MalformedDeclaration)
       (fun _ ->
       bind
         (require (names_unique (map mutual_name inputs))
           DuplicateDeclaration)
         (fun _ ->
         let view = safety_environment mode env in
         bind (check_mutual_headers fuel0 view ps mode inputs)
           (fun placeholders ->
           bind (check_mutual_values fuel0 (app placeholders view) inputs)
             (fun generated -> Accept generated))))
   | _ -> Reject MalformedDeclaration)

(** val nested_delta :
    nat -> environment -> declaration list -> declaration list -> declaration
    list -> environment result **)

let nested_delta fuel0 env types ctors recs =
  bind (prepare_inductive env types ctors recs) (fun prepared ->
    let Pair (p0, specs) = prepared in
    let Pair (ps, np) = p0 in
    bind
      (require
        (negb (existsb (fun d -> uses_reserved_nested d.decl_type) ctors))
        MalformedDeclaration)
      (fun _ ->
      bind (eliminate_nested fuel0 env ps np specs) (fun transformed ->
        bind (derive_inductive fuel0 env ps np transformed.nested_specs)
          (fun generated ->
          match eqb transformed.nested_aux_count O with
          | True ->
            bind (verify_members (app types (app ctors recs)) generated)
              (fun _ -> Accept generated)
          | False ->
            (match types with
             | Nil -> Reject MalformedDeclaration
             | Cons (main, _) ->
               let all = ind_names types in
               let auxiliary =
                 skipn (length types)
                   (map (fun s -> s.spec_decl.decl_name)
                     transformed.nested_specs)
               in
               let rec_map0 =
                 auxiliary_rec_names main.decl_name auxiliary (S O)
               in
               bind
                 (map_result (restore_inductive generated transformed all)
                   all)
                 (fun restored_inds ->
                 bind
                   (map_result
                     (restore_constructor fuel0 generated transformed)
                     (ind_names ctors))
                   (fun restored_ctors ->
                   bind
                     (map_result
                       (restore_recursor fuel0 generated transformed rec_map0
                         all)
                       (map rec_name (app all auxiliary)))
                     (fun restored_recs ->
                     let restored =
                       app restored_recs (app restored_ctors restored_inds)
                     in
                     bind
                       (verify_members (app types (app ctors recs)) restored)
                       (fun _ ->
                       let final_env = app restored env in
                       bind
                         (map_result (fun entry ->
                           bind
                             (infer fuel0 final_env ps
                               transformed.nested_context (fst entry))
                             (fun _ -> Accept Tt))
                           transformed.nested_mapping)
                         (fun _ -> Accept restored))))))))))

(** val inductive_delta :
    nat -> declaration list -> declaration list -> declaration list ->
    declaration list -> environment result **)

let inductive_delta fuel0 env types ctors recs =
  match inductive_input_unsafe types with
  | True ->
    let view = safety_environment InputUnsafe env in
    bind (admit_inductive_nested fuel0 view types ctors recs) (fun next ->
      let generated =
        filter (fun d ->
          match find_decl d.decl_name env with
          | Some _ -> False
          | None -> True) next
      in
      Accept (map mark_unsafe_inductive generated))
  | False -> nested_delta fuel0 env types ctors recs

(** val cached_dag_admit :
    (name -> n) -> indexed_state -> dag_admission_kind -> nat -> nat -> name
    -> name list -> (PositiveMap.key, dag_node) prod list -> positive ->
    positive -> environment result **)

let cached_dag_admit hash s kind budget fuel0 n0 ps rows0 tr br =
  let env = s.state_environment in
  (match use_index fuel0 env with
   | True ->
     admit_with_preparation (fun _ -> state_lookup hash s) kind budget fuel0
       env n0 ps rows0 tr br
   | False -> linear_env_admit kind budget fuel0 env n0 ps rows0 tr br)

type admission_batch =
| BatchDag of dag_admission_kind * nat * name * name list
   * (positive, dag_node) prod list * positive * positive
| BatchOrdinary of input_decl
| BatchQuotient of name * name list * expr * quotient_kind
| BatchInductive of declaration list * declaration list * declaration list
| BatchMutual of input_decl list

(** val reference_batch :
    nat -> environment -> admission_batch -> environment result **)

let reference_batch fuel0 env = function
| BatchDag (kind, budget, n0, ps, rows0, tr, br) ->
  indexed_dag_admit kind budget fuel0 env n0 ps rows0 tr br
| BatchOrdinary input -> admit_extended fuel0 env input
| BatchQuotient (n0, ps, ty0, kind) -> admit_quotient fuel0 env n0 ps ty0 kind
| BatchInductive (types, ctors, recs) ->
  admit_inductive_extended fuel0 env types ctors recs
| BatchMutual inputs -> admit_mutual fuel0 env inputs

(** val batch_delta :
    (name -> n) -> nat -> indexed_state -> admission_batch -> environment
    result **)

let batch_delta hash fuel0 s request =
  let env = s.state_environment in
  (match request with
   | BatchDag (kind, budget, n0, ps, rows0, tr, br) ->
     single_delta
       (cached_dag_admit hash s kind budget fuel0 n0 ps rows0 tr br)
   | BatchOrdinary input -> single_delta (admit_extended fuel0 env input)
   | BatchQuotient (n0, ps, ty0, kind) ->
     single_delta (admit_quotient fuel0 env n0 ps ty0 kind)
   | BatchInductive (types, ctors, recs) ->
     inductive_delta fuel0 env types ctors recs
   | BatchMutual inputs -> mutual_delta fuel0 env inputs)

(** val state_step :
    (name -> n) -> nat -> indexed_state -> admission_batch -> indexed_state
    result **)

let state_step hash fuel0 s request =
  bind (batch_delta hash fuel0 s request) (fun added -> Accept
    (extend_state hash s added))

(** val project_result :
    (name -> n) -> indexed_state result -> environment result **)

let project_result _ r =
  result_map (fun i -> i.state_environment) r

(** val transaction :
    (name -> n) -> nat -> indexed_state -> admission_batch -> (indexed_state,
    unit0 result) prod **)

let transaction hash fuel0 s request =
  match state_step hash fuel0 s request with
  | Accept next -> Pair (next, (Accept Tt))
  | Reject reason -> Pair (s, (Reject reason))
  | Decline reason -> Pair (s, (Decline reason))

(** val state_stream :
    (name -> n) -> nat -> indexed_state -> admission_batch list ->
    indexed_state result **)

let rec state_stream hash fuel0 s = function
| Nil -> Accept s
| Cons (request, rest) ->
  bind (state_step hash fuel0 s request) (fun next ->
    state_stream hash fuel0 next rest)

(** val reference_stream :
    nat -> environment -> admission_batch list -> environment result **)

let rec reference_stream fuel0 env = function
| Nil -> Accept env
| Cons (request, rest) ->
  bind (reference_batch fuel0 env request) (fun next ->
    reference_stream fuel0 next rest)

(** val generated_batch :
    environment -> name list -> nat -> ind_spec list -> admission_batch result **)

let generated_batch env ps np specs =
  bind (derive_inductive Metadata.fuel env ps np specs) (fun generated ->
    Accept (BatchInductive ((filter Metadata.is_ind generated),
    (filter Metadata.is_ctor generated), (filter Metadata.is_rec generated))))

module NestedRegression =
 struct
  (** val nm : string -> name **)

  let nm s =
    NameStr (NameAnon, s)

  (** val ty : expr **)

  let ty =
    ESort (LSucc LZero)

  (** val pi : expr -> expr -> expr **)

  let pi x0 x1 =
    EPi (NameAnon, BDefault, x0, x1)

  (** val lam : expr -> expr -> expr **)

  let lam x0 x1 =
    ELam (NameAnon, BDefault, x0, x1)

  (** val v : name **)

  let v =
    nm (String ((Ascii (False, True, True, False, True, True, True, False)),
      EmptyString))

  (** val accepts : 'a1 result -> bool **)

  let accepts = function
  | Accept _ -> True
  | _ -> False

  (** val loc : string -> expr -> ind_local **)

  let loc n0 t0 =
    { il_id = (nm n0); il_user = NameAnon; il_binder = BDefault; il_type =
      t0 }

  (** val p : ind_local **)

  let p =
    loc (String ((Ascii (False, False, False, False, True, True, True,
      False)), EmptyString)) ty

  (** val q : ind_local **)

  let q =
    loc (String ((Ascii (True, False, False, False, True, True, True,
      False)), EmptyString)) ty

  (** val old : name **)

  let old =
    nm (String ((Ascii (True, True, True, True, False, False, True, False)),
      (String ((Ascii (False, False, True, True, False, True, True, False)),
      (String ((Ascii (False, False, True, False, False, True, True, False)),
      EmptyString))))))

  (** val aux : name **)

  let aux =
    nested_aux_name (S O)

  (** val aux_ctor : name **)

  let aux_ctor =
    NameNum ((NameStr (aux, (String ((Ascii (True, False, True, True, False,
      True, True, False)), (String ((Ascii (True, True, False, True, False,
      True, True, False)), EmptyString)))))), (Npos (XO XH)))

  (** val old_ctor : name **)

  let old_ctor =
    NameNum ((NameStr (old, (String ((Ascii (True, False, True, True, False,
      True, True, False)), (String ((Ascii (True, True, False, True, False,
      True, True, False)), EmptyString)))))), (Npos (XO XH)))

  (** val symbolic_result : nested_elimination **)

  let symbolic_result =
    { nested_params = (Cons (p, Nil)); nested_context = empty_context;
      nested_specs = Nil; nested_mapping = (Cons ((Pair ((EApp ((EConst (old,
      (Cons ((LParam v), Nil)))), (local_expr p))), aux)), Nil));
      nested_aux_names = (Cons (aux, Nil)); nested_aux_count = (S O) }

  (** val symbolic_ctor : declaration **)

  let symbolic_ctor =
    { decl_name = aux_ctor; decl_params = (Cons (v, Nil)); decl_type = ty;
      decl_value = None; decl_kind_of = (DConstructor { ctor_induct = aux;
      ctor_index = O; ctor_num_params = (S O); ctor_num_fields = (S O);
      ctor_is_unsafe = False }); decl_hints = HintOpaque }

  (** val rec_map : (name, name) prod list **)

  let rec_map =
    auxiliary_rec_names
      (nm (String ((Ascii (False, False, True, False, True, False, True,
        False)), (String ((Ascii (False, True, False, False, True, True,
        True, False)), (String ((Ascii (True, False, True, False, False,
        True, True, False)), (String ((Ascii (True, False, True, False,
        False, True, True, False)), EmptyString)))))))))
      (Cons (aux, Nil)) (S O)

  (** val reserved : name **)

  let reserved =
    NameStr
      ((nm (String ((Ascii (True, True, True, True, True, False, True,
         False)), (String ((Ascii (False, True, True, True, False, True,
         True, False)), (String ((Ascii (True, False, True, False, False,
         True, True, False)), (String ((Ascii (True, True, False, False,
         True, True, True, False)), (String ((Ascii (False, False, True,
         False, True, True, True, False)), (String ((Ascii (True, False,
         True, False, False, True, True, False)), (String ((Ascii (False,
         False, True, False, False, True, True, False)),
         EmptyString))))))))))))))),
      (String ((Ascii (False, False, True, False, True, False, True, False)),
      EmptyString)))

  (** val ind_decl :
      name -> nat -> nat -> name list -> bool -> expr -> declaration **)

  let ind_decl n0 np nested cs recursive t0 =
    { decl_name = n0; decl_params = Nil; decl_type = t0; decl_value = None;
      decl_kind_of = (DInductive { ind_num_params = np; ind_num_indices = O;
      ind_all = (Cons (n0, Nil)); ind_ctors = cs; ind_num_nested = nested;
      ind_is_rec = recursive; ind_is_reflexive = False; ind_is_unsafe =
      False }); decl_hints = HintOpaque }

  (** val ctor_decl :
      name -> name -> nat -> nat -> nat -> expr -> declaration **)

  let ctor_decl n0 owner index np fields t0 =
    { decl_name = n0; decl_params = Nil; decl_type = t0; decl_value = None;
      decl_kind_of = (DConstructor { ctor_induct = owner; ctor_index = index;
      ctor_num_params = np; ctor_num_fields = fields; ctor_is_unsafe =
      False }); decl_hints = HintOpaque }

  (** val rec_decl :
      name -> name -> nat -> nat -> nat -> expr -> recursor_rule list ->
      declaration **)

  let rec_decl n0 owner np motives minors t0 rules =
    { decl_name = n0; decl_params = (Cons (v, Nil)); decl_type = t0;
      decl_value = None; decl_kind_of = (DRecursor { rec_all = (Cons (owner,
      Nil)); rec_num_params = np; rec_num_indices = O; rec_num_motives =
      motives; rec_num_minors = minors; rec_rules = rules; rec_k = False;
      rec_is_unsafe = False }); decl_hints = HintOpaque }

  (** val with_kind : declaration -> decl_kind -> declaration **)

  let with_kind d k =
    { decl_name = d.decl_name; decl_params = d.decl_params; decl_type =
      d.decl_type; decl_value = d.decl_value; decl_kind_of = k; decl_hints =
      d.decl_hints }

  (** val with_type : declaration -> expr -> declaration **)

  let with_type d t0 =
    { decl_name = d.decl_name; decl_params = d.decl_params; decl_type = t0;
      decl_value = d.decl_value; decl_kind_of = d.decl_kind_of; decl_hints =
      d.decl_hints }

  (** val with_rec_k : declaration -> bool -> declaration **)

  let with_rec_k d k =
    match d.decl_kind_of with
    | DRecursor r ->
      with_kind d (DRecursor { rec_all = r.rec_all; rec_num_params =
        r.rec_num_params; rec_num_indices = r.rec_num_indices;
        rec_num_motives = r.rec_num_motives; rec_num_minors =
        r.rec_num_minors; rec_rules = r.rec_rules; rec_k = k; rec_is_unsafe =
        r.rec_is_unsafe })
    | _ -> d

  (** val with_rules : declaration -> recursor_rule list -> declaration **)

  let with_rules d rules =
    match d.decl_kind_of with
    | DRecursor r ->
      with_kind d (DRecursor { rec_all = r.rec_all; rec_num_params =
        r.rec_num_params; rec_num_indices = r.rec_num_indices;
        rec_num_motives = r.rec_num_motives; rec_num_minors =
        r.rec_num_minors; rec_rules = rules; rec_k = r.rec_k; rec_is_unsafe =
        r.rec_is_unsafe })
    | _ -> d

  (** val empty_name : name **)

  let empty_name =
    nm (String ((Ascii (False, True, False, False, True, False, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (True, True, True, False, False, True, True,
      False)), (String ((Ascii (False, True, False, False, True, True, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (True, True, False, False, True, True, True,
      False)), (String ((Ascii (True, True, False, False, True, True, True,
      False)), (String ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, True, True, True, False, True, True,
      False)), (String ((Ascii (True, False, True, False, False, False, True,
      False)), (String ((Ascii (True, False, True, True, False, True, True,
      False)), (String ((Ascii (False, False, False, False, True, True, True,
      False)), (String ((Ascii (False, False, True, False, True, True, True,
      False)), (String ((Ascii (True, False, False, True, True, True, True,
      False)), EmptyString))))))))))))))))))))))))))))))

  (** val empty_type : expr **)

  let empty_type =
    EConst (empty_name, Nil)

  (** val empty_decl : declaration **)

  let empty_decl =
    ind_decl empty_name O O Nil False ty

  (** val empty_rec : declaration **)

  let empty_rec =
    rec_decl (rec_name empty_name) empty_name O (S O) O
      (pi (pi empty_type (ESort (LParam v)))
        (pi empty_type (EApp ((EBVar (S O)), (EBVar O)))))
      Nil

  (** val box : name **)

  let box =
    nm (String ((Ascii (False, True, False, False, True, False, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (True, True, True, False, False, True, True,
      False)), (String ((Ascii (False, True, False, False, True, True, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (True, True, False, False, True, True, True,
      False)), (String ((Ascii (True, True, False, False, True, True, True,
      False)), (String ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, True, True, True, False, True, True,
      False)), (String ((Ascii (False, True, False, False, False, False,
      True, False)), (String ((Ascii (True, True, True, True, False, True,
      True, False)), (String ((Ascii (False, False, False, True, True, True,
      True, False)), EmptyString))))))))))))))))))))))))))

  (** val box_mk : name **)

  let box_mk =
    NameStr (box, (String ((Ascii (True, False, True, True, False, True,
      True, False)), (String ((Ascii (True, True, False, True, False, True,
      True, False)), EmptyString)))))

  (** val box_at : expr -> expr **)

  let box_at a =
    EApp ((EConst (box, Nil)), a)

  (** val box_val : expr -> expr -> expr **)

  let box_val a x0 =
    apply_exprs (EConst (box_mk, Nil)) (Cons (a, (Cons (x0, Nil))))

  (** val coq_A : ind_local **)

  let coq_A =
    loc (String ((Ascii (True, False, False, False, False, False, True,
      False)), EmptyString)) ty

  (** val x : ind_local **)

  let x =
    loc (String ((Ascii (False, False, False, True, True, True, True,
      False)), EmptyString)) (local_expr coq_A)

  (** val box_motive : ind_local **)

  let box_motive =
    loc (String ((Ascii (False, True, False, False, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, False, False, True, True, True, True,
      False)), (String ((Ascii (True, True, True, True, True, False, True,
      False)), (String ((Ascii (True, False, True, True, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, False, True, False, True, True, True,
      False)), (String ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (False, True, True, False, True, True, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), EmptyString))))))))))))))))))))
      (pi (box_at (local_expr coq_A)) (ESort (LParam v)))

  (** val box_minor : ind_local **)

  let box_minor =
    loc (String ((Ascii (False, True, False, False, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, False, False, True, True, True, True,
      False)), (String ((Ascii (True, True, True, True, True, False, True,
      False)), (String ((Ascii (True, False, True, True, False, True, True,
      False)), (String ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (False, True, True, True, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, True, False, False, True, True, True,
      False)), EmptyString))))))))))))))))))
      (close_pi (Cons (x, Nil)) (EApp ((local_expr box_motive),
        (box_val (local_expr coq_A) (local_expr x)))))

  (** val box_major : ind_local **)

  let box_major =
    loc (String ((Ascii (False, True, False, False, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, False, False, True, True, True, True,
      False)), (String ((Ascii (True, True, True, True, True, False, True,
      False)), (String ((Ascii (True, False, True, True, False, True, True,
      False)), (String ((Ascii (True, False, False, False, False, True, True,
      False)), (String ((Ascii (False, True, False, True, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, True, False, False, True, True, True,
      False)), EmptyString)))))))))))))))))) (box_at (local_expr coq_A))

  (** val box_decl : declaration **)

  let box_decl =
    ind_decl box (S O) O (Cons (box_mk, Nil)) False (pi ty ty)

  (** val box_ctor : declaration **)

  let box_ctor =
    ctor_decl box_mk box O (S O) (S O)
      (close_pi (Cons (coq_A, (Cons (x, Nil)))) (box_at (local_expr coq_A)))

  (** val box_rule : recursor_rule **)

  let box_rule =
    { rule_ctor = box_mk; rule_nfields = (S O); rule_rhs =
      (close_lam (Cons (coq_A, (Cons (box_motive, (Cons (box_minor, (Cons (x,
        Nil)))))))) (EApp ((local_expr box_minor), (local_expr x)))) }

  (** val box_rec : declaration **)

  let box_rec =
    rec_decl (rec_name box) box (S O) (S O) (S O)
      (close_pi (Cons (coq_A, (Cons (box_motive, (Cons (box_minor, (Cons
        (box_major, Nil)))))))) (EApp ((local_expr box_motive),
        (local_expr box_major))))
      (Cons (box_rule, Nil))

  (** val box_admission : environment result **)

  let box_admission =
    admit_inductive_nested (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      Nil (Cons (box_decl, Nil)) (Cons (box_ctor, Nil)) (Cons (box_rec, Nil))

  (** val tree : name **)

  let tree =
    nm (String ((Ascii (False, True, False, False, True, False, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (True, True, True, False, False, True, True,
      False)), (String ((Ascii (False, True, False, False, True, True, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (True, True, False, False, True, True, True,
      False)), (String ((Ascii (True, True, False, False, True, True, True,
      False)), (String ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, True, True, True, False, True, True,
      False)), (String ((Ascii (False, False, True, False, True, False, True,
      False)), (String ((Ascii (False, True, False, False, True, True, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), EmptyString))))))))))))))))))))))))))))

  (** val tree_ty : expr **)

  let tree_ty =
    EConst (tree, Nil)

  (** val leaf : name **)

  let leaf =
    NameStr (tree, (String ((Ascii (False, False, True, True, False, True,
      True, False)), (String ((Ascii (True, False, True, False, False, True,
      True, False)), (String ((Ascii (True, False, False, False, False, True,
      True, False)), (String ((Ascii (False, True, True, False, False, True,
      True, False)), EmptyString)))))))))

  (** val node : name **)

  let node =
    NameStr (tree, (String ((Ascii (False, True, True, True, False, True,
      True, False)), (String ((Ascii (True, True, True, True, False, True,
      True, False)), (String ((Ascii (False, False, True, False, False, True,
      True, False)), (String ((Ascii (True, False, True, False, False, True,
      True, False)), EmptyString)))))))))

  (** val nested_rec : name **)

  let nested_rec =
    NameStr (tree, (String ((Ascii (False, True, False, False, True, True,
      True, False)), (String ((Ascii (True, False, True, False, False, True,
      True, False)), (String ((Ascii (True, True, False, False, False, True,
      True, False)), (String ((Ascii (True, True, True, True, True, False,
      True, False)), (String ((Ascii (True, False, False, False, True, True,
      False, False)), EmptyString)))))))))))

  (** val mt : ind_local **)

  let mt =
    loc (String ((Ascii (True, False, True, True, False, True, True, False)),
      (String ((Ascii (False, False, True, False, True, True, True, False)),
      EmptyString)))) (pi tree_ty (ESort (LParam v)))

  (** val mb : ind_local **)

  let mb =
    loc (String ((Ascii (True, False, True, True, False, True, True, False)),
      (String ((Ascii (False, True, False, False, False, True, True, False)),
      EmptyString)))) (pi (box_at tree_ty) (ESort (LParam v)))

  (** val leaf_minor : ind_local **)

  let leaf_minor =
    loc (String ((Ascii (False, False, True, True, False, True, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (True, False, False, False, False, True, True,
      False)), (String ((Ascii (False, True, True, False, False, True, True,
      False)), (String ((Ascii (True, True, True, True, True, False, True,
      False)), (String ((Ascii (True, False, True, True, False, True, True,
      False)), (String ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (False, True, True, True, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, True, False, False, True, True, True,
      False)), EmptyString)))))))))))))))))))) (EApp ((local_expr mt),
      (EConst (leaf, Nil))))

  (** val bt : ind_local **)

  let bt =
    loc (String ((Ascii (False, True, False, False, False, True, True,
      False)), (String ((Ascii (False, False, True, False, True, True, True,
      False)), EmptyString)))) (box_at tree_ty)

  (** val bt_ih : ind_local **)

  let bt_ih =
    loc (String ((Ascii (False, True, False, False, False, True, True,
      False)), (String ((Ascii (False, False, True, False, True, True, True,
      False)), (String ((Ascii (True, True, True, True, True, False, True,
      False)), (String ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (False, False, False, True, False, True, True,
      False)), EmptyString)))))))))) (EApp ((local_expr mb), (local_expr bt)))

  (** val node_minor : ind_local **)

  let node_minor =
    loc (String ((Ascii (False, True, True, True, False, True, True, False)),
      (String ((Ascii (True, True, True, True, False, True, True, False)),
      (String ((Ascii (False, False, True, False, False, True, True, False)),
      (String ((Ascii (True, False, True, False, False, True, True, False)),
      (String ((Ascii (True, True, True, True, True, False, True, False)),
      (String ((Ascii (True, False, True, True, False, True, True, False)),
      (String ((Ascii (True, False, False, True, False, True, True, False)),
      (String ((Ascii (False, True, True, True, False, True, True, False)),
      (String ((Ascii (True, True, True, True, False, True, True, False)),
      (String ((Ascii (False, True, False, False, True, True, True, False)),
      EmptyString))))))))))))))))))))
      (close_pi (Cons (bt, (Cons (bt_ih, Nil)))) (EApp ((local_expr mt),
        (EApp ((EConst (node, Nil)), (local_expr bt))))))

  (** val tt : ind_local **)

  let tt =
    loc (String ((Ascii (False, False, True, False, True, True, True,
      False)), (String ((Ascii (False, False, True, False, True, True, True,
      False)), EmptyString)))) tree_ty

  (** val tt_ih : ind_local **)

  let tt_ih =
    loc (String ((Ascii (False, False, True, False, True, True, True,
      False)), (String ((Ascii (False, False, True, False, True, True, True,
      False)), (String ((Ascii (True, True, True, True, True, False, True,
      False)), (String ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (False, False, False, True, False, True, True,
      False)), EmptyString)))))))))) (EApp ((local_expr mt), (local_expr tt)))

  (** val box_tree_minor : ind_local **)

  let box_tree_minor =
    loc (String ((Ascii (False, True, False, False, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, False, False, True, True, True, True,
      False)), (String ((Ascii (True, True, True, True, True, False, True,
      False)), (String ((Ascii (False, False, True, False, True, True, True,
      False)), (String ((Ascii (False, True, False, False, True, True, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), (String ((Ascii (True, True, True, True, True, False, True,
      False)), (String ((Ascii (True, False, True, True, False, True, True,
      False)), (String ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (False, True, True, True, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, True, False, False, True, True, True,
      False)), EmptyString))))))))))))))))))))))))))))
      (close_pi (Cons (tt, (Cons (tt_ih, Nil)))) (EApp ((local_expr mb),
        (box_val tree_ty (local_expr tt)))))

  (** val handlers : ind_local list **)

  let handlers =
    Cons (mt, (Cons (mb, (Cons (leaf_minor, (Cons (node_minor, (Cons
      (box_tree_minor, Nil)))))))))

  (** val tree_decl : nat -> declaration **)

  let tree_decl nested =
    ind_decl tree O nested (Cons (leaf, (Cons (node, Nil)))) True ty

  (** val leaf_ctor : declaration **)

  let leaf_ctor =
    ctor_decl leaf tree O O O tree_ty

  (** val node_ctor : declaration **)

  let node_ctor =
    ctor_decl node tree (S O) O (S O) (pi (box_at tree_ty) tree_ty)

  (** val leaf_rule : recursor_rule **)

  let leaf_rule =
    { rule_ctor = leaf; rule_nfields = O; rule_rhs =
      (close_lam handlers (local_expr leaf_minor)) }

  (** val node_rule : recursor_rule **)

  let node_rule =
    { rule_ctor = node; rule_nfields = (S O); rule_rhs =
      (close_lam (app handlers (Cons (bt, Nil)))
        (apply_exprs (local_expr node_minor) (Cons ((local_expr bt), (Cons
          ((apply_locals (EConst (nested_rec, (Cons ((LParam v), Nil))))
             (app handlers (Cons (bt, Nil)))),
          Nil)))))) }

  (** val box_tree_rule : recursor_rule **)

  let box_tree_rule =
    { rule_ctor = box_mk; rule_nfields = (S O); rule_rhs =
      (close_lam (app handlers (Cons (tt, Nil)))
        (apply_exprs (local_expr box_tree_minor) (Cons ((local_expr tt),
          (Cons
          ((apply_locals (EConst ((rec_name tree), (Cons ((LParam v), Nil))))
             (app handlers (Cons (tt, Nil)))),
          Nil)))))) }

  (** val tree_rec : declaration **)

  let tree_rec =
    rec_decl (rec_name tree) tree O (S (S O)) (S (S (S O)))
      (close_pi (app handlers (Cons (tt, Nil))) (EApp ((local_expr mt),
        (local_expr tt))))
      (Cons (leaf_rule, (Cons (node_rule, Nil))))

  (** val tree_aux_rec : declaration **)

  let tree_aux_rec =
    rec_decl nested_rec tree O (S (S O)) (S (S (S O)))
      (close_pi (app handlers (Cons (bt, Nil))) (EApp ((local_expr mb),
        (local_expr bt))))
      (Cons (box_tree_rule, Nil))

  (** val admit_tree :
      declaration -> declaration list -> declaration list -> environment
      result **)

  let admit_tree d cs rs =
    bind box_admission (fun env ->
      admit_inductive_nested (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        env (Cons (d, Nil)) cs rs)

  (** val tree_admission : environment result **)

  let tree_admission =
    admit_tree (tree_decl (S O)) (Cons (leaf_ctor, (Cons (node_ctor, Nil))))
      (Cons (tree_rec, (Cons (tree_aux_rec, Nil))))

  module DependentParameters =
   struct
    (** val a_type : ind_local **)

    let a_type =
      loc (String ((Ascii (True, False, False, False, False, True, True,
        False)), (String ((Ascii (True, True, True, True, True, False, True,
        False)), (String ((Ascii (False, False, True, False, True, True,
        True, False)), (String ((Ascii (True, False, False, True, True, True,
        True, False)), (String ((Ascii (False, False, False, False, True,
        True, True, False)), (String ((Ascii (True, False, True, False,
        False, True, True, False)), EmptyString)))))))))))) ty

    (** val a_value : ind_local **)

    let a_value =
      loc (String ((Ascii (True, False, False, False, False, True, True,
        False)), (String ((Ascii (True, True, True, True, True, False, True,
        False)), (String ((Ascii (False, True, True, False, True, True, True,
        False)), (String ((Ascii (True, False, False, False, False, True,
        True, False)), (String ((Ascii (False, False, True, True, False,
        True, True, False)), (String ((Ascii (True, False, True, False, True,
        True, True, False)), (String ((Ascii (True, False, True, False,
        False, True, True, False)), EmptyString))))))))))))))
        (local_expr a_type)

    (** val parameters : ind_local list **)

    let parameters =
      Cons (a_type, (Cons (a_value, Nil)))

    (** val tname : name **)

    let tname =
      nm (String ((Ascii (False, False, True, False, False, False, True,
        False)), (String ((Ascii (True, False, True, False, False, True,
        True, False)), (String ((Ascii (False, False, False, False, True,
        True, True, False)), (String ((Ascii (True, False, True, False,
        False, True, True, False)), (String ((Ascii (False, True, True, True,
        False, True, True, False)), (String ((Ascii (False, False, True,
        False, False, True, True, False)), (String ((Ascii (True, False,
        True, False, False, True, True, False)), (String ((Ascii (False,
        True, True, True, False, True, True, False)), (String ((Ascii (False,
        False, True, False, True, True, True, False)), (String ((Ascii
        (False, True, True, True, False, False, True, False)), (String
        ((Ascii (True, False, True, False, False, True, True, False)),
        (String ((Ascii (True, True, False, False, True, True, True, False)),
        (String ((Ascii (False, False, True, False, True, True, True,
        False)), (String ((Ascii (True, False, True, False, False, True,
        True, False)), (String ((Ascii (False, False, True, False, False,
        True, True, False)), (String ((Ascii (False, False, True, False,
        True, False, True, False)), (String ((Ascii (False, True, False,
        False, True, True, True, False)), (String ((Ascii (True, False, True,
        False, False, True, True, False)), (String ((Ascii (True, False,
        True, False, False, True, True, False)),
        EmptyString))))))))))))))))))))))))))))))))))))))

    (** val t : expr **)

    let t =
      apply_locals (EConst (tname, Nil)) parameters

    (** val cleaf : name **)

    let cleaf =
      NameStr (tname, (String ((Ascii (False, False, True, True, False, True,
        True, False)), (String ((Ascii (True, False, True, False, False,
        True, True, False)), (String ((Ascii (True, False, False, False,
        False, True, True, False)), (String ((Ascii (False, True, True,
        False, False, True, True, False)), EmptyString)))))))))

    (** val cnode : name **)

    let cnode =
      NameStr (tname, (String ((Ascii (False, True, True, True, False, True,
        True, False)), (String ((Ascii (True, True, True, True, False, True,
        True, False)), (String ((Ascii (False, False, True, False, False,
        True, True, False)), (String ((Ascii (True, False, True, False,
        False, True, True, False)), EmptyString)))))))))

    (** val raux : name **)

    let raux =
      NameStr (tname, (String ((Ascii (False, True, False, False, True, True,
        True, False)), (String ((Ascii (True, False, True, False, False,
        True, True, False)), (String ((Ascii (True, True, False, False,
        False, True, True, False)), (String ((Ascii (True, True, True, True,
        True, False, True, False)), (String ((Ascii (True, False, False,
        False, True, True, False, False)), EmptyString)))))))))))

    (** val motive_t : ind_local **)

    let motive_t =
      loc (String ((Ascii (True, False, True, True, False, True, True,
        False)), (String ((Ascii (True, True, True, True, False, True, True,
        False)), (String ((Ascii (False, False, True, False, True, True,
        True, False)), (String ((Ascii (True, False, False, True, False,
        True, True, False)), (String ((Ascii (False, True, True, False, True,
        True, True, False)), (String ((Ascii (True, False, True, False,
        False, True, True, False)), (String ((Ascii (True, True, True, True,
        True, False, True, False)), (String ((Ascii (False, False, True,
        False, True, True, True, False)), EmptyString))))))))))))))))
        (pi t (ESort (LParam v)))

    (** val motive_b : ind_local **)

    let motive_b =
      loc (String ((Ascii (True, False, True, True, False, True, True,
        False)), (String ((Ascii (True, True, True, True, False, True, True,
        False)), (String ((Ascii (False, False, True, False, True, True,
        True, False)), (String ((Ascii (True, False, False, True, False,
        True, True, False)), (String ((Ascii (False, True, True, False, True,
        True, True, False)), (String ((Ascii (True, False, True, False,
        False, True, True, False)), (String ((Ascii (True, True, True, True,
        True, False, True, False)), (String ((Ascii (False, True, False,
        False, False, True, True, False)), EmptyString))))))))))))))))
        (pi (box_at t) (ESort (LParam v)))

    (** val minor_leaf : ind_local **)

    let minor_leaf =
      loc (String ((Ascii (True, False, True, True, False, True, True,
        False)), (String ((Ascii (True, False, False, True, False, True,
        True, False)), (String ((Ascii (False, True, True, True, False, True,
        True, False)), (String ((Ascii (True, True, True, True, False, True,
        True, False)), (String ((Ascii (False, True, False, False, True,
        True, True, False)), (String ((Ascii (True, True, True, True, True,
        False, True, False)), (String ((Ascii (False, False, True, True,
        False, True, True, False)), (String ((Ascii (True, False, True,
        False, False, True, True, False)), (String ((Ascii (True, False,
        False, False, False, True, True, False)), (String ((Ascii (False,
        True, True, False, False, True, True, False)),
        EmptyString)))))))))))))))))))) (EApp ((local_expr motive_t),
        (apply_locals (EConst (cleaf, Nil)) parameters)))

    (** val field_b : ind_local **)

    let field_b =
      loc (String ((Ascii (False, True, True, False, False, True, True,
        False)), (String ((Ascii (True, False, False, True, False, True,
        True, False)), (String ((Ascii (True, False, True, False, False,
        True, True, False)), (String ((Ascii (False, False, True, True,
        False, True, True, False)), (String ((Ascii (False, False, True,
        False, False, True, True, False)), (String ((Ascii (True, True, True,
        True, True, False, True, False)), (String ((Ascii (False, True,
        False, False, False, True, True, False)), EmptyString))))))))))))))
        (box_at t)

    (** val ih_b : ind_local **)

    let ih_b =
      loc (String ((Ascii (True, False, False, True, False, True, True,
        False)), (String ((Ascii (False, False, False, True, False, True,
        True, False)), (String ((Ascii (True, True, True, True, True, False,
        True, False)), (String ((Ascii (False, True, False, False, False,
        True, True, False)), EmptyString)))))))) (EApp
        ((local_expr motive_b), (local_expr field_b)))

    (** val minor_node : ind_local **)

    let minor_node =
      loc (String ((Ascii (True, False, True, True, False, True, True,
        False)), (String ((Ascii (True, False, False, True, False, True,
        True, False)), (String ((Ascii (False, True, True, True, False, True,
        True, False)), (String ((Ascii (True, True, True, True, False, True,
        True, False)), (String ((Ascii (False, True, False, False, True,
        True, True, False)), (String ((Ascii (True, True, True, True, True,
        False, True, False)), (String ((Ascii (False, True, True, True,
        False, True, True, False)), (String ((Ascii (True, True, True, True,
        False, True, True, False)), (String ((Ascii (False, False, True,
        False, False, True, True, False)), (String ((Ascii (True, False,
        True, False, False, True, True, False)),
        EmptyString))))))))))))))))))))
        (close_pi (Cons (field_b, (Cons (ih_b, Nil)))) (EApp
          ((local_expr motive_t),
          (apply_locals (EConst (cnode, Nil))
            (app parameters (Cons (field_b, Nil)))))))

    (** val field_t : ind_local **)

    let field_t =
      loc (String ((Ascii (False, True, True, False, False, True, True,
        False)), (String ((Ascii (True, False, False, True, False, True,
        True, False)), (String ((Ascii (True, False, True, False, False,
        True, True, False)), (String ((Ascii (False, False, True, True,
        False, True, True, False)), (String ((Ascii (False, False, True,
        False, False, True, True, False)), (String ((Ascii (True, True, True,
        True, True, False, True, False)), (String ((Ascii (False, False,
        True, False, True, True, True, False)), EmptyString)))))))))))))) t

    (** val ih_t : ind_local **)

    let ih_t =
      loc (String ((Ascii (True, False, False, True, False, True, True,
        False)), (String ((Ascii (False, False, False, True, False, True,
        True, False)), (String ((Ascii (True, True, True, True, True, False,
        True, False)), (String ((Ascii (False, False, True, False, True,
        True, True, False)), EmptyString)))))))) (EApp
        ((local_expr motive_t), (local_expr field_t)))

    (** val minor_box : ind_local **)

    let minor_box =
      loc (String ((Ascii (True, False, True, True, False, True, True,
        False)), (String ((Ascii (True, False, False, True, False, True,
        True, False)), (String ((Ascii (False, True, True, True, False, True,
        True, False)), (String ((Ascii (True, True, True, True, False, True,
        True, False)), (String ((Ascii (False, True, False, False, True,
        True, True, False)), (String ((Ascii (True, True, True, True, True,
        False, True, False)), (String ((Ascii (False, True, False, False,
        False, True, True, False)), (String ((Ascii (True, True, True, True,
        False, True, True, False)), (String ((Ascii (False, False, False,
        True, True, True, True, False)), EmptyString))))))))))))))))))
        (close_pi (Cons (field_t, (Cons (ih_t, Nil)))) (EApp
          ((local_expr motive_b), (box_val t (local_expr field_t)))))

    (** val prefix : ind_local list **)

    let prefix =
      app parameters (Cons (motive_t, (Cons (motive_b, (Cons (minor_leaf,
        (Cons (minor_node, (Cons (minor_box, Nil))))))))))

    (** val idecl : declaration **)

    let idecl =
      ind_decl tname (S (S O)) (S O) (Cons (cleaf, (Cons (cnode, Nil)))) True
        (close_pi parameters ty)

    (** val leaf_decl : declaration **)

    let leaf_decl =
      ctor_decl cleaf tname O (S (S O)) O (close_pi parameters t)

    (** val node_decl : declaration **)

    let node_decl =
      ctor_decl cnode tname (S O) (S (S O)) (S O)
        (close_pi parameters (pi (box_at t) t))

    (** val leaf_iota : recursor_rule **)

    let leaf_iota =
      { rule_ctor = cleaf; rule_nfields = O; rule_rhs =
        (close_lam prefix (local_expr minor_leaf)) }

    (** val node_iota : recursor_rule **)

    let node_iota =
      { rule_ctor = cnode; rule_nfields = (S O); rule_rhs =
        (close_lam (app prefix (Cons (field_b, Nil)))
          (apply_exprs (local_expr minor_node) (Cons ((local_expr field_b),
            (Cons
            ((apply_locals (EConst (raux, (Cons ((LParam v), Nil))))
               (app prefix (Cons (field_b, Nil)))),
            Nil)))))) }

    (** val box_iota : recursor_rule **)

    let box_iota =
      { rule_ctor = box_mk; rule_nfields = (S O); rule_rhs =
        (close_lam (app prefix (Cons (field_t, Nil)))
          (apply_exprs (local_expr minor_box) (Cons ((local_expr field_t),
            (Cons
            ((apply_locals (EConst ((rec_name tname), (Cons ((LParam v),
               Nil)))) (app prefix (Cons (field_t, Nil)))),
            Nil)))))) }

    (** val main_rec : declaration **)

    let main_rec =
      rec_decl (rec_name tname) tname (S (S O)) (S (S O)) (S (S (S O)))
        (close_pi (app prefix (Cons (field_t, Nil))) (EApp
          ((local_expr motive_t), (local_expr field_t))))
        (Cons (leaf_iota, (Cons (node_iota, Nil))))

    (** val aux_rec : declaration **)

    let aux_rec =
      rec_decl raux tname (S (S O)) (S (S O)) (S (S (S O)))
        (close_pi (app prefix (Cons (field_b, Nil))) (EApp
          ((local_expr motive_b), (local_expr field_b))))
        (Cons (box_iota, Nil))

    (** val admission : declaration list -> environment result **)

    let admission recs =
      bind box_admission (fun env ->
        admit_inductive_nested (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          env (Cons (idecl, Nil)) (Cons (leaf_decl, (Cons (node_decl, Nil))))
          recs)
   end
 end

(** val sp_pi : expr -> expr -> expr **)

let sp_pi a b =
  EPi (NameAnon, BDefault, a, b)

(** val sp_lam : expr -> expr -> expr **)

let sp_lam a b =
  ELam (NameAnon, BDefault, a, b)

(** val sp_type : expr **)

let sp_type =
  ESort (LSucc LZero)

(** val sp_u : name **)

let sp_u =
  core_name (String ((Ascii (True, False, True, False, True, True, True,
    False)), EmptyString))

(** val sp_decl : name -> name list -> expr -> decl_kind -> declaration **)

let sp_decl n0 ps ty0 k =
  { decl_name = n0; decl_params = ps; decl_type = ty0; decl_value = None;
    decl_kind_of = k; decl_hints = HintOpaque }

(** val sp_ind :
    name -> name list -> nat -> expr -> name list -> declaration **)

let sp_ind n0 ps np ty0 cs =
  sp_decl n0 ps ty0 (DInductive { ind_num_params = np; ind_num_indices = O;
    ind_all = (Cons (n0, Nil)); ind_ctors = cs; ind_num_nested = O;
    ind_is_rec = False; ind_is_reflexive = False; ind_is_unsafe = False })

(** val sp_ctor :
    name -> name -> name list -> nat -> nat -> nat -> expr -> declaration **)

let sp_ctor n0 owner ps np i nf ty0 =
  sp_decl n0 ps ty0 (DConstructor { ctor_induct = owner; ctor_index = i;
    ctor_num_params = np; ctor_num_fields = nf; ctor_is_unsafe = False })

(** val sp_is_ind : declaration -> bool **)

let sp_is_ind d =
  match d.decl_kind_of with
  | DInductive _ -> True
  | _ -> False

(** val sp_is_ctor : declaration -> bool **)

let sp_is_ctor d =
  match d.decl_kind_of with
  | DConstructor _ -> True
  | _ -> False

(** val sp_is_rec : declaration -> bool **)

let sp_is_rec d =
  match d.decl_kind_of with
  | DRecursor _ -> True
  | _ -> False

(** val sp_install_ind :
    environment -> name list -> nat -> ind_spec -> environment result **)

let sp_install_ind env ps np spec =
  bind
    (derive_inductive (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      env ps np (Cons (spec, Nil)))
    (fun generated ->
    admit_inductive (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      env (filter sp_is_ind generated) (filter sp_is_ctor generated)
      (filter sp_is_rec generated))

(** val sp_define :
    environment -> name -> name list -> expr -> expr -> environment result **)

let sp_define env n0 ps ty0 body =
  admit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    env (InputDefinition (HintOpaque, n0, ps, ty0, body, InputSafe))

(** val sp_success : 'a1 result -> bool **)

let sp_success = function
| Accept _ -> True
| _ -> False

(** val sp_nat : environment result **)

let sp_nat =
  sp_install_ind Nil Nil O { spec_decl =
    (sp_ind core_nat_name Nil O sp_type (Cons (core_zero_name, (Cons
      (core_succ_name, Nil)))));
    spec_ctors = (Cons
    ((sp_ctor core_zero_name core_nat_name Nil O O O core_nat), (Cons
    ((sp_ctor core_succ_name core_nat_name Nil O (S O) (S O)
       (sp_pi core_nat core_nat)),
    Nil)))) }

(** val sp_list : expr -> expr **)

let sp_list a =
  EApp ((EConst (core_list_name, (Cons ((LParam sp_u), Nil)))), a)

(** val sp_list_spec : ind_spec **)

let sp_list_spec =
  { spec_decl =
    (sp_ind core_list_name (Cons (sp_u, Nil)) (S O)
      (sp_pi (ESort (LSucc (LParam sp_u))) (ESort (LSucc (LParam sp_u))))
      (Cons ((NameStr (core_list_name, (String ((Ascii (False, True, True,
      True, False, True, True, False)), (String ((Ascii (True, False, False,
      True, False, True, True, False)), (String ((Ascii (False, False, True,
      True, False, True, True, False)), EmptyString)))))))), (Cons ((NameStr
      (core_list_name, (String ((Ascii (True, True, False, False, False,
      True, True, False)), (String ((Ascii (True, True, True, True, False,
      True, True, False)), (String ((Ascii (False, True, True, True, False,
      True, True, False)), (String ((Ascii (True, True, False, False, True,
      True, True, False)), EmptyString)))))))))), Nil)))));
    spec_ctors = (Cons
    ((sp_ctor (NameStr (core_list_name, (String ((Ascii (False, True, True,
       True, False, True, True, False)), (String ((Ascii (True, False, False,
       True, False, True, True, False)), (String ((Ascii (False, False, True,
       True, False, True, True, False)), EmptyString)))))))) core_list_name
       (Cons (sp_u, Nil)) (S O) O O
       (sp_pi (ESort (LSucc (LParam sp_u))) (sp_list (EBVar O)))),
    (Cons
    ((sp_ctor (NameStr (core_list_name, (String ((Ascii (True, True, False,
       False, False, True, True, False)), (String ((Ascii (True, True, True,
       True, False, True, True, False)), (String ((Ascii (False, True, True,
       True, False, True, True, False)), (String ((Ascii (True, True, False,
       False, True, True, True, False)), EmptyString)))))))))) core_list_name
       (Cons (sp_u, Nil)) (S O) (S O) (S (S O))
       (sp_pi (ESort (LSucc (LParam sp_u)))
         (sp_pi (EBVar O)
           (sp_pi (sp_list (EBVar (S O))) (sp_list (EBVar (S (S O)))))))),
    Nil)))) }

(** val sp_base : environment result **)

let sp_base =
  bind sp_nat (fun env ->
    bind (sp_install_ind env (Cons (sp_u, Nil)) (S O) sp_list_spec)
      (fun env0 -> sp_define env0 core_char_name Nil sp_type core_nat))

(** val sp_nil : expr **)

let sp_nil =
  EApp ((EConst ((NameStr (core_list_name, (String ((Ascii (False, True,
    True, True, False, True, True, False)), (String ((Ascii (True, False,
    False, True, False, True, True, False)), (String ((Ascii (False, False,
    True, True, False, True, True, False)), EmptyString)))))))), (Cons
    (LZero, Nil)))), primitive_char)

(** val sp_mk : name **)

let sp_mk =
  NameStr (core_string_name, (String ((Ascii (True, False, True, True, False,
    True, True, False)), (String ((Ascii (True, True, False, True, False,
    True, True, False)), EmptyString)))))

(** val sp_string_spec : ind_spec **)

let sp_string_spec =
  { spec_decl = (sp_ind core_string_name Nil O sp_type (Cons (sp_mk, Nil)));
    spec_ctors = (Cons
    ((sp_ctor sp_mk core_string_name Nil O O (S O)
       (sp_pi primitive_list_char primitive_string)),
    Nil)) }

(** val sp_text_env : bool -> bool -> bool -> environment result **)

let sp_text_env structure collapsed_char collapsed_string =
  bind sp_base (fun env ->
    bind
      (match structure with
       | True -> sp_install_ind env Nil O sp_string_spec
       | False ->
         sp_define env core_string_name Nil sp_type primitive_list_char)
      (fun env0 ->
      bind
        (sp_define env0 core_char_of_nat Nil (primitive_signature PCharOfNat)
          (sp_lam core_nat
            (match collapsed_char with
             | True -> ELit (LitNat N0)
             | False -> EBVar O)))
        (fun env1 ->
        sp_define env1 core_string_of_list Nil
          (primitive_signature PStringOfList)
          (sp_lam primitive_list_char
            (let value =
               match collapsed_string with
               | True -> sp_nil
               | False -> EBVar O
             in
             match structure with
             | True -> EApp ((EConst (sp_mk, Nil)), value)
             | False -> value)))))

(** val sp_literal : string -> expr **)

let sp_literal s =
  ELit (LitString s)

(** val sp_checked_pair : environment -> expr -> expr -> unit0 result **)

let sp_checked_pair env a b =
  bind
    (check (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      env Nil empty_context a primitive_string)
    (fun _ ->
    bind
      (check (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        env Nil empty_context b primitive_string)
      (fun _ -> Accept Tt))

(** val sp_pair_gate : bool -> bool -> bool -> string -> unit0 result **)

let sp_pair_gate structure cc cs s =
  bind (sp_text_env structure cc cs) (fun env ->
    bind (core_expand_string s) (fun expanded ->
      sp_checked_pair env (sp_literal s) expanded))

(** val sp_compare :
    bool -> bool -> bool -> bool -> string -> unit0 result **)

let sp_compare structure cc cs reverse s =
  bind (sp_text_env structure cc cs) (fun env ->
    bind (core_expand_string s) (fun expanded ->
      bind (sp_checked_pair env (sp_literal s) expanded) (fun _ ->
        match reverse with
        | True ->
          check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            env Nil empty_context expanded (sp_literal s)
        | False ->
          check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            env Nil empty_context (sp_literal s) expanded)))

(** val sp_compare_normal : bool -> bool -> bool -> string -> unit0 result **)

let sp_compare_normal structure cc cs s =
  bind (sp_text_env structure cc cs) (fun env ->
    bind (core_expand_string s) (fun expanded ->
      bind
        (whnf (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
          env Nil empty_context expanded)
        (fun expanded0 ->
        bind (sp_checked_pair env (sp_literal s) expanded0) (fun _ ->
          check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            env Nil empty_context (sp_literal s) expanded0))))

(** val sp_distinct : bool -> bool -> bool -> unit0 result **)

let sp_distinct structure cc cs =
  bind (sp_text_env structure cc cs) (fun env ->
    bind
      (sp_checked_pair env
        (sp_literal (String ((Ascii (True, False, False, False, False, False,
          True, False)), EmptyString)))
        (sp_literal (String ((Ascii (False, True, False, False, False, False,
          True, False)), EmptyString))))
      (fun _ ->
      check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        env Nil empty_context
        (sp_literal (String ((Ascii (True, False, False, False, False, False,
          True, False)), EmptyString)))
        (sp_literal (String ((Ascii (False, True, False, False, False, False,
          True, False)), EmptyString)))))

(** val sp_projection : string -> unit0 result **)

let sp_projection s =
  bind (sp_text_env True False False) (fun env ->
    let p0 = EProj (core_string_name, O, (sp_literal s)) in
    bind
      (check (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        env Nil empty_context p0 primitive_list_char)
      (fun _ ->
      check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        env Nil empty_context p0
        (core_char_list (match core_utf8 s with
                         | Some cs -> cs
                         | None -> Nil))))

(** val sp_recursor : string -> unit0 result **)

let sp_recursor s =
  bind (sp_text_env True False False) (fun env ->
    let fold0 =
      core_apps (EConst ((rec_name core_string_name), (Cons ((LSucc LZero),
        Nil)))) (Cons ((sp_lam primitive_string primitive_list_char), (Cons
        ((sp_lam primitive_list_char (EBVar O)), (Cons ((sp_literal s),
        Nil))))))
    in
    bind
      (check (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        env Nil empty_context fold0 primitive_list_char)
      (fun _ ->
      check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        env Nil empty_context fold0
        (core_char_list (match core_utf8 s with
                         | Some cs -> cs
                         | None -> Nil))))

(** val sp_eq_name : name **)

let sp_eq_name =
  core_name (String ((Ascii (True, False, True, False, False, False, True,
    False)), (String ((Ascii (True, False, False, False, True, True, True,
    False)), EmptyString))))

(** val sp_eq_at : level -> expr -> expr -> expr -> expr **)

let sp_eq_at u0 a x0 y =
  core_apps (EConst (sp_eq_name, (Cons (u0, Nil)))) (Cons (a, (Cons (x0,
    (Cons (y, Nil))))))

(** val sp_eq_spec : ind_spec **)

let sp_eq_spec =
  { spec_decl =
    (sp_ind sp_eq_name (Cons (sp_u, Nil)) (S (S O))
      (sp_pi (ESort (LParam sp_u))
        (sp_pi (EBVar O) (sp_pi (EBVar (S O)) (ESort LZero))))
      (Cons ((NameStr (sp_eq_name, (String ((Ascii (False, True, False,
      False, True, True, True, False)), (String ((Ascii (True, False, True,
      False, False, True, True, False)), (String ((Ascii (False, True, True,
      False, False, True, True, False)), (String ((Ascii (False, False, True,
      True, False, True, True, False)), EmptyString)))))))))), Nil)));
    spec_ctors = (Cons
    ((sp_ctor (NameStr (sp_eq_name, (String ((Ascii (False, True, False,
       False, True, True, True, False)), (String ((Ascii (True, False, True,
       False, False, True, True, False)), (String ((Ascii (False, True, True,
       False, False, True, True, False)), (String ((Ascii (False, False,
       True, True, False, True, True, False)), EmptyString))))))))))
       sp_eq_name (Cons (sp_u, Nil)) (S (S O)) O O
       (sp_pi (ESort (LParam sp_u))
         (sp_pi (EBVar O)
           (sp_eq_at (LParam sp_u) (EBVar (S O)) (EBVar O) (EBVar O))))),
    Nil)) }

(** val sp_eq_env : bool -> environment result **)

let sp_eq_env structure =
  bind (sp_text_env structure True False) (fun env ->
    sp_install_ind env (Cons (sp_u, Nil)) (S (S O)) sp_eq_spec)

(** val sp_refl : expr -> expr **)

let sp_refl e =
  core_apps (EConst ((NameStr (sp_eq_name, (String ((Ascii (False, True,
    False, False, True, True, True, False)), (String ((Ascii (True, False,
    True, False, False, True, True, False)), (String ((Ascii (False, True,
    True, False, False, True, True, False)), (String ((Ascii (False, False,
    True, True, False, True, True, False)), EmptyString)))))))))), (Cons
    ((LSucc LZero), Nil)))) (Cons (primitive_string, (Cons (e, Nil))))

(** val sp_literal_equality : expr **)

let sp_literal_equality =
  sp_eq_at (LSucc LZero) primitive_string
    (sp_literal (String ((Ascii (True, False, False, False, False, False,
      True, False)), EmptyString)))
    (sp_literal (String ((Ascii (False, True, False, False, False, False,
      True, False)), EmptyString)))

(** val sp_expanded_proof_gate : bool -> unit0 result **)

let sp_expanded_proof_gate structure =
  bind (sp_eq_env structure) (fun env ->
    bind
      (core_expand_string (String ((Ascii (True, False, False, False, False,
        False, True, False)), EmptyString)))
      (fun expanded ->
      check (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        env Nil empty_context (sp_refl expanded)
        (sp_eq_at (LSucc LZero) primitive_string expanded expanded)))

(** val sp_expanded_theorem : bool -> unit0 result **)

let sp_expanded_theorem structure =
  bind (sp_eq_env structure) (fun env ->
    bind
      (core_expand_string (String ((Ascii (True, False, False, False, False,
        False, True, False)), EmptyString)))
      (fun expanded ->
      bind (sp_expanded_proof_gate structure) (fun _ ->
        bind
          (admit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
            env (InputTheorem
            ((core_name (String ((Ascii (True, False, True, False, False,
               False, True, False)), (String ((Ascii (False, False, False,
               True, True, True, True, False)), (String ((Ascii (False,
               False, False, False, True, True, True, False)), (String
               ((Ascii (True, False, False, False, False, True, True,
               False)), (String ((Ascii (False, True, True, True, False,
               True, True, False)), (String ((Ascii (False, False, True,
               False, False, True, True, False)), (String ((Ascii (True,
               False, True, False, False, True, True, False)), (String
               ((Ascii (False, False, True, False, False, True, True,
               False)), (String ((Ascii (False, False, True, False, True,
               False, True, False)), (String ((Ascii (True, False, True,
               False, False, True, True, False)), (String ((Ascii (False,
               False, False, True, True, True, True, False)), (String ((Ascii
               (False, False, True, False, True, True, True, False)), (String
               ((Ascii (True, False, True, False, False, False, True,
               False)), (String ((Ascii (True, False, False, False, True,
               True, True, False)), (String ((Ascii (True, False, True,
               False, True, True, True, False)), (String ((Ascii (True,
               False, False, False, False, True, True, False)), (String
               ((Ascii (False, False, True, True, False, True, True, False)),
               (String ((Ascii (True, False, False, True, False, True, True,
               False)), (String ((Ascii (False, False, True, False, True,
               True, True, False)), (String ((Ascii (True, False, False,
               True, True, True, True, False)),
               EmptyString))))))))))))))))))))))))))))))))))))))))),
            Nil, sp_literal_equality, (sp_refl expanded))))
          (fun _ -> Accept Tt))))

(** val sp_literal_theorem : bool -> unit0 result **)

let sp_literal_theorem structure =
  bind (sp_eq_env structure) (fun env ->
    bind
      (admit (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S
        O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        env (InputTheorem
        ((core_name (String ((Ascii (False, False, True, True, False, False,
           True, False)), (String ((Ascii (True, False, False, True, False,
           True, True, False)), (String ((Ascii (False, False, True, False,
           True, True, True, False)), (String ((Ascii (True, False, True,
           False, False, True, True, False)), (String ((Ascii (False, True,
           False, False, True, True, True, False)), (String ((Ascii (True,
           False, False, False, False, True, True, False)), (String ((Ascii
           (False, False, True, True, False, True, True, False)), (String
           ((Ascii (False, False, True, False, True, False, True, False)),
           (String ((Ascii (True, False, True, False, False, True, True,
           False)), (String ((Ascii (False, False, False, True, True, True,
           True, False)), (String ((Ascii (False, False, True, False, True,
           True, True, False)), (String ((Ascii (True, False, True, False,
           False, False, True, False)), (String ((Ascii (True, False, False,
           False, True, True, True, False)), (String ((Ascii (True, False,
           True, False, True, True, True, False)), (String ((Ascii (True,
           False, False, False, False, True, True, False)), (String ((Ascii
           (False, False, True, True, False, True, True, False)), (String
           ((Ascii (True, False, False, True, False, True, True, False)),
           (String ((Ascii (False, False, True, False, True, True, True,
           False)), (String ((Ascii (True, False, False, True, True, True,
           True, False)), EmptyString))))))))))))))))))))))))))))))))))))))),
        Nil, sp_literal_equality,
        (sp_refl
          (sp_literal (String ((Ascii (True, False, False, False, False,
            False, True, False)), EmptyString)))))))
      (fun _ -> Accept Tt))

(** val sp_gate_results : unit0 -> bool list **)

let sp_gate_results _ =
  Cons ((sp_success sp_nat), (Cons ((sp_success sp_base), (Cons
    ((sp_success (sp_text_env False False False)), (Cons
    ((sp_success (sp_text_env False True False)), (Cons
    ((sp_success (sp_text_env False False True)), (Cons
    ((sp_success (sp_text_env True False False)), (Cons
    ((sp_success (sp_text_env True True False)), (Cons
    ((sp_success (sp_text_env True False True)), (Cons
    ((sp_success
       (sp_pair_gate False False False (String ((Ascii (True, False, False,
         False, False, False, True, False)), EmptyString)))),
    (Cons
    ((sp_success
       (sp_pair_gate True False False (String ((Ascii (True, False, False,
         False, False, False, True, False)), EmptyString)))),
    (Cons ((sp_success (sp_eq_env False)), (Cons
    ((sp_success (sp_eq_env True)), (Cons
    ((sp_success (sp_expanded_proof_gate False)), (Cons
    ((sp_success (sp_expanded_proof_gate True)),
    Nil)))))))))))))))))))))))))))

(** val sp_observations : unit0 -> unit0 result list **)

let sp_observations _ =
  Cons
    ((sp_compare False False False False (String ((Ascii (True, False, False,
       False, False, False, True, False)), EmptyString))),
    (Cons
    ((sp_compare False False False True (String ((Ascii (True, False, False,
       False, False, False, True, False)), EmptyString))),
    (Cons
    ((sp_compare False True False False (String ((Ascii (True, False, False,
       False, False, False, True, False)), EmptyString))),
    (Cons
    ((sp_compare False False True False (String ((Ascii (True, False, False,
       False, False, False, True, False)), EmptyString))),
    (Cons ((sp_compare False False False False EmptyString), (Cons
    ((sp_compare_normal False False False (String ((Ascii (True, False,
       False, False, False, False, True, False)), EmptyString))),
    (Cons
    ((sp_compare True False False False (String ((Ascii (True, False, False,
       False, False, False, True, False)), EmptyString))),
    (Cons
    ((sp_compare True False False True (String ((Ascii (True, False, False,
       False, False, False, True, False)), EmptyString))),
    (Cons
    ((sp_compare True True False False (String ((Ascii (True, False, False,
       False, False, False, True, False)), EmptyString))),
    (Cons
    ((sp_compare True False True False (String ((Ascii (True, False, False,
       False, False, False, True, False)), EmptyString))),
    (Cons
    ((sp_projection (String ((Ascii (True, False, False, False, False, False,
       True, False)), EmptyString))),
    (Cons ((sp_projection EmptyString), (Cons
    ((sp_recursor (String ((Ascii (True, False, False, False, False, False,
       True, False)), EmptyString))),
    (Cons ((sp_recursor EmptyString), (Cons ((sp_distinct False True False),
    (Cons ((sp_distinct False False True), (Cons
    ((sp_distinct True True False), (Cons ((sp_distinct True False True),
    (Cons ((sp_expanded_theorem False), (Cons ((sp_expanded_theorem True),
    (Cons ((sp_literal_theorem False), (Cons ((sp_literal_theorem True),
    Nil)))))))))))))))))))))))))))))))))))))))))))

module NR = NestedRegression

(** val nested_box_batch : admission_batch **)

let nested_box_batch =
  BatchInductive ((Cons (NR.box_decl, Nil)), (Cons (NR.box_ctor, Nil)), (Cons
    (NR.box_rec, Nil)))

(** val nested_tree_batch : admission_batch **)

let nested_tree_batch =
  BatchInductive ((Cons ((NR.tree_decl (S O)), Nil)), (Cons (NR.leaf_ctor,
    (Cons (NR.node_ctor, Nil)))), (Cons (NR.tree_rec, (Cons (NR.tree_aux_rec,
    Nil)))))

(** val nested_mutations : admission_batch list **)

let nested_mutations =
  Cons ((BatchInductive ((Cons ((NR.tree_decl O), Nil)), (Cons (NR.leaf_ctor,
    (Cons (NR.node_ctor, Nil)))), (Cons (NR.tree_rec, (Cons (NR.tree_aux_rec,
    Nil)))))), (Cons ((BatchInductive ((Cons ((NR.tree_decl (S O)), Nil)),
    (Cons (NR.leaf_ctor, (Cons (NR.node_ctor, Nil)))), (Cons (NR.tree_rec,
    Nil)))), (Cons ((BatchInductive ((Cons ((NR.tree_decl (S O)), Nil)),
    (Cons (NR.leaf_ctor, (Cons (NR.node_ctor, Nil)))), (Cons
    ((NR.with_rec_k NR.tree_rec True), (Cons (NR.tree_aux_rec, Nil)))))),
    (Cons ((BatchInductive ((Cons ((NR.tree_decl (S O)), Nil)), (Cons
    (NR.leaf_ctor, (Cons
    ((NR.ctor_decl NR.node NR.tree (S O) O O NR.node_ctor.decl_type),
    Nil)))), (Cons (NR.tree_rec, (Cons (NR.tree_aux_rec, Nil)))))), (Cons
    ((BatchInductive ((Cons ((NR.tree_decl (S O)), Nil)), (Cons
    (NR.leaf_ctor, (Cons (NR.node_ctor, Nil)))), (Cons (NR.tree_rec, (Cons
    ((NR.with_rules NR.tree_aux_rec Nil), Nil)))))), Nil)))))))))
