
type unit0 =
| Tt

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
| Pair (x, _) -> x

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
   | S p -> S (add p m)
end
include Coq__1

(** val sub : nat -> nat -> nat **)

let rec sub n0 m =
  match n0 with
  | O -> n0
  | S k -> (match m with
            | O -> n0
            | S l -> sub k l)

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

  (** val max : nat -> nat -> nat **)

  let rec max n0 m =
    match n0 with
    | O -> m
    | S n' -> (match m with
               | O -> n0
               | S m' -> S (max n' m'))
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
        | Cons (x, _) -> Some x)
| S n1 -> (match l with
           | Nil -> None
           | Cons (_, l') -> nth_error l' n1)

(** val rev : 'a1 list -> 'a1 list **)

let rec rev = function
| Nil -> Nil
| Cons (x, l') -> app (rev l') (Cons (x, Nil))

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

(** val find : ('a1 -> bool) -> 'a1 list -> 'a1 option **)

let rec find f = function
| Nil -> None
| Cons (x, tl) -> (match f x with
                   | True -> Some x
                   | False -> find f tl)

type positive =
| XI of positive
| XO of positive
| XH

type n =
| N0
| Npos of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val pred_N : positive -> n **)

  let pred_N = function
  | XI p -> Npos (XO p)
  | XO p -> Npos (pred_double p)
  | XH -> N0

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

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

  (** val coq_Nsucc_double : n -> n **)

  let coq_Nsucc_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val coq_Ndouble : n -> n **)

  let coq_Ndouble = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val coq_lor : positive -> positive -> positive **)

  let rec coq_lor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XI (coq_lor p0 q0)
       | XH -> p)
    | XO p0 ->
      (match q with
       | XI q0 -> XI (coq_lor p0 q0)
       | XO q0 -> XO (coq_lor p0 q0)
       | XH -> XI p0)
    | XH -> (match q with
             | XO q0 -> XI q0
             | _ -> q)

  (** val coq_land : positive -> positive -> n **)

  let rec coq_land p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> Npos XH)
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_land p0 q0)
       | XO q0 -> coq_Ndouble (coq_land p0 q0)
       | XH -> N0)
    | XH -> (match q with
             | XO _ -> N0
             | _ -> Npos XH)

  (** val coq_lxor : positive -> positive -> n **)

  let rec coq_lxor p q =
    match p with
    | XI p0 ->
      (match q with
       | XI q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XO q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XH -> Npos (XO p0))
    | XO p0 ->
      (match q with
       | XI q0 -> coq_Nsucc_double (coq_lxor p0 q0)
       | XO q0 -> coq_Ndouble (coq_lxor p0 q0)
       | XH -> Npos (XI p0))
    | XH ->
      (match q with
       | XI q0 -> Npos (XO q0)
       | XO q0 -> Npos (XI q0)
       | XH -> N0)

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double_mask (sub_mask p q)
       | XO q -> succ_double_mask (sub_mask p q)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> succ_double_mask (sub_mask_carry p q)
       | XO q -> double_mask (sub_mask p q)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q -> double_mask (sub_mask_carry p q)
       | XO q -> succ_double_mask (sub_mask_carry p q)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z -> z
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> compare_cont r p q
       | XO q -> compare_cont Gt p q
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q -> compare_cont Lt p q
       | XO q -> compare_cont r p q
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val pow : positive -> positive -> positive **)

  let pow x =
    iter (mul x) XH

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O

  (** val size : positive -> positive **)

  let rec size = function
  | XI p0 -> succ (size p0)
  | XO p0 -> succ (size p0)
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

  let shiftl p = function
  | N0 -> p
  | Npos n1 -> iter (fun x -> XO x) p n1
 end

module N =
 struct
  (** val succ_double : n -> n **)

  let succ_double = function
  | N0 -> Npos XH
  | Npos p -> Npos (XI p)

  (** val double : n -> n **)

  let double = function
  | N0 -> N0
  | Npos p -> Npos (XO p)

  (** val sub : n -> n -> n **)

  let sub n0 m =
    match n0 with
    | N0 -> N0
    | Npos n' ->
      (match m with
       | N0 -> n0
       | Npos m' ->
         (match Pos.sub_mask n' m' with
          | Pos.IsPos p -> Npos p
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

  let leb x y =
    match compare x y with
    | Gt -> False
    | _ -> True

  (** val pos_div_eucl : positive -> n -> (n, n) prod **)

  let rec pos_div_eucl a b =
    match a with
    | XI a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = succ_double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XO a' ->
      let Pair (q, r) = pos_div_eucl a' b in
      let r' = double r in
      (match leb b r' with
       | True -> Pair ((succ_double q), (sub r' b))
       | False -> Pair ((double q), r'))
    | XH ->
      (match b with
       | N0 -> Pair (N0, (Npos XH))
       | Npos p ->
         (match p with
          | XH -> Pair ((Npos XH), N0)
          | _ -> Pair (N0, (Npos XH))))

  (** val coq_lor : n -> n -> n **)

  let coq_lor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Pos.coq_lor p q))

  (** val coq_land : n -> n -> n **)

  let coq_land n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Pos.coq_land p q)

  (** val coq_lxor : n -> n -> n **)

  let coq_lxor n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Pos.coq_lxor p q)

  (** val succ : n -> n **)

  let succ = function
  | N0 -> Npos XH
  | Npos p -> Npos (Pos.succ p)

  (** val pred : n -> n **)

  let pred = function
  | N0 -> N0
  | Npos p -> Pos.pred_N p

  (** val add : n -> n -> n **)

  let add n0 m =
    match n0 with
    | N0 -> m
    | Npos p -> (match m with
                 | N0 -> n0
                 | Npos q -> Npos (Coq_Pos.add p q))

  (** val mul : n -> n -> n **)

  let mul n0 m =
    match n0 with
    | N0 -> N0
    | Npos p -> (match m with
                 | N0 -> N0
                 | Npos q -> Npos (Coq_Pos.mul p q))

  (** val eqb : n -> n -> bool **)

  let eqb n0 m =
    match n0 with
    | N0 -> (match m with
             | N0 -> True
             | Npos _ -> False)
    | Npos p -> (match m with
                 | N0 -> False
                 | Npos q -> Pos.eqb p q)

  (** val ltb : n -> n -> bool **)

  let ltb x y =
    match compare x y with
    | Lt -> True
    | _ -> False

  (** val div2 : n -> n **)

  let div2 = function
  | N0 -> N0
  | Npos p0 -> (match p0 with
                | XI p -> Npos p
                | XO p -> Npos p
                | XH -> N0)

  (** val pow : n -> n -> n **)

  let pow n0 = function
  | N0 -> Npos XH
  | Npos p0 -> (match n0 with
                | N0 -> N0
                | Npos q -> Npos (Coq_Pos.pow q p0))

  (** val log2 : n -> n **)

  let log2 = function
  | N0 -> N0
  | Npos p0 ->
    (match p0 with
     | XI p -> Npos (Coq_Pos.size p)
     | XO p -> Npos (Coq_Pos.size p)
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
    | Npos p -> (match b with
                 | N0 -> a
                 | Npos q -> Npos (Coq_Pos.gcd p q))

  (** val shiftl : n -> n -> n **)

  let shiftl a n0 =
    match a with
    | N0 -> N0
    | Npos a0 -> Npos (Coq_Pos.shiftl a0 n0)

  (** val shiftr : n -> n -> n **)

  let shiftr a = function
  | N0 -> a
  | Npos p -> Pos.iter div2 a p

  (** val to_nat : n -> nat **)

  let to_nat = function
  | N0 -> O
  | Npos p -> Pos.to_nat p

  (** val of_nat : nat -> n **)

  let of_nat = function
  | O -> N0
  | S n' -> Npos (Pos.of_succ_nat n')
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val zero : ascii **)

let zero =
  Ascii (False, False, False, False, False, False, False, False)

(** val one : ascii **)

let one =
  Ascii (True, False, False, False, False, False, False, False)

(** val shift : bool -> ascii -> ascii **)

let shift c = function
| Ascii (a1, a2, a3, a4, a5, a6, a7, _) ->
  Ascii (c, a1, a2, a3, a4, a5, a6, a7)

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

(** val ascii_of_pos : positive -> ascii **)

let ascii_of_pos =
  let rec loop n0 p =
    match n0 with
    | O -> zero
    | S n' ->
      (match p with
       | XI p' -> shift True (loop n' p')
       | XO p' -> shift False (loop n' p')
       | XH -> one)
  in loop (S (S (S (S (S (S (S (S O))))))))

(** val ascii_of_N : n -> ascii **)

let ascii_of_N = function
| N0 -> zero
| Npos p -> ascii_of_pos p

(** val ascii_of_nat : nat -> ascii **)

let ascii_of_nat a =
  ascii_of_N (N.of_nat a)

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

(** val list_eqb : ('a1 -> 'a1 -> bool) -> 'a1 list -> 'a1 list -> bool **)

let rec list_eqb eqb2 xs ys =
  match xs with
  | Nil -> (match ys with
            | Nil -> True
            | Cons (_, _) -> False)
  | Cons (x, xs0) ->
    (match ys with
     | Nil -> False
     | Cons (y, ys0) ->
       (match eqb2 x y with
        | True -> list_eqb eqb2 xs0 ys0
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
  | Cons (p, ps0) ->
    (match us with
     | Nil -> LParam n0
     | Cons (u0, us0) ->
       (match name_eqb p n0 with
        | True -> u0
        | False -> lookup_level ps0 us0 n0))

(** val subst_level : name list -> level list -> level -> level **)

let rec subst_level ps us = function
| LSucc v0 -> LSucc (subst_level ps us v0)
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

(** val literal_eqb : literal -> literal -> bool **)

let literal_eqb a b =
  match a with
  | LitNat n0 -> (match b with
                  | LitNat m -> N.eqb n0 m
                  | LitString _ -> False)
  | LitString s -> (match b with
                    | LitNat _ -> False
                    | LitString t -> eqb1 s t)

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
  | EApp (f, x) ->
    (match b with
     | EApp (g, y) ->
       (match expr_eqb f g with
        | True -> expr_eqb x y
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
     | ELet (_, c, w0, d, _) ->
       (match match expr_eqb a0 c with
              | True -> expr_eqb v0 w0
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

let push_binding g ty value =
  { bound_context = (Cons ({ binding_type = ty; binding_value = value },
    g.bound_context)); free_context = g.free_context }

(** val find_free : name -> (name, binding) prod list -> binding option **)

let rec find_free n0 = function
| Nil -> None
| Cons (p, xs0) ->
  let Pair (m, b) = p in
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

(** val level_eval : (name -> nat) -> level -> nat **)

let rec level_eval rho = function
| LSucc v0 -> S (level_eval rho v0)
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

let rec normalize_aux fuel u0 path k =
  match fuel with
  | O -> Decline OutOfFuel
  | S fuel0 ->
    (match u0 with
     | LZero -> Accept (const_atom path k)
     | LSucc v0 -> normalize_aux fuel0 v0 path (S k)
     | LMax (a, b) ->
       combine_levels (normalize_aux fuel0 a path k)
         (normalize_aux fuel0 b path k)
     | LIMax (a, b) ->
       (match b with
        | LZero -> Accept (const_atom path k)
        | LSucc v0 ->
          combine_levels (normalize_aux fuel0 a path k)
            (normalize_aux fuel0 v0 path (S k))
        | LMax (v0, w0) ->
          combine_levels (normalize_aux fuel0 (LIMax (a, v0)) path k)
            (normalize_aux fuel0 (LIMax (a, w0)) path k)
        | LIMax (v0, w0) ->
          combine_levels (normalize_aux fuel0 (LIMax (a, w0)) path k)
            (normalize_aux fuel0 (LIMax (v0, w0)) path k)
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

let normalize_level fuel u0 =
  match level_has_meta u0 with
  | True -> Reject MetaVariable
  | False -> normalize_aux fuel u0 Nil O

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

let level_le fuel u0 v0 =
  bind (normalize_level fuel u0) (fun xs ->
    bind (normalize_level fuel v0) (fun ys -> Accept (sublevels_le xs ys)))

(** val level_equiv : nat -> level -> level -> bool result **)

let level_equiv fuel u0 v0 =
  bind (normalize_level fuel u0) (fun xs ->
    bind (normalize_level fuel v0) (fun ys -> Accept
      (match sublevels_le xs ys with
       | True -> sublevels_le ys xs
       | False -> False)))

(** val levels_equiv : nat -> level list -> level list -> bool result **)

let rec levels_equiv fuel us vs =
  match us with
  | Nil -> (match vs with
            | Nil -> Accept True
            | Cons (_, _) -> Accept False)
  | Cons (u0, us0) ->
    (match vs with
     | Nil -> Accept False
     | Cons (v0, vs0) ->
       bind (level_equiv fuel u0 v0) (fun b ->
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

let nat_probe_allowed mode t s =
  match mode with
  | NormalReduction ->
    (match negb (has_external_local t) with
     | True -> negb (has_external_local s)
     | False -> False)
  | EagerReduction -> True

(** val true_probe_allowed : reduction_mode -> expr -> bool **)

let true_probe_allowed mode t =
  match mode with
  | NormalReduction -> negb (has_external_local t)
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
                     | DPrimitive p ->
                       (match p with
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
                     | DPrimitive p ->
                       (match p with
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
  fold_left (fun x x0 -> EApp (x, x0)) args e

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

let core_ctor_shape env n0 parent index fields ty =
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
        | True -> expr_eqb d.decl_type ty
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
        | DPrimitive p ->
          (match p with
           | PCharOfNat ->
             (match s.decl_kind_of with
              | DPrimitive p0 ->
                (match p0 with
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
  bind (rec0.infer_method g e) (fun t ->
    bind (rec0.whnf_method g t) (fun t0 ->
      match t0 with
      | ESort u0 -> Accept u0
      | _ -> Reject ExpectedSort))

(** val core_apply_type :
    methods -> context -> expr -> expr list -> expr result **)

let rec core_apply_type rec0 g ty = function
| Nil -> Accept ty
| Cons (a, args0) ->
  bind (rec0.whnf_method g ty) (fun ty0 ->
    match ty0 with
    | EPi (_, _, _, body) -> core_apply_type rec0 g (instantiate body a) args0
    | _ -> Reject ExpectedPi)

(** val core_projection_field :
    methods -> nat -> context -> name -> expr -> bool -> nat -> nat -> expr
    -> expr result **)

let rec core_projection_field rec0 fuel g owner value maybe_prop skip index ty =
  bind (rec0.whnf_method g ty) (fun reduced ->
    match reduced with
    | EPi (_, _, domain, body) ->
      let verify_prop = fun _ ->
        bind (sort_of rec0 g domain) (fun u0 ->
          bind (level_equiv fuel u0 LZero) (fun ok -> require ok TypeMismatch))
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
           core_projection_field rec0 fuel g owner value maybe_prop skip0 (S
             index) (instantiate body (EProj (owner, index, value)))))
    | _ -> Reject ExpectedPi)

(** val core_infer_projection :
    methods -> nat -> environment -> context -> name -> nat -> expr -> expr
    result **)

let core_infer_projection rec0 fuel env g owner index value =
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
                             (fun ty ->
                             bind (sort_of rec0 g st0) (fun u0 ->
                               core_projection_field rec0 fuel g owner value
                                 (negb (core_level_positive u0)) index O ty)))
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

let core_shiftr fuel a b =
  match N.ltb (N.log2 a) b with
  | True -> Accept N0
  | False ->
    (match N.leb b (N.of_nat fuel) with
     | True -> Accept (N.shiftr a b)
     | False -> Decline OutOfFuel)

(** val core_binary_nat :
    nat -> environment -> primitive_kind -> n -> n -> expr option result **)

let core_binary_nat fuel env op a b =
  let numeric = fun n0 -> Accept (Some (ELit (LitNat n0))) in
  let bounded = fun operation ->
    match N.leb b (N.of_nat fuel) with
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
   | PNatShiftRight -> bind (core_shiftr fuel a b) numeric
   | _ -> Accept None)

(** val core_reduce_nat :
    methods -> nat -> environment -> context -> expr -> expr option result **)

let core_reduce_nat rec0 fuel env g e =
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
                      | DPrimitive p ->
                        (match p with
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
                                      core_binary_nat fuel env op a1 b1
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
   | True -> option_map (fun x -> Cons ((N.of_nat n0), x)) (core_utf8 rest)
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
                 option_map (fun x -> Cons
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
                   x)) (core_utf8 tail)
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
                       option_map (fun x -> Cons
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
                         x)) (core_utf8 tail)
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
                             option_map (fun x -> Cons
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
                               x)) (core_utf8 tail)
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

let core_to_constructor rec0 fuel env g owner k_rule value =
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
               bind (rec0.infer_method g reduced) (fun ty ->
                 bind (rec0.whnf_method g ty) (fun ty0 ->
                   let Pair (head, args) = core_spine ty0 Nil in
                   (match head with
                    | EConst (n1, us) ->
                      (match negb (name_eqb n1 owner) with
                       | True -> Accept reduced
                       | False ->
                         (match core_make_structure env owner us args reduced with
                          | Some candidate ->
                            (match k_rule with
                             | True ->
                               bind (sort_of rec0 g ty0) (fun sort ->
                                 bind (level_equiv fuel sort LZero)
                                   (fun prop1 ->
                                   match prop1 with
                                   | True ->
                                     bind (rec0.infer_method g candidate)
                                       (fun ct ->
                                       bind (rec0.defeq_method g ty0 ct)
                                         (fun ok ->
                                         match ok with
                                         | True -> Accept candidate
                                         | False -> Accept reduced))
                                   | False -> Accept reduced))
                             | False ->
                               bind (sort_of rec0 g ty0) (fun sort ->
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
            bind (rec0.infer_method g reduced) (fun ty ->
              bind (rec0.whnf_method g ty) (fun ty0 ->
                let Pair (head, args) = core_spine ty0 Nil in
                (match head with
                 | EConst (n0, us) ->
                   (match negb (name_eqb n0 owner) with
                    | True -> Accept reduced
                    | False ->
                      (match core_make_structure env owner us args reduced with
                       | Some candidate ->
                         (match k_rule with
                          | True ->
                            bind (sort_of rec0 g ty0) (fun sort ->
                              bind (level_equiv fuel sort LZero)
                                (fun prop1 ->
                                match prop1 with
                                | True ->
                                  bind (rec0.infer_method g candidate)
                                    (fun ct ->
                                    bind (rec0.defeq_method g ty0 ct)
                                      (fun ok ->
                                      match ok with
                                      | True -> Accept candidate
                                      | False -> Accept reduced))
                                | False -> Accept reduced))
                          | False ->
                            bind (sort_of rec0 g ty0) (fun sort ->
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

let core_reduce_recursor rec0 fuel env g e =
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
                   (core_to_constructor rec0 fuel env g owner info.rec_k
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
          | DQuotient q ->
            (match q with
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
                                      | DQuotient q ->
                                        (match q with
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

let rec infer_step rec0 fuel env ps checking g = function
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
  bind (infer_step rec0 fuel env ps checking g f) (fun ft ->
    bind (rec0.whnf_method g ft) (fun ft0 ->
      match ft0 with
      | EPi (_, _, domain, body) ->
        bind
          (match checking with
           | True ->
             bind (infer_step rec0 fuel env ps True g a) (fun arg_type ->
               bind (application_type_defeq rec0 g a domain arg_type)
                 (fun ok -> require ok TypeMismatch))
           | False -> Accept Tt)
          (fun _ -> Accept (instantiate body a))
      | _ -> Reject ExpectedPi))
| ELam (n0, bi, domain, body) ->
  bind
    (match checking with
     | True ->
       bind (infer_step rec0 fuel env ps True g domain) (fun dt ->
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
      (infer_step rec0 fuel env ps checking (push_binding g domain None) body)
      (fun bt -> Accept (EPi (n0, bi, domain, bt))))
| EPi (_, _, domain, body) ->
  bind (infer_step rec0 fuel env ps checking g domain) (fun dt ->
    bind (rec0.whnf_method g dt) (fun dt0 ->
      bind (match dt0 with
            | ESort u0 -> Accept u0
            | _ -> Reject ExpectedSort)
        (fun u0 ->
        let gb = push_binding g domain None in
        bind (infer_step rec0 fuel env ps checking gb body) (fun bt ->
          bind (rec0.whnf_method gb bt) (fun bt0 ->
            bind
              (match bt0 with
               | ESort v0 -> Accept v0
               | _ -> Reject ExpectedSort)
              (fun v0 -> Accept (ESort (LIMax (u0, v0)))))))))
| ELet (_, ty, value, body, _) ->
  bind
    (match checking with
     | True ->
       bind (infer_step rec0 fuel env ps True g ty) (fun sort_type ->
         bind (rec0.whnf_method g sort_type) (fun sort_type0 ->
           bind
             (match sort_type0 with
              | EBVar _ -> Reject ExpectedSort
              | EFVar _ -> Reject ExpectedSort
              | EMVar _ -> Reject ExpectedSort
              | ESort _ -> Accept Tt
              | _ -> Reject ExpectedSort)
             (fun _ ->
             bind (infer_step rec0 fuel env ps True g value) (fun vt ->
               bind (rec0.defeq_method g vt ty) (fun ok ->
                 require ok TypeMismatch)))))
     | False -> Accept Tt)
    (fun _ ->
    bind
      (infer_step rec0 fuel env ps checking (push_binding g ty (Some value))
        body)
      (fun bt -> Accept (instantiate bt value)))
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
       fuel env g owner index value
   | None -> Decline UnsupportedExpression)
| EMData body -> infer_step rec0 fuel env ps checking g body

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

let whnf_core_step rec0 fuel env ps cheap g e = match e with
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
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot ->
        bind
          (match quot with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | EFVar _ ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot ->
        bind
          (match quot with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | EMVar _ ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot ->
        bind
          (match quot with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | ESort _ ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot ->
        bind
          (match quot with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | EConst (_, _) ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot ->
        bind
          (match quot with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | EApp (_, _) ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot ->
        bind
          (match quot with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | ELam (_, _, _, _) -> rec0.whnf_core_method cheap g (core_beta fn args)
    | EPi (_, _, _, _) ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot ->
        bind
          (match quot with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | ELet (_, _, _, _, _) ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot ->
        bind
          (match quot with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | ELit _ ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot ->
        bind
          (match quot with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | EProj (_, _, _) ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot ->
        bind
          (match quot with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel env g rebuilt)
          (fun step ->
          match step with
          | Some value -> rec0.whnf_core_method cheap g value
          | None -> Accept rebuilt))
    | EMData _ ->
      let rebuilt = core_apps fn args in
      bind (core_reduce_quotient rec0 env g rebuilt) (fun quot ->
        bind
          (match quot with
           | Some value -> Accept (Some value)
           | None -> core_reduce_recursor rec0 fuel env g rebuilt)
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

let whnf_round_step rec0 fuel env ps g e =
  bind (whnf_core_step rec0 fuel env ps False g e) (fun reduced ->
    match reduced with
    | EBVar _ ->
      bind (core_reduce_nat rec0 fuel env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | EFVar _ ->
      bind (core_reduce_nat rec0 fuel env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | EMVar _ ->
      bind (core_reduce_nat rec0 fuel env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | ESort _ ->
      bind (core_reduce_nat rec0 fuel env g reduced) (fun native ->
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
      bind (core_reduce_nat rec0 fuel env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | ELam (_, _, _, _) ->
      bind (core_reduce_nat rec0 fuel env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | EPi (_, _, _, _) ->
      bind (core_reduce_nat rec0 fuel env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | ELet (_, _, _, _, _) ->
      bind (core_reduce_nat rec0 fuel env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | ELit _ ->
      bind (core_reduce_nat rec0 fuel env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | EProj (_, _, _) ->
      bind (core_reduce_nat rec0 fuel env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced)
    | EMData _ ->
      bind (core_reduce_nat rec0 fuel env g reduced) (fun native ->
        match native with
        | Some value -> Accept (WhnfDone value)
        | None -> finish_whnf_unfold env ps reduced))

(** val whnf_loop :
    nat -> methods -> nat -> environment -> name list -> context -> expr ->
    expr result **)

let whnf_loop rounds rec0 fuel env ps g e =
  run_whnf_rounds rounds (whnf_round_step rec0 fuel env ps g) e

(** val eta_compare :
    methods -> context -> expr -> expr -> expr -> bool result **)

let eta_compare rec0 g domain body other =
  bind (rec0.infer_method g other) (fun ty ->
    bind (rec0.whnf_method g ty) (fun ty0 ->
      match ty0 with
      | EPi (_, _, domain', _) ->
        bind (rec0.defeq_method g domain domain') (fun ok ->
          match ok with
          | True ->
            rec0.defeq_method (push_binding g domain None) body (EApp
              ((lift (S O) O other), (EBVar O)))
          | False -> Accept False)
      | _ -> Accept False))

(** val core_alpha : nat -> expr -> expr -> (bool, nat) prod **)

let rec core_alpha budget t s =
  match budget with
  | O -> Pair (False, O)
  | S budget0 ->
    (match t with
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
        | ELet (_, c, w0, d, _) ->
          let Pair (ok, remaining) = core_alpha budget0 a c in
          (match ok with
           | True ->
             let Pair (ok0, remaining0) = core_alpha remaining v0 w0 in
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

let core_alpha_eq t s =
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
      t s)

(** val core_compare_args :
    methods -> context -> expr list -> expr list -> bool result **)

let rec core_compare_args rec0 g xs ys =
  match xs with
  | Nil -> (match ys with
            | Nil -> Accept True
            | Cons (_, _) -> Accept False)
  | Cons (x, xs0) ->
    (match ys with
     | Nil -> Accept False
     | Cons (y, ys0) ->
       bind (rec0.defeq_method g x y) (fun ok ->
         match ok with
         | True -> core_compare_args rec0 g xs0 ys0
         | False -> Accept False))

(** val core_same_head : nat -> expr -> expr -> bool result **)

let core_same_head fuel t s =
  match t with
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
        | True -> levels_equiv fuel us vs
        | False -> Accept False)
     | _ -> Accept False)
  | _ -> Accept False

(** val core_congruent_apps :
    methods -> nat -> context -> expr -> expr -> bool result **)

let core_congruent_apps rec0 fuel g t s =
  match t with
  | EApp (_, _) ->
    (match s with
     | EApp (_, _) ->
       let Pair (tf, ta) = core_spine t Nil in
       let Pair (sf, sa) = core_spine s Nil in
       bind (core_same_head fuel tf sf) (fun same ->
         match match same with
               | True -> Nat.eqb (length ta) (length sa)
               | False -> False with
         | True -> core_compare_args rec0 g (rev ta) (rev sa)
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

let core_delta_sides env t s =
  match core_delta_info env t with
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

let core_delta_congruent rec0 fuel env g t s =
  match core_delta_info env t with
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
                        (match core_erasing_delta env t with
                         | True -> True
                         | False -> core_erasing_delta env s)
                    | False -> False with
              | True -> core_congruent_apps rec0 fuel g t s
              | False -> Accept False)
           | _ -> Accept False)
        | _ -> Accept False)
     | None -> Accept False)
  | None -> Accept False

(** val compare_heads :
    methods -> nat -> context -> expr -> expr -> bool result **)

let compare_heads rec0 fuel g t s =
  match t with
  | EBVar n0 ->
    (match s with
     | EBVar m -> Accept (Nat.eqb n0 m)
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t
     | _ -> Accept False)
  | EFVar n0 ->
    (match s with
     | EFVar m -> Accept (name_eqb n0 m)
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t
     | _ -> Accept False)
  | EMVar _ ->
    (match s with
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t
     | _ -> Accept False)
  | EConst (n0, us) ->
    (match s with
     | EConst (m, vs) ->
       (match name_eqb n0 m with
        | True -> levels_equiv fuel us vs
        | False -> Accept False)
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t
     | _ -> Accept False)
  | EApp (_, _) ->
    (match s with
     | EApp (_, _) ->
       let Pair (tf, ta) = core_spine t Nil in
       let Pair (sf, sa) = core_spine s Nil in
       (match Nat.eqb (length ta) (length sa) with
        | True ->
          bind (rec0.defeq_method g tf sf) (fun ok ->
            match ok with
            | True -> core_compare_args rec0 g ta sa
            | False -> Accept False)
        | False -> Accept False)
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t
     | _ -> Accept False)
  | ELam (_, _, domain, body) -> eta_compare rec0 g domain body s
  | EPi (_, _, _, _) ->
    (match s with
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t
     | _ -> Accept False)
  | ELet (_, _, _, _, _) ->
    (match s with
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t
     | _ -> Accept False)
  | EProj (n0, i, a) ->
    (match s with
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t
     | EProj (m, j, b) ->
       (match match name_eqb n0 m with
              | True -> Nat.eqb i j
              | False -> False with
        | True -> rec0.defeq_method g a b
        | False -> Accept False)
     | _ -> Accept False)
  | _ ->
    (match s with
     | ELam (_, _, domain, body) -> eta_compare rec0 g domain body t
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

let core_unit_like rec0 env g t s =
  bind (rec0.infer_method g t) (fun ty ->
    bind (rec0.whnf_method g ty) (fun ty0 ->
      match fst (core_spine ty0 Nil) with
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
                            rec0.defeq_method g ty0 sty)
                        | False -> Accept False)
                     | None -> Accept False)
                  | Cons (_, _) -> Accept False))
            | None -> Accept False)
         | False -> Accept False)
      | _ -> Accept False))

(** val core_try_string_expansion :
    methods -> context -> expr -> expr -> bool option result **)

let core_try_string_expansion rec0 g t s =
  let expand = fun text other ->
    bind (core_expand_string text) (fun expanded ->
      bind (rec0.defeq_method g expanded other) (fun ok -> Accept (Some ok)))
  in
  (match t with
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
                  | True -> expand text t
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

let core_compare_fallback rec0 fuel env g t s =
  bind (compare_heads rec0 fuel g t s) (fun ok ->
    match ok with
    | True -> Accept True
    | False ->
      bind (core_structure_eta rec0 env g t s) (fun ok0 ->
        match ok0 with
        | True -> Accept True
        | False ->
          bind (core_structure_eta rec0 env g s t) (fun ok1 ->
            match ok1 with
            | True -> Accept True
            | False ->
              bind (core_try_string_expansion rec0 g t s) (fun expanded ->
                match expanded with
                | Some ok2 -> Accept ok2
                | None -> core_unit_like rec0 env g t s))))

(** val compare_after_whnf :
    methods -> nat -> environment -> context -> expr -> expr -> bool result **)

let compare_after_whnf rec0 fuel env g t s =
  match core_alpha_eq t s with
  | True -> Accept True
  | False ->
    (match t with
     | ESort u0 ->
       (match s with
        | ESort v0 -> level_equiv fuel u0 v0
        | _ ->
          bind (rec0.infer_method g t) (fun tt ->
            bind (sort_of rec0 g tt) (fun sort ->
              bind (level_equiv fuel sort LZero) (fun is_prop ->
                match is_prop with
                | True ->
                  bind (rec0.infer_method g s) (fun st ->
                    rec0.defeq_method g tt st)
                | False -> core_compare_fallback rec0 fuel env g t s))))
     | ELam (_, _, a, b) ->
       (match s with
        | ELam (_, _, c, d) ->
          bind (rec0.defeq_method g a c) (fun ok ->
            match ok with
            | True -> rec0.defeq_method (push_binding g a None) b d
            | False -> Accept False)
        | _ ->
          bind (rec0.infer_method g t) (fun tt ->
            bind (sort_of rec0 g tt) (fun sort ->
              bind (level_equiv fuel sort LZero) (fun is_prop ->
                match is_prop with
                | True ->
                  bind (rec0.infer_method g s) (fun st ->
                    rec0.defeq_method g tt st)
                | False -> core_compare_fallback rec0 fuel env g t s))))
     | EPi (_, _, a, b) ->
       (match s with
        | EPi (_, _, c, d) ->
          bind (rec0.defeq_method g a c) (fun ok ->
            match ok with
            | True -> rec0.defeq_method (push_binding g a None) b d
            | False -> Accept False)
        | _ ->
          bind (rec0.infer_method g t) (fun tt ->
            bind (sort_of rec0 g tt) (fun sort ->
              bind (level_equiv fuel sort LZero) (fun is_prop ->
                match is_prop with
                | True ->
                  bind (rec0.infer_method g s) (fun st ->
                    rec0.defeq_method g tt st)
                | False -> core_compare_fallback rec0 fuel env g t s))))
     | ELit l ->
       (match l with
        | LitNat n0 ->
          (match s with
           | ELit l0 ->
             (match l0 with
              | LitNat m -> Accept (N.eqb n0 m)
              | LitString _ ->
                bind (rec0.infer_method g t) (fun tt ->
                  bind (sort_of rec0 g tt) (fun sort ->
                    bind (level_equiv fuel sort LZero) (fun is_prop ->
                      match is_prop with
                      | True ->
                        bind (rec0.infer_method g s) (fun st ->
                          rec0.defeq_method g tt st)
                      | False -> core_compare_fallback rec0 fuel env g t s))))
           | _ ->
             bind (rec0.infer_method g t) (fun tt ->
               bind (sort_of rec0 g tt) (fun sort ->
                 bind (level_equiv fuel sort LZero) (fun is_prop ->
                   match is_prop with
                   | True ->
                     bind (rec0.infer_method g s) (fun st ->
                       rec0.defeq_method g tt st)
                   | False -> core_compare_fallback rec0 fuel env g t s))))
        | LitString a ->
          (match s with
           | ELit l0 ->
             (match l0 with
              | LitNat _ ->
                bind (rec0.infer_method g t) (fun tt ->
                  bind (sort_of rec0 g tt) (fun sort ->
                    bind (level_equiv fuel sort LZero) (fun is_prop ->
                      match is_prop with
                      | True ->
                        bind (rec0.infer_method g s) (fun st ->
                          rec0.defeq_method g tt st)
                      | False -> core_compare_fallback rec0 fuel env g t s)))
              | LitString b -> Accept (eqb1 a b))
           | _ ->
             bind (rec0.infer_method g t) (fun tt ->
               bind (sort_of rec0 g tt) (fun sort ->
                 bind (level_equiv fuel sort LZero) (fun is_prop ->
                   match is_prop with
                   | True ->
                     bind (rec0.infer_method g s) (fun st ->
                       rec0.defeq_method g tt st)
                   | False -> core_compare_fallback rec0 fuel env g t s)))))
     | _ ->
       bind (rec0.infer_method g t) (fun tt ->
         bind (sort_of rec0 g tt) (fun sort ->
           bind (level_equiv fuel sort LZero) (fun is_prop ->
             match is_prop with
             | True ->
               bind (rec0.infer_method g s) (fun st ->
                 rec0.defeq_method g tt st)
             | False -> core_compare_fallback rec0 fuel env g t s))))

(** val core_quick :
    methods -> nat -> context -> expr -> expr -> bool option result **)

let core_quick rec0 fuel g t s =
  match core_alpha_eq t s with
  | True -> Accept (Some True)
  | False ->
    (match t with
     | ESort u0 ->
       (match s with
        | ESort v0 ->
          bind (level_equiv fuel u0 v0) (fun ok -> Accept (Some ok))
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

let core_proof_irrel rec0 fuel g t s =
  bind (rec0.infer_method g t) (fun ty ->
    bind (sort_of rec0 g ty) (fun sort ->
      bind (level_equiv fuel sort LZero) (fun is_prop ->
        match is_prop with
        | True ->
          bind (rec0.infer_method g s) (fun sty ->
            bind (rec0.defeq_method g ty sty) (fun ok -> Accept (Some ok)))
        | False -> Accept None)))

type conversion_progress =
| ConversionDone of bool
| ConversionStuck of expr * expr

(** val core_offset :
    methods -> environment -> context -> expr -> expr -> bool option result **)

let core_offset rec0 env g t s =
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
    (match match zero0 t with
           | True -> zero0 s
           | False -> False with
     | True -> Accept (Some True)
     | False ->
       (match pred_of t with
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

let core_opposite_projection rec0 env g t s =
  match core_delta_info env t with
  | Some _ ->
    (match core_delta_info env s with
     | Some _ -> Accept None
     | None ->
       bind (core_try_unfold_proj_app rec0 g s) (fun reduced -> Accept
         (match reduced with
          | Some s' -> Some (Pair (t, s'))
          | None -> None)))
  | None ->
    (match core_delta_info env s with
     | Some _ ->
       bind (core_try_unfold_proj_app rec0 g t) (fun reduced -> Accept
         (match reduced with
          | Some t' -> Some (Pair (t', s))
          | None -> None))
     | None -> Accept None)

(** val core_lazy_delta :
    nat -> methods -> nat -> environment -> name list -> context -> expr ->
    expr -> conversion_progress result **)

let rec core_lazy_delta rounds rec0 fuel env ps g t s =
  match rounds with
  | O -> Decline OutOfFuel
  | S rounds0 ->
    bind (core_quick rec0 fuel g t s) (fun quick ->
      match quick with
      | Some ok -> Accept (ConversionDone ok)
      | None ->
        bind (core_offset rec0 env g t s) (fun offset ->
          match offset with
          | Some ok -> Accept (ConversionDone ok)
          | None ->
            let eligible =
              pair_probe_guard
                (nat_probe_head find_decl core_succ_name env
                  (core_spine t Nil))
                (nat_probe_head find_decl core_succ_name env
                  (core_spine s Nil))
                (fun _ -> nat_probe_allowed rec0.method_mode t s)
            in
            bind
              (match eligible with
               | True -> core_reduce_nat rec0 fuel env g t
               | False -> Accept None)
              (fun tn ->
              match tn with
              | Some tn0 ->
                bind (rec0.defeq_method g tn0 s) (fun ok -> Accept
                  (ConversionDone ok))
              | None ->
                bind
                  (match eligible with
                   | True -> core_reduce_nat rec0 fuel env g s
                   | False -> Accept None)
                  (fun sn ->
                  match sn with
                  | Some sn0 ->
                    bind (rec0.defeq_method g t sn0) (fun ok -> Accept
                      (ConversionDone ok))
                  | None ->
                    bind (core_delta_congruent rec0 fuel env g t s)
                      (fun same ->
                      match same with
                      | True -> Accept (ConversionDone True)
                      | False ->
                        bind (core_opposite_projection rec0 env g t s)
                          (fun projected ->
                          match projected with
                          | Some p ->
                            let Pair (tn0, sn0) = p in
                            core_lazy_delta rounds0 rec0 fuel env ps g tn0 sn0
                          | None ->
                            let Pair (unfold_left, unfold_right) =
                              core_delta_sides env t s
                            in
                            bind
                              (match unfold_left with
                               | True -> core_unfold env ps t
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
                                     | None -> Accept t)
                                    (fun tn0 ->
                                    bind
                                      (match sd with
                                       | Some e ->
                                         rec0.whnf_core_method True g e
                                       | None -> Accept s)
                                      (fun sn0 ->
                                      core_lazy_delta rounds0 rec0 fuel env
                                        ps g tn0 sn0))
                                | None ->
                                  (match sd with
                                   | Some _ ->
                                     bind
                                       (match td with
                                        | Some e ->
                                          rec0.whnf_core_method True g e
                                        | None -> Accept t)
                                       (fun tn0 ->
                                       bind
                                         (match sd with
                                          | Some e ->
                                            rec0.whnf_core_method True g e
                                          | None -> Accept s)
                                         (fun sn0 ->
                                         core_lazy_delta rounds0 rec0 fuel
                                           env ps g tn0 sn0))
                                   | None -> Accept (ConversionStuck (t, s)))))))))))

(** val core_finish_conversion :
    methods -> nat -> environment -> context -> expr -> expr -> bool result **)

let core_finish_conversion rec0 fuel env g t s =
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
  bind (project t) (fun tp ->
    bind (project s) (fun sp ->
      match tp with
      | Some t0 ->
        (match sp with
         | Some s0 -> rec0.defeq_method g t0 s0
         | None -> rec0.defeq_method g t0 s)
      | None ->
        (match sp with
         | Some s0 -> rec0.defeq_method g t s0
         | None -> compare_after_whnf rec0 fuel env g t s)))

(** val core_is_true : expr -> bool **)

let core_is_true = function
| EConst (n0, l) ->
  (match l with
   | Nil -> name_eqb n0 core_true_name
   | Cons (_, _) -> False)
| _ -> False

(** val core_true_shortcut :
    methods -> environment -> context -> expr -> expr -> bool result **)

let core_true_shortcut rec0 env g t s =
  match match match core_is_true s with
              | True -> true_probe_allowed rec0.method_mode t
              | False -> False with
        | True -> core_bool_ready env
        | False -> False with
  | True -> bind (rec0.whnf_method g t) (fun tn -> Accept (core_is_true tn))
  | False -> Accept False

(** val defeq_step :
    methods -> nat -> environment -> name list -> context -> expr -> expr ->
    bool result **)

let defeq_step rec0 fuel env ps g t s =
  let rec1 = inference_only rec0 in
  bind (core_quick rec1 fuel g t s) (fun quick ->
    match quick with
    | Some ok -> Accept ok
    | None ->
      bind (core_true_shortcut rec1 env g t s) (fun shortcut ->
        match shortcut with
        | True -> Accept True
        | False ->
          bind (core_proof_irrel rec1 fuel g t s) (fun irrelevant ->
            match irrelevant with
            | Some ok -> Accept ok
            | None ->
              bind (rec1.whnf_core_method True g t) (fun tn ->
                bind (rec1.whnf_core_method True g s) (fun sn ->
                  bind (core_lazy_delta (S fuel) rec1 fuel env ps g tn sn)
                    (fun progress ->
                    match progress with
                    | ConversionDone ok -> Accept ok
                    | ConversionStuck (tn0, sn0) ->
                      core_finish_conversion rec1 fuel env g tn0 sn0))))))

(** val checker_mode :
    reduction_mode -> nat -> environment -> name list -> methods **)

let rec checker_mode mode fuel env ps =
  match fuel with
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
      whnf_core_step rec0 n0 env ps cheap g e); defeq_method = (fun g t s ->
      let rec0 = checker_mode mode n0 env ps in
      defeq_step rec0 n0 env ps g t s); method_mode = mode;
      eager_defeq_method = (fun g t s ->
      let rec0 = checker_mode EagerReduction n0 env ps in
      defeq_step rec0 n0 env ps g t s) }

(** val checker : nat -> environment -> name list -> methods **)

let checker =
  checker_mode NormalReduction

(** val infer :
    nat -> environment -> name list -> context -> expr -> expr result **)

let infer fuel env ps g e =
  (checker fuel env ps).infer_method g e

(** val whnf :
    nat -> environment -> name list -> context -> expr -> expr result **)

let whnf fuel env ps g e =
  match fuel with
  | O -> Decline OutOfFuel
  | S _ ->
    (match core_supported env e with
     | True -> (checker fuel env ps).whnf_method g e
     | False -> Decline UnsupportedExpression)

(** val defeq :
    nat -> environment -> name list -> context -> expr -> expr -> bool result **)

let defeq fuel env ps g t s =
  match fuel with
  | O -> Decline OutOfFuel
  | S _ ->
    (match match core_supported env t with
           | True -> core_supported env s
           | False -> False with
     | True -> (checker fuel env ps).defeq_method g t s
     | False -> Decline UnsupportedExpression)

(** val check :
    nat -> environment -> name list -> context -> expr -> expr -> unit0 result **)

let check fuel env ps g e ty =
  bind (sort_of (checker fuel env ps) g ty) (fun _ ->
    bind (infer fuel env ps g e) (fun et ->
      bind (defeq fuel env ps g et ty) (fun ok -> require ok TypeMismatch)))

(** val check_defeq :
    nat -> environment -> name list -> context -> expr -> expr -> unit0 result **)

let check_defeq fuel env ps g t s =
  bind (infer fuel env ps g t) (fun tt ->
    bind (infer fuel env ps g s) (fun st ->
      bind (defeq fuel env ps g tt st) (fun same_type ->
        bind (require same_type TypeMismatch) (fun _ ->
          bind (defeq fuel env ps g t s) (fun same_term ->
            require same_term NotDefinitionallyEqual)))))

type ind_local = { il_id : name; il_user : name; il_binder : binder_info;
                   il_type : expr }

type ind_state = { ist_next : nat; ist_context : context }

(** val initial_ind_state : ind_state **)

let initial_ind_state =
  { ist_next = O; ist_context = empty_context }

(** val local_expr : ind_local -> expr **)

let local_expr x =
  EFVar x.il_id

(** val local_exprs : ind_local list -> expr list **)

let local_exprs xs =
  map local_expr xs

(** val ind_fresh :
    ind_state -> name -> binder_info -> expr -> (ind_local, ind_state) prod **)

let ind_fresh s user bi ty =
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
  let x = { il_id = id; il_user = user; il_binder = bi; il_type = ty } in
  let g = s.ist_context in
  Pair (x, { ist_next = (S s.ist_next); ist_context = { bound_context =
  g.bound_context; free_context = (Cons ((Pair (id, { binding_type = ty;
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

(** val close_lam : ind_local list -> expr -> expr **)

let close_lam xs body =
  fold_right (fun x b -> ELam (x.il_user, x.il_binder, x.il_type,
    (abstract_local x.il_id O b))) body xs

(** val apply_exprs : expr -> expr list -> expr **)

let apply_exprs fn args =
  fold_left (fun x x0 -> EApp (x, x0)) args fn

(** val apply_locals : expr -> ind_local list -> expr **)

let apply_locals fn args =
  apply_exprs fn (local_exprs args)

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

let rec primitive_check_signature fuel actual expected =
  match fuel with
  | O -> Decline OutOfFuel
  | S fuel0 ->
    (match actual with
     | EApp (a, b) ->
       (match expected with
        | EApp (c, d) ->
          bind (primitive_check_signature fuel0 a c) (fun _ ->
            primitive_check_signature fuel0 b d)
        | _ -> require (expr_eqb actual expected) TypeMismatch)
     | EPi (_, _, a, b) ->
       (match expected with
        | EPi (_, _, c, d) ->
          bind (primitive_check_signature fuel0 a c) (fun _ ->
            primitive_check_signature fuel0 b d)
        | _ -> require (expr_eqb actual expected) TypeMismatch)
     | EMData a -> primitive_check_signature fuel0 a expected
     | _ -> require (expr_eqb actual expected) TypeMismatch)

(** val primitive_authenticated :
    nat -> environment -> primitive_kind -> unit0 result **)

let primitive_authenticated fuel env op =
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
            primitive_check_signature fuel d.decl_type
              (primitive_signature op))
        | None -> Reject MalformedDeclaration)
     | _ -> Reject MalformedDeclaration)
  | None -> Reject MalformedDeclaration

(** val primitive_dependencies :
    nat -> environment -> primitive_kind -> unit0 result **)

let primitive_dependencies fuel env op =
  bind (require (core_nat_ready env) MalformedDeclaration) (fun _ ->
    match op with
    | PNatSub -> primitive_authenticated fuel env PNatPred
    | PNatMul -> primitive_authenticated fuel env PNatAdd
    | PNatPow -> primitive_authenticated fuel env PNatMul
    | PNatBEq -> require (core_bool_ready env) MalformedDeclaration
    | PNatBLE -> require (core_bool_ready env) MalformedDeclaration
    | PNatShiftLeft -> primitive_authenticated fuel env PNatMul
    | PNatShiftRight -> primitive_authenticated fuel env PNatDiv
    | _ -> Accept Tt)

(** val primitive_closed : nat -> nat -> expr -> unit0 result **)

let rec primitive_closed fuel depth e =
  match fuel with
  | O -> Decline OutOfFuel
  | S fuel0 ->
    (match e with
     | EBVar i -> require (Nat.ltb i depth) LooseBoundVariable
     | EFVar _ -> Reject UnknownFreeVariable
     | EMVar _ -> Reject MetaVariable
     | EApp (a, b) ->
       bind (primitive_closed fuel0 depth a) (fun _ ->
         primitive_closed fuel0 depth b)
     | ELam (_, _, a, b) ->
       bind (primitive_closed fuel0 depth a) (fun _ ->
         primitive_closed fuel0 (S depth) b)
     | EPi (_, _, a, b) ->
       bind (primitive_closed fuel0 depth a) (fun _ ->
         primitive_closed fuel0 (S depth) b)
     | ELet (_, a, v0, b, _) ->
       bind (primitive_closed fuel0 depth a) (fun _ ->
         bind (primitive_closed fuel0 depth v0) (fun _ ->
           primitive_closed fuel0 (S depth) b))
     | EProj (_, _, a) -> primitive_closed fuel0 depth a
     | EMData a -> primitive_closed fuel0 depth a
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
  let f = fun x y -> core_apps body (Cons (x, (Cons (y, Nil)))) in
  let x = EBVar O in
  let xx = EBVar (S O) in
  let y = EBVar O in
  let base = fun z -> eqx (f x primitive_zero) z in
  let step = fun z -> eqxy (f xx (primitive_succ y)) z in
  (match op with
   | PNatAdd ->
     Some (Cons ((base x), (Cons ((step (primitive_succ (f xx y))), Nil))))
   | PNatPred ->
     Some (Cons ((eq0 (EApp (body, primitive_zero)) primitive_zero), (Cons
       ((eqx (EApp (body, (primitive_succ x))) x), Nil))))
   | PNatSub ->
     Some (Cons ((base x), (Cons
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
       ((eqx (f primitive_zero (primitive_succ x))
          (match op with
           | PNatBEq -> primitive_false
           | _ -> primitive_true)),
       (Cons ((eqx (f (primitive_succ x) primitive_zero) primitive_false),
       (Cons ((eqxy (f (primitive_succ xx) (primitive_succ y)) (f xx y)),
       Nil))))))))
   | PNatBLE ->
     Some (Cons ((eq0 (f primitive_zero primitive_zero) primitive_true),
       (Cons
       ((eqx (f primitive_zero (primitive_succ x))
          (match op with
           | PNatBEq -> primitive_false
           | _ -> primitive_true)),
       (Cons ((eqx (f (primitive_succ x) primitive_zero) primitive_false),
       (Cons ((eqxy (f (primitive_succ xx) (primitive_succ y)) (f xx y)),
       Nil))))))))
   | PNatShiftLeft ->
     Some (Cons ((base x), (Cons
       ((step
          (f
            (primitive_call PNatMul (Cons (primitive_two, (Cons (xx, Nil)))))
            y)),
       Nil))))
   | PNatShiftRight ->
     Some (Cons ((base x), (Cons
       ((step
          (primitive_call PNatDiv (Cons ((f xx y), (Cons (primitive_two,
            Nil)))))),
       Nil))))
   | _ -> None)

(** val primitive_check_equations :
    nat -> nat -> environment -> primitive_equation list -> unit0 result **)

let rec primitive_check_equations steps fuel env = function
| Nil -> Accept Tt
| Cons (e, es) ->
  (match steps with
   | O -> Decline OutOfFuel
   | S steps0 ->
     bind
       (check_defeq fuel env Nil e.primitive_context e.primitive_lhs
         e.primitive_rhs)
       (fun _ -> primitive_check_equations steps0 fuel env es))

(** val primitive_path : string list -> name **)

let primitive_path parts =
  fold_left (fun x x0 -> NameStr (x, x0)) parts NameAnon

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

  let eq a x y =
    apps
      (const (Cons ((String ((Ascii (True, False, True, False, False, False,
        True, False)), (String ((Ascii (True, False, False, False, True,
        True, True, False)), EmptyString)))), Nil)) (Cons ((LSucc LZero),
        Nil)))
      (Cons (a, (Cons (x, (Cons (y, Nil))))))

  (** val refl : term -> term -> term **)

  let refl a x =
    apps
      (const (Cons ((String ((Ascii (True, False, True, False, False, False,
        True, False)), (String ((Ascii (True, False, False, False, True,
        True, True, False)), EmptyString)))), (Cons ((String ((Ascii (False,
        True, False, False, True, True, True, False)), (String ((Ascii (True,
        False, True, False, False, True, True, False)), (String ((Ascii
        (False, True, True, False, False, True, True, False)), (String
        ((Ascii (False, False, True, True, False, True, True, False)),
        EmptyString)))))))), Nil)))) (Cons ((LSucc LZero), Nil)))
      (Cons (a, (Cons (x, Nil))))

  (** val not : term -> term **)

  let not p =
    app
      (const (Cons ((String ((Ascii (False, True, True, True, False, False,
        True, False)), (String ((Ascii (True, True, True, True, False, True,
        True, False)), (String ((Ascii (False, False, True, False, True,
        True, True, False)), EmptyString)))))), Nil)) Nil)
      p

  (** val dec : term -> term **)

  let dec p =
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
      p

  (** val is_true : term -> term -> term **)

  let is_true p h =
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
      (Cons (p, (Cons (h, Nil))))

  (** val is_false : term -> term -> term **)

  let is_false p h =
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
      (Cons (p, (Cons (h, Nil))))

  (** val ite : term -> term -> term -> term -> term -> term **)

  let ite ty p d t e =
    apps
      (const (Cons ((String ((Ascii (True, False, False, True, False, True,
        True, False)), (String ((Ascii (False, False, True, False, True,
        True, True, False)), (String ((Ascii (True, False, True, False,
        False, True, True, False)), EmptyString)))))), Nil)) (Cons ((LSucc
        LZero), Nil)))
      (Cons (ty, (Cons (p, (Cons (d, (Cons (t, (Cons (e, Nil))))))))))

  (** val dite :
      term -> term -> term -> (term -> term) -> (term -> term) -> term **)

  let dite ty p d t e =
    apps
      (const (Cons ((String ((Ascii (False, False, True, False, False, True,
        True, False)), (String ((Ascii (True, False, False, True, False,
        True, True, False)), (String ((Ascii (False, False, True, False,
        True, True, True, False)), (String ((Ascii (True, False, True, False,
        False, True, True, False)), EmptyString)))))))), Nil)) (Cons ((LSucc
        LZero), Nil)))
      (Cons (ty, (Cons (p, (Cons (d, (Cons ((lam p t), (Cons
      ((lam (not p) e), Nil))))))))))

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
    (PQ.lam PQ.prop (fun p ->
      PQ.lam PQ.bool (fun b ->
        PQ.pi PQ.prop (fun q ->
          PQ.arrow
            (PQ.arrow (PQ.arrow (PQ.eq PQ.bool b PQ.tru) p)
              (PQ.arrow
                (PQ.arrow
                  (match false_eq with
                   | True -> PQ.eq PQ.bool b PQ.fal
                   | False -> PQ.not (PQ.eq PQ.bool b PQ.tru))
                  (PQ.not p))
                q))
            q))))

(** val primitive_reflection_make : bool -> primitive_reflection **)

let primitive_reflection_make false_eq =
  let rt = primitive_reflection_type false_eq in
  let relation = fun p b -> PQ.apps (PQ.embed rt) (Cons (p, (Cons (b, Nil))))
  in
  { reflection_type = rt; reflection_true =
  (PQ.run
    (PQ.lam PQ.prop (fun p ->
      PQ.lam (relation p PQ.tru) (fun h ->
        PQ.apps h (Cons (p, (Cons
          ((PQ.lam (PQ.arrow (PQ.eq PQ.bool PQ.tru PQ.tru) p) (fun hp ->
             PQ.lam
               (PQ.arrow
                 (match false_eq with
                  | True -> PQ.eq PQ.bool PQ.tru PQ.fal
                  | False -> PQ.not (PQ.eq PQ.bool PQ.tru PQ.tru))
                 (PQ.not p))
               (fun _ -> PQ.app hp (PQ.refl PQ.bool PQ.tru)))),
          Nil))))))));
  reflection_false =
  (PQ.run
    (PQ.lam PQ.prop (fun p ->
      PQ.lam (relation p PQ.fal) (fun h ->
        PQ.apps h (Cons ((PQ.not p), (Cons
          ((PQ.lam (PQ.arrow (PQ.eq PQ.bool PQ.fal PQ.tru) p) (fun _ ->
             PQ.lam
               (PQ.arrow
                 (match false_eq with
                  | True -> PQ.eq PQ.bool PQ.fal PQ.fal
                  | False -> PQ.not (PQ.eq PQ.bool PQ.fal PQ.tru))
                 (PQ.not p))
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
    (PQ.lam PQ.prop (fun p ->
      PQ.lam PQ.bool (fun b ->
        PQ.lam (relation p b) (fun h ->
          let pos = fun hp ->
            PQ.is_true p
              (PQ.apps h (Cons (p, (Cons
                ((PQ.lam (PQ.arrow (PQ.eq PQ.bool b PQ.tru) p) (fun yes ->
                   PQ.lam
                     (PQ.arrow
                       (match false_eq with
                        | True -> PQ.eq PQ.bool b PQ.fal
                        | False -> PQ.not (PQ.eq PQ.bool b PQ.tru))
                       (PQ.not p))
                     (fun _ -> PQ.app yes hp))),
                Nil)))))
          in
          let neg = fun hn ->
            PQ.is_false p
              (PQ.apps h (Cons ((PQ.not p), (Cons
                ((PQ.lam (PQ.arrow (PQ.eq PQ.bool b PQ.tru) p) (fun _ ->
                   PQ.lam
                     (PQ.arrow
                       (match false_eq with
                        | True -> PQ.eq PQ.bool b PQ.fal
                        | False -> PQ.not (PQ.eq PQ.bool b PQ.tru))
                       (PQ.not p))
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
                    PQ.arrow (PQ.eq PQ.bool b b') (PQ.dec p))),
                 (Cons ((PQ.lam (PQ.eq PQ.bool b PQ.fal) neg), (Cons
                 ((PQ.lam (PQ.eq PQ.bool b PQ.tru) pos), (Cons (b,
                 Nil)))))))))
               (PQ.refl PQ.bool b)
           | False ->
             PQ.dite (PQ.dec p) (PQ.eq PQ.bool b PQ.tru) (PQ.bool_dec b) pos
               neg)))))) }

(** val primitive_reflection_ite : primitive_reflection -> expr **)

let primitive_reflection_ite r =
  PQ.run
    (PQ.lam PQ.prop (fun p ->
      PQ.lam PQ.bool (fun b ->
        PQ.lam
          (PQ.apps (PQ.embed r.reflection_type) (Cons (p, (Cons (b, Nil)))))
          (fun h ->
          PQ.lam PQ.type0 (fun a ->
            PQ.apps
              (PQ.const (Cons ((String ((Ascii (True, False, False, True,
                False, True, True, False)), (String ((Ascii (False, False,
                True, False, True, True, True, False)), (String ((Ascii
                (True, False, True, False, False, True, True, False)),
                EmptyString)))))), Nil)) (Cons ((LSucc LZero), Nil)))
              (Cons (a, (Cons (p, (Cons
              ((PQ.apps (PQ.embed r.reflection_dec) (Cons (p, (Cons (b, (Cons
                 (h, Nil))))))),
              Nil)))))))))))

(** val primitive_reflection_dite : primitive_reflection -> expr **)

let primitive_reflection_dite r =
  PQ.run
    (PQ.lam PQ.prop (fun p ->
      PQ.lam PQ.bool (fun b ->
        PQ.lam
          (PQ.apps (PQ.embed r.reflection_type) (Cons (p, (Cons (b, Nil)))))
          (fun h ->
          PQ.apps
            (PQ.const (Cons ((String ((Ascii (False, False, True, False,
              False, True, True, False)), (String ((Ascii (True, False,
              False, True, False, True, True, False)), (String ((Ascii
              (False, False, True, False, True, True, True, False)), (String
              ((Ascii (True, False, True, False, False, True, True, False)),
              EmptyString)))))))), Nil)) (Cons ((LSucc LZero), Nil)))
            (Cons (PQ.nat, (Cons (p, (Cons
            ((PQ.apps (PQ.embed r.reflection_dec) (Cons (p, (Cons (b, (Cons
               (h, Nil))))))),
            Nil))))))))))

(** val primitive_eq_closed :
    nat -> environment -> PQ.term -> PQ.term -> unit0 result **)

let primitive_eq_closed fuel env a b =
  check_defeq fuel env Nil empty_context (PQ.run a) (PQ.run b)

(** val primitive_check_closed :
    nat -> environment -> PQ.term -> PQ.term -> unit0 result **)

let primitive_check_closed fuel env a ty =
  check fuel env Nil empty_context (PQ.run a) (PQ.run ty)

(** val primitive_check_reflection :
    nat -> environment -> primitive_reflection -> bool -> bool -> unit0 result **)

let primitive_check_reflection fuel env r with_ite with_dite =
  let relation = fun p b ->
    PQ.apps (PQ.embed r.reflection_type) (Cons (p, (Cons (b, Nil))))
  in
  bind
    (primitive_check_closed fuel env (PQ.embed r.reflection_type)
      (PQ.arrow PQ.prop (PQ.arrow PQ.bool PQ.prop)))
    (fun _ ->
    bind
      (match with_ite with
       | True ->
         let it = PQ.embed (primitive_reflection_ite r) in
         bind
           (primitive_check_closed fuel env it
             (PQ.pi PQ.prop (fun p ->
               PQ.pi PQ.bool (fun b ->
                 PQ.arrow (relation p b)
                   (PQ.pi PQ.type0 (fun a -> PQ.arrow a (PQ.arrow a a)))))))
           (fun _ ->
           bind
             (primitive_eq_closed fuel env
               (PQ.lam PQ.prop (fun p ->
                 PQ.lam (relation p PQ.tru) (fun h ->
                   PQ.apps it (Cons (p, (Cons (PQ.tru, (Cons (h, Nil)))))))))
               (PQ.lam PQ.prop (fun p ->
                 PQ.lam (relation p PQ.tru) (fun _ ->
                   PQ.lam PQ.type0 (fun a ->
                     PQ.lam a (fun x -> PQ.lam a (fun _ -> x)))))))
             (fun _ ->
             primitive_eq_closed fuel env
               (PQ.lam PQ.prop (fun p ->
                 PQ.lam (relation p PQ.fal) (fun h ->
                   PQ.apps it (Cons (p, (Cons (PQ.fal, (Cons (h, Nil)))))))))
               (PQ.lam PQ.prop (fun p ->
                 PQ.lam (relation p PQ.fal) (fun _ ->
                   PQ.lam PQ.type0 (fun a ->
                     PQ.lam a (fun _ -> PQ.lam a (fun x -> x))))))))
       | False -> Accept Tt)
      (fun _ ->
      match with_dite with
      | True ->
        let di = PQ.embed (primitive_reflection_dite r) in
        bind
          (primitive_check_closed fuel env
            (PQ.const (Cons ((String ((Ascii (False, True, True, True, False,
              False, True, False)), (String ((Ascii (True, True, True, True,
              False, True, True, False)), (String ((Ascii (False, False,
              True, False, True, True, True, False)), EmptyString)))))),
              Nil)) Nil)
            (PQ.arrow PQ.prop PQ.prop))
          (fun _ ->
          bind
            (primitive_check_closed fuel env di
              (PQ.pi PQ.prop (fun p ->
                PQ.pi PQ.bool (fun b ->
                  PQ.arrow (relation p b)
                    (PQ.arrow (PQ.arrow p PQ.nat)
                      (PQ.arrow (PQ.arrow (PQ.not p) PQ.nat) PQ.nat))))))
            (fun _ ->
            bind
              (primitive_check_closed fuel env (PQ.embed r.reflection_true)
                (PQ.pi PQ.prop (fun p -> PQ.arrow (relation p PQ.tru) p)))
              (fun _ ->
              bind
                (primitive_check_closed fuel env
                  (PQ.embed r.reflection_false)
                  (PQ.pi PQ.prop (fun p ->
                    PQ.arrow (relation p PQ.fal) (PQ.not p))))
                (fun _ ->
                let lhs = fun b ->
                  PQ.lam PQ.prop (fun p ->
                    PQ.lam (PQ.arrow p PQ.nat) (fun yes ->
                      PQ.lam (PQ.arrow (PQ.not p) PQ.nat) (fun no ->
                        PQ.lam (relation p b) (fun h ->
                          PQ.apps di (Cons (p, (Cons (b, (Cons (h, (Cons
                            (yes, (Cons (no, Nil))))))))))))))
                in
                let rhs = fun b positive0 ->
                  PQ.lam PQ.prop (fun p ->
                    PQ.lam (PQ.arrow p PQ.nat) (fun yes ->
                      PQ.lam (PQ.arrow (PQ.not p) PQ.nat) (fun no ->
                        PQ.lam (relation p b) (fun h ->
                          PQ.app
                            (match positive0 with
                             | True -> yes
                             | False -> no)
                            (PQ.apps
                              (PQ.embed
                                (match positive0 with
                                 | True -> r.reflection_true
                                 | False -> r.reflection_false))
                              (Cons (p, (Cons (h, Nil)))))))))
                in
                bind
                  (primitive_eq_closed fuel env (lhs PQ.tru)
                    (rhs PQ.tru True))
                  (fun _ ->
                  primitive_eq_closed fuel env (lhs PQ.fal) (rhs PQ.fal False))))))
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

let primitive_condition_ite c a args t e =
  PQ.ite a (PQ.apps (PQ.embed (primitive_condition_prop c)) args)
    (PQ.apps (PQ.embed (primitive_condition_dec c)) args) t e

(** val primitive_condition_dite :
    primitive_condition -> PQ.term list -> (PQ.term -> PQ.term) -> (PQ.term
    -> PQ.term) -> PQ.term **)

let primitive_condition_dite c args t e =
  PQ.dite PQ.nat (PQ.apps (PQ.embed (primitive_condition_prop c)) args)
    (PQ.apps (PQ.embed (primitive_condition_dec c)) args) t e

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
    (PQ.lam PQ.nat (fun x ->
      PQ.lam PQ.nat (fun y ->
        let p =
          PQ.apps (PQ.embed (primitive_condition_prop c)) (Cons (x, (Cons (y,
            Nil))))
        in
        let b =
          PQ.call (match is_eq with
                   | True -> PNatBEq
                   | False -> PNatBLE)
            (Cons (x, (Cons (y, Nil))))
        in
        PQ.lam PQ.prop (fun q ->
          PQ.lam
            (PQ.arrow (PQ.arrow (PQ.eq PQ.bool b PQ.tru) p)
              (PQ.arrow
                (PQ.arrow
                  (match is_eq with
                   | True -> PQ.eq PQ.bool b PQ.fal
                   | False -> PQ.not (PQ.eq PQ.bool b PQ.tru))
                  (PQ.not p))
                q))
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
                 (Cons (x, (Cons (y, Nil))))),
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
                 (Cons (x, (Cons (y, Nil))))),
              Nil)))))))))

(** val primitive_check_condition :
    nat -> environment -> primitive_condition -> bool -> bool -> unit0 result **)

let primitive_check_condition fuel env c with_ite with_dite =
  bind (require (core_bool_ready env) MalformedDeclaration) (fun _ ->
    bind (infer fuel env Nil empty_context (primitive_condition_dec c))
      (fun _ ->
      match c with
      | PCBool ->
        bind
          (primitive_check_closed fuel env
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
                 (primitive_check_closed fuel env it
                   (PQ.arrow PQ.bool
                     (PQ.arrow PQ.nat (PQ.arrow PQ.nat PQ.nat))))
                 (fun _ ->
                 bind
                   (primitive_eq_closed fuel env (PQ.app it PQ.tru)
                     (PQ.lam PQ.nat (fun a -> PQ.lam PQ.nat (fun _ -> a))))
                   (fun _ ->
                   primitive_eq_closed fuel env (PQ.app it PQ.fal)
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
        bind (primitive_authenticated fuel env op) (fun _ ->
          let r = primitive_reflection_make is_eq in
          bind (primitive_check_reflection fuel env r with_ite with_dite)
            (fun _ ->
            let gadget =
              PQ.lam PQ.nat (fun x ->
                PQ.lam PQ.nat (fun y ->
                  PQ.apps
                    (PQ.lam PQ.prop (fun p ->
                      PQ.lam PQ.bool (fun b ->
                        PQ.lam
                          (PQ.apps (PQ.embed r.reflection_type) (Cons (p,
                            (Cons (b, Nil)))))
                          (fun h ->
                          PQ.apps (PQ.embed r.reflection_dec) (Cons (p, (Cons
                            (b, (Cons (h, Nil))))))))))
                    (Cons
                    ((PQ.apps (PQ.embed (primitive_condition_prop c)) (Cons
                       (x, (Cons (y, Nil))))),
                    (Cons ((PQ.call op (Cons (x, (Cons (y, Nil))))), (Cons
                    ((PQ.apps (PQ.embed (primitive_condition_proof c)) (Cons
                       (x, (Cons (y, Nil))))),
                    Nil))))))))
            in
            primitive_eq_closed fuel env gadget
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

let primitive_le x y =
  PQ.apps (PQ.embed (primitive_condition_prop PCNatLE)) (Cons (x, (Cons (y,
    Nil))))

(** val primitive_go_type : expr **)

let primitive_go_type =
  PQ.run
    (PQ.pi PQ.nat (fun y ->
      PQ.arrow (primitive_le PQ.one y)
        (PQ.pi PQ.nat (fun fuel ->
          PQ.pi PQ.nat (fun x ->
            PQ.arrow (primitive_le (PQ.succ x) fuel) PQ.nat)))))

(** val primitive_fuel_top : bool -> expr **)

let primitive_fuel_top modulo0 =
  let go = PQ.embed (EConst ((primitive_go_name modulo0), Nil)) in
  PQ.run
    (PQ.lam PQ.nat (fun x ->
      PQ.lam PQ.nat (fun y ->
        let n0 = match modulo0 with
                 | True -> PQ.succ x
                 | False -> x in
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
    (PQ.lam PQ.nat (fun x ->
      PQ.lam PQ.nat (fun y ->
        PQ.lam (primitive_le PQ.one y) (fun hy ->
          PQ.lam PQ.nat (fun t ->
            PQ.lam (primitive_le (PQ.succ x) (PQ.succ t)) (fun h ->
              match rhs with
              | True ->
                primitive_condition_dite PCNatLE (Cons (y, (Cons (x, Nil))))
                  (fun hle ->
                  let rec0 =
                    PQ.apps go (Cons (y, (Cons (hy, (Cons (t, (Cons
                      ((PQ.call PNatSub (Cons (x, (Cons (y, Nil))))), (Cons
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
                         (Cons (x, (Cons (y, (Cons (t, (Cons (hy, (Cons (hle,
                         (Cons (h, Nil))))))))))))),
                      Nil))))))))))
                  in
                  (match modulo0 with
                   | True -> rec0
                   | False -> PQ.succ rec0))
                  (fun _ -> match modulo0 with
                            | True -> x
                            | False -> PQ.zero)
              | False ->
                PQ.apps go (Cons (y, (Cons (hy, (Cons ((PQ.succ t), (Cons (x,
                  (Cons (h, Nil))))))))))))))))

(** val primitive_check_fuel_rec :
    nat -> environment -> bool -> expr -> unit0 result **)

let primitive_check_fuel_rec fuel env modulo0 body =
  bind
    (require
      (match core_nat_ready env with
       | True -> core_bool_ready env
       | False -> False)
      MalformedDeclaration)
    (fun _ ->
    bind (primitive_authenticated fuel env PNatSub) (fun _ ->
      bind
        (primitive_check_closed fuel env
          (PQ.embed (primitive_condition_prop PCNatLE))
          (PQ.arrow PQ.nat (PQ.arrow PQ.nat PQ.prop)))
        (fun _ ->
        bind
          (check fuel env Nil empty_context (EConst
            ((primitive_go_name modulo0), Nil)) primitive_go_type)
          (fun _ ->
          bind (primitive_check_condition fuel env PCNatLE modulo0 True)
            (fun _ ->
            bind
              (match modulo0 with
               | True ->
                 primitive_eq_closed fuel env
                   (PQ.lam PQ.nat (fun x ->
                     PQ.apps (PQ.embed body) (Cons (PQ.zero, (Cons (x, Nil))))))
                   (PQ.lam PQ.nat (fun _ -> PQ.zero))
               | False -> Accept Tt)
              (fun _ ->
              bind
                (primitive_eq_closed fuel env
                  (PQ.lam PQ.nat (fun x ->
                    PQ.lam PQ.nat (fun y ->
                      PQ.apps (PQ.embed body) (Cons
                        ((match modulo0 with
                          | True -> PQ.succ x
                          | False -> x),
                        (Cons (y, Nil)))))))
                  (PQ.embed (primitive_fuel_top modulo0)))
                (fun _ ->
                check_defeq fuel env Nil empty_context
                  (primitive_fuel_step modulo0 False)
                  (primitive_fuel_step modulo0 True))))))))

(** val primitive_whnf_core :
    nat -> environment -> context -> expr -> expr result **)

let primitive_whnf_core fuel env g e =
  (checker fuel env Nil).whnf_core_method False g e

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

let rec primitive_lambda_telescope depth fuel env s e =
  match depth with
  | O -> Decline OutOfFuel
  | S depth0 ->
    (match e with
     | ELam (n0, bi, ty, b) ->
       bind (sort_of (checker fuel env Nil) s.ist_context ty) (fun _ ->
         let Pair (x, s0) = ind_fresh s n0 bi ty in
         bind
           (primitive_lambda_telescope depth0 fuel env s0
             (instantiate b (local_expr x)))
           (fun rest ->
           let Pair (p, s1) = rest in
           let Pair (xs, b0) = p in
           Accept (Pair ((Pair ((Cons (x, xs)), b0)), s1))))
     | EMData e0 -> primitive_lambda_telescope depth0 fuel env s e0
     | _ -> Accept (Pair ((Pair (Nil, e)), s)))

(** val primitive_no_free : nat -> name -> expr -> unit0 result **)

let rec primitive_no_free fuel n0 e =
  match fuel with
  | O -> Decline OutOfFuel
  | S fuel0 ->
    (match e with
     | EFVar m -> require (negb (name_eqb n0 m)) MalformedDeclaration
     | EApp (a, b) ->
       bind (primitive_no_free fuel0 n0 a) (fun _ ->
         primitive_no_free fuel0 n0 b)
     | ELam (_, _, a, b) ->
       bind (primitive_no_free fuel0 n0 a) (fun _ ->
         primitive_no_free fuel0 n0 b)
     | EPi (_, _, a, b) ->
       bind (primitive_no_free fuel0 n0 a) (fun _ ->
         primitive_no_free fuel0 n0 b)
     | ELet (_, a, v0, b, _) ->
       bind (primitive_no_free fuel0 n0 a) (fun _ ->
         bind (primitive_no_free fuel0 n0 v0) (fun _ ->
           primitive_no_free fuel0 n0 b))
     | EProj (_, _, a) -> primitive_no_free fuel0 n0 a
     | EMData a -> primitive_no_free fuel0 n0 a
     | _ -> Accept Tt)

(** val primitive_proof :
    nat -> environment -> context -> expr -> unit0 result **)

let primitive_proof fuel env g e =
  bind (infer fuel env Nil g e) (fun ty ->
    bind (sort_of (checker fuel env Nil) g ty) (fun u0 ->
      bind (level_equiv fuel u0 LZero) (fun is_prop ->
        require is_prop TypeMismatch)))

type primitive_probe = { probe_pack : expr; probe_dom : expr;
                         probe_functional : expr }

(** val primitive_check_go :
    nat -> environment -> ind_state -> expr -> unit0 result **)

let primitive_check_go fuel env s go =
  bind (primitive_unfold env go) (fun value ->
    bind (primitive_lambda_telescope fuel fuel env s value) (fun opened ->
      let Pair (p, st) = opened in
      let Pair (xs, b) = p in
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
                   | Cons (t, l3) ->
                     (match l3 with
                      | Nil ->
                        (match b with
                         | EApp (nat_rec, t') ->
                           bind
                             (require (expr_eqb t' (local_expr t))
                               NotDefinitionallyEqual)
                             (fun _ ->
                             bind (primitive_no_free fuel t.il_id nat_rec)
                               (fun _ ->
                               bind
                                 (infer fuel env Nil st.ist_context
                                   (primitive_succ (local_expr t)))
                                 (fun _ ->
                                 let next = EApp (nat_rec,
                                   (primitive_succ (local_expr t)))
                                 in
                                 bind
                                   (infer fuel env Nil st.ist_context next)
                                   (fun _ ->
                                   bind
                                     (primitive_whnf_core fuel env
                                       st.ist_context next)
                                     (fun next0 ->
                                     bind
                                       (primitive_lambda_telescope fuel fuel
                                         env st next0)
                                       (fun opened0 ->
                                       let Pair (p0, st0) = opened0 in
                                       let Pair (ys, b0) = p0 in
                                       (match ys with
                                        | Nil ->
                                          Decline UnsupportedDeclaration
                                        | Cons (x, l4) ->
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
                                                         (local_expr x))))
                                                       NotDefinitionallyEqual)
                                                     (fun _ ->
                                                     bind
                                                       (primitive_lambda_telescope
                                                         fuel fuel env st0 ih)
                                                       (fun opened1 ->
                                                       let Pair (p1, st1) =
                                                         opened1
                                                       in
                                                       let Pair (zs, b1) = p1
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
                                                                    fuel env
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
                                                                    t), (Cons
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

let primitive_unfold_nat_well_founded fuel env s e measure =
  bind (primitive_lambda_telescope fuel fuel env s measure) (fun opened ->
    let Pair (p, st) = opened in
    let Pair (locals, measure_body) = p in
    let applied = apply_locals e locals in
    bind (infer fuel env Nil st.ist_context applied) (fun _ ->
      bind (primitive_whnf_core fuel env st.ist_context applied) (fun top ->
        bind (primitive_unfold env top) (fun top0 ->
          bind (primitive_whnf_core fuel env st.ist_context top0)
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
                                              (infer fuel env Nil
                                                st.ist_context packed)
                                              (fun ty ->
                                              let Pair (a, sa) =
                                                ind_fresh st NameAnon
                                                  BDefault ty
                                              in
                                              let av = local_expr a in
                                              bind
                                                (check fuel env Nil
                                                  sa.ist_context (EApp (meas,
                                                  av)) core_nat)
                                                (fun _ ->
                                                bind
                                                  (check_defeq fuel env Nil
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
                                                        fuel env
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
                                                                    fuel env
                                                                    sa.ist_context
                                                                    pf)
                                                                    (fun _ ->
                                                                    match fuel_expr with
                                                                    | EApp (
                                                                    eager, n0) ->
                                                                    bind
                                                                    (check_defeq
                                                                    fuel env
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
                                                                    fuel env
                                                                    PNatBEq)
                                                                    (fun _ ->
                                                                    let Pair (
                                                                    x, sx) =
                                                                    ind_fresh
                                                                    sa
                                                                    NameAnon
                                                                    BDefault
                                                                    core_nat
                                                                    in
                                                                    let xv =
                                                                    PQ.embed
                                                                    (local_expr
                                                                    x)
                                                                    in
                                                                    bind
                                                                    (check_defeq
                                                                    fuel env
                                                                    Nil
                                                                    sx.ist_context
                                                                    (EApp
                                                                    (eager,
                                                                    (local_expr
                                                                    x)))
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
                                                                    fuel env
                                                                    s go)
                                                                    (fun _ ->
                                                                    bind
                                                                    (infer
                                                                    fuel env
                                                                    Nil
                                                                    s.ist_context
                                                                    functional)
                                                                    (fun fty ->
                                                                    bind
                                                                    (whnf
                                                                    fuel env
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
                                                                    fuel env
                                                                    Nil
                                                                    st.ist_context
                                                                    ty domain)
                                                                    (fun _ ->
                                                                    let Pair (
                                                                    z, sz) =
                                                                    ind_fresh
                                                                    s
                                                                    NameAnon
                                                                    BDefault
                                                                    domain
                                                                    in
                                                                    bind
                                                                    (whnf
                                                                    fuel env
                                                                    Nil
                                                                    sz.ist_context
                                                                    (instantiate
                                                                    cod
                                                                    (local_expr
                                                                    z)))
                                                                    (fun cod0 ->
                                                                    match cod0 with
                                                                    | EPi (
                                                                    _, _,
                                                                    ih_domain,
                                                                    _) ->
                                                                    let dom =
                                                                    close_lam
                                                                    (Cons (z,
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
                                                                    fuel env
                                                                    Nil
                                                                    s.ist_context
                                                                    pack)
                                                                    (fun _ ->
                                                                    bind
                                                                    (infer
                                                                    fuel env
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

let primitive_run_probe fuel env s p args rhs =
  let a = core_apps p.probe_pack args in
  let Pair (ih, si) = ind_fresh s NameAnon BDefault (EApp (p.probe_dom, a)) in
  check_defeq fuel env Nil si.ist_context
    (core_apps p.probe_functional (Cons (a, (Cons ((local_expr ih), Nil)))))
    (rhs (local_expr ih))

(** val primitive_first_measure : expr **)

let primitive_first_measure =
  PQ.run (PQ.lam PQ.nat (fun m -> PQ.lam PQ.nat (fun _ -> m)))

(** val primitive_check_gcd : nat -> environment -> expr -> unit0 result **)

let primitive_check_gcd fuel env body =
  bind
    (require
      (match core_nat_ready env with
       | True -> core_bool_ready env
       | False -> False)
      MalformedDeclaration)
    (fun _ ->
    bind (primitive_authenticated fuel env PNatMod) (fun _ ->
      bind (primitive_check_condition fuel env PCBool True False) (fun _ ->
        bind
          (primitive_unfold_nat_well_founded fuel env initial_ind_state body
            primitive_first_measure)
          (fun p ->
          let Pair (n0, sn) =
            ind_fresh initial_ind_state NameAnon BDefault core_nat
          in
          bind
            (primitive_run_probe fuel env sn p (Cons (primitive_zero, (Cons
              ((local_expr n0), Nil)))) (fun _ -> local_expr n0))
            (fun _ ->
            let Pair (m, sm) = ind_fresh sn NameAnon BDefault core_nat in
            primitive_run_probe fuel env sm p (Cons
              ((primitive_succ (local_expr m)), (Cons ((local_expr n0),
              Nil)))) (fun ih ->
              let mm = PQ.embed (local_expr m) in
              let nn = PQ.embed (local_expr n0) in
              PQ.run
                (PQ.apps (PQ.embed ih) (Cons
                  ((PQ.apps (PQ.embed p.probe_pack) (Cons
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

let primitive_check_bitwise fuel env body =
  bind
    (require
      (match core_nat_ready env with
       | True -> core_bool_ready env
       | False -> False)
      MalformedDeclaration)
    (fun _ ->
    bind (primitive_authenticated fuel env PNatAdd) (fun _ ->
      bind (primitive_authenticated fuel env PNatDiv) (fun _ ->
        bind (primitive_authenticated fuel env PNatMod) (fun _ ->
          bind (primitive_check_condition fuel env PCNatEq True True)
            (fun _ ->
            bind (primitive_check_condition fuel env PCBool True False)
              (fun _ ->
              let Pair (f, sf) =
                ind_fresh initial_ind_state NameAnon BDefault
                  primitive_bool_operator_type
              in
              bind
                (primitive_unfold_nat_well_founded fuel env sf (EApp (body,
                  (local_expr f))) primitive_first_measure)
                (fun p ->
                let Pair (n0, sn) = ind_fresh sf NameAnon BDefault core_nat in
                let Pair (m, sm) = ind_fresh sn NameAnon BDefault core_nat in
                primitive_run_probe fuel env sm p (Cons ((local_expr n0),
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
                             ((PQ.apps (PQ.embed p.probe_pack) (Cons (n',
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

let primitive_check_boolean_operator fuel env op operator =
  bind
    (check fuel env Nil empty_context operator primitive_bool_operator_type)
    (fun _ ->
    let f = PQ.embed operator in
    let fx = fun b ->
      PQ.lam PQ.bool (fun x -> PQ.apps f (Cons (b, (Cons (x, Nil)))))
    in
    (match op with
     | PNatLAnd ->
       bind
         (primitive_eq_closed fuel env (fx PQ.fal)
           (PQ.lam PQ.bool (fun _ -> PQ.fal)))
         (fun _ ->
         primitive_eq_closed fuel env (fx PQ.tru)
           (PQ.lam PQ.bool (fun x -> x)))
     | PNatLOr ->
       bind
         (primitive_eq_closed fuel env (fx PQ.fal)
           (PQ.lam PQ.bool (fun x -> x)))
         (fun _ ->
         primitive_eq_closed fuel env (fx PQ.tru)
           (PQ.lam PQ.bool (fun _ -> PQ.tru)))
     | PNatXor ->
       bind
         (primitive_eq_closed fuel env
           (PQ.apps f (Cons (PQ.fal, (Cons (PQ.fal, Nil))))) PQ.fal)
         (fun _ ->
         bind
           (primitive_eq_closed fuel env
             (PQ.apps f (Cons (PQ.tru, (Cons (PQ.fal, Nil))))) PQ.tru)
           (fun _ ->
           bind
             (primitive_eq_closed fuel env
               (PQ.apps f (Cons (PQ.fal, (Cons (PQ.tru, Nil))))) PQ.tru)
             (fun _ ->
             primitive_eq_closed fuel env
               (PQ.apps f (Cons (PQ.tru, (Cons (PQ.tru, Nil))))) PQ.fal)))
     | _ -> Decline UnsupportedDeclaration))

(** val primitive_check_bitwise_instance :
    nat -> environment -> primitive_kind -> expr -> unit0 result **)

let primitive_check_bitwise_instance fuel env op body =
  bind (primitive_authenticated fuel env PNatBitwise) (fun _ ->
    match body with
    | EApp (e, operator) ->
      (match e with
       | EConst (n0, l) ->
         (match l with
          | Nil ->
            bind
              (require (name_eqb n0 primitive_bitwise_name)
                MalformedDeclaration)
              (fun _ -> primitive_check_boolean_operator fuel env op operator)
          | Cons (_, _) -> Decline UnsupportedDeclaration)
       | _ -> Decline UnsupportedDeclaration)
    | _ -> Decline UnsupportedDeclaration)

(** val primitive_is_text : primitive_kind -> bool **)

let primitive_is_text = function
| PCharOfNat -> True
| PStringOfList -> True
| _ -> False

(** val primitive_ensure_type : nat -> environment -> expr -> unit0 result **)

let primitive_ensure_type fuel env e =
  bind (sort_of (checker fuel env Nil) empty_context e) (fun _ -> Accept Tt)

(** val primitive_check_text_interface :
    nat -> environment -> primitive_kind -> unit0 result **)

let primitive_check_text_interface fuel env = function
| PCharOfNat ->
  bind (require (core_nat_ready env) MalformedDeclaration) (fun _ ->
    primitive_ensure_type fuel env primitive_char)
| PStringOfList ->
  bind (primitive_ensure_type fuel env primitive_list_char) (fun _ ->
    bind (primitive_ensure_type fuel env primitive_char) (fun _ ->
      bind
        (check fuel env Nil empty_context (EApp ((EConst ((NameStr
          (core_list_name, (String ((Ascii (False, True, True, True, False,
          True, True, False)), (String ((Ascii (True, False, False, True,
          False, True, True, False)), (String ((Ascii (False, False, True,
          True, False, True, True, False)), EmptyString)))))))), (Cons
          (LZero, Nil)))), primitive_char)) primitive_list_char)
        (fun _ ->
        check fuel env Nil empty_context (EApp ((EConst ((NameStr
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

let primitive_check_nat_equations fuel env op body =
  match primitive_equations op body with
  | Some equations ->
    bind (primitive_dependencies fuel env op) (fun _ ->
      primitive_check_equations fuel fuel env equations)
  | None ->
    (match op with
     | PNatGcd -> primitive_check_gcd fuel env body
     | PNatMod -> primitive_check_fuel_rec fuel env True body
     | PNatDiv -> primitive_check_fuel_rec fuel env False body
     | PNatLAnd -> primitive_check_bitwise_instance fuel env op body
     | PNatLOr -> primitive_check_bitwise_instance fuel env op body
     | PNatXor -> primitive_check_bitwise_instance fuel env op body
     | PNatBitwise -> primitive_check_bitwise fuel env body
     | _ -> Decline UnsupportedDeclaration)

(** val classify_primitive :
    nat -> environment -> name -> name list -> expr -> expr -> primitive_kind
    option result **)

let classify_primitive fuel env n0 params ty body =
  match primitive_lookup n0 with
  | Some op ->
    bind
      (match find_decl n0 env with
       | Some _ -> Reject DuplicateDeclaration
       | None -> Accept Tt)
      (fun _ ->
      bind (require (Nat.eqb (length params) O) UniverseArity) (fun _ ->
        bind (primitive_check_signature fuel ty (primitive_signature op))
          (fun _ ->
          bind (primitive_closed fuel O body) (fun _ ->
            bind
              (match primitive_is_text op with
               | True -> primitive_check_text_interface fuel env op
               | False -> primitive_check_nat_equations fuel env op body)
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

let check_header fuel env n0 ps ty =
  match find_decl n0 env with
  | Some _ -> Reject DuplicateDeclaration
  | None ->
    (match negb (names_unique ps) with
     | True -> Reject DuplicateUniverse
     | False ->
       (match negb (scoped O ty) with
        | True -> Reject MalformedDeclaration
        | False ->
          bind (infer fuel env ps empty_context ty) (fun inferred ->
            bind (whnf fuel env ps empty_context inferred) (fun reduced ->
              match reduced with
              | ESort _ -> Accept Tt
              | _ -> Reject ExpectedSort))))

(** val check_proposition :
    nat -> environment -> name list -> expr -> unit0 result **)

let check_proposition fuel env ps ty =
  bind (infer fuel env ps empty_context ty) (fun inferred ->
    bind (whnf fuel env ps empty_context inferred) (fun reduced ->
      match reduced with
      | ESort u0 ->
        bind (level_equiv fuel u0 LZero) (fun is_zero ->
          match is_zero with
          | True -> Accept Tt
          | False -> Reject MalformedDeclaration)
      | _ -> Reject ExpectedSort))

(** val checked_constant :
    nat -> environment -> name -> name list -> expr -> expr option ->
    decl_kind -> environment result **)

let checked_constant fuel env n0 ps ty body kind =
  bind (check_header fuel env n0 ps ty) (fun _ ->
    bind
      (match body with
       | Some value ->
         (match scoped O value with
          | True -> check fuel env ps empty_context value ty
          | False -> Reject MalformedDeclaration)
       | None -> Accept Tt)
      (fun _ -> Accept (Cons ({ decl_name = n0; decl_params = ps; decl_type =
      ty; decl_value = body; decl_kind_of = kind; decl_hints = HintOpaque },
      env))))

(** val admit : nat -> environment -> input_decl -> environment result **)

let admit fuel env = function
| InputAxiom (n0, ps, ty, unsafe) ->
  (match unsafe with
   | True -> Decline UnsupportedDeclaration
   | False ->
     (match name_mem n0 reserved_names with
      | True -> Reject MalformedDeclaration
      | False -> checked_constant fuel env n0 ps ty None DAssumption))
| InputDefinition (hints, n0, ps, ty, body, i) ->
  (match i with
   | InputSafe ->
     bind (check_header fuel env n0 ps ty) (fun _ ->
       bind (require (scoped O body) MalformedDeclaration) (fun _ ->
         bind (check fuel env ps empty_context body ty) (fun _ ->
           bind (classify_primitive fuel env n0 ps ty body) (fun primitive ->
             let kind =
               match primitive with
               | Some p -> DPrimitive p
               | None -> DDefinition
             in
             Accept (Cons ({ decl_name = n0; decl_params = ps; decl_type =
             ty; decl_value = (Some body); decl_kind_of = kind; decl_hints =
             hints }, env))))))
   | _ -> Decline UnsupportedDeclaration)
| InputTheorem (n0, ps, ty, body) ->
  (match name_mem n0 reserved_names with
   | True -> Reject MalformedDeclaration
   | False ->
     bind (check_header fuel env n0 ps ty) (fun _ ->
       bind (check_proposition fuel env ps ty) (fun _ ->
         checked_constant fuel env n0 ps ty (Some body) DTheorem)))
| InputOpaque (n0, ps, ty, body, unsafe) ->
  (match unsafe with
   | True -> Decline UnsupportedDeclaration
   | False ->
     (match name_mem n0 reserved_names with
      | True -> Reject MalformedDeclaration
      | False -> checked_constant fuel env n0 ps ty (Some body) DOpaque))
| InputUnsupported -> Decline UnsupportedDeclaration

(** val check_declarations :
    nat -> environment -> input_decl list -> environment result **)

let rec check_declarations fuel env = function
| Nil -> Accept env
| Cons (d, ds0) ->
  bind (admit fuel env d) (fun next -> check_declarations fuel next ds0)

(** val nm : string -> name **)

let nm s =
  NameStr (NameAnon, s)

(** val u : level **)

let u =
  LParam
    (nm (String ((Ascii (True, False, True, False, True, True, True, False)),
      EmptyString)))

(** val v : level **)

let v =
  LParam
    (nm (String ((Ascii (False, True, True, False, True, True, True, False)),
      EmptyString)))

(** val w : level **)

let w =
  LParam
    (nm (String ((Ascii (True, True, True, False, True, True, True, False)),
      EmptyString)))

(** val one0 : level **)

let one0 =
  LSucc LZero

(** val two0 : level **)

let two0 =
  LSucc one0

(** val prop0 : expr **)

let prop0 =
  ESort LZero

(** val type1 : expr **)

let type1 =
  ESort one0

(** val type2 : expr **)

let type2 =
  ESort two0

(** val id_type : expr **)

let id_type =
  EPi
    ((nm (String ((Ascii (True, False, False, False, False, False, True,
       False)), EmptyString))),
    BDefault, type1, (EPi
    ((nm (String ((Ascii (False, False, False, True, True, True, True,
       False)), EmptyString))),
    BDefault, (EBVar O), (EBVar (S O)))))

(** val id_term : expr **)

let id_term =
  ELam
    ((nm (String ((Ascii (True, False, False, False, False, False, True,
       False)), EmptyString))),
    BDefault, type1, (ELam
    ((nm (String ((Ascii (False, False, False, True, True, True, True,
       False)), EmptyString))),
    BDefault, (EBVar O), (EBVar O))))

(** val prop_id_type : expr **)

let prop_id_type =
  EPi
    ((nm (String ((Ascii (False, False, False, False, True, False, True,
       False)), EmptyString))),
    BDefault, prop0, (EPi
    ((nm (String ((Ascii (False, False, False, True, False, True, True,
       False)), EmptyString))),
    BDefault, (EBVar O), (EBVar (S O)))))

(** val prop_id : expr **)

let prop_id =
  ELam
    ((nm (String ((Ascii (False, False, False, False, True, False, True,
       False)), EmptyString))),
    BDefault, prop0, (ELam
    ((nm (String ((Ascii (False, False, False, True, False, True, True,
       False)), EmptyString))),
    BDefault, (EBVar O), (EBVar O))))

(** val proof_context : context **)

let proof_context =
  { bound_context = Nil; free_context = (Cons ((Pair
    ((nm (String ((Ascii (False, False, False, False, True, True, True,
       False)), EmptyString))),
    { binding_type = (EFVar
    (nm (String ((Ascii (False, False, False, False, True, False, True,
      False)), EmptyString))));
    binding_value = None })), (Cons ((Pair
    ((nm (String ((Ascii (True, False, False, False, True, True, True,
       False)), EmptyString))),
    { binding_type = (EFVar
    (nm (String ((Ascii (False, False, False, False, True, False, True,
      False)), EmptyString))));
    binding_value = None })), (Cons ((Pair
    ((nm (String ((Ascii (False, True, False, False, True, True, True,
       False)), EmptyString))),
    { binding_type = (EFVar
    (nm (String ((Ascii (True, False, False, False, True, False, True,
      False)), EmptyString))));
    binding_value = None })), (Cons ((Pair
    ((nm (String ((Ascii (False, False, False, False, True, False, True,
       False)), EmptyString))),
    { binding_type = prop0; binding_value = None })), (Cons ((Pair
    ((nm (String ((Ascii (True, False, False, False, True, False, True,
       False)), EmptyString))),
    { binding_type = prop0; binding_value = None })), Nil)))))))))) }

(** val function_context : context **)

let function_context =
  { bound_context = Nil; free_context = (Cons ((Pair
    ((nm (String ((Ascii (False, True, True, False, False, True, True,
       False)), EmptyString))),
    { binding_type = (EPi
    ((nm (String ((Ascii (False, False, False, True, True, True, True,
       False)), EmptyString))),
    BDefault, type1, type1)); binding_value = None })), Nil)) }

(** val eta_f : expr **)

let eta_f =
  ELam
    ((nm (String ((Ascii (False, False, False, True, True, True, True,
       False)), EmptyString))),
    BDefault, type1, (EApp ((EFVar
    (nm (String ((Ascii (False, True, True, False, False, True, True,
      False)), EmptyString)))),
    (EBVar O))))

(** val id_decl : decl_kind -> declaration **)

let id_decl kind =
  { decl_name =
    (nm (String ((Ascii (False, False, False, False, True, True, True,
      False)), (String ((Ascii (False, True, False, False, True, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (True, True, True, True, False, True, True,
      False)), (String ((Ascii (False, True, True, False, False, True, True,
      False)), (String ((Ascii (True, True, True, True, True, False, True,
      False)), (String ((Ascii (True, False, False, True, False, True, True,
      False)), (String ((Ascii (False, False, True, False, False, True, True,
      False)), EmptyString)))))))))))))))));
    decl_params = Nil; decl_type = prop_id_type; decl_value = (Some prop_id);
    decl_kind_of = kind; decl_hints = HintOpaque }

(** val level_decl : declaration **)

let level_decl =
  { decl_name =
    (nm (String ((Ascii (True, True, False, False, True, True, True, False)),
      (String ((Ascii (True, True, True, True, False, True, True, False)),
      (String ((Ascii (False, True, False, False, True, True, True, False)),
      (String ((Ascii (False, False, True, False, True, True, True, False)),
      EmptyString)))))))));
    decl_params = (Cons
    ((nm (String ((Ascii (True, False, True, False, True, True, True,
       False)), EmptyString))),
    Nil)); decl_type = (ESort (LSucc u)); decl_value = (Some (ESort u));
    decl_kind_of = DDefinition; decl_hints = HintOpaque }

(** val cyclic_decl : declaration **)

let cyclic_decl =
  { decl_name =
    (nm (String ((Ascii (True, True, False, False, False, True, True,
      False)), (String ((Ascii (True, False, False, True, True, True, True,
      False)), (String ((Ascii (True, True, False, False, False, True, True,
      False)), (String ((Ascii (False, False, True, True, False, True, True,
      False)), (String ((Ascii (True, False, True, False, False, True, True,
      False)), EmptyString)))))))))));
    decl_params = Nil; decl_type = prop0; decl_value = (Some (EConst
    ((nm (String ((Ascii (True, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, True, True, True, True,
       False)), (String ((Ascii (True, True, False, False, False, True, True,
       False)), (String ((Ascii (False, False, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, False, True, True,
       False)), EmptyString))))))))))),
    Nil))); decl_kind_of = DDefinition; decl_hints = HintOpaque }

(** val accepted : 'a1 result -> bool **)

let accepted = function
| Accept _ -> True
| _ -> False

(** val rejected : 'a1 result -> bool **)

let rejected = function
| Reject _ -> True
| _ -> False

(** val declined : 'a1 result -> bool **)

let declined = function
| Decline _ -> True
| _ -> False

(** val decided_true : bool result -> bool **)

let decided_true = function
| Accept b -> b
| _ -> False

(** val regression_checks : unit0 -> bool list **)

let regression_checks _ =
  Cons
    ((decided_true
       (level_equiv (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))) (LIMax (u, (LMax (v, w)))) (LMax
         ((LIMax (u, v)), (LIMax (u, w)))))),
    (Cons
    ((decided_true
       (level_le (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))) (LIMax (two0, u)) (LMax (two0, u)))),
    (Cons
    ((negb
       (decided_true
         (level_equiv (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O)))))))))))))))))))))))))))))))) (LIMax (two0, u)) (LMax (two0,
           u))))),
    (Cons
    ((accepted
       (check (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         Nil Nil empty_context id_term id_type)),
    (Cons
    ((accepted
       (check (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         Nil Nil empty_context prop_id prop_id_type)),
    (Cons
    ((rejected
       (check (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
         Nil Nil empty_context prop0 type2)),
    (Cons
    ((rejected
       (infer (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
         Nil Nil empty_context (EApp (prop0, prop0)))),
    (Cons
    ((rejected
       (infer (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
         Nil Nil empty_context (EApp (id_term, type1)))),
    (Cons
    ((accepted
       (check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         Nil Nil proof_context (EFVar
         (nm (String ((Ascii (False, False, False, False, True, True, True,
           False)), EmptyString))))
         (EFVar
         (nm (String ((Ascii (True, False, False, False, True, True, True,
           False)), EmptyString)))))),
    (Cons
    ((negb
       (decided_true
         (defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           Nil Nil proof_context (EFVar
           (nm (String ((Ascii (False, False, False, False, True, True, True,
             False)), EmptyString))))
           (EFVar
           (nm (String ((Ascii (False, True, False, False, True, True, True,
             False)), EmptyString))))))),
    (Cons
    ((accepted
       (check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         Nil Nil function_context eta_f (EFVar
         (nm (String ((Ascii (False, True, True, False, False, True, True,
           False)), EmptyString)))))),
    (Cons
    ((accepted
       (check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         Nil Nil function_context (EFVar
         (nm (String ((Ascii (False, True, True, False, False, True, True,
           False)), EmptyString))))
         eta_f)),
    (Cons
    ((declined
       (whnf (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
         (Cons (cyclic_decl, Nil)) Nil empty_context (EConst
         ((nm (String ((Ascii (True, True, False, False, False, True, True,
            False)), (String ((Ascii (True, False, False, True, True, True,
            True, False)), (String ((Ascii (True, True, False, False, False,
            True, True, False)), (String ((Ascii (False, False, True, True,
            False, True, True, False)), (String ((Ascii (True, False, True,
            False, False, True, True, False)), EmptyString))))))))))),
         Nil)))),
    (Cons
    ((declined
       (infer (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
         Nil Nil empty_context (ELit (LitNat (Npos (XO (XO (XO (XO (XO (XO
         (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
         (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
         (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
         (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
         (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XO (XI (XI (XI (XI (XO (XO
         (XI (XO (XO (XO (XI (XO (XO (XI (XO (XO (XO (XO (XO (XI (XI (XO (XO
         (XO (XI (XO (XO (XI (XI (XI (XO (XO (XO (XI (XI (XO (XI (XO (XI (XO
         (XO (XO
         XH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons
    ((match whnf (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))) (Cons ((id_decl DTheorem),
              Nil)) Nil empty_context (EConst
              ((nm (String ((Ascii (False, False, False, False, True, True,
                 True, False)), (String ((Ascii (False, True, False, False,
                 True, True, True, False)), (String ((Ascii (True, True,
                 True, True, False, True, True, False)), (String ((Ascii
                 (True, True, True, True, False, True, True, False)), (String
                 ((Ascii (False, True, True, False, False, True, True,
                 False)), (String ((Ascii (True, True, True, True, True,
                 False, True, False)), (String ((Ascii (True, False, False,
                 True, False, True, True, False)), (String ((Ascii (False,
                 False, True, False, False, True, True, False)),
                 EmptyString))))))))))))))))),
              Nil)) with
      | Accept e -> expr_eqb e prop_id
      | _ -> False),
    (Cons
    ((match whnf (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))) (Cons ((id_decl DOpaque),
              Nil)) Nil empty_context (EConst
              ((nm (String ((Ascii (False, False, False, False, True, True,
                 True, False)), (String ((Ascii (False, True, False, False,
                 True, True, True, False)), (String ((Ascii (True, True,
                 True, True, False, True, True, False)), (String ((Ascii
                 (True, True, True, True, False, True, True, False)), (String
                 ((Ascii (False, True, True, False, False, True, True,
                 False)), (String ((Ascii (True, True, True, True, True,
                 False, True, False)), (String ((Ascii (True, False, False,
                 True, False, True, True, False)), (String ((Ascii (False,
                 False, True, False, False, True, True, False)),
                 EmptyString))))))))))))))))),
              Nil)) with
      | Accept e ->
        expr_eqb e (EConst
          ((nm (String ((Ascii (False, False, False, False, True, True, True,
             False)), (String ((Ascii (False, True, False, False, True, True,
             True, False)), (String ((Ascii (True, True, True, True, False,
             True, True, False)), (String ((Ascii (True, True, True, True,
             False, True, True, False)), (String ((Ascii (False, True, True,
             False, False, True, True, False)), (String ((Ascii (True, True,
             True, True, True, False, True, False)), (String ((Ascii (True,
             False, False, True, False, True, True, False)), (String ((Ascii
             (False, False, True, False, False, True, True, False)),
             EmptyString))))))))))))))))),
          Nil))
      | _ -> False),
    (Cons
    ((match whnf (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))) (Cons (level_decl, Nil)) Nil
              empty_context (EConst
              ((nm (String ((Ascii (True, True, False, False, True, True,
                 True, False)), (String ((Ascii (True, True, True, True,
                 False, True, True, False)), (String ((Ascii (False, True,
                 False, False, True, True, True, False)), (String ((Ascii
                 (False, False, True, False, True, True, True, False)),
                 EmptyString))))))))),
              (Cons (LZero, Nil)))) with
      | Accept e -> expr_eqb e prop0
      | _ -> False),
    Nil)))))))))))))))))))))))))))))))))

(** val ext_ctor : name -> nat -> nat -> constructor_data **)

let ext_ctor parent index fields =
  { ctor_induct = parent; ctor_index = index; ctor_num_params = O;
    ctor_num_fields = fields; ctor_is_unsafe = False }

(** val ext_ind : name -> name list -> bool -> inductive_data **)

let ext_ind n0 ctors recursive =
  { ind_num_params = O; ind_num_indices = O; ind_all = (Cons (n0, Nil));
    ind_ctors = ctors; ind_num_nested = O; ind_is_rec = recursive;
    ind_is_reflexive = False; ind_is_unsafe = False }

(** val ext_decl : name -> expr -> decl_kind -> expr option -> declaration **)

let ext_decl n0 ty kind value =
  { decl_name = n0; decl_params = Nil; decl_type = ty; decl_value = value;
    decl_kind_of = kind; decl_hints = HintOpaque }

(** val ext_nat_decl : declaration **)

let ext_nat_decl =
  ext_decl core_nat_name type1 (DInductive
    (ext_ind core_nat_name (Cons (core_zero_name, (Cons (core_succ_name,
      Nil)))) True))
    None

(** val ext_zero_decl : declaration **)

let ext_zero_decl =
  ext_decl core_zero_name core_nat (DConstructor
    (ext_ctor core_nat_name O O)) None

(** val ext_succ_decl : declaration **)

let ext_succ_decl =
  ext_decl core_succ_name (EPi (NameAnon, BDefault, core_nat, core_nat))
    (DConstructor (ext_ctor core_nat_name (S O) (S O))) None

(** val ext_nat_env : declaration list **)

let ext_nat_env =
  Cons (ext_succ_decl, (Cons (ext_zero_decl, (Cons (ext_nat_decl, Nil)))))

(** val ext_box_name : name **)

let ext_box_name =
  nm (String ((Ascii (False, True, False, False, False, False, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, True, True, True, True, False)),
    EmptyString))))))

(** val ext_box_mk : name **)

let ext_box_mk =
  NameStr (ext_box_name, (String ((Ascii (True, False, True, True, False,
    True, True, False)), (String ((Ascii (True, True, False, True, False,
    True, True, False)), EmptyString)))))

(** val ext_box : expr **)

let ext_box =
  EConst (ext_box_name, Nil)

(** val ext_box_decl : declaration **)

let ext_box_decl =
  ext_decl ext_box_name type1 (DInductive
    (ext_ind ext_box_name (Cons (ext_box_mk, Nil)) False)) None

(** val ext_box_ctor : declaration **)

let ext_box_ctor =
  ext_decl ext_box_mk (EPi (NameAnon, BDefault, core_nat, ext_box))
    (DConstructor (ext_ctor ext_box_name O (S O))) None

(** val ext_box_env : declaration list **)

let ext_box_env =
  Cons (ext_box_ctor, (Cons (ext_box_decl, ext_nat_env)))

(** val ext_box_value : expr **)

let ext_box_value =
  EApp ((EConst (ext_box_mk, Nil)), (ELit (LitNat (Npos (XO (XI (XO (XI (XO
    XH)))))))))

(** val ext_box_ctx : context **)

let ext_box_ctx =
  { bound_context = Nil; free_context = (Cons ((Pair
    ((nm (String ((Ascii (False, True, False, False, False, True, True,
       False)), EmptyString))),
    { binding_type = ext_box; binding_value = None })), Nil)) }

(** val ext_box_motive : expr **)

let ext_box_motive =
  EPi (NameAnon, BDefault, ext_box, type1)

(** val ext_box_minor : expr **)

let ext_box_minor =
  EPi (NameAnon, BDefault, core_nat, (EApp ((EBVar (S O)), (EApp ((EConst
    (ext_box_mk, Nil)), (EBVar O))))))

(** val ext_box_rec_type : expr **)

let ext_box_rec_type =
  EPi (NameAnon, BDefault, ext_box_motive, (EPi (NameAnon, BDefault,
    ext_box_minor, (EPi (NameAnon, BDefault, ext_box, (EApp ((EBVar (S (S
    O))), (EBVar O))))))))

(** val ext_box_rule : expr **)

let ext_box_rule =
  ELam (NameAnon, BDefault, ext_box_motive, (ELam (NameAnon, BDefault,
    ext_box_minor, (ELam (NameAnon, BDefault, core_nat, (EApp ((EBVar (S O)),
    (EBVar O))))))))

(** val ext_box_rec_data : recursor_data **)

let ext_box_rec_data =
  { rec_all = (Cons (ext_box_name, Nil)); rec_num_params = O;
    rec_num_indices = O; rec_num_motives = (S O); rec_num_minors = (S O);
    rec_rules = (Cons ({ rule_ctor = ext_box_mk; rule_nfields = (S O);
    rule_rhs = ext_box_rule }, Nil)); rec_k = False; rec_is_unsafe = False }

(** val ext_box_rec_name : name **)

let ext_box_rec_name =
  NameStr (ext_box_name, (String ((Ascii (False, True, False, False, True,
    True, True, False)), (String ((Ascii (True, False, True, False, False,
    True, True, False)), (String ((Ascii (True, True, False, False, False,
    True, True, False)), EmptyString)))))))

(** val ext_box_rec_decl : declaration **)

let ext_box_rec_decl =
  ext_decl ext_box_rec_name ext_box_rec_type (DRecursor ext_box_rec_data) None

(** val ext_rec_env : declaration list **)

let ext_rec_env =
  Cons (ext_box_rec_decl, ext_box_env)

(** val ext_unbox : expr -> expr **)

let ext_unbox b =
  core_apps (EConst (ext_box_rec_name, Nil)) (Cons ((ELam (NameAnon,
    BDefault, ext_box, core_nat)), (Cons ((ELam (NameAnon, BDefault,
    core_nat, (EBVar O))), (Cons (b, Nil))))))

(** val ext_utf8_emoji : string **)

let ext_utf8_emoji =
  String
    ((ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (String
    ((ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S
       O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (String
    ((ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (String
    ((ascii_of_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    EmptyString)))))))

(** val ext_q_name : name **)

let ext_q_name =
  nm (String ((Ascii (True, False, False, False, True, False, True, False)),
    (String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))

(** val ext_q_mk : name **)

let ext_q_mk =
  NameStr (ext_q_name, (String ((Ascii (True, False, True, True, False, True,
    True, False)), (String ((Ascii (True, True, False, True, False, True,
    True, False)), EmptyString)))))

(** val ext_q_lift : name **)

let ext_q_lift =
  NameStr (ext_q_name, (String ((Ascii (False, False, True, True, False,
    True, True, False)), (String ((Ascii (True, False, False, True, False,
    True, True, False)), (String ((Ascii (False, True, True, False, False,
    True, True, False)), (String ((Ascii (False, False, True, False, True,
    True, True, False)), EmptyString)))))))))

(** val ext_q_ind : name **)

let ext_q_ind =
  NameStr (ext_q_name, (String ((Ascii (True, False, False, True, False,
    True, True, False)), (String ((Ascii (False, True, True, True, False,
    True, True, False)), (String ((Ascii (False, False, True, False, False,
    True, True, False)), EmptyString)))))))

(** val ext_q_env : declaration list **)

let ext_q_env =
  Cons ((ext_decl ext_q_mk prop0 (DQuotient QCtor) None), (Cons
    ((ext_decl ext_q_lift prop0 (DQuotient QLift) None), (Cons
    ((ext_decl ext_q_ind prop0 (DQuotient QInd) None), Nil)))))

(** val ext_q_value : expr **)

let ext_q_value =
  core_apps (EConst (ext_q_mk, Nil)) (Cons (type1, (Cons (prop0, (Cons
    (prop0, Nil))))))

(** val ext_q_function : expr **)

let ext_q_function =
  ELam (NameAnon, BDefault, type1, (EBVar O))

(** val ext_q_lift_app : expr **)

let ext_q_lift_app =
  core_apps (EConst (ext_q_lift, Nil)) (Cons (type1, (Cons (prop0, (Cons
    (type1, (Cons (ext_q_function, (Cons (prop0, (Cons (ext_q_value,
    Nil))))))))))))

(** val ext_safety_name : name **)

let ext_safety_name =
  nm (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, True, True, True, True, False)),
    (String ((Ascii (True, True, True, True, True, False, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))

(** val ext_safety_decl : decl_kind -> declaration **)

let ext_safety_decl kind =
  ext_decl ext_safety_name type1 kind (Some prop0)

(** val ext_safety_term : expr **)

let ext_safety_term =
  EConst (ext_safety_name, Nil)

(** val extension_checks : unit0 -> bool list **)

let extension_checks _ =
  Cons
    ((accepted
       (infer (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
         ext_nat_env Nil empty_context (ELit (LitNat (Npos (XO (XO (XO (XO
         (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
         (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
         (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
         (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO
         (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XO (XI (XI (XI (XI
         (XO (XO (XI (XO (XO (XO (XI (XO (XO (XI (XO (XO (XO (XO (XO (XI (XI
         (XO (XO (XO (XI (XO (XO (XI (XI (XI (XO (XO (XO (XI (XI (XO (XI (XO
         (XI (XO (XO (XO
         XH)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons
    ((accepted
       (check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))) ext_nat_env Nil empty_context
         (EConst (core_zero_name, Nil)) (ELit (LitNat N0)))),
    (Cons
    ((accepted
       (check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         ext_rec_env Nil empty_context (ext_unbox ext_box_value) (ELit
         (LitNat (Npos (XO (XI (XO (XI (XO XH)))))))))),
    (Cons
    ((accepted
       (check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         ext_rec_env Nil ext_box_ctx
         (ext_unbox (EFVar
           (nm (String ((Ascii (False, True, False, False, False, True, True,
             False)), EmptyString)))))
         (EProj (ext_box_name, O, (EFVar
         (nm (String ((Ascii (False, True, False, False, False, True, True,
           False)), EmptyString)))))))),
    (Cons
    ((accepted
       (check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         ext_box_env Nil ext_box_ctx (EFVar
         (nm (String ((Ascii (False, True, False, False, False, True, True,
           False)), EmptyString))))
         (EApp ((EConst (ext_box_mk, Nil)), (EProj (ext_box_name, O, (EFVar
         (nm (String ((Ascii (False, True, False, False, False, True, True,
           False)), EmptyString)))))))))),
    (Cons
    ((rejected
       (infer (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
         ext_box_env Nil empty_context (EProj (ext_box_name, (S O),
         ext_box_value)))),
    (Cons
    ((match core_utf8 ext_utf8_emoji with
      | Some l ->
        (match l with
         | Nil -> False
         | Cons (n0, l0) ->
           (match l0 with
            | Nil ->
              N.eqb n0 (Npos (XO (XO (XO (XO (XO (XO (XO (XO (XO (XI (XI (XO
                (XI (XI (XI (XI XH)))))))))))))))))
            | Cons (_, _) -> False))
      | None -> False),
    (Cons
    ((declined
       (core_binary_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))) ext_nat_env PNatPow (Npos (XO XH))
         (Npos (XO (XO (XO (XO (XO (XO (XI (XO (XO (XI (XO (XO (XO (XO (XI
         (XO (XI (XI (XI XH)))))))))))))))))))))),
    (Cons
    ((match core_reduce_quotient
              (checker (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                O)))))))))))))))))))))))))))))))) ext_q_env Nil)
              ext_q_env empty_context ext_q_lift_app with
      | Accept o ->
        (match o with
         | Some e -> expr_eqb e (EApp (ext_q_function, prop0))
         | None -> False)
      | _ -> False),
    (Cons
    ((match core_reduce_quotient
              (checker (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                O)))))))))))))))))))))))))))))))) ext_q_env Nil)
              Nil empty_context ext_q_lift_app with
      | Accept o -> (match o with
                     | Some _ -> False
                     | None -> True)
      | _ -> False),
    (Cons
    ((rejected
       (infer (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
         (Cons ((ext_safety_decl (DUnsafe DDefinition)), Nil)) Nil
         empty_context ext_safety_term)),
    (Cons
    ((rejected
       (whnf (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))
         (Cons ((ext_safety_decl DPartial), Nil)) Nil empty_context
         ext_safety_term)),
    (Cons
    ((match core_binary_nat (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))) ext_nat_env PNatBitwise (Npos
              (XO (XI (XO (XI (XO XH)))))) (Npos (XI (XI (XI XH)))) with
      | Accept o -> (match o with
                     | Some _ -> False
                     | None -> True)
      | _ -> False),
    Nil)))))))))))))))))))))))))

(** val perf_delay : nat -> expr -> expr **)

let rec perf_delay n0 value =
  match n0 with
  | O -> value
  | S n1 ->
    ELet (NameAnon, core_nat, (ELit (LitNat N0)),
      (perf_delay n1 (lift (S O) O value)), False)

(** val perf_arrow : expr **)

let perf_arrow =
  EPi (NameAnon, BDefault, core_nat, core_nat)

(** val perf_slow : name **)

let perf_slow =
  nm (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, False, True, True, True, False)),
    EmptyString))))))))

(** val perf_slow_opaque : declaration **)

let perf_slow_opaque =
  ext_decl perf_slow perf_arrow DDefinition (Some (ELam (NameAnon, BDefault,
    core_nat,
    (perf_delay (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (EBVar O)))))

(** val perf_slow_decl : declaration **)

let perf_slow_decl =
  { decl_name = perf_slow_opaque.decl_name; decl_params = Nil; decl_type =
    perf_slow_opaque.decl_type; decl_value = perf_slow_opaque.decl_value;
    decl_kind_of = DDefinition; decl_hints = (HintRegular N0) }

(** val perf_env : declaration list **)

let perf_env =
  Cons (perf_slow_decl, ext_nat_env)

(** val perf_two : expr **)

let perf_two =
  ELit (LitNat (Npos (XO XH)))

(** val perf_beta_two : expr **)

let perf_beta_two =
  EApp ((ELam (NameAnon, BDefault, core_nat, (EBVar O))), perf_two)

(** val perf_app : expr -> expr **)

let perf_app arg =
  EApp ((EConst (perf_slow, Nil)), arg)

(** val perf_discard : name **)

let perf_discard =
  nm (String ((Ascii (False, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, False, True, True, False)),
    EmptyString))))))))))))))

(** val perf_discard_decl : declaration **)

let perf_discard_decl =
  ext_decl perf_discard perf_arrow DDefinition (Some (ELam (NameAnon,
    BDefault, core_nat, perf_two)))

(** val perf_prop : name **)

let perf_prop =
  nm (String ((Ascii (False, False, False, False, True, False, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, True, False, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, False, True, True, True, False)),
    EmptyString))))))))))))))))

(** val perf_proof : name **)

let perf_proof =
  nm (String ((Ascii (False, False, False, False, True, False, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    (String ((Ascii (False, False, False, False, True, False, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    EmptyString))))))))))))))))))

(** val perf_slow_proof : name **)

let perf_slow_proof =
  nm (String ((Ascii (True, True, False, False, True, False, True, False)),
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, False, True, True, True, False)),
    (String ((Ascii (False, False, False, False, True, False, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, False, True, True, False)),
    EmptyString))))))))))))))))))

(** val perf_proof_type : expr **)

let perf_proof_type =
  EConst (perf_prop, Nil)

(** val perf_proof_env : declaration list **)

let perf_proof_env =
  app (Cons
    ((ext_decl perf_slow_proof perf_proof_type DTheorem (Some
       (perf_delay (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         (EConst (perf_proof, Nil))))),
    (Cons ((ext_decl perf_proof perf_proof_type DAssumption None), (Cons
    ((ext_decl perf_prop prop0 DAssumption None), Nil)))))) ext_nat_env

(** val perf_succs : nat -> expr **)

let rec perf_succs = function
| O -> ELit (LitNat N0)
| S n1 -> EApp ((EConst (core_succ_name, Nil)), (perf_succs n1))

(** val perf_fnbox : name **)

let perf_fnbox =
  nm (String ((Ascii (False, True, True, False, False, False, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, False, False, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, False, False, True, True, True, True, False)),
    EmptyString))))))))))

(** val perf_fnmk : name **)

let perf_fnmk =
  NameStr (perf_fnbox, (String ((Ascii (True, False, True, True, False, True,
    True, False)), (String ((Ascii (True, True, False, True, False, True,
    True, False)), EmptyString)))))

(** val perf_fnind : declaration **)

let perf_fnind =
  ext_decl perf_fnbox type1 (DInductive
    (ext_ind perf_fnbox (Cons (perf_fnmk, Nil)) False)) None

(** val perf_fnctor : declaration **)

let perf_fnctor =
  ext_decl perf_fnmk (EPi (NameAnon, BDefault, perf_arrow, (EConst
    (perf_fnbox, Nil)))) (DConstructor (ext_ctor perf_fnbox O (S O))) None

(** val perf_fnvalue : expr **)

let perf_fnvalue =
  EApp ((EConst (perf_fnmk, Nil)), (ELam (NameAnon, BDefault, core_nat,
    (EBVar O))))

(** val perf_fnalias : declaration **)

let perf_fnalias =
  ext_decl
    (nm (String ((Ascii (False, True, True, False, False, False, True,
      False)), (String ((Ascii (False, True, True, True, False, True, True,
      False)), (String ((Ascii (True, False, False, False, False, False,
      True, False)), (String ((Ascii (False, False, True, True, False, True,
      True, False)), (String ((Ascii (True, False, False, True, False, True,
      True, False)), (String ((Ascii (True, False, False, False, False, True,
      True, False)), (String ((Ascii (True, True, False, False, True, True,
      True, False)), EmptyString)))))))))))))))
    (EConst (perf_fnbox, Nil)) DDefinition (Some perf_fnvalue)

(** val perf_fnenv : declaration list **)

let perf_fnenv =
  Cons (perf_fnalias, (Cons (perf_fnctor, (Cons (perf_fnind, ext_nat_env)))))

(** val perf_fnapp : expr **)

let perf_fnapp =
  EApp ((EProj (perf_fnbox, O, (EConst
    ((nm (String ((Ascii (False, True, True, False, False, False, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, False, False, False, False,
       True, False)), (String ((Ascii (False, False, True, True, False, True,
       True, False)), (String ((Ascii (True, False, False, True, False, True,
       True, False)), (String ((Ascii (True, False, False, False, False,
       True, True, False)), (String ((Ascii (True, True, False, False, True,
       True, True, False)), EmptyString))))))))))))))),
    Nil)))), perf_two)

(** val perf_peano : name **)

let perf_peano =
  nm (String ((Ascii (False, False, False, False, True, False, True, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, False, False, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    EmptyString))))))))))

(** val perf_zero : name **)

let perf_zero =
  NameNum (perf_peano, N0)

(** val perf_succ : name **)

let perf_succ =
  NameNum (perf_peano, (Npos XH))

(** val perf_peano_type : expr **)

let perf_peano_type =
  EConst (perf_peano, Nil)

(** val perf_peano_env : declaration list **)

let perf_peano_env =
  Cons
    ((ext_decl perf_succ (EPi (NameAnon, BDefault, perf_peano_type,
       perf_peano_type)) (DConstructor (ext_ctor perf_peano (S O) (S O)))
       None),
    (Cons
    ((ext_decl perf_zero perf_peano_type (DConstructor
       (ext_ctor perf_peano O O)) None),
    (Cons
    ((ext_decl perf_peano type1 (DInductive
       (ext_ind perf_peano (Cons (perf_zero, (Cons (perf_succ, Nil)))) True))
       None),
    Nil)))))

(** val perf_peano_numeral : nat -> expr **)

let rec perf_peano_numeral = function
| O -> EConst (perf_zero, Nil)
| S n1 -> EApp ((EConst (perf_succ, Nil)), (perf_peano_numeral n1))

(** val perf_batch_function : expr **)

let perf_batch_function =
  ELam (NameAnon, BDefault, perf_arrow, (ELam (NameAnon, BDefault, core_nat,
    (EApp ((EBVar (S O)), (EBVar O))))))

(** val performance_checks : unit0 -> bool list **)

let performance_checks _ =
  Cons
    ((accepted
       (check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S O)))))))))))))))))))))))) perf_env Nil empty_context
         (perf_app perf_two) (perf_app perf_beta_two))),
    (Cons
    ((declined
       (whnf (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S O)))))))))))))))))))))))) perf_env Nil empty_context
         (perf_app perf_two))),
    (Cons
    ((accepted
       (check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S O)))))))))))))))))))))))) perf_proof_env Nil
         empty_context (EConst (perf_slow_proof, Nil)) (EConst (perf_proof,
         Nil)))),
    (Cons
    ((accepted
       (infer (S (S (S (S (S (S (S (S O)))))))) ext_nat_env Nil empty_context
         (perf_succs (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
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
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Cons
    ((rejected
       (infer (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S O)))))))))))))))))))))))) (Cons (perf_discard_decl,
         ext_nat_env)) Nil empty_context (EApp ((EConst (perf_discard, Nil)),
         prop0)))),
    (Cons
    ((accepted
       (check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
         perf_fnenv Nil empty_context perf_fnapp perf_two)),
    (Cons
    ((match defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S
              O)))))))))))))))))))))))))))))))) perf_peano_env Nil
              empty_context
              (perf_peano_numeral (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S O)))))))))))))))))
              (perf_peano_numeral (S (S (S (S (S (S (S (S (S (S (S (S (S (S
                (S (S (S O)))))))))))))))))) with
      | Accept b -> (match b with
                     | True -> False
                     | False -> True)
      | _ -> False),
    (Cons
    ((accepted
       (check_defeq (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S O)))))))))))))))))))))))) (Cons (perf_discard_decl,
         ext_nat_env)) Nil empty_context (EApp ((EConst (perf_discard, Nil)),
         (perf_delay (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
           perf_two)))
         (EApp ((EConst (perf_discard, Nil)), (ELit (LitNat N0)))))),
    (Cons
    ((expr_eqb
       (core_beta perf_batch_function (Cons ((EBVar O), (Cons ((EBVar (S O)),
         Nil)))))
       (EApp ((EBVar O), (EBVar (S O))))),
    (Cons
    ((match whnf (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))
              ext_nat_env Nil (push_binding empty_context core_nat None)
              (core_apps perf_batch_function (Cons ((ELam (NameAnon,
                BDefault, core_nat, (EBVar (S O)))), (Cons (perf_two, Nil))))) with
      | Accept e -> expr_eqb e (EBVar O)
      | _ -> False),
    Nil)))))))))))))))))))
