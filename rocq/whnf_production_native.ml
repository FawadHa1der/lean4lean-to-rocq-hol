
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
| S u -> u

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

type level =
| LZero
| LSucc of level
| LMax of level * level
| LIMax of level * level
| LParam of name
| LMVar of name

(** val level_eqb : level -> level -> bool **)

let rec level_eqb u v =
  match u with
  | LZero -> (match v with
              | LZero -> True
              | _ -> False)
  | LSucc u0 -> (match v with
                 | LSucc v0 -> level_eqb u0 v0
                 | _ -> False)
  | LMax (a, b) ->
    (match v with
     | LMax (c, d) ->
       (match level_eqb a c with
        | True -> level_eqb b d
        | False -> False)
     | _ -> False)
  | LIMax (a, b) ->
    (match v with
     | LIMax (c, d) ->
       (match level_eqb a c with
        | True -> level_eqb b d
        | False -> False)
     | _ -> False)
  | LParam a -> (match v with
                 | LParam b -> name_eqb a b
                 | _ -> False)
  | LMVar a -> (match v with
                | LMVar b -> name_eqb a b
                | _ -> False)

(** val level_wf : name list -> level -> bool **)

let rec level_wf ps = function
| LZero -> True
| LSucc v -> level_wf ps v
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
  | ESort u -> (match b with
                | ESort v -> level_eqb u v
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
  | ELet (_, a0, v, b0, _) ->
    (match b with
     | ELet (_, c, w, d, _) ->
       (match match expr_eqb a0 c with
              | True -> expr_eqb v w
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
| ELet (_, a, v, b, _) ->
  (match match has_external_local_at depth a with
         | True -> True
         | False -> has_external_local_at depth v with
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
| ELet (_, a, v, b, _) ->
  (match match core_occurs index a with
         | True -> True
         | False -> core_occurs index v with
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

(** val check_level : name list -> level -> unit0 result **)

let check_level ps u =
  match level_has_meta u with
  | True -> Reject MetaVariable
  | False -> require (level_wf ps u) UnknownUniverse

(** val check_levels : name list -> level list -> unit0 result **)

let rec check_levels ps = function
| Nil -> Accept Tt
| Cons (u, us0) -> bind (check_level ps u) (fun _ -> check_levels ps us0)

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
      | ESort u -> Accept u
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
        bind (sort_of rec0 g domain) (fun u ->
          bind (level_equiv fuel u LZero) (fun ok -> require ok TypeMismatch))
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
                             bind (sort_of rec0 g st0) (fun u ->
                               core_projection_field rec0 fuel g owner value
                                 (negb (core_level_positive u)) index O ty)))
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
                                   (fun prop ->
                                   match prop with
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
                              bind (level_equiv fuel sort LZero) (fun prop ->
                                match prop with
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
| ESort u -> bind (check_level ps u) (fun _ -> Accept (ESort (LSucc u)))
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
            | ESort u -> Accept u
            | _ -> Reject ExpectedSort)
        (fun u ->
        let gb = push_binding g domain None in
        bind (infer_step rec0 fuel env ps checking gb body) (fun bt ->
          bind (rec0.whnf_method gb bt) (fun bt0 ->
            bind
              (match bt0 with
               | ESort v -> Accept v
               | _ -> Reject ExpectedSort)
              (fun v -> Accept (ESort (LIMax (u, v)))))))))
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
      | Some v -> rec0.whnf_core_method cheap g (lift (S i) O v)
      | None -> Accept e)
   | None -> Reject LooseBoundVariable)
| EFVar n0 ->
  (match find_free n0 g.free_context with
   | Some b ->
     (match b.binding_value with
      | Some v -> rec0.whnf_core_method cheap g v
      | None -> Accept e)
   | None -> Reject UnknownFreeVariable)
| EMVar _ -> Reject MetaVariable
| ESort u -> bind (check_level ps u) (fun _ -> Accept e)
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
     | ESort u ->
       (match s with
        | ESort v -> Pair ((level_eqb u v), budget0)
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
     | ELet (_, a, v, b, _) ->
       (match s with
        | ELet (_, c, w, d, _) ->
          let Pair (ok, remaining) = core_alpha budget0 a c in
          (match ok with
           | True ->
             let Pair (ok0, remaining0) = core_alpha remaining v w in
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
     | ESort u ->
       (match s with
        | ESort v -> level_equiv fuel u v
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
     | ESort u ->
       (match s with
        | ESort v -> bind (level_equiv fuel u v) (fun ok -> Accept (Some ok))
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
    let zero = fun e ->
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
    (match match zero t with
           | True -> zero s
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

(** val checker_eager_mode :
    reduction_mode -> nat -> environment -> name list -> methods **)

let rec checker_eager_mode mode fuel env ps =
  match fuel with
  | O ->
    { infer_method = (fun _ _ -> Decline OutOfFuel); infer_type_method =
      (fun _ _ -> Decline OutOfFuel); whnf_method = (fun _ _ -> Decline
      OutOfFuel); whnf_core_method = (fun _ _ _ -> Decline OutOfFuel);
      defeq_method = (fun _ _ _ -> Decline OutOfFuel); method_mode = mode;
      eager_defeq_method = (fun _ _ _ -> Decline OutOfFuel) }
  | S n0 ->
    let rec0 = checker_eager_mode mode n0 env ps in
    { infer_method = (infer_step rec0 n0 env ps True); infer_type_method =
    (infer_step rec0 n0 env ps False); whnf_method =
    (whnf_loop (whnf_round_limit mode) rec0 n0 env ps); whnf_core_method =
    (whnf_core_step rec0 n0 env ps); defeq_method =
    (defeq_step rec0 n0 env ps); method_mode = mode; eager_defeq_method =
    (fun g t s ->
    let rec1 = checker_eager_mode EagerReduction n0 env ps in
    defeq_step rec1 n0 env ps g t s) }

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
  | ELet (_, a, v, b, _) ->
    (match match core_occurs index a with
           | True -> True
           | False -> core_occurs index v with
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

  let core_ctor_shape resolve env n0 parent index fields ty =
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
          | True -> expr_eqb d.decl_type ty
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
          | DPrimitive p ->
            (match p with
             | PCharOfNat ->
               (match s.decl_kind_of with
                | DPrimitive p0 ->
                  (match p0 with
                   | PStringOfList -> core_nat_ready resolve env
                   | _ -> False)
                | _ -> False)
             | _ -> False)
          | _ -> False)
       | None -> False)
    | None -> False

  (** val check_level : name list -> level -> unit0 result **)

  let check_level ps u =
    match level_has_meta u with
    | True -> Reject MetaVariable
    | False -> require (level_wf ps u) UnknownUniverse

  (** val check_levels : name list -> level list -> unit0 result **)

  let rec check_levels ps = function
  | Nil -> Accept Tt
  | Cons (u, us0) -> bind (check_level ps u) (fun _ -> check_levels ps us0)

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
    bind (rec0.infer_method g e) (fun t ->
      bind (rec0.whnf_method g t) (fun t0 ->
        match t0 with
        | ESort u -> Accept u
        | _ -> Reject ExpectedSort))

  (** val core_apply_type :
      methods -> context -> expr -> expr list -> expr result **)

  let rec core_apply_type rec0 g ty = function
  | Nil -> Accept ty
  | Cons (a, args0) ->
    bind (rec0.whnf_method g ty) (fun ty0 ->
      match ty0 with
      | EPi (_, _, _, body) ->
        core_apply_type rec0 g (instantiate body a) args0
      | _ -> Reject ExpectedPi)

  (** val core_projection_field :
      methods -> nat -> context -> name -> expr -> bool -> nat -> nat -> expr
      -> expr result **)

  let rec core_projection_field rec0 fuel g owner value maybe_prop skip index ty =
    bind (rec0.whnf_method g ty) (fun reduced ->
      match reduced with
      | EPi (_, _, domain, body) ->
        let verify_prop = fun _ ->
          bind (sort_of rec0 g domain) (fun u ->
            bind (level_equiv fuel u LZero) (fun ok ->
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
             core_projection_field rec0 fuel g owner value maybe_prop skip0
               (S index) (instantiate body (EProj (owner, index, value)))))
      | _ -> Reject ExpectedPi)

  (** val core_infer_projection :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> name -> nat -> expr -> expr result **)

  let core_infer_projection resolve rec0 fuel env g owner index value =
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
                               (fun ty ->
                               bind (sort_of rec0 g st0) (fun u ->
                                 core_projection_field rec0 fuel g owner
                                   value (negb (core_level_positive u)) index
                                   O ty)))
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

  let core_shiftr fuel a b =
    match N.ltb (N.log2 a) b with
    | True -> Accept N0
    | False ->
      (match N.leb b (N.of_nat fuel) with
       | True -> Accept (N.shiftr a b)
       | False -> Decline OutOfFuel)

  (** val core_binary_nat :
      (name -> environment -> declaration option) -> nat -> environment ->
      primitive_kind -> n -> n -> expr option result **)

  let core_binary_nat resolve fuel env op a b =
    let numeric = fun n0 -> Accept (Some (ELit (LitNat n0))) in
    let bounded = fun operation ->
      match N.leb b (N.of_nat fuel) with
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
     | PNatShiftRight -> bind (core_shiftr fuel a b) numeric
     | _ -> Accept None)

  (** val core_reduce_nat :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> expr -> expr option result **)

  let core_reduce_nat resolve rec0 fuel env g e =
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
                        | DPrimitive p ->
                          (match p with
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
                                        core_binary_nat resolve fuel env op
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
     | True -> option_map (fun x -> Cons ((N.of_nat n0), x)) (core_utf8 rest)
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
                   option_map (fun x -> Cons
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
                     x)) (core_utf8 tail)
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
                               option_map (fun x -> Cons
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
                                 x)) (core_utf8 tail)
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

  let core_to_constructor resolve rec0 fuel env g owner k_rule value =
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
                 bind (rec0.infer_method g reduced) (fun ty ->
                   bind (rec0.whnf_method g ty) (fun ty0 ->
                     let Pair (head, args) = core_spine ty0 Nil in
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
                                 bind (sort_of rec0 g ty0) (fun sort ->
                                   bind (level_equiv fuel sort LZero)
                                     (fun prop ->
                                     match prop with
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
                     | False -> core_structure resolve env owner) with
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
                        (match core_make_structure resolve env owner us args
                                 reduced with
                         | Some candidate ->
                           (match k_rule with
                            | True ->
                              bind (sort_of rec0 g ty0) (fun sort ->
                                bind (level_equiv fuel sort LZero)
                                  (fun prop ->
                                  match prop with
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
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> expr -> expr option result **)

  let core_reduce_recursor resolve rec0 fuel env g e =
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
                     (core_to_constructor resolve rec0 fuel env g owner
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
                                    (match resolve cn env with
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
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> name list -> bool -> context -> expr -> expr result **)

  let rec infer_step resolve rec0 fuel env ps checking g = function
  | EBVar i ->
    (match nth_error g.bound_context i with
     | Some b -> Accept (lift (S i) O b.binding_type)
     | None -> Reject LooseBoundVariable)
  | EFVar n0 ->
    (match find_free n0 g.free_context with
     | Some b -> Accept b.binding_type
     | None -> Reject UnknownFreeVariable)
  | EMVar _ -> Reject MetaVariable
  | ESort u -> bind (check_level ps u) (fun _ -> Accept (ESort (LSucc u)))
  | EConst (n0, us) ->
    bind (get_constant resolve env ps n0 us) (fun d -> Accept
      (instantiate_levels d.decl_params us d.decl_type))
  | EApp (f, a) ->
    bind (infer_step resolve rec0 fuel env ps checking g f) (fun ft ->
      bind (rec0.whnf_method g ft) (fun ft0 ->
        match ft0 with
        | EPi (_, _, domain, body) ->
          bind
            (match checking with
             | True ->
               bind (infer_step resolve rec0 fuel env ps True g a)
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
         bind (infer_step resolve rec0 fuel env ps True g domain) (fun dt ->
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
        (infer_step resolve rec0 fuel env ps checking
          (push_binding g domain None) body)
        (fun bt -> Accept (EPi (n0, bi, domain, bt))))
  | EPi (_, _, domain, body) ->
    bind (infer_step resolve rec0 fuel env ps checking g domain) (fun dt ->
      bind (rec0.whnf_method g dt) (fun dt0 ->
        bind (match dt0 with
              | ESort u -> Accept u
              | _ -> Reject ExpectedSort)
          (fun u ->
          let gb = push_binding g domain None in
          bind (infer_step resolve rec0 fuel env ps checking gb body)
            (fun bt ->
            bind (rec0.whnf_method gb bt) (fun bt0 ->
              bind
                (match bt0 with
                 | ESort v -> Accept v
                 | _ -> Reject ExpectedSort)
                (fun v -> Accept (ESort (LIMax (u, v)))))))))
  | ELet (_, ty, value, body, _) ->
    bind
      (match checking with
       | True ->
         bind (infer_step resolve rec0 fuel env ps True g ty)
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
               bind (infer_step resolve rec0 fuel env ps True g value)
                 (fun vt ->
                 bind (rec0.defeq_method g vt ty) (fun ok ->
                   require ok TypeMismatch)))))
       | False -> Accept Tt)
      (fun _ ->
      bind
        (infer_step resolve rec0 fuel env ps checking
          (push_binding g ty (Some value)) body)
        (fun bt -> Accept (instantiate bt value)))
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
         fuel env g owner index value
     | None -> Decline UnsupportedExpression)
  | EMData body -> infer_step resolve rec0 fuel env ps checking g body

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

  let whnf_core_step resolve rec0 fuel env ps cheap g e = match e with
  | EBVar i ->
    (match nth_error g.bound_context i with
     | Some b ->
       (match b.binding_value with
        | Some v -> rec0.whnf_core_method cheap g (lift (S i) O v)
        | None -> Accept e)
     | None -> Reject LooseBoundVariable)
  | EFVar n0 ->
    (match find_free n0 g.free_context with
     | Some b ->
       (match b.binding_value with
        | Some v -> rec0.whnf_core_method cheap g v
        | None -> Accept e)
     | None -> Reject UnknownFreeVariable)
  | EMVar _ -> Reject MetaVariable
  | ESort u -> bind (check_level ps u) (fun _ -> Accept e)
  | EConst (n0, us) ->
    bind (get_constant resolve env ps n0 us) (fun _ -> Accept e)
  | EApp (_, _) ->
    let Pair (head, args) = core_spine e Nil in
    bind (rec0.whnf_core_method cheap g head) (fun fn ->
      match fn with
      | EBVar _ ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot ->
          bind
            (match quot with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | EFVar _ ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot ->
          bind
            (match quot with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | EMVar _ ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot ->
          bind
            (match quot with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | ESort _ ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot ->
          bind
            (match quot with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | EConst (_, _) ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot ->
          bind
            (match quot with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | EApp (_, _) ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot ->
          bind
            (match quot with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | ELam (_, _, _, _) -> rec0.whnf_core_method cheap g (core_beta fn args)
      | EPi (_, _, _, _) ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot ->
          bind
            (match quot with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | ELet (_, _, _, _, _) ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot ->
          bind
            (match quot with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | ELit _ ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot ->
          bind
            (match quot with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | EProj (_, _, _) ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot ->
          bind
            (match quot with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel env g rebuilt)
            (fun step ->
            match step with
            | Some value -> rec0.whnf_core_method cheap g value
            | None -> Accept rebuilt))
      | EMData _ ->
        let rebuilt = core_apps fn args in
        bind (core_reduce_quotient resolve rec0 env g rebuilt) (fun quot ->
          bind
            (match quot with
             | Some value -> Accept (Some value)
             | None -> core_reduce_recursor resolve rec0 fuel env g rebuilt)
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

  let whnf_round_step resolve rec0 fuel env ps g e =
    bind (whnf_core_step resolve rec0 fuel env ps False g e) (fun reduced ->
      match reduced with
      | EBVar _ ->
        bind (core_reduce_nat resolve rec0 fuel env g reduced) (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | EFVar _ ->
        bind (core_reduce_nat resolve rec0 fuel env g reduced) (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | EMVar _ ->
        bind (core_reduce_nat resolve rec0 fuel env g reduced) (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | ESort _ ->
        bind (core_reduce_nat resolve rec0 fuel env g reduced) (fun native ->
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
        bind (core_reduce_nat resolve rec0 fuel env g reduced) (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | ELam (_, _, _, _) ->
        bind (core_reduce_nat resolve rec0 fuel env g reduced) (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | EPi (_, _, _, _) ->
        bind (core_reduce_nat resolve rec0 fuel env g reduced) (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | ELet (_, _, _, _, _) ->
        bind (core_reduce_nat resolve rec0 fuel env g reduced) (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | ELit _ ->
        bind (core_reduce_nat resolve rec0 fuel env g reduced) (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | EProj (_, _, _) ->
        bind (core_reduce_nat resolve rec0 fuel env g reduced) (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced)
      | EMData _ ->
        bind (core_reduce_nat resolve rec0 fuel env g reduced) (fun native ->
          match native with
          | Some value -> Accept (WhnfDone value)
          | None -> finish_whnf_unfold resolve env ps reduced))

  (** val whnf_loop :
      (name -> environment -> declaration option) -> nat -> methods -> nat ->
      environment -> name list -> context -> expr -> expr result **)

  let whnf_loop resolve rounds rec0 fuel env ps g e =
    run_whnf_rounds rounds (whnf_round_step resolve rec0 fuel env ps g) e

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
       | ESort u ->
         (match s with
          | ESort v -> Pair ((level_eqb u v), budget0)
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
       | ELet (_, a, v, b, _) ->
         (match s with
          | ELet (_, c, w, d, _) ->
            let Pair (ok, remaining) = core_alpha budget0 a c in
            (match ok with
             | True ->
               let Pair (ok0, remaining0) = core_alpha remaining v w in
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

  let core_delta_sides resolve env t s =
    match core_delta_info resolve env t with
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

  let core_delta_congruent resolve rec0 fuel env g t s =
    match core_delta_info resolve env t with
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
                          (match core_erasing_delta resolve env t with
                           | True -> True
                           | False -> core_erasing_delta resolve env s)
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

  let core_unit_like resolve rec0 env g t s =
    bind (rec0.infer_method g t) (fun ty ->
      bind (rec0.whnf_method g ty) (fun ty0 ->
        match fst (core_spine ty0 Nil) with
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
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> expr -> expr -> bool result **)

  let core_compare_fallback resolve rec0 fuel env g t s =
    bind (compare_heads rec0 fuel g t s) (fun ok ->
      match ok with
      | True -> Accept True
      | False ->
        bind (core_structure_eta resolve rec0 env g t s) (fun ok0 ->
          match ok0 with
          | True -> Accept True
          | False ->
            bind (core_structure_eta resolve rec0 env g s t) (fun ok1 ->
              match ok1 with
              | True -> Accept True
              | False ->
                bind (core_try_string_expansion rec0 g t s) (fun expanded ->
                  match expanded with
                  | Some ok2 -> Accept ok2
                  | None -> core_unit_like resolve rec0 env g t s))))

  (** val compare_after_whnf :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> expr -> expr -> bool result **)

  let compare_after_whnf resolve rec0 fuel env g t s =
    match core_alpha_eq t s with
    | True -> Accept True
    | False ->
      (match t with
       | ESort u ->
         (match s with
          | ESort v -> level_equiv fuel u v
          | _ ->
            bind (rec0.infer_method g t) (fun tt ->
              bind (sort_of rec0 g tt) (fun sort ->
                bind (level_equiv fuel sort LZero) (fun is_prop ->
                  match is_prop with
                  | True ->
                    bind (rec0.infer_method g s) (fun st ->
                      rec0.defeq_method g tt st)
                  | False -> core_compare_fallback resolve rec0 fuel env g t s))))
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
                  | False -> core_compare_fallback resolve rec0 fuel env g t s))))
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
                  | False -> core_compare_fallback resolve rec0 fuel env g t s))))
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
                        | False ->
                          core_compare_fallback resolve rec0 fuel env g t s))))
             | _ ->
               bind (rec0.infer_method g t) (fun tt ->
                 bind (sort_of rec0 g tt) (fun sort ->
                   bind (level_equiv fuel sort LZero) (fun is_prop ->
                     match is_prop with
                     | True ->
                       bind (rec0.infer_method g s) (fun st ->
                         rec0.defeq_method g tt st)
                     | False ->
                       core_compare_fallback resolve rec0 fuel env g t s))))
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
                        | False ->
                          core_compare_fallback resolve rec0 fuel env g t s)))
                | LitString b -> Accept (eqb1 a b))
             | _ ->
               bind (rec0.infer_method g t) (fun tt ->
                 bind (sort_of rec0 g tt) (fun sort ->
                   bind (level_equiv fuel sort LZero) (fun is_prop ->
                     match is_prop with
                     | True ->
                       bind (rec0.infer_method g s) (fun st ->
                         rec0.defeq_method g tt st)
                     | False ->
                       core_compare_fallback resolve rec0 fuel env g t s)))))
       | _ ->
         bind (rec0.infer_method g t) (fun tt ->
           bind (sort_of rec0 g tt) (fun sort ->
             bind (level_equiv fuel sort LZero) (fun is_prop ->
               match is_prop with
               | True ->
                 bind (rec0.infer_method g s) (fun st ->
                   rec0.defeq_method g tt st)
               | False -> core_compare_fallback resolve rec0 fuel env g t s))))

  (** val core_quick :
      methods -> nat -> context -> expr -> expr -> bool option result **)

  let core_quick rec0 fuel g t s =
    match core_alpha_eq t s with
    | True -> Accept (Some True)
    | False ->
      (match t with
       | ESort u ->
         (match s with
          | ESort v ->
            bind (level_equiv fuel u v) (fun ok -> Accept (Some ok))
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

  (** val core_offset :
      (name -> environment -> declaration option) -> methods -> environment
      -> context -> expr -> expr -> bool option result **)

  let core_offset resolve rec0 env g t s =
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
      let zero = fun e ->
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
      (match match zero t with
             | True -> zero s
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
      (name -> environment -> declaration option) -> methods -> environment
      -> context -> expr -> expr -> (expr, expr) prod option result **)

  let core_opposite_projection resolve rec0 env g t s =
    match core_delta_info resolve env t with
    | Some _ ->
      (match core_delta_info resolve env s with
       | Some _ -> Accept None
       | None ->
         bind (core_try_unfold_proj_app rec0 g s) (fun reduced -> Accept
           (match reduced with
            | Some s' -> Some (Pair (t, s'))
            | None -> None)))
    | None ->
      (match core_delta_info resolve env s with
       | Some _ ->
         bind (core_try_unfold_proj_app rec0 g t) (fun reduced -> Accept
           (match reduced with
            | Some t' -> Some (Pair (t', s))
            | None -> None))
       | None -> Accept None)

  (** val core_lazy_delta :
      (name -> environment -> declaration option) -> nat -> methods -> nat ->
      environment -> name list -> context -> expr -> expr ->
      conversion_progress result **)

  let rec core_lazy_delta resolve rounds rec0 fuel env ps g t s =
    match rounds with
    | O -> Decline OutOfFuel
    | S rounds0 ->
      bind (core_quick rec0 fuel g t s) (fun quick ->
        match quick with
        | Some ok -> Accept (ConversionDone ok)
        | None ->
          bind (core_offset resolve rec0 env g t s) (fun offset ->
            match offset with
            | Some ok -> Accept (ConversionDone ok)
            | None ->
              let eligible =
                pair_probe_guard
                  (nat_probe_head resolve core_succ_name env
                    (core_spine t Nil))
                  (nat_probe_head resolve core_succ_name env
                    (core_spine s Nil))
                  (fun _ -> nat_probe_allowed rec0.method_mode t s)
              in
              bind
                (match eligible with
                 | True -> core_reduce_nat resolve rec0 fuel env g t
                 | False -> Accept None)
                (fun tn ->
                match tn with
                | Some tn0 ->
                  bind (rec0.defeq_method g tn0 s) (fun ok -> Accept
                    (ConversionDone ok))
                | None ->
                  bind
                    (match eligible with
                     | True -> core_reduce_nat resolve rec0 fuel env g s
                     | False -> Accept None)
                    (fun sn ->
                    match sn with
                    | Some sn0 ->
                      bind (rec0.defeq_method g t sn0) (fun ok -> Accept
                        (ConversionDone ok))
                    | None ->
                      bind (core_delta_congruent resolve rec0 fuel env g t s)
                        (fun same ->
                        match same with
                        | True -> Accept (ConversionDone True)
                        | False ->
                          bind
                            (core_opposite_projection resolve rec0 env g t s)
                            (fun projected ->
                            match projected with
                            | Some p ->
                              let Pair (tn0, sn0) = p in
                              core_lazy_delta resolve rounds0 rec0 fuel env
                                ps g tn0 sn0
                            | None ->
                              let Pair (unfold_left, unfold_right) =
                                core_delta_sides resolve env t s
                              in
                              bind
                                (match unfold_left with
                                 | True -> core_unfold resolve env ps t
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
                                       | None -> Accept t)
                                      (fun tn0 ->
                                      bind
                                        (match sd with
                                         | Some e ->
                                           rec0.whnf_core_method True g e
                                         | None -> Accept s)
                                        (fun sn0 ->
                                        core_lazy_delta resolve rounds0 rec0
                                          fuel env ps g tn0 sn0))
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
                                           core_lazy_delta resolve rounds0
                                             rec0 fuel env ps g tn0 sn0))
                                     | None -> Accept (ConversionStuck (t, s)))))))))))

  (** val core_finish_conversion :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> context -> expr -> expr -> bool result **)

  let core_finish_conversion resolve rec0 fuel env g t s =
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
           | None -> compare_after_whnf resolve rec0 fuel env g t s)))

  (** val core_true_shortcut :
      (name -> environment -> declaration option) -> methods -> environment
      -> context -> expr -> expr -> bool result **)

  let core_true_shortcut resolve rec0 env g t s =
    match match match core_is_true s with
                | True -> true_probe_allowed rec0.method_mode t
                | False -> False with
          | True -> core_bool_ready resolve env
          | False -> False with
    | True -> bind (rec0.whnf_method g t) (fun tn -> Accept (core_is_true tn))
    | False -> Accept False

  (** val defeq_step :
      (name -> environment -> declaration option) -> methods -> nat ->
      environment -> name list -> context -> expr -> expr -> bool result **)

  let defeq_step resolve rec0 fuel env ps g t s =
    let rec1 = inference_only rec0 in
    bind (core_quick rec1 fuel g t s) (fun quick ->
      match quick with
      | Some ok -> Accept ok
      | None ->
        bind (core_true_shortcut resolve rec1 env g t s) (fun shortcut ->
          match shortcut with
          | True -> Accept True
          | False ->
            bind (core_proof_irrel rec1 fuel g t s) (fun irrelevant ->
              match irrelevant with
              | Some ok -> Accept ok
              | None ->
                bind (rec1.whnf_core_method True g t) (fun tn ->
                  bind (rec1.whnf_core_method True g s) (fun sn ->
                    bind
                      (core_lazy_delta resolve (S fuel) rec1 fuel env ps g tn
                        sn)
                      (fun progress ->
                      match progress with
                      | ConversionDone ok -> Accept ok
                      | ConversionStuck (tn0, sn0) ->
                        core_finish_conversion resolve rec1 fuel env g tn0 sn0))))))

  (** val checker_eager_mode :
      (name -> environment -> declaration option) -> reduction_mode -> nat ->
      environment -> name list -> methods **)

  let rec checker_eager_mode resolve mode fuel env ps =
    match fuel with
    | O ->
      { infer_method = (fun _ _ -> Decline OutOfFuel); infer_type_method =
        (fun _ _ -> Decline OutOfFuel); whnf_method = (fun _ _ -> Decline
        OutOfFuel); whnf_core_method = (fun _ _ _ -> Decline OutOfFuel);
        defeq_method = (fun _ _ _ -> Decline OutOfFuel); method_mode = mode;
        eager_defeq_method = (fun _ _ _ -> Decline OutOfFuel) }
    | S n0 ->
      let rec0 = checker_eager_mode resolve mode n0 env ps in
      { infer_method = (infer_step resolve rec0 n0 env ps True);
      infer_type_method = (infer_step resolve rec0 n0 env ps False);
      whnf_method =
      (whnf_loop resolve (whnf_round_limit mode) rec0 n0 env ps);
      whnf_core_method = (whnf_core_step resolve rec0 n0 env ps);
      defeq_method = (defeq_step resolve rec0 n0 env ps); method_mode = mode;
      eager_defeq_method = (fun g t s ->
      let rec1 = checker_eager_mode resolve EagerReduction n0 env ps in
      defeq_step resolve rec1 n0 env ps g t s) }

  (** val checker_mode :
      (name -> environment -> declaration option) -> reduction_mode -> nat ->
      environment -> name list -> methods **)

  let rec checker_mode resolve mode fuel env ps =
    match fuel with
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
        (fun g t s ->
        let rec0 = checker_mode resolve mode n0 env ps in
        defeq_step resolve rec0 n0 env ps g t s); method_mode = mode;
        eager_defeq_method = (fun g t s ->
        let rec0 = checker_mode resolve EagerReduction n0 env ps in
        defeq_step resolve rec0 n0 env ps g t s) }
 end
