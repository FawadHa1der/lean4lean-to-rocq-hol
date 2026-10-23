prelude

unsafe inductive UEmpty : Type

unsafe inductive UNeg : Type where
  | mk : (UNeg -> UNeg) -> UNeg

unsafe def uId : UNeg -> UNeg := fun x => x

mutual
  unsafe def uA : UNeg -> UNeg := uB
  unsafe def uB : UNeg -> UNeg := fun x => uA x
end
