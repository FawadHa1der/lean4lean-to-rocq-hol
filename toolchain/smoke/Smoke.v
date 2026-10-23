From Stdlib Require Import Arith Extraction ExtrOcamlNatInt.

Theorem plus_zero : forall n : nat, n + 0 = n.
Proof. intro n. apply Nat.add_0_r. Qed.

Print Assumptions plus_zero.
Definition successor (n : nat) : nat := S n.
Extraction Language OCaml.
Extraction "smoke_extracted.ml" successor.
