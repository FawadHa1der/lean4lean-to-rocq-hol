(* SPDX-License-Identifier: Apache-2.0
   Copyright 2026 Fawad Haider.
   Rocq port of Lean4Lean/Theory/LevelSat.lean:
   coNP-hardness of universe level equivalence (vlevel_equiv) and inequality
   (vlevel_le) via a linear-size dual-rail reduction from CNF unsatisfiability. *)
From Stdlib Require Import List Bool Arith PeanoNat Lia Eqdep_dec.
From LeanPort Require Import Syntax Universes UniverseSoundness SemanticModel.
Import ListNotations.
Set Implicit Arguments.

(* ========================================================================= *)
(* 1. Bounded Variable Indices and CNF Formulas                              *)
(* ========================================================================= *)

Record Fin (n : nat) : Type := mkFin {
  fin_val : nat;
  fin_ltb : (fin_val <? n) = true
}.

Arguments mkFin {n} fin_val fin_ltb.

Lemma fin_isLt {n : nat} (i : Fin n) : fin_val i < n.
Proof.
  apply Nat.ltb_lt. exact (fin_ltb i).
Qed.

Lemma Fin_eq {n : nat} (i j : Fin n) :
  fin_val i = fin_val j -> i = j.
Proof.
  destruct i as [iv ilt], j as [jv jlt]; simpl.
  intros Heq; subst jv.
  f_equal. apply (UIP_dec Bool.bool_dec).
Qed.

(* A literal is a bounded variable in Fin n paired with its polarity. *)
Definition Lit (n : nat) : Type := (Fin n * bool)%type.

(* A clause is a disjunction of literals. *)
Definition Clause (n : nat) : Type := list (Lit n).

(* A CNF formula over n variables is a conjunction of clauses. *)
Definition CNF (n : nat) : Type := list (Clause n).

(* An assignment satisfies a clause if it agrees with at least one literal. *)
Definition ClauseSat {n : nat} (a : Fin n -> bool) (C : Clause n) : Prop :=
  exists l, In l C /\ a (fst l) = snd l.

(* Satisfiability of a CNF formula over Fin n. *)
Definition Sat {n : nat} (phi : CNF n) : Prop :=
  exists a : Fin n -> bool, forall C, In C phi -> ClauseSat a C.

(* Dual-rail parameter indices: yes i = 2*i (positive rail), no i = 2*i+1 (negative rail). *)
Definition yes (i : nat) : nat := 2 * i.

Definition no (i : nat) : nat := 2 * i + 1.

Definition rail {n : nat} (l : Lit n) : nat :=
  if snd l then yes (fin_val (fst l)) else no (fin_val (fst l)).

Theorem rail_lt {n : nat} (l : Lit n) : rail l < 2 * n.
Proof.
  pose proof (fin_isLt (fst l)) as Hlt.
  unfold rail, yes, no. destruct (snd l); lia.
Qed.

Theorem rail_pos {n : nat} (l : Lit n) :
  snd l = true -> rail l = yes (fin_val (fst l)).
Proof.
  intros H; unfold rail; rewrite H; reflexivity.
Qed.

Theorem rail_neg {n : nat} (l : Lit n) :
  snd l = false -> rail l = no (fin_val (fst l)).
Proof.
  intros H; unfold rail; rewrite H; reflexivity.
Qed.

(* ========================================================================= *)
(* 2. Universe Level Constructions for the Reduction                         *)
(* ========================================================================= *)

(* Constant universe level 2. *)
Definition two : VLevel := VLSucc (VLSucc VLZero).

(* Disjunction of a clause as max of the rails of its literals. *)
Definition clauseLvl {n : nat} (C : Clause n) : VLevel :=
  fold_right (fun l acc => VLMax (VLParam (rail l)) acc) VLZero C.

(* Constant 2 gated by every clause of phi via imax. *)
Definition gates {n : nat} (phi : CNF n) : VLevel :=
  fold_left VLIMax (map (@clauseLvl n) phi) two.

(* Variable rail consistency gadget: max i+ (imax (imax 2 i+) i-). *)
Definition var (i : nat) : VLevel :=
  VLMax (VLParam (yes i))
        (VLIMax (VLIMax two (VLParam (yes i))) (VLParam (no i))).

(* Rail inconsistency detector and parameter bound over variables 0 .. n-1. *)
Fixpoint small (n : nat) : VLevel :=
  match n with
  | 0 => VLZero
  | S i => VLMax (small i) (var i)
  end.

(* Larger level of the reduction: small n combined with the gated 2. *)
Definition big {n : nat} (phi : CNF n) : VLevel :=
  VLMax (small n) (gates phi).

(* ========================================================================= *)
(* 3. Evaluation Lemmas                                                      *)
(* ========================================================================= *)

Lemma vlevel_imax_nat_eq a b :
  vlevel_imax_nat a b = if Nat.eqb b 0 then 0 else Nat.max a b.
Proof.
  destruct b as [|b']; reflexivity.
Qed.

Lemma eval_two ls : vlevel_eval ls two = 2.
Proof. reflexivity. Qed.

Lemma eval_clauseLvl_cons {n : nat} (l : Lit n) (C : Clause n) ls :
  vlevel_eval ls (clauseLvl (l :: C)) =
  Nat.max (nth (rail l) ls 0) (vlevel_eval ls (clauseLvl C)).
Proof. reflexivity. Qed.

Theorem eval_clauseLvl_le {n : nat} (C : Clause n) ls c :
  (forall l, In l C -> nth (rail l) ls 0 <= c) ->
  vlevel_eval ls (clauseLvl C) <= c.
Proof.
  induction C as [|l C IH]; intros H.
  - simpl. lia.
  - rewrite eval_clauseLvl_cons.
    pose proof (H l (or_introl eq_refl)) as Hl.
    pose proof (IH (fun l' Hl' => H l' (or_intror Hl'))) as HC.
    lia.
Qed.

Theorem eval_clauseLvl_ne_zero {n : nat} (C : Clause n) ls :
  vlevel_eval ls (clauseLvl C) <> 0 <->
  exists l, In l C /\ nth (rail l) ls 0 <> 0.
Proof.
  induction C as [|l C IH].
  - simpl. split.
    + intros H; exfalso; apply H; reflexivity.
    + intros [l [Hin _]]; contradiction.
  - rewrite eval_clauseLvl_cons. split.
    + intros Hnz.
      destruct (Nat.eq_dec (nth (rail l) ls 0) 0) as [Hz | Hpos].
      * assert (HC : vlevel_eval ls (clauseLvl C) <> 0) by lia.
        apply IH in HC as [l' [Hin Hnz']].
        exists l'. split; [right; exact Hin | exact Hnz'].
      * exists l. split; [left; reflexivity | exact Hpos].
    + intros [l' [[Heq | Hin] Hnz]].
      * subst l'. lia.
      * assert (HC : vlevel_eval ls (clauseLvl C) <> 0).
        { apply IH. exists l'. split; assumption. }
        lia.
Qed.

(* Gate fold bounds *)

Theorem eval_foldl_imax_le (gs : list VLevel) ls c (b : VLevel) :
  (forall g, In g gs -> vlevel_eval ls g <= c) ->
  vlevel_eval ls (fold_left VLIMax gs b) <= Nat.max (vlevel_eval ls b) c.
Proof.
  revert b.
  induction gs as [|g gs IH]; intros b Hg; simpl.
  - lia.
  - assert (Hstep : vlevel_eval ls (VLIMax b g) <= Nat.max (vlevel_eval ls b) c).
    { simpl. rewrite vlevel_imax_nat_eq.
      pose proof (Hg g (or_introl eq_refl)) as Hg0.
      destruct (Nat.eqb (vlevel_eval ls g) 0); lia. }
    pose proof (IH (VLIMax b g) (fun g' Hin => Hg g' (or_intror Hin))) as Hrest.
    lia.
Qed.

Theorem eval_foldl_imax_le_of_zero (gs : list VLevel) ls c (b : VLevel) :
  (forall g, In g gs -> vlevel_eval ls g <= c) ->
  (exists g, In g gs /\ vlevel_eval ls g = 0) ->
  vlevel_eval ls (fold_left VLIMax gs b) <= c.
Proof.
  revert b.
  induction gs as [|g gs IH]; intros b Hg [g0 [Hin Hz]]; simpl in *.
  - contradiction.
  - destruct (Nat.eq_dec (vlevel_eval ls g) 0) as [Hg0 | Hgnz].
    + assert (Himax0 : vlevel_eval ls (VLIMax b g) = 0).
      { simpl. rewrite Hg0. reflexivity. }
      pose proof (@eval_foldl_imax_le gs ls c (VLIMax b g)
                    (fun g' Hin' => Hg g' (or_intror Hin'))) as Hbound.
      rewrite Himax0 in Hbound. lia.
    + destruct Hin as [Heq | Hin].
      * subst g0. congruence.
      * apply IH.
        -- intros g' Hin'. apply Hg. right; exact Hin'.
        -- exists g0. split; assumption.
Qed.

Theorem le_eval_foldl_imax (gs : list VLevel) ls (b : VLevel) :
  (forall g, In g gs -> vlevel_eval ls g <> 0) ->
  vlevel_eval ls b <= vlevel_eval ls (fold_left VLIMax gs b).
Proof.
  revert b.
  induction gs as [|g gs IH]; intros b Hg; simpl.
  - lia.
  - assert (Hstep : vlevel_eval ls b <= vlevel_eval ls (VLIMax b g)).
    { simpl. rewrite vlevel_imax_nat_eq.
      pose proof (Hg g (or_introl eq_refl)) as Hnz.
      destruct (Nat.eqb (vlevel_eval ls g) 0) eqn:Heqb.
      - apply Nat.eqb_eq in Heqb. congruence.
      - lia. }
    pose proof (IH (VLIMax b g) (fun g' Hin => Hg g' (or_intror Hin))) as Hrest.
    lia.
Qed.

(* Variable summand evaluation *)

Theorem eval_var_eq i ls :
  vlevel_eval ls (var i) =
    if Nat.eqb (nth (no i) ls 0) 0 then nth (yes i) ls 0
    else if Nat.eqb (nth (yes i) ls 0) 0 then nth (no i) ls 0
    else Nat.max 2 (Nat.max (nth (yes i) ls 0) (nth (no i) ls 0)).
Proof.
  unfold var. cbn [vlevel_eval two].
  destruct (nth (no i) ls 0) as [|b];
    destruct (nth (yes i) ls 0) as [|a];
    cbn [vlevel_imax_nat Nat.eqb]; lia.
Qed.

Theorem yes_le_eval_var i ls :
  nth (yes i) ls 0 <= vlevel_eval ls (var i).
Proof.
  rewrite eval_var_eq.
  destruct (Nat.eqb (nth (no i) ls 0) 0) eqn:Hno.
  - lia.
  - destruct (Nat.eqb (nth (yes i) ls 0) 0) eqn:Hyes.
    + apply Nat.eqb_eq in Hyes. lia.
    + lia.
Qed.

Theorem no_le_eval_var i ls :
  nth (no i) ls 0 <= vlevel_eval ls (var i).
Proof.
  rewrite eval_var_eq.
  destruct (Nat.eqb (nth (no i) ls 0) 0) eqn:Hno.
  - apply Nat.eqb_eq in Hno. lia.
  - destruct (Nat.eqb (nth (yes i) ls 0) 0); lia.
Qed.

Theorem two_le_eval_var i ls :
  nth (yes i) ls 0 <> 0 ->
  nth (no i) ls 0 <> 0 ->
  2 <= vlevel_eval ls (var i).
Proof.
  intros Hyes Hno. rewrite eval_var_eq.
  apply Nat.eqb_neq in Hyes. apply Nat.eqb_neq in Hno.
  rewrite Hno, Hyes. lia.
Qed.

Theorem eval_var_le_one i ls :
  (nth (yes i) ls 0 = 0 \/ nth (no i) ls 0 = 0) ->
  nth (yes i) ls 0 <= 1 ->
  nth (no i) ls 0 <= 1 ->
  vlevel_eval ls (var i) <= 1.
Proof.
  intros Hex H1 H2. rewrite eval_var_eq.
  destruct (Nat.eqb (nth (no i) ls 0) 0) eqn:Hno; [lia|].
  destruct (Nat.eqb (nth (yes i) ls 0) 0) eqn:Hyes; [lia|].
  apply Nat.eqb_neq in Hno. apply Nat.eqb_neq in Hyes.
  destruct Hex; congruence.
Qed.

Theorem le_eval_small n j ls :
  j < 2 * n -> nth j ls 0 <= vlevel_eval ls (small n).
Proof.
  induction n as [|n IH]; intros Hj.
  - lia.
  - cbn [small vlevel_eval]. destruct (lt_dec j (2 * n)) as [Hlt | Hge].
    + specialize (IH Hlt). lia.
    + assert (Hor : j = yes n \/ j = no n) by (unfold yes, no; lia).
      destruct Hor as [-> | ->].
      * pose proof (yes_le_eval_var n ls). lia.
      * pose proof (no_le_eval_var n ls). lia.
Qed.

Theorem two_le_eval_small n i ls :
  i < n ->
  nth (yes i) ls 0 <> 0 ->
  nth (no i) ls 0 <> 0 ->
  2 <= vlevel_eval ls (small n).
Proof.
  induction n as [|n IH]; intros Hi Hyes Hno.
  - lia.
  - cbn [small vlevel_eval]. assert (Hor : i < n \/ i = n) by lia.
    destruct Hor as [Hlt | ->].
    + specialize (IH Hlt Hyes Hno). lia.
    + pose proof (@two_le_eval_var n ls Hyes Hno). lia.
Qed.

Theorem eval_small_le_one n ls :
  (forall i, i < n -> nth (yes i) ls 0 = 0 \/ nth (no i) ls 0 = 0) ->
  (forall j, j < 2 * n -> nth j ls 0 <= 1) ->
  vlevel_eval ls (small n) <= 1.
Proof.
  induction n as [|n IH]; intros Hex H1.
  - cbn [small vlevel_eval]. lia.
  - cbn [small vlevel_eval].
    assert (IH' : vlevel_eval ls (small n) <= 1).
    { apply IH.
      - intros i Hi. apply Hex. lia.
      - intros j Hj. apply H1. lia. }
    assert (Hvar : vlevel_eval ls (var n) <= 1).
    { apply eval_var_le_one.
      - apply Hex. lia.
      - apply H1. unfold yes. lia.
      - apply H1. unfold no. lia. }
    lia.
Qed.

(* ========================================================================= *)
(* 4. Dual-Rail Encoding of a Boolean Assignment                             *)
(* ========================================================================= *)

Definition railVal (a : nat -> bool) (j : nat) : nat :=
  if Bool.eqb (a (j / 2)) (Nat.eqb (j mod 2) 0) then 1 else 0.

Definition railList (n : nat) (a : nat -> bool) : list nat :=
  map (railVal a) (seq 0 (2 * n)).

Definition ofFin {n : nat} (a : Fin n -> bool) (i : nat) : bool :=
  match Bool.bool_dec (i <? n) true with
  | left h => a (mkFin i h)
  | right _ => false
  end.

Lemma ofFin_val {n : nat} (a : Fin n -> bool) (i : Fin n) :
  ofFin a (fin_val i) = a i.
Proof.
  unfold ofFin.
  destruct (Bool.bool_dec (fin_val i <? n) true) as [h | hn].
  - f_equal. apply Fin_eq. reflexivity.
  - exfalso. exact (hn (fin_ltb i)).
Qed.

Theorem railVal_le a j : railVal a j <= 1.
Proof.
  unfold railVal. destruct (Bool.eqb _ _); lia.
Qed.

Theorem railVal_yes a i :
  railVal a (yes i) = if a i then 1 else 0.
Proof.
  unfold railVal.
  assert (Hdiv : yes i / 2 = i).
  { symmetry. apply (Nat.div_unique (yes i) 2 i 0); unfold yes; lia. }
  assert (Hmod : yes i mod 2 = 0).
  { symmetry. apply (Nat.mod_unique (yes i) 2 i 0); unfold yes; lia. }
  rewrite Hdiv, Hmod. simpl.
  destruct (a i); reflexivity.
Qed.

Theorem railVal_no a i :
  railVal a (no i) = if negb (a i) then 1 else 0.
Proof.
  unfold railVal.
  assert (Hdiv : no i / 2 = i).
  { symmetry. apply (Nat.div_unique (no i) 2 i 1); unfold no; lia. }
  assert (Hmod : no i mod 2 = 1).
  { symmetry. apply (Nat.mod_unique (no i) 2 i 1); unfold no; lia. }
  rewrite Hdiv, Hmod. simpl.
  destruct (a i); reflexivity.
Qed.

Theorem railVal_rail {n : nat} a (l : Lit n) :
  railVal a (rail l) = if Bool.eqb (a (fin_val (fst l))) (snd l) then 1 else 0.
Proof.
  destruct (snd l) eqn:Hb.
  - rewrite (@rail_pos n l Hb), railVal_yes.
    destruct (a (fin_val (fst l))); reflexivity.
  - rewrite (@rail_neg n l Hb), railVal_no.
    destruct (a (fin_val (fst l))); reflexivity.
Qed.

Theorem nth_railList a n j :
  nth j (railList n a) 0 = if j <? 2 * n then railVal a j else 0.
Proof.
  unfold railList.
  destruct (j <? 2 * n) eqn:Hlt.
  - apply Nat.ltb_lt in Hlt.
    rewrite nth_indep with (d' := railVal a 0) by (rewrite length_map, length_seq; exact Hlt).
    rewrite map_nth, seq_nth by exact Hlt. simpl. reflexivity.
  - apply Nat.ltb_ge in Hlt.
    apply nth_overflow. rewrite length_map, length_seq. exact Hlt.
Qed.

Theorem nth_railList_le a n j :
  nth j (railList n a) 0 <= 1.
Proof.
  rewrite nth_railList. destruct (j <? 2 * n); [apply railVal_le | lia].
Qed.

Theorem nth_railList_yes a n i :
  i < n -> nth (yes i) (railList n a) 0 = if a i then 1 else 0.
Proof.
  intros Hi. rewrite nth_railList.
  assert (Hlt : (yes i <? 2 * n) = true) by (apply Nat.ltb_lt; unfold yes; lia).
  rewrite Hlt. apply railVal_yes.
Qed.

Theorem nth_railList_no a n i :
  i < n -> nth (no i) (railList n a) 0 = if negb (a i) then 1 else 0.
Proof.
  intros Hi. rewrite nth_railList.
  assert (Hlt : (no i <? 2 * n) = true) by (apply Nat.ltb_lt; unfold no; lia).
  rewrite Hlt. apply railVal_no.
Qed.

Theorem nth_railList_rail {n : nat} a (l : Lit n) :
  nth (rail l) (railList n a) 0 =
  if Bool.eqb (a (fin_val (fst l))) (snd l) then 1 else 0.
Proof.
  rewrite nth_railList.
  assert (Hlt : (rail l <? 2 * n) = true) by (apply Nat.ltb_lt; apply rail_lt).
  rewrite Hlt. apply railVal_rail.
Qed.

(* ========================================================================= *)
(* 5. Main coNP-Hardness Reduction Theorems                                  *)
(* ========================================================================= *)

Theorem small_le_big {n : nat} (phi : CNF n) :
  vlevel_le (small n) (big phi).
Proof.
  intros ls. unfold big. cbn [vlevel_eval]. apply Nat.le_max_l.
Qed.

Theorem big_equiv_small_iff_unsat {n : nat} (phi : CNF n) :
  vlevel_equiv (big phi) (small n) <-> ~ Sat phi.
Proof.
  split.
  - (* Satisfying assignment produces a railList point where big = 2 and small <= 1 *)
    intros Heq [a Ha].
    set (ls := railList n (ofFin a)).
    specialize (Heq ls).
    assert (Hsmall : vlevel_eval ls (small n) <= 1).
    { apply eval_small_le_one.
      - intros i Hi. unfold ls.
        rewrite (@nth_railList_yes (ofFin a) n i Hi), (@nth_railList_no (ofFin a) n i Hi).
        destruct (ofFin a i); simpl; [right | left]; reflexivity.
      - intros j _. unfold ls. apply nth_railList_le. }
    assert (Hgates : 2 <= vlevel_eval ls (gates phi)).
    { unfold gates. change 2 with (vlevel_eval ls two) at 1.
      apply le_eval_foldl_imax.
      intros g Hin. apply in_map_iff in Hin as [C [<- HC]].
      destruct (Ha C HC) as [l [Hl Hal]].
      apply eval_clauseLvl_ne_zero.
      exists l. split; [exact Hl |].
      unfold ls. rewrite nth_railList_rail.
      rewrite ofFin_val, Hal, Bool.eqb_reflx. discriminate. }
    unfold big in Heq. cbn [vlevel_eval] in Heq. lia.
  - (* Conversely, any witness ls where big != small decodes to a satisfying assignment *)
    intros Hunsat ls.
    destruct (Nat.eq_dec (vlevel_eval ls (big phi)) (vlevel_eval ls (small n))) as [Heq | Hneq];
      [exact Heq |].
    exfalso. apply Hunsat.
    assert (Hcl : forall C : Clause n, vlevel_eval ls (clauseLvl C) <= vlevel_eval ls (small n)).
    { intros C. apply eval_clauseLvl_le.
      intros l _. apply le_eval_small. apply rail_lt. }
    exists (fun i : Fin n => negb (Nat.eqb (nth (yes (fin_val i)) ls 0) 0)).
    intros C HC.
    unfold big in Hneq. cbn [vlevel_eval] in Hneq.
    assert (Hcz : vlevel_eval ls (clauseLvl C) <> 0).
    { intros Hz.
      assert (Hgle : vlevel_eval ls (gates phi) <= vlevel_eval ls (small n)).
      { unfold gates.
        eapply eval_foldl_imax_le_of_zero.
        - intros g Hin. apply in_map_iff in Hin as [C' [<- _]]. apply Hcl.
        - exists (clauseLvl C). split; [apply in_map; exact HC | exact Hz]. }
      lia. }
    apply eval_clauseLvl_ne_zero in Hcz as [l [Hl Hlnz]].
    exists l. split; [exact Hl |].
    destruct (snd l) eqn:Hpol.
    + rewrite (@rail_pos n l Hpol) in Hlnz.
      apply Nat.eqb_neq in Hlnz. rewrite Hlnz. reflexivity.
    + rewrite (@rail_neg n l Hpol) in Hlnz.
      destruct (Nat.eqb (nth (yes (fin_val (fst l))) ls 0) 0) eqn:Hyes.
      * reflexivity.
      * exfalso.
        apply Nat.eqb_neq in Hyes.
        pose proof (@two_le_eval_small n (fin_val (fst l)) ls (fin_isLt (fst l)) Hyes Hlnz) as H2le.
        assert (Hub : vlevel_eval ls (gates phi) <= Nat.max 2 (vlevel_eval ls (small n))).
        { unfold gates. change 2 with (vlevel_eval ls two).
          apply eval_foldl_imax_le.
          intros g Hin. apply in_map_iff in Hin as [C' [<- _]]. apply Hcl. }
        lia.
Qed.

Theorem equiv_iff_unsat {n : nat} (phi : CNF n) :
  vlevel_equiv (small n) (big phi) <-> ~ Sat phi.
Proof.
  rewrite <- big_equiv_small_iff_unsat.
  split; apply vlevel_equiv_symm.
Qed.

Theorem le_iff_unsat {n : nat} (phi : CNF n) :
  vlevel_le (big phi) (small n) <-> ~ Sat phi.
Proof.
  rewrite <- big_equiv_small_iff_unsat, vlevel_equiv_le_iff.
  pose proof (small_le_big phi) as Hsb.
  tauto.
Qed.

(* ========================================================================= *)
(* 6. Linear Size Bounds                                                     *)
(* ========================================================================= *)

Fixpoint vlevel_size (u : VLevel) : nat :=
  match u with
  | VLZero | VLParam _ => 1
  | VLSucc l => vlevel_size l + 1
  | VLMax a b | VLIMax a b => vlevel_size a + vlevel_size b + 1
  end.

Definition cnfSize {n : nat} (phi : CNF n) : nat :=
  list_sum (map (fun C : Clause n => List.length C + 1) phi).

Theorem size_two : vlevel_size two = 3.
Proof. reflexivity. Qed.

Theorem size_clauseLvl {n : nat} (C : Clause n) :
  vlevel_size (clauseLvl C) = 2 * List.length C + 1.
Proof.
  induction C as [|l C IH]; unfold clauseLvl in *; cbn [fold_right vlevel_size List.length]; lia.
Qed.

Theorem size_foldl_imax (gs : list VLevel) (b : VLevel) :
  vlevel_size (fold_left VLIMax gs b) =
  vlevel_size b + list_sum (map (fun g => vlevel_size g + 1) gs).
Proof.
  revert b.
  induction gs as [|g gs IH]; intros b; simpl.
  - lia.
  - rewrite IH. simpl. lia.
Qed.

Theorem size_gates {n : nat} (phi : CNF n) :
  vlevel_size (gates phi) = 2 * cnfSize phi + 3.
Proof.
  unfold gates. rewrite size_foldl_imax, size_two.
  assert (Hsum : list_sum (map (fun g => vlevel_size g + 1) (map (@clauseLvl n) phi)) =
                 2 * cnfSize phi).
  { induction phi as [|C phi' IH]; unfold cnfSize in *; simpl in *.
    - reflexivity.
    - rewrite size_clauseLvl, IH. lia. }
  lia.
Qed.

Theorem size_var i : vlevel_size (var i) = 9.
Proof. reflexivity. Qed.

Theorem size_small n : vlevel_size (small n) = 10 * n + 1.
Proof.
  induction n as [|n IH]; cbn [small vlevel_size]; [reflexivity |].
  rewrite IH, size_var. lia.
Qed.

Theorem size_big {n : nat} (phi : CNF n) :
  vlevel_size (big phi) = 10 * n + 2 * cnfSize phi + 5.
Proof.
  unfold big. cbn [vlevel_size]. rewrite size_small, size_gates. lia.
Qed.

(* ========================================================================= *)
(* 7. Concrete Worked Instances                                              *)
(* ========================================================================= *)

Definition fin0_1 : Fin 1 := @mkFin 1 0 eq_refl.

(* x_0 /\ ~x_0 is unsatisfiable *)
Definition selfContradiction : CNF 1 :=
  [[(fin0_1, true)]; [(fin0_1, false)]].

Theorem not_sat_selfContradiction : ~ Sat selfContradiction.
Proof.
  intros [a Ha].
  destruct (Ha [(fin0_1, true)] (or_introl eq_refl)) as [l1 [[Heq1 | []] Hsat1]].
  destruct (Ha [(fin0_1, false)] (or_intror (or_introl eq_refl))) as [l2 [[Heq2 | []] Hsat2]].
  subst l1 l2. simpl in Hsat1, Hsat2. congruence.
Qed.

Example equiv_selfContradiction :
  vlevel_equiv (small 1) (big selfContradiction).
Proof.
  apply equiv_iff_unsat. exact not_sat_selfContradiction.
Qed.

(* Single positive clause [[(0, true)]] is satisfiable and distinguishes big from small at [1; 0]. *)
Definition singlePos : CNF 1 := [[(fin0_1, true)]].

Example sat_singlePos : Sat singlePos.
Proof.
  exists (fun _ => true).
  intros C [<- | []].
  exists (fin0_1, true). split; [left; reflexivity | reflexivity].
Qed.

Example not_equiv_singlePos : ~ vlevel_equiv (small 1) (big singlePos).
Proof.
  intros Heq. apply (proj1 (equiv_iff_unsat singlePos) Heq). exact sat_singlePos.
Qed.

Example eval_singlePos_witness :
  vlevel_eval [1; 0] (big singlePos) = 2 /\ vlevel_eval [1; 0] (small 1) = 1.
Proof.
  split; reflexivity.
Qed.

(* ========================================================================= *)
(* Axiom Audit                                                               *)
(* ========================================================================= *)

Print Assumptions small_le_big.
Print Assumptions equiv_iff_unsat.
Print Assumptions big_equiv_small_iff_unsat.
Print Assumptions le_iff_unsat.
Print Assumptions size_big.
Print Assumptions not_sat_selfContradiction.
Print Assumptions equiv_selfContradiction.
