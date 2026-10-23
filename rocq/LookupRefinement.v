(* SPDX-License-Identifier: Apache-2.0
   Pointwise implementation refinement; no functional extensionality. *)
From Stdlib Require Import List Bool Arith NArith.
From LeanPort Require Import Syntax Universes EagerPolicy NatProbeDispatch WhnfPolicy Checker LookupCore.
Import ListNotations.

Record methods_equivalent (a b : methods) : Prop := {
  same_infer : forall g e, infer_method a g e = infer_method b g e;
  same_infer_type : forall g e, infer_type_method a g e = infer_type_method b g e;
  same_whnf : forall g e, whnf_method a g e = whnf_method b g e;
  same_whnf_core : forall cheap g e,
    whnf_core_method a cheap g e = whnf_core_method b cheap g e;
  same_defeq : forall g t s, defeq_method a g t s = defeq_method b g t s;
  same_mode : method_mode a = method_mode b;
  same_eager_defeq : forall g t s,
    eager_defeq_method a g t s = eager_defeq_method b g t s
}.
Lemma methods_equivalent_refl m : methods_equivalent m m.
Proof. constructor; reflexivity. Qed.
Lemma nat_probe_allowed_refines a b t s : methods_equivalent a b ->
  nat_probe_allowed (method_mode a) t s = nat_probe_allowed (method_mode b) t s.
Proof. intro H. rewrite (same_mode _ _ H). reflexivity. Qed.
Lemma true_probe_allowed_refines a b t : methods_equivalent a b ->
  true_probe_allowed (method_mode a) t = true_probe_allowed (method_mode b) t.
Proof. intro H. rewrite (same_mode _ _ H). reflexivity. Qed.
Lemma inference_only_equivalent a b : methods_equivalent a b ->
  methods_equivalent (Accessor.inference_only a) (Checker.inference_only b).
Proof. intros [Hi Ht Hw Hc Hd Hmode He]; constructor; assumption. Qed.
Lemma checking_view_equivalent (checking : bool) a b : methods_equivalent a b ->
  methods_equivalent (if checking then a else Accessor.inference_only a)
    (if checking then b else Checker.inference_only b).
Proof. destruct checking; auto using inference_only_equivalent. Qed.
Lemma reduction_view_equivalent (cheap : bool) a b : methods_equivalent a b ->
  forall g e,
    (if cheap then whnf_core_method a true else whnf_method a) g e =
    (if cheap then whnf_core_method b true else whnf_method b) g e.
Proof. intros Hm g e. destruct cheap; eauto using same_whnf, same_whnf_core. Qed.

Lemma bind_pointwise {A B} (x y : result A) (f h : A -> result B) :
  x = y -> (forall a, f a = h a) -> bind x f = bind y h.
Proof. intros -> H. destruct y; simpl; auto. Qed.

Create HintDb lookup_refinement.
#[local] Hint Resolve same_infer same_infer_type same_whnf same_whnf_core same_defeq
  same_mode same_eager_defeq
  nat_probe_allowed_refines true_probe_allowed_refines
  methods_equivalent_refl inference_only_equivalent checking_view_equivalent
  reduction_view_equivalent : lookup_refinement.

Ltac pointwise :=
  first [reflexivity | solve [eauto 4 with lookup_refinement] |
    progress cbn beta iota zeta; pointwise |
    lazymatch goal with
    | |- @bind ?A ?B ?x ?f = @bind ?A ?B ?y ?h =>
        apply bind_pointwise; [pointwise | intro; pointwise]
    | |- (match ?x with _ => _ end) = (match ?x with _ => _ end) =>
        destruct x; pointwise
    | |- (match ?x with _ => _ end) = (match ?y with _ => _ end) =>
        let H := fresh "Hscrutinee" in
        assert (H : x = y) by pointwise;
        rewrite H; destruct y; pointwise
    | |- (if ?c then _ else _) = _ => destruct c; pointwise
    | |- ?f ?x1 ?x2 = ?f ?y1 ?y2 => f_equal; pointwise
    | |- ?f ?x = ?f ?y => f_equal; pointwise
    end | match goal with |- ?G => idtac "Unsolved:" G; fail 1 end].

Lemma application_type_defeq_refines a b g argument domain argument_type :
  methods_equivalent a b ->
  application_type_defeq a g argument domain argument_type =
    application_type_defeq b g argument domain argument_type.
Proof. intro Hm. unfold application_type_defeq. pointwise. Qed.
#[local] Hint Resolve application_type_defeq_refines : lookup_refinement.

Section Refinement.
Variable resolve : name -> environment -> option declaration.
Variable env : environment.
Hypothesis lookup_correct : forall n, resolve n env = find_decl n env.
#[local] Hint Resolve lookup_correct : lookup_refinement.

Lemma nat_probe_head_refines e :
  nat_probe_head resolve Accessor.core_succ_name env (Accessor.core_spine e []) =
    nat_probe_head find_decl Checker.core_succ_name env (Checker.core_spine e []).
Proof. unfold nat_probe_head. pointwise. Qed.
#[local] Hint Resolve nat_probe_head_refines : lookup_refinement.

Lemma pair_probe_guard_refines a b t s : methods_equivalent a b ->
  pair_probe_guard
    (nat_probe_head resolve Accessor.core_succ_name env (Accessor.core_spine t []))
    (nat_probe_head resolve Accessor.core_succ_name env (Accessor.core_spine s []))
    (fun _ => nat_probe_allowed (method_mode a) t s) =
  pair_probe_guard
    (nat_probe_head find_decl Checker.core_succ_name env (Checker.core_spine t []))
    (nat_probe_head find_decl Checker.core_succ_name env (Checker.core_spine s []))
    (fun _ => nat_probe_allowed (method_mode b) t s).
Proof. intro Hm. unfold pair_probe_guard. pointwise. Qed.
#[local] Hint Resolve pair_probe_guard_refines : lookup_refinement.

Lemma core_inductive_refines n :
  Accessor.core_inductive resolve env n = Checker.core_inductive env n.
Proof. unfold Accessor.core_inductive, Checker.core_inductive. pointwise. Qed.
#[local] Hint Resolve core_inductive_refines : lookup_refinement.

Lemma core_constructor_refines n :
  Accessor.core_constructor resolve env n = Checker.core_constructor env n.
Proof. unfold Accessor.core_constructor, Checker.core_constructor. pointwise. Qed.
#[local] Hint Resolve core_constructor_refines : lookup_refinement.

Lemma core_structure_refines n :
  Accessor.core_structure resolve env n = Checker.core_structure env n.
Proof. unfold Accessor.core_structure, Checker.core_structure. pointwise. Qed.
#[local] Hint Resolve core_structure_refines : lookup_refinement.

Lemma core_ctor_shape_refines n parent index fields ty :
  Accessor.core_ctor_shape resolve env n parent index fields ty =
    Checker.core_ctor_shape env n parent index fields ty.
Proof. unfold Accessor.core_ctor_shape, Checker.core_ctor_shape. pointwise. Qed.
#[local] Hint Resolve core_ctor_shape_refines : lookup_refinement.

Lemma core_nat_ready_refines :
  Accessor.core_nat_ready resolve env = Checker.core_nat_ready env.
Proof. unfold Accessor.core_nat_ready, Checker.core_nat_ready. pointwise. Qed.
#[local] Hint Resolve core_nat_ready_refines : lookup_refinement.

Lemma core_bool_ready_refines :
  Accessor.core_bool_ready resolve env = Checker.core_bool_ready env.
Proof. unfold Accessor.core_bool_ready, Checker.core_bool_ready. pointwise. Qed.
#[local] Hint Resolve core_bool_ready_refines : lookup_refinement.

Lemma core_string_ready_refines :
  Accessor.core_string_ready resolve env = Checker.core_string_ready env.
Proof. unfold Accessor.core_string_ready, Checker.core_string_ready. pointwise. Qed.
#[local] Hint Resolve core_string_ready_refines : lookup_refinement.

Lemma core_supported_refines e :
  Accessor.core_supported resolve env e = Checker.core_supported env e.
Proof.
  induction e; cbn [Accessor.core_supported Checker.core_supported];
    try (destruct l); pointwise.
Qed.
#[local] Hint Resolve core_supported_refines : lookup_refinement.

Lemma get_constant_refines ps n us :
  Accessor.get_constant resolve env ps n us = Checker.get_constant env ps n us.
Proof. unfold Accessor.get_constant, Checker.get_constant. pointwise. Qed.
#[local] Hint Resolve get_constant_refines : lookup_refinement.

Lemma sort_of_refines a b g e : methods_equivalent a b ->
  Accessor.sort_of a g e = Checker.sort_of b g e.
Proof. intro Hm. unfold Accessor.sort_of, Checker.sort_of. pointwise. Qed.
#[local] Hint Resolve sort_of_refines : lookup_refinement.

Lemma core_apply_type_refines a b g ty args : methods_equivalent a b ->
  Accessor.core_apply_type a g ty args = Checker.core_apply_type b g ty args.
Proof.
  intro Hm. revert ty. induction args; intro ty;
    cbn [Accessor.core_apply_type Checker.core_apply_type]; pointwise.
Qed.
#[local] Hint Resolve core_apply_type_refines : lookup_refinement.

Lemma core_projection_field_refines a b fuel g owner value prop skip index ty :
  methods_equivalent a b ->
  Accessor.core_projection_field a fuel g owner value prop skip index ty =
    Checker.core_projection_field b fuel g owner value prop skip index ty.
Proof.
  intro Hm. revert index ty. induction skip; intros index ty;
    cbn [Accessor.core_projection_field Checker.core_projection_field]; pointwise.
Qed.
#[local] Hint Resolve core_projection_field_refines : lookup_refinement.

Lemma core_infer_projection_refines a b fuel g owner index value :
  methods_equivalent a b ->
  Accessor.core_infer_projection resolve a fuel env g owner index value =
    Checker.core_infer_projection b fuel env g owner index value.
Proof.
  intro Hm. unfold Accessor.core_infer_projection, Checker.core_infer_projection. pointwise.
Qed.
#[local] Hint Resolve core_infer_projection_refines : lookup_refinement.

Lemma core_binary_nat_refines fuel op a b :
  Accessor.core_binary_nat resolve fuel env op a b = Checker.core_binary_nat fuel env op a b.
Proof. destruct op; unfold Accessor.core_binary_nat, Checker.core_binary_nat; pointwise. Qed.
#[local] Hint Resolve core_binary_nat_refines : lookup_refinement.

Lemma core_reduce_nat_refines a b fuel g e : methods_equivalent a b ->
  Accessor.core_reduce_nat resolve a fuel env g e = Checker.core_reduce_nat b fuel env g e.
Proof. intro Hm. unfold Accessor.core_reduce_nat, Checker.core_reduce_nat. pointwise. Qed.
#[local] Hint Resolve core_reduce_nat_refines : lookup_refinement.

Lemma core_make_structure_refines owner us args value :
  Accessor.core_make_structure resolve env owner us args value =
    Checker.core_make_structure env owner us args value.
Proof. unfold Accessor.core_make_structure, Checker.core_make_structure. pointwise. Qed.
#[local] Hint Resolve core_make_structure_refines : lookup_refinement.

Lemma core_to_constructor_refines a b fuel g owner k value : methods_equivalent a b ->
  Accessor.core_to_constructor resolve a fuel env g owner k value =
    Checker.core_to_constructor b fuel env g owner k value.
Proof. intro Hm. unfold Accessor.core_to_constructor, Checker.core_to_constructor. pointwise. Qed.
#[local] Hint Resolve core_to_constructor_refines : lookup_refinement.

Lemma core_reduce_recursor_refines a b fuel g e : methods_equivalent a b ->
  Accessor.core_reduce_recursor resolve a fuel env g e = Checker.core_reduce_recursor b fuel env g e.
Proof. intro Hm. unfold Accessor.core_reduce_recursor, Checker.core_reduce_recursor. pointwise. Qed.
#[local] Hint Resolve core_reduce_recursor_refines : lookup_refinement.

Lemma core_reduce_projection_with_refines a b reduce1 reduce2 g owner index value :
  methods_equivalent a b -> (forall g e, reduce1 g e = reduce2 g e) ->
  Accessor.core_reduce_projection_with resolve a reduce1 env g owner index value =
    Checker.core_reduce_projection_with b reduce2 env g owner index value.
Proof.
  intros Hm Hr. unfold Accessor.core_reduce_projection_with, Checker.core_reduce_projection_with.
  pointwise.
Qed.
#[local] Hint Resolve core_reduce_projection_with_refines : lookup_refinement.

Lemma core_reduce_projection_refines a b g owner index value : methods_equivalent a b ->
  Accessor.core_reduce_projection resolve a env g owner index value =
    Checker.core_reduce_projection b env g owner index value.
Proof.
  intro Hm. unfold Accessor.core_reduce_projection, Checker.core_reduce_projection. pointwise.
Qed.
#[local] Hint Resolve core_reduce_projection_refines : lookup_refinement.

Lemma core_reduce_quotient_refines a b g e : methods_equivalent a b ->
  Accessor.core_reduce_quotient resolve a env g e = Checker.core_reduce_quotient b env g e.
Proof. intro Hm. unfold Accessor.core_reduce_quotient, Checker.core_reduce_quotient. pointwise. Qed.
#[local] Hint Resolve core_reduce_quotient_refines : lookup_refinement.

Lemma core_reduce_head_refines a b fuel g e : methods_equivalent a b ->
  Accessor.core_reduce_head resolve a fuel env g e = Checker.core_reduce_head b fuel env g e.
Proof. intro Hm. unfold Accessor.core_reduce_head, Checker.core_reduce_head. pointwise. Qed.
#[local] Hint Resolve core_reduce_head_refines : lookup_refinement.

Lemma infer_step_refines a b fuel ps checking g e : methods_equivalent a b ->
  Accessor.infer_step resolve a fuel env ps checking g e =
    Checker.infer_step b fuel env ps checking g e.
Proof.
  intro Hm. revert checking g. induction e; intros checking g;
    cbn [Accessor.infer_step Checker.infer_step]; try (destruct l); pointwise.
Qed.
#[local] Hint Resolve infer_step_refines : lookup_refinement.

Lemma core_unfold_refines ps e :
  Accessor.core_unfold resolve env ps e = Checker.core_unfold env ps e.
Proof. unfold Accessor.core_unfold, Checker.core_unfold. pointwise. Qed.
#[local] Hint Resolve core_unfold_refines : lookup_refinement.

Lemma whnf_core_step_refines a b fuel ps cheap g e : methods_equivalent a b ->
  Accessor.whnf_core_step resolve a fuel env ps cheap g e =
    Checker.whnf_core_step b fuel env ps cheap g e.
Proof. intro Hm. unfold Accessor.whnf_core_step, Checker.whnf_core_step. pointwise. Qed.
#[local] Hint Resolve whnf_core_step_refines : lookup_refinement.

Lemma whnf_step_refines a b fuel ps g e : methods_equivalent a b ->
  Accessor.whnf_step resolve a fuel env ps g e = Checker.whnf_step b fuel env ps g e.
Proof. intro Hm. unfold Accessor.whnf_step, Checker.whnf_step. pointwise. Qed.
#[local] Hint Resolve whnf_step_refines : lookup_refinement.

Lemma finish_whnf_unfold_refines ps e :
  Accessor.finish_whnf_unfold resolve env ps e = Checker.finish_whnf_unfold env ps e.
Proof.
  unfold Accessor.finish_whnf_unfold, Checker.finish_whnf_unfold.
  rewrite core_unfold_refines. reflexivity.
Qed.

Lemma whnf_round_step_refines a b fuel ps g e : methods_equivalent a b ->
  Accessor.whnf_round_step resolve a fuel env ps g e =
    Checker.whnf_round_step b fuel env ps g e.
Proof.
  intro Hm. unfold Accessor.whnf_round_step, Checker.whnf_round_step.
  rewrite (whnf_core_step_refines a b fuel ps false g e Hm).
  apply bind_pointwise; [reflexivity|]. intro reduced.
  destruct reduced; cbn [bind].
  all: try (rewrite (core_reduce_nat_refines a b fuel g _ Hm);
    apply bind_pointwise; [reflexivity|]; intros [value|];
    [reflexivity|apply finish_whnf_unfold_refines]).
  rewrite core_nat_ready_refines.
  replace Accessor.core_zero_name with Checker.core_zero_name by reflexivity.
  destruct (name_eqb n Checker.core_zero_name && Checker.core_nat_ready env);
    [reflexivity|apply finish_whnf_unfold_refines].
Qed.

Lemma whnf_loop_refines rounds a b fuel ps g e : methods_equivalent a b ->
  Accessor.whnf_loop resolve rounds a fuel env ps g e =
    Checker.whnf_loop rounds b fuel env ps g e.
Proof.
  intro Hm. unfold Accessor.whnf_loop, Checker.whnf_loop.
  apply run_whnf_rounds_extensional. intro term.
  apply whnf_round_step_refines. exact Hm.
Qed.
#[local] Hint Resolve whnf_loop_refines : lookup_refinement.

Lemma eta_compare_refines a b g domain body other : methods_equivalent a b ->
  Accessor.eta_compare a g domain body other = Checker.eta_compare b g domain body other.
Proof. intro Hm. unfold Accessor.eta_compare, Checker.eta_compare. pointwise. Qed.
#[local] Hint Resolve eta_compare_refines : lookup_refinement.

Lemma core_compare_args_refines a b g xs ys : methods_equivalent a b ->
  Accessor.core_compare_args a g xs ys = Checker.core_compare_args b g xs ys.
Proof.
  intro Hm. revert ys. induction xs; intros [|y ys];
    cbn [Accessor.core_compare_args Checker.core_compare_args]; pointwise.
Qed.
#[local] Hint Resolve core_compare_args_refines : lookup_refinement.

Lemma core_congruent_apps_refines a b fuel g t s : methods_equivalent a b ->
  Accessor.core_congruent_apps a fuel g t s = Checker.core_congruent_apps b fuel g t s.
Proof. intro Hm. unfold Accessor.core_congruent_apps, Checker.core_congruent_apps. pointwise. Qed.
#[local] Hint Resolve core_congruent_apps_refines : lookup_refinement.

Lemma core_delta_info_refines e :
  Accessor.core_delta_info resolve env e = Checker.core_delta_info env e.
Proof. unfold Accessor.core_delta_info, Checker.core_delta_info. pointwise. Qed.
#[local] Hint Resolve core_delta_info_refines : lookup_refinement.

Lemma core_delta_sides_refines t s :
  Accessor.core_delta_sides resolve env t s = Checker.core_delta_sides env t s.
Proof. unfold Accessor.core_delta_sides, Checker.core_delta_sides. pointwise. Qed.
#[local] Hint Resolve core_delta_sides_refines : lookup_refinement.

Lemma core_delta_head_refines e :
  Accessor.core_delta_head resolve env e = Checker.core_delta_head env e.
Proof. unfold Accessor.core_delta_head, Checker.core_delta_head. pointwise. Qed.
#[local] Hint Resolve core_delta_head_refines : lookup_refinement.

Lemma core_erasing_delta_refines e :
  Accessor.core_erasing_delta resolve env e = Checker.core_erasing_delta env e.
Proof. unfold Accessor.core_erasing_delta, Checker.core_erasing_delta. pointwise. Qed.
#[local] Hint Resolve core_erasing_delta_refines : lookup_refinement.

Lemma core_delta_congruent_refines a b fuel g t s : methods_equivalent a b ->
  Accessor.core_delta_congruent resolve a fuel env g t s =
    Checker.core_delta_congruent b fuel env g t s.
Proof. intro Hm. unfold Accessor.core_delta_congruent, Checker.core_delta_congruent. pointwise. Qed.
#[local] Hint Resolve core_delta_congruent_refines : lookup_refinement.

Lemma compare_heads_refines a b fuel g t s : methods_equivalent a b ->
  Accessor.compare_heads a fuel g t s = Checker.compare_heads b fuel g t s.
Proof. intro Hm. unfold Accessor.compare_heads, Checker.compare_heads. pointwise. Qed.
#[local] Hint Resolve compare_heads_refines : lookup_refinement.

Lemma core_compare_fields_refines a b g owner value index fields : methods_equivalent a b ->
  Accessor.core_compare_fields a g owner value index fields =
    Checker.core_compare_fields b g owner value index fields.
Proof.
  intro Hm. revert index. induction fields; intro index;
    cbn [Accessor.core_compare_fields Checker.core_compare_fields]; pointwise.
Qed.
#[local] Hint Resolve core_compare_fields_refines : lookup_refinement.

Lemma core_structure_eta_refines a b g value constructed : methods_equivalent a b ->
  Accessor.core_structure_eta resolve a env g value constructed =
    Checker.core_structure_eta b env g value constructed.
Proof. intro Hm. unfold Accessor.core_structure_eta, Checker.core_structure_eta. pointwise. Qed.
#[local] Hint Resolve core_structure_eta_refines : lookup_refinement.

Lemma core_unit_like_refines a b g t s : methods_equivalent a b ->
  Accessor.core_unit_like resolve a env g t s = Checker.core_unit_like b env g t s.
Proof. intro Hm. unfold Accessor.core_unit_like, Checker.core_unit_like. pointwise. Qed.
#[local] Hint Resolve core_unit_like_refines : lookup_refinement.

Lemma core_try_string_expansion_refines a b g t s : methods_equivalent a b ->
  Accessor.core_try_string_expansion a g t s = Checker.core_try_string_expansion b g t s.
Proof.
  intro Hm. unfold Accessor.core_try_string_expansion, Checker.core_try_string_expansion.
  pointwise.
Qed.
#[local] Hint Resolve core_try_string_expansion_refines : lookup_refinement.

Lemma core_compare_fallback_refines a b fuel g t s : methods_equivalent a b ->
  Accessor.core_compare_fallback resolve a fuel env g t s =
    Checker.core_compare_fallback b fuel env g t s.
Proof. intro Hm. unfold Accessor.core_compare_fallback, Checker.core_compare_fallback. pointwise. Qed.
#[local] Hint Resolve core_compare_fallback_refines : lookup_refinement.

Lemma compare_after_whnf_refines a b fuel g t s : methods_equivalent a b ->
  Accessor.compare_after_whnf resolve a fuel env g t s =
    Checker.compare_after_whnf b fuel env g t s.
Proof. intro Hm. unfold Accessor.compare_after_whnf, Checker.compare_after_whnf. pointwise. Qed.
#[local] Hint Resolve compare_after_whnf_refines : lookup_refinement.

Lemma core_quick_refines a b fuel g t s : methods_equivalent a b ->
  Accessor.core_quick a fuel g t s = Checker.core_quick b fuel g t s.
Proof. intro Hm. unfold Accessor.core_quick, Checker.core_quick. pointwise. Qed.
#[local] Hint Resolve core_quick_refines : lookup_refinement.

Lemma core_proof_irrel_refines a b fuel g t s : methods_equivalent a b ->
  Accessor.core_proof_irrel a fuel g t s = Checker.core_proof_irrel b fuel g t s.
Proof. intro Hm. unfold Accessor.core_proof_irrel, Checker.core_proof_irrel. pointwise. Qed.
#[local] Hint Resolve core_proof_irrel_refines : lookup_refinement.

Lemma core_offset_refines a b g t s : methods_equivalent a b ->
  Accessor.core_offset resolve a env g t s = Checker.core_offset b env g t s.
Proof. intro Hm. unfold Accessor.core_offset, Checker.core_offset. pointwise. Qed.
#[local] Hint Resolve core_offset_refines : lookup_refinement.

Lemma core_try_unfold_proj_app_refines a b g e : methods_equivalent a b ->
  Accessor.core_try_unfold_proj_app a g e = Checker.core_try_unfold_proj_app b g e.
Proof.
  intro Hm. unfold Accessor.core_try_unfold_proj_app, Checker.core_try_unfold_proj_app.
  pointwise.
Qed.
#[local] Hint Resolve core_try_unfold_proj_app_refines : lookup_refinement.

Lemma core_opposite_projection_refines a b g t s : methods_equivalent a b ->
  Accessor.core_opposite_projection resolve a env g t s =
    Checker.core_opposite_projection b env g t s.
Proof.
  intro Hm. unfold Accessor.core_opposite_projection, Checker.core_opposite_projection.
  pointwise.
Qed.
#[local] Hint Resolve core_opposite_projection_refines : lookup_refinement.

(* Complete result equality is to the new ordinary strategy, not the prior
   strategy at the same fuel or with the prior callback/error ordering.
   In particular both implementations now short-circuit Nat probes before
   speculative congruence; this theorem also preserves Reject/Decline results. *)
Lemma core_lazy_delta_refines rounds a b fuel ps g t s : methods_equivalent a b ->
  Accessor.core_lazy_delta resolve rounds a fuel env ps g t s =
    Checker.core_lazy_delta rounds b fuel env ps g t s.
Proof.
  intro Hm. revert t s. induction rounds; intros t s;
    cbn [Accessor.core_lazy_delta Checker.core_lazy_delta]; pointwise.
Qed.
#[local] Hint Resolve core_lazy_delta_refines : lookup_refinement.

Lemma core_finish_conversion_refines a b fuel g t s : methods_equivalent a b ->
  Accessor.core_finish_conversion resolve a fuel env g t s =
    Checker.core_finish_conversion b fuel env g t s.
Proof. intro Hm. unfold Accessor.core_finish_conversion, Checker.core_finish_conversion. pointwise. Qed.
#[local] Hint Resolve core_finish_conversion_refines : lookup_refinement.

Lemma core_true_shortcut_refines a b g t s : methods_equivalent a b ->
  Accessor.core_true_shortcut resolve a env g t s = Checker.core_true_shortcut b env g t s.
Proof. intro Hm. unfold Accessor.core_true_shortcut, Checker.core_true_shortcut. pointwise. Qed.
#[local] Hint Resolve core_true_shortcut_refines : lookup_refinement.

Lemma defeq_step_refines a b fuel ps g t s : methods_equivalent a b ->
  Accessor.defeq_step resolve a fuel env ps g t s = Checker.defeq_step b fuel env ps g t s.
Proof. intro Hm. unfold Accessor.defeq_step, Checker.defeq_step. pointwise. Qed.
#[local] Hint Resolve defeq_step_refines : lookup_refinement.

Theorem checker_mode_lookup_refines mode fuel ps :
  methods_equivalent (Accessor.checker_mode resolve mode fuel env ps)
    (Checker.checker_mode mode fuel env ps).
Proof.
  revert mode. induction fuel; intro mode; constructor; intros;
    cbn [Accessor.checker_mode Checker.checker_mode]; pointwise.
Qed.

Theorem checker_lookup_refines fuel ps :
  methods_equivalent (Accessor.checker resolve fuel env ps) (Checker.checker fuel env ps).
Proof.
  apply checker_mode_lookup_refines.
Qed.

End Refinement.

Print Assumptions checker_lookup_refines.
Print Assumptions checker_mode_lookup_refines.
