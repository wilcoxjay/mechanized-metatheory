Require Import JRWTactics.

Require Import SyntaxAndSemantics.
Require Import BasicTheorems.
Require Import MultiSubstitutions.

Set Firstorder Solver (subst; eauto).
Hint Constructors has_type.

Fixpoint V (tau : type) (e : term) : Prop :=
  has_type TypingContext.empty e tau /\
  match tau with 
  | TBool => exists b, e = TConst b
  | TArrow ty1 ty2 => 
    exists x e', 
    e = TAbs x ty1 e' /\ 
    forall v, V ty1 v -> 
         forall e'', step_star (subs x v e') e'' -> irreducible e'' -> V ty2 e''
  end.

Definition E (tau : type) (e : term) : Prop := 
  forall e', step_star e e' -> irreducible e' -> V tau e'.

Lemma V_is_value : 
  forall e tau, 
    V tau e -> is_value e.
Proof.
  destruct tau; simpl; intros.
  - firstorder. simpl. auto.
  - firstorder. simpl. auto.
Qed.

Axiom irreducible_decidable : 
  forall e, irreducible e \/ exists e', step e e'.

Theorem E_safe : 
  forall e tau e',  
    E tau e -> 
    step_star e e' -> 
    is_value e' \/
    exists e'', step e' e''.
Proof.
  unfold E.
  intros.
  assert (irreducible e' \/ exists e'', step e' e'') by eauto using irreducible_decidable.
  intuition.
  eauto using V_is_value.
Qed.

Definition G (Gamma : typing_context) (gamma : substitution) : Prop :=
  (forall x v, Substitution.get x gamma = Some v -> exists tau, TypingContext.get x Gamma = Some tau /\ V tau v) /\
  (forall x tau, TypingContext.get x Gamma = Some tau -> exists v, Substitution.get x gamma = Some v).

Definition has_semantic_type (Gamma : typing_context) (e : term) (tau : type) : Prop :=
  forall gamma, G Gamma gamma -> E tau (multi_subs gamma e).

Lemma G_typing_context_Some_substitution_Some : 
  forall Gamma gamma x tau, 
    G Gamma gamma -> 
    TypingContext.get x Gamma = Some tau -> 
    exists v, Substitution.get x gamma = Some v /\
         V tau v.
Proof.
  firstorder.
  find_copy_apply_hyp_hyp. break_exists_exists. intuition.
  find_apply_hyp_hyp. break_exists. intuition. congruence.
Qed.

Lemma G_substitution_Some_typing_context_Some : 
  forall Gamma gamma x v,
    G Gamma gamma -> 
    Substitution.get x gamma = Some v -> 
    exists tau, TypingContext.get x Gamma = Some tau.
Proof.
  firstorder.
Qed.

Lemma V_TConst : 
  forall b, 
    V TBool (TConst b).
Proof.
  red. eauto.
Qed.

Lemma E_TConst : 
  forall b, 
    E TBool (TConst b).
Proof.
  intros.
  red. intros. 
  find_apply_lem_hyp step_star_TConst. subst.
  auto using V_TConst.
Qed.

Lemma V_implies_E : 
  forall tau e, 
    V tau e -> E tau e.
Proof.
  destruct tau; simpl.
  - intros. break_and. break_exists. subst. auto using E_TConst.
  - intros. break_and. break_exists. break_and. 
    subst. red. simpl. intros.
    find_apply_lem_hyp step_star_TAbs. subst.
    intuition.
    eexists. eexists. intuition eauto.
Qed.

Lemma V_TBool_elim : 
  forall x, 
    V TBool x -> exists b, x = TConst b.
Proof.
  firstorder.
Qed.

Lemma V_has_type :
  forall tau e, 
    V tau e -> 
    has_type TypingContext.empty e tau.
Proof.
  destruct tau; firstorder.
Qed.

Lemma G_substitution_for_typing_context : 
  forall Gamma gamma, 
    G Gamma gamma -> 
    substitution_for_typing_context gamma Gamma.
Proof.
  unfold substitution_for_typing_context.
  intros.
  find_eapply_lem_hyp G_typing_context_Some_substitution_Some; eauto.
  break_exists. intuition.
  eapply V_has_type. congruence.
Qed.

Lemma G_has_type_empty : 
  forall Gamma gamma x y vy,
    G Gamma gamma -> 
    Substitution.get y gamma = Some vy -> 
    is_free_in x vy -> 
    False.
Proof.
  intros.
  find_copy_eapply_lem_hyp G_substitution_Some_typing_context_Some; eauto.
  break_exists.
  find_eapply_lem_hyp G_typing_context_Some_substitution_Some; eauto.
  break_exists_name vy'. break_and. assert (vy = vy') by congruence. subst.
  find_apply_lem_hyp V_has_type.
  find_eapply_lem_hyp has_type_free; eauto.
  break_exists. rewrite TypingContext.get_empty in *. discriminate.
Qed.

Lemma extend_G : 
  forall gamma Gamma x v tau, 
    G Gamma gamma -> 
    V tau v -> 
    G (TypingContext.shadow x tau Gamma)
      (Substitution.shadow x v (Substitution.delete x gamma)).
Proof.
  unfold G.
  firstorder.
  - destruct (name_eq_dec x x0).
    + subst. rewrite Substitution.get_shadow_same in *.
      rewrite TypingContext.get_shadow_same in *.
      eexists. intuition eauto. congruence.
    + rewrite Substitution.get_shadow_diff in * by auto.
      rewrite Substitution.get_delete_diff in * by auto.
      rewrite TypingContext.get_shadow_diff in * by auto.
      auto.
  - destruct (name_eq_dec x x0).
    + subst. rewrite Substitution.get_shadow_same in *.
      rewrite TypingContext.get_shadow_same in *. eauto.
    + rewrite Substitution.get_shadow_diff in * by auto.
      rewrite Substitution.get_delete_diff in * by auto.
      rewrite TypingContext.get_shadow_diff in * by auto.
      eauto.
Qed.

Hint Constructors step.

Theorem fundamental_property : 
  forall Gamma e tau, 
    has_type Gamma e tau -> 
    has_semantic_type Gamma e tau.
Proof.
  unfold has_semantic_type.
  induction 1; intros.
  - simpl. auto using E_TConst.
  - simpl. find_copy_eapply_lem_hyp G_typing_context_Some_substitution_Some; eauto.
    break_exists.  break_and.
    find_rewrite. auto using V_implies_E.
  - unfold E in *. 
    specialize (IHhas_type1 _ $(eauto)$).
    simpl.
    intros.
    find_apply_lem_hyp step_star_if_inv; auto.
    break_exists. break_and.
    assert (V TBool x) by eauto.
    find_apply_lem_hyp V_TBool_elim. break_exists. subst.
    find_apply_lem_hyp step_star_left_inv. 
    intuition.
    + subst. exfalso. 
      destruct x0;
      match goal with 
      | [  H : irreducible (TIf _ _ _) |- _ ] => 
        eapply H; auto
      end.
    + break_exists. break_and. 
      match goal with 
      | [ H : step _ _ |- _ ] => invc H
      end; eauto.
      solve_by_inversion.
  - unfold E in *. simpl.
    intros.
    find_apply_lem_hyp step_star_TAbs. subst.
    intuition.
    + replace (TAbs x tyx (multi_subs (Substitution.delete x gamma) e))
      with (multi_subs gamma (TAbs x tyx e)) by auto.
      apply multi_subs_has_type_empty with (Gamma := Gamma); eauto. 
      * auto using G_substitution_for_typing_context.
      * intros. find_eapply_lem_hyp G_typing_context_Some_substitution_Some; eauto.
        firstorder.
    + eexists. eexists. intuition eauto.
      rewrite subs_multi_subs in *.
      * eapply IHhas_type; eauto. auto using extend_G.
      * auto using Substitution.get_delete_same.
      * intros. find_apply_lem_hyp SubstitutionFacts.get_delete_Some.
        eauto using G_has_type_empty.
  - unfold E in *.
    simpl. intros.
    find_apply_lem_hyp step_star_app_inv_1; auto.
    break_exists. break_and.
    assert (V (TArrow ty2 tau) x) by eauto.
    simpl in *. break_and. break_exists. break_and.
    subst.
    find_apply_lem_hyp step_star_app_inv_2; simpl; auto.
    break_exists. break_and.
    assert (V ty2 x) by eauto.
    find_apply_lem_hyp step_star_left_inv.
    intuition.
    + subst. exfalso. 
      match goal with 
      | [  H : irreducible (TApp _ _) |- _ ] => 
        eapply H; auto
      end. econstructor. eauto using V_is_value.
    + break_exists. break_and.
      match goal with 
      | [ H : step _ _ |- _ ] => invc H
      end; eauto.
      * solve_by_inversion.
      * exfalso. eauto using irreducible_no_step.
Qed.
