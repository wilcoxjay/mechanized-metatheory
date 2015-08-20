Require Import JRWTactics.

Require Import Relations.
Require Import Operators_Properties.

Require Import SyntaxAndSemantics.
Require Import BasicTheorems.
Require Import TypeSoundness.
Require Import MultiSubstitutions.

Fixpoint P (tau : type) (e : term) : Prop := 
  has_type TypingContext.empty e tau /\
  terminates e /\
  match tau with 
  | TBool => True
  | TArrow ty1 ty2 => forall e1, P ty1 e1 -> P ty2 (TApp e e1)
  end.

Lemma P_has_type : 
  forall tau e, 
    P tau e -> 
    has_type TypingContext.empty e tau.
Proof.
  destruct tau; simpl; intuition.
Qed.

Lemma P_forward_reduction : 
  forall tau e e', 
    has_type TypingContext.empty e tau -> 
    P tau e -> 
    step e e' -> 
    P tau e'.
Proof.
  induction tau; simpl; intuition eauto using preservation, terminates_forward_reduction.
  eapply IHtau2 with (e := TApp e e1); 
    auto using P_has_type.
Qed.

Lemma P_backward_reduction : 
  forall tau e e', 
    has_type TypingContext.empty e tau -> 
    P tau e' -> 
    step e e' -> 
    P tau e.
Proof.
  induction tau; simpl; intuition.
  - eauto using terminates_backward_reduction.
  - eauto using terminates_backward_reduction.
  - apply IHtau2 with (e' := (TApp e' e1)); 
    eauto using P_has_type.
Qed.

Definition substitution_satisfies_typing_context (gamma : substitution) (Gamma : typing_context) : Prop := 
  (forall x v, Substitution.get x gamma = Some v -> exists tau, TypingContext.get x Gamma = Some tau /\
                                                   P tau v) /\
  (forall x tau, TypingContext.get x Gamma = Some tau -> exists v, Substitution.get x gamma = Some v).

Lemma satisfies_typing_context_in_substitution : 
  forall gamma Gamma x tau, 
    substitution_satisfies_typing_context gamma Gamma -> 
    TypingContext.get x Gamma = Some tau -> 
    exists v, Substitution.get x gamma = Some v /\ P tau v.
Proof.
  unfold substitution_satisfies_typing_context.
  intuition.
  find_copy_apply_hyp_hyp. break_exists_exists. intuition.
  find_apply_hyp_hyp. break_exists.  intuition. congruence.
Qed.

Lemma substitution_for_typing_context_empty : 
  forall gamma, 
    substitution_for_typing_context gamma TypingContext.empty.
Proof.
  unfold substitution_for_typing_context.
  simpl. intros. rewrite TypingContext.get_empty in *. discriminate.
Qed.

Lemma satisfies_for : 
  forall gamma Gamma, 
    substitution_satisfies_typing_context gamma Gamma -> 
    substitution_for_typing_context gamma Gamma.
Proof.
  unfold substitution_for_typing_context, substitution_satisfies_typing_context.
  firstorder.
  find_apply_hyp_hyp.
  break_exists. break_and. find_rewrite. find_inversion.
  auto using P_has_type.
Qed.

Lemma P_terminates : 
  forall tau e, 
    P tau e -> 
    terminates e.
Proof.
  unfold P.
  destruct tau; firstorder.
Qed.

Lemma P_many_forward : 
  forall e e' tau, 
    step_star e e' -> 
    P tau e -> 
    P tau e'.
Proof.
  induction 1; intros; auto.
  eapply P_forward_reduction with (e := y); auto.
  eapply preservation_many; eauto.
  auto using P_has_type.
Qed.

Lemma P_many_backward : 
  forall tau e e', 
    step_star e e' -> 
    has_type TypingContext.empty e tau -> 
    P tau e' -> 
    P tau e.
Proof.
  induction 1; intros; auto.
  apply IHclos_refl_trans_n1; auto.
  eapply P_backward_reduction; eauto.
  eapply preservation_many; eauto.
Qed.

Lemma satisfies_has_type : 
  forall gamma Gamma x v tau, 
    substitution_satisfies_typing_context gamma Gamma -> 
    Substitution.get x gamma = Some v -> 
    TypingContext.get x Gamma = Some tau -> 
    has_type TypingContext.empty v tau.
Proof.
  intros.
  eapply substitution_for_typing_context_has_type; eauto.
  auto using satisfies_for.
Qed.

Lemma satisfies_substitution_in_typing_context : 
  forall gamma Gamma x v, 
    substitution_satisfies_typing_context gamma Gamma -> 
    Substitution.get x gamma = Some v -> 
    exists tau, TypingContext.get x Gamma = Some tau.
Proof.
  firstorder.
Qed.

Lemma extend_satisfies : 
  forall gamma Gamma x v tau, 
    substitution_satisfies_typing_context gamma Gamma -> 
    P tau v -> 
    substitution_satisfies_typing_context (Substitution.shadow x v (Substitution.delete x gamma)) 
                                   (TypingContext.shadow x tau Gamma).
Proof.
  unfold substitution_satisfies_typing_context.
  firstorder.
  - destruct (name_eq_dec x x0).
    + subst. 
      rewrite Substitution.get_shadow_same in *. find_inversion.
      rewrite TypingContext.get_shadow_same. eauto.
    + rewrite Substitution.get_shadow_diff in * by auto. 
      rewrite Substitution.get_delete_diff in * by auto. 
      rewrite TypingContext.get_shadow_diff by auto. eauto.
  - destruct (name_eq_dec x x0).
    + subst. rewrite Substitution.get_shadow_same. eauto. 
    + rewrite Substitution.get_shadow_diff in * by auto. 
      rewrite Substitution.get_delete_diff in * by auto. 
      rewrite TypingContext.get_shadow_diff in * by auto. eauto.
Qed.

Lemma P_if_intro : 
  forall tau e1 e2 e3, 
    P TBool e1 -> 
    P tau e2 -> 
    P tau e3 -> 
    P tau (TIf e1 e2 e3).
Proof.
  intros.
  copy_apply P_terminates H.
  copy_apply P_has_type H.
  unfold terminates in *.
  break_exists. break_and.
  find_copy_eapply_lem_hyp type_soundness; eauto.
  break_and. find_copy_eapply_lem_hyp canonical_forms_bool; auto.

  eapply P_many_backward.
  - eapply step_star_if; eauto.
  - auto using P_has_type.
  - break_or_hyp; subst.
    + eapply P_backward_reduction with (e' := e2); auto using P_has_type.
    + eapply P_backward_reduction with (e' := e3); auto using P_has_type.
Qed.
  
Lemma P_substitution : 
  forall gamma Gamma e tau, 
    has_type Gamma e tau -> 
    substitution_satisfies_typing_context gamma Gamma -> 
    P tau (multi_subs gamma e).
Proof.
  intros.
  prep_induction H. 
  induction H; intros.
  - simpl. intuition. auto using const_terminates.
  - simpl. find_copy_eapply_lem_hyp satisfies_typing_context_in_substitution; eauto.
    break_exists. break_and. find_rewrite. auto.
  - simpl. auto using P_if_intro.
  - assert (has_type TypingContext.empty (multi_subs gamma (TAbs x tyx e)) (TArrow tyx tau)).
    { 
      eapply multi_subs_has_type_empty with (Gamma := Gamma). 
      * auto using satisfies_for.
      * firstorder.
      * auto.
    }
    cbn [P]. intuition.
    + simpl. auto using lambda_terminates.
    + find_copy_eapply_lem_hyp P_terminates.
      unfold terminates in *. break_exists_name v1. break_and.
      find_copy_eapply_lem_hyp type_soundness; eauto using P_has_type. break_and.
      assert (P tyx v1) by eauto using P_many_forward.
      simpl. 
      eapply P_many_backward.
      * { eapply step_star_trans. 
          - eauto using app_step_star_2. 
          - eapply clos_rt_rtn1.
            eapply rt_trans.
            + eapply rt_step. constructor. auto.
            + apply rt_refl.
        } 
      * econstructor; eauto using P_has_type.
      * { rewrite subs_multi_subs.
          - eauto using extend_satisfies.
          - auto using Substitution.get_delete_same.
          - intros. find_apply_lem_hyp SubstitutionFacts.get_delete_Some.
            find_copy_eapply_lem_hyp satisfies_substitution_in_typing_context; eauto.
            break_exists.
            find_copy_eapply_lem_hyp satisfies_has_type; eauto.
            find_eapply_lem_hyp has_type_free; eauto. break_exists.
            simpl in *. rewrite TypingContext.get_empty in *. discriminate.
        } 
  - firstorder. 
Qed.

Lemma empty_substitution_satisfies_empty_typing_context : 
  substitution_satisfies_typing_context Substitution.empty TypingContext.empty.
Proof.
  unfold substitution_satisfies_typing_context.
  intuition.
  - rewrite Substitution.get_empty in *. discriminate.
  - rewrite TypingContext.get_empty in *. discriminate.
Qed.

Theorem strong_normalization : 
  forall e tau, 
    has_type TypingContext.empty e tau -> 
    terminates e.
Proof.
  intros.
  eapply P_terminates with (tau := tau).
  rewrite <- multi_subs_empty_substitution.
  eapply P_substitution; eauto.
  auto using empty_substitution_satisfies_empty_typing_context.
Qed.
