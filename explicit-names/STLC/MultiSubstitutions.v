Require Import JRWTactics.

Require Import SyntaxAndSemantics.
Require Import BasicTheorems.

Require Import Alist.
Require Import EqMapFacts.

Module TermAny.
  Definition t := term.
End TermAny.

Module Substitution := alist Name TermAny.

Definition substitution := Substitution.t.

Fixpoint multi_subs (gamma : substitution) (e : term) : term := 
  match e with 
  | TConst _ => e 
  | TVar x => match Substitution.get x gamma with 
             | Some e' => e'
             | None => e
             end
  | TIf e1 e2 e3 => TIf (multi_subs gamma e1) (multi_subs gamma e2) (multi_subs gamma e3)
  | TAbs x tau e => TAbs x tau (multi_subs (Substitution.delete x gamma) e)
  | TApp e1 e2 => TApp (multi_subs gamma e1) (multi_subs gamma e2)
  end.

Definition substitution_for_typing_context (gamma : substitution) (Gamma : typing_context) : Prop :=
  (forall x tau v, TypingContext.get x Gamma = Some tau -> 
             Substitution.get x gamma = Some v -> 
             has_type TypingContext.empty v tau).

Lemma substitution_for_typing_context_has_type : 
  forall gamma Gamma x tau v, 
    substitution_for_typing_context gamma Gamma -> 
    TypingContext.get x Gamma = Some tau -> 
    Substitution.get x gamma = Some v -> 
    has_type TypingContext.empty v tau.
Proof.
  unfold substitution_for_typing_context.
  intuition eauto.
Qed.

Lemma substitution_for_typing_context_inside_lambda : 
  forall gamma Gamma x tyx, 
    substitution_for_typing_context gamma Gamma -> 
    substitution_for_typing_context (Substitution.delete x gamma) (TypingContext.shadow x tyx Gamma).
Proof.
  unfold substitution_for_typing_context. 
  intros.
  destruct (name_eq_dec x0 x).
  - subst. rewrite Substitution.get_delete_same in *. discriminate.
  - rewrite Substitution.get_delete_diff in * by auto.
    rewrite TypingContext.get_shadow_diff in * by auto. eauto.
Qed.

Lemma multi_substitution : 
  forall e Gamma gamma tau, 
    substitution_for_typing_context gamma Gamma -> 
    has_type Gamma e tau -> 
    has_type Gamma (multi_subs gamma e) tau.
Proof.
  intros.
  prep_induction H0.
  induction H0; simpl; intros.
  - auto.
  - break_match.
    + apply weakening_empty.
      eauto using substitution_for_typing_context_has_type.
    + auto.
  - eauto.
  - constructor. apply IHhas_type.
    auto using substitution_for_typing_context_inside_lambda.
  - eauto.
Qed.

Lemma multi_subs_free : 
  forall e gamma x vx, 
    Substitution.get x gamma = Some vx -> 
    is_free_in x (multi_subs gamma e) -> 
    exists y vy, Substitution.get y gamma = Some vy /\
            is_free_in y e /\
            is_free_in x vy.
Proof.
  induction e; simpl; intros.
  - intuition.
  - break_match.
    + eauto.
    + simpl in *. congruence.
  - intuition; find_apply_hyp_hyp; break_exists; intuition eauto 10.
  - intuition.
    eapply IHe with (vx := vx) in H2.
    + break_exists. destruct (name_eq_dec x0 n).
      * break_and. subst. 
        rewrite Substitution.get_delete_same in *. discriminate.
      * rewrite Substitution.get_delete_diff in * by auto. intuition eauto 10.
    + rewrite Substitution.get_delete_diff in * by auto. auto.
  - intuition; find_apply_hyp_hyp; break_exists; intuition eauto 10.
Qed.

Lemma multi_subs_has_type_empty : 
  forall Gamma gamma e tau, 
    substitution_for_typing_context gamma Gamma -> 
    (forall x tau, 
        TypingContext.get x Gamma = Some tau -> 
        exists v, 
          Substitution.get x gamma = Some v) -> 
    has_type Gamma e tau -> 
    has_type TypingContext.empty (multi_subs gamma e) tau.
Proof.
  intros.
  eapply has_type_ext with (Gamma := Gamma).
  - auto using multi_substitution.
  - intros. 
    find_copy_eapply_lem_hyp multi_substitution; eauto.
    find_copy_eapply_lem_hyp has_type_free; eauto.
    break_exists.
    find_apply_hyp_hyp. break_exists.
    find_copy_eapply_lem_hyp multi_subs_free; eauto.
    break_exists. break_and.
    eapply has_type_free in H6; eauto. break_exists.
    find_eapply_lem_hyp substitution_for_typing_context_has_type; eauto.
    find_eapply_lem_hyp has_type_free; eauto.
    break_exists. rewrite TypingContext.get_empty in *. discriminate.
Qed.

Module SubstitutionFacts := EqMapFacts.EqMapFacts Name TermAny Substitution.

Lemma subs_multi_subs : 
  forall e gamma x vx, 
    Substitution.get x gamma = None -> 
    (forall y vy, Substitution.get y gamma = Some vy -> is_free_in x vy -> False) -> 
    subs x vx (multi_subs gamma e) = multi_subs (Substitution.shadow x vx gamma) e.
Proof.
  induction e; simpl; intros.
  - auto.
  - repeat break_match; simpl; destruct (name_eq_dec x n); 
    try rewrite Substitution.get_shadow_diff in * by auto; 
    subst; try rewrite Substitution.get_shadow_same in *; try congruence.

    rewrite subs_not_free_same by eauto. congruence.
  - f_equal; firstorder.
  - break_if.
    + subst. rewrite Substitution.delete_shadow_same. auto.
    + f_equal. rewrite Substitution.delete_shadow_diff by auto. eapply IHe.
      * rewrite Substitution.get_delete_diff by auto; auto.
      * intros. find_apply_lem_hyp SubstitutionFacts.get_delete_Some. eauto.
  - f_equal; firstorder.
Qed.

Lemma multi_subs_empty_substitution : 
  forall e, 
    multi_subs Substitution.empty e = e.
Proof.
  induction e; intros; simpl; f_equal; auto.
  - break_match; auto. rewrite Substitution.get_empty in *. discriminate.
  - rewrite Substitution.delete_empty. auto.
Qed.
