Require Import JRWTactics.

Require Import SyntaxAndSemantics.
Require Import BasicTheorems.

Lemma subs_preserves_has_type : 
  forall Gamma e tau x tyx v, 
    has_type Gamma e tau -> 
    TypingContext.get x Gamma = Some tyx -> 
    has_type TypingContext.empty v tyx -> 
    has_type Gamma (subs x v e) tau.
Proof.
  intros.
  prep_induction H.
  induction H; intros; simpl; firstorder.
  - break_if.
    + subst. apply weakening_empty. congruence.
    + auto.
  - break_if.
    + firstorder.
    + constructor. eapply IHhas_type; eauto.
      rewrite TypingContext.get_shadow_diff by auto. auto.
Qed.

Lemma preservation : 
  forall e tau e', 
    has_type TypingContext.empty e tau ->
    step e e' -> 
    has_type TypingContext.empty e' tau.
Proof.
  intros.
  match goal with 
  | [ H : step _ _ |- _ ] => prep_induction H; induction H
  end; intros; 
  match goal with 
  | [ H : has_type _ _ _ |- _ ] => invc H
  end; eauto.
  
  match goal with 
  | [ H : has_type _ (TAbs _ _ _) _ |- _ ] => invc H
  end.
  eapply has_type_ext.
  eapply subs_preserves_has_type; eauto. 
  + auto using TypingContext.get_shadow_same. 
  + intros. destruct (name_eq_dec x0 x).
    * subst. exfalso. eauto using subs_not_free.
    * auto using  TypingContext.get_shadow_diff. 
Qed.

Corollary preservation_many : 
  forall e tau e', 
    has_type TypingContext.empty e tau -> 
    step_star e e' -> 
    has_type TypingContext.empty e' tau.
Proof.
  intros.
  match goal with 
  | [ H : step_star _ _ |- _ ] => induction H
  end; 
    eauto using preservation.
Qed.

Hint Constructors step.

Lemma progress : 
  forall e tau, 
    has_type TypingContext.empty e tau ->
    is_value e \/ exists e', step e e'.
Proof.
  induction e; intros; invc H.
  - firstorder.
  - rewrite TypingContext.get_empty in *. discriminate.
  - match goal with 
    | [ H : _ |- _ ] => copy_apply IHe1 H
    end.
    intuition.
    + find_apply_lem_hyp canonical_forms_bool; firstorder.
    + firstorder.
  - firstorder.
  - match goal with 
    | [ H : _ |- _ ] => copy_apply IHe1 H
    end.
    firstorder.
    find_apply_lem_hyp canonical_forms_arrow; firstorder.
Qed.

Theorem type_soundness : 
  forall e tau v, 
    has_type TypingContext.empty e tau -> 
    step_star e v -> 
    irreducible v -> 
    is_value v /\ has_type TypingContext.empty v tau.
Proof.
  intros.
  eapply preservation_many in H0; eauto.
  find_copy_apply_lem_hyp progress.
  firstorder.
Qed.    
