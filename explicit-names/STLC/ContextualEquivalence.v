Require Import JRWTactics.

Require Import Relations.
Require Import Operators_Properties.

Require Import SyntaxAndSemantics.
Require Import BasicTheorems.
Require Import MultiSubstitutions.

Inductive context : Type :=
| CHole : context 
| CIf1 : context -> term -> term -> context
| CIf2 : term -> context -> term -> context 
| CIf3 : term -> term -> context -> context
| CAbs : name -> type -> context -> context 
| CApp1 : context -> term -> context
| CApp2 : term -> context -> context.

Fixpoint plug (e : term) (C : context) : term := 
  match C with 
  | CHole => e
  | CIf1 C' e2 e3 => TIf (plug e C') e2 e3
  | CIf2 e1 C' e3 => TIf e1 (plug e C') e3
  | CIf3 e1 e2 C' => TIf e1 e2 (plug e C')
  | CAbs x tau C' => TAbs x tau (plug e C')
  | CApp1 C' e2 => TApp (plug e C') e2
  | CApp2 e1 C' => TApp e1 (plug e C')
  end.

Inductive context_has_type : context -> typing_context -> type -> typing_context -> type -> Prop :=
| CHT_hole : forall Gamma tau, context_has_type CHole Gamma tau Gamma tau
| CHT_if1 : forall C Gamma tau Gamma' tau' e2 e3, 
    context_has_type C Gamma tau Gamma' TBool -> 
    has_type Gamma' e2 tau' -> 
    has_type Gamma' e3 tau' -> 
    context_has_type (CIf1 C e2 e3) Gamma tau Gamma' tau'
| CHT_if2 : forall C Gamma tau Gamma' tau' e1 e3, 
    has_type Gamma' e1 TBool -> 
    context_has_type C Gamma tau Gamma' tau' -> 
    has_type Gamma' e3 tau' -> 
    context_has_type (CIf2 e1 C e3) Gamma tau Gamma' tau'
| CHT_if3 : forall C Gamma tau Gamma' tau' e1 e2, 
    has_type Gamma' e1 TBool -> 
    has_type Gamma' e2 tau' -> 
    context_has_type C Gamma tau Gamma' tau' -> 
    context_has_type (CIf3 e1 e2 C) Gamma tau Gamma' tau'
| CHT_abs : forall C Gamma tau x tau1 tau' Gamma', 
    context_has_type C (TypingContext.shadow x tau1 Gamma) tau (TypingContext.shadow x tau1 Gamma') tau' -> 
    context_has_type (CAbs x tau1 C) (TypingContext.shadow x tau1 Gamma) tau Gamma' (TArrow tau1 tau')
| CHT_app1 : forall C Gamma tau Gamma' tau1 tau2 e, 
    context_has_type C Gamma tau Gamma' (TArrow tau1 tau2) -> 
    has_type Gamma' e tau1 -> 
    context_has_type (CApp1 C e) Gamma tau Gamma' tau2
| CHT_app2 : forall C Gamma tau Gamma' tau1 tau2 e, 
    has_type Gamma' e (TArrow tau1 tau2) -> 
    context_has_type C Gamma tau Gamma' tau1 -> 
    context_has_type (CApp2 e C) Gamma tau Gamma' tau2.

Theorem CHT_plug : 
  forall C Gamma tau Gamma' tau' e, 
    context_has_type C Gamma tau Gamma' tau' -> 
    has_type Gamma e tau -> 
    has_type Gamma' (plug e C) tau'.
Proof.
  intros.
  prep_induction H.
  induction H; intros; simpl; eauto.
Qed.

Fixpoint V (tau : type) (e1 e2 : term) : Prop := 
  has_type TypingContext.empty e1 tau /\
  has_type TypingContext.empty e2 tau /\
  match tau with 
  | TBool => e1 = e2 /\ (exists b, e1 = TConst b)
  | TArrow tau1 tau2 => 
    exists x y e1' e2',
    e1 = TAbs x tau1 e1' /\
    e2 = TAbs y tau1 e2' /\
    forall v1 v2, 
      V tau1 v1 v2 ->
      exists v1' v2', 
        step_star (subs x v1 e1') v1' /\
        step_star (subs y v2 e2') v2' /\
        V tau2 v1' v2'
  end.

Definition E (tau : type) (e1 e2 : term) : Prop := 
  has_type TypingContext.empty e1 tau /\
  has_type TypingContext.empty e2 tau /\
  exists v1 v2, 
    step_star e1 v1 /\
    step_star e2 v2 /\
    V tau v1 v2.

Definition G (Gamma : TypingContext.t) (gamma1 gamma2 : Substitution.t) : Prop := 
  (forall x tau, 
      TypingContext.get x Gamma = Some tau -> 
      exists v1 v2, 
        Substitution.get x gamma1 = Some v1 /\
        Substitution.get x gamma2 = Some v2 /\
        V tau v1 v2) /\
  (forall x v, 
      Substitution.get x gamma1 = Some v -> 
      exists tau, TypingContext.get x Gamma = Some tau) /\
  (forall x v, 
      Substitution.get x gamma2 = Some v -> 
      exists tau, TypingContext.get x Gamma = Some tau).

Definition semantic_relation (Gamma : TypingContext.t) (e1 e2 : term) (tau : type) : Prop := 
  forall gamma1 gamma2, 
    G Gamma gamma1 gamma2 -> 
    E tau (multi_subs gamma1 e1) (multi_subs gamma2 e2).

Lemma G_typing_context_Some_substitution_Some_1 : 
  forall Gamma gamma1 gamma2 x tau, 
    G Gamma gamma1 gamma2 -> 
    TypingContext.get x Gamma = Some tau -> 
    exists v1 : term, 
      Substitution.get x gamma1 = Some v1.
Proof.
  firstorder.
Qed.

Lemma G_typing_context_Some_substitution_Some_2 : 
  forall Gamma gamma1 gamma2 x tau, 
    G Gamma gamma1 gamma2 -> 
    TypingContext.get x Gamma = Some tau -> 
    exists v2 : term, 
      Substitution.get x gamma2 = Some v2.
Proof.
  firstorder.
Qed.

Lemma G_substitution_Some_typing_context_Some: 
  forall Gamma gamma1 gamma2 x v1 v2, 
    G Gamma gamma1 gamma2 -> 
    Substitution.get x gamma1 = Some v1 -> 
    Substitution.get x gamma2 = Some v2 -> 
    exists tau, 
      TypingContext.get x Gamma = Some tau /\
      V tau v1 v2.
Proof.
  firstorder.
  find_copy_apply_hyp_hyp.
  break_exists_exists.
  find_copy_apply_hyp_hyp.
  firstorder.
  congruence.
Qed.

Lemma V_has_type_1 : 
  forall tau e1 e2, 
    V tau e1 e2 -> 
    has_type TypingContext.empty e1 tau.
Proof.
  destruct tau; simpl; firstorder.
Qed.

Lemma V_has_type_2 : 
  forall tau e1 e2, 
    V tau e1 e2 -> 
    has_type TypingContext.empty e2 tau.
Proof.
  destruct tau; simpl; firstorder.
Qed.

Lemma V_implies_E : 
  forall tau e1 e2, 
    V tau e1 e2 -> 
    E tau e1 e2.
Proof.
  unfold E.
  intuition; eauto using V_has_type_1, V_has_type_2.
  exists e1, e2. intuition; constructor.
Qed.

Lemma var_compatability : 
  forall Gamma x tau, 
    TypingContext.get x Gamma = Some tau -> 
    semantic_relation Gamma (TVar x) (TVar x) tau.
Proof.
  unfold semantic_relation.
  intros. simpl. 
  find_copy_eapply_lem_hyp G_typing_context_Some_substitution_Some_1; eauto.
  find_copy_eapply_lem_hyp G_typing_context_Some_substitution_Some_2; eauto.
  break_exists.
  repeat find_rewrite.
  apply V_implies_E.
  find_eapply_lem_hyp G_substitution_Some_typing_context_Some; eauto.
  break_exists. intuition.
  congruence.
Qed.

Lemma V_refl : 
  forall tau (x : name), 
  exists e, 
    V tau e e.
Proof.
  intros.
  induction tau.
  - exists (TConst true). simpl. intuition eauto.
  - break_exists_name e2. break_exists_name e1.
    exists (TAbs x tau1 e2).
    simpl. intuition.
    + eauto using V_has_type_2, weakening_empty.
    + eauto using V_has_type_1, weakening_empty.
    + eexists. eexists. eexists. eexists. intuition eauto.
      eexists e2, e2.
      rewrite subs_not_free_same by eauto using has_type_empty_not_free, V_has_type_2.
      rewrite subs_not_free_same by eauto using has_type_empty_not_free, V_has_type_1.
      intuition; constructor.
Qed.

Lemma extend_satisfies : 
  forall gamma1 gamma2 Gamma x v1 v2 tau, 
    G Gamma gamma1 gamma2 -> 
    V tau v1 v2 -> 
    G (TypingContext.shadow x tau Gamma) (Substitution.shadow x v1 gamma1) (Substitution.shadow x v2 gamma2).
Proof.
  unfold G.
  intuition; destruct (name_eq_dec x0 x); subst; 
  repeat rewrite Substitution.get_shadow_same;
  try rewrite TypingContext.get_shadow_same in *; 
  repeat rewrite Substitution.get_shadow_diff in * by auto; 
  repeat rewrite TypingContext.get_shadow_diff in * by auto; 
  try find_inversion;
  eauto.
Qed.

Lemma extend_delete_satisfies : 
  forall gamma1 gamma2 Gamma x v1 v2 tau, 
    G Gamma gamma1 gamma2 -> 
    V tau v1 v2 -> 
    G (TypingContext.shadow x tau Gamma) 
      (Substitution.shadow x v1 (Substitution.delete x gamma1))
      (Substitution.shadow x v2 (Substitution.delete x gamma2)).
Proof.
  unfold G.
  intuition; destruct (name_eq_dec x0 x); subst; 
  repeat rewrite Substitution.get_shadow_same;
  try rewrite TypingContext.get_shadow_same in *; 
  repeat rewrite Substitution.get_shadow_diff in * by auto; 
  repeat rewrite TypingContext.get_shadow_diff in * by auto; 
  repeat rewrite Substitution.get_delete_diff in * by auto;
  try find_inversion;
  eauto.
Qed.

Lemma G_substitution_Some_typing_context_Some_1 : 
  forall Gamma gamma1 gamma2 x v, 
    G Gamma gamma1 gamma2 -> 
    Substitution.get x gamma1 = Some v -> 
    exists tau, TypingContext.get x Gamma = Some tau /\
         has_type TypingContext.empty v tau.
Proof.
  unfold G.
  intuition.
  find_copy_apply_hyp_hyp.
  break_exists.
  find_copy_apply_hyp_hyp.
  break_exists. break_and.
  eexists. intuition eauto.
  find_apply_lem_hyp V_has_type_1. congruence.
Qed.

Lemma G_substitution_Some_typing_context_Some_2 : 
  forall Gamma gamma1 gamma2 x v, 
    G Gamma gamma1 gamma2 -> 
    Substitution.get x gamma2 = Some v -> 
    exists tau, TypingContext.get x Gamma = Some tau /\
         has_type TypingContext.empty v tau.
Proof.
  unfold G.
  intuition.
  find_copy_apply_hyp_hyp.
  break_exists.
  find_copy_apply_hyp_hyp.
  break_exists. break_and.
  eexists. intuition eauto.
  find_apply_lem_hyp V_has_type_2. congruence.
Qed.

Lemma G_for_context_2 : 
  forall Gamma gamma1 gamma2, 
    G Gamma gamma1 gamma2 -> 
    substitution_for_typing_context gamma2 Gamma.
Proof.
  unfold substitution_for_typing_context.
  intros.
  find_eapply_lem_hyp G_substitution_Some_typing_context_Some_2; eauto.
  break_exists. intuition. congruence.
Qed.

Lemma G_for_context_1 : 
  forall Gamma gamma1 gamma2, 
    G Gamma gamma1 gamma2 -> 
    substitution_for_typing_context gamma1 Gamma.
Proof.
  unfold substitution_for_typing_context.
  intros.
  find_eapply_lem_hyp G_substitution_Some_typing_context_Some_1; eauto.
  break_exists. intuition. congruence.
Qed.

Lemma abs_compatability : 
  forall Gamma x tau tau' e1 e2, 
    has_type (TypingContext.shadow x tau Gamma) e1 tau' -> 
    has_type (TypingContext.shadow x tau Gamma) e2 tau' -> 
    semantic_relation (TypingContext.shadow x tau Gamma) e1 e2 tau' -> 
    semantic_relation Gamma (TAbs x tau e1) (TAbs x tau e2) (TArrow tau tau').
Proof.
  unfold semantic_relation.
  intros.
  apply V_implies_E.
  cbn [V].
  intuition.
  - apply multi_subs_has_type_empty with (Gamma := Gamma).
    + eauto using G_for_context_1.
    + eauto using G_typing_context_Some_substitution_Some_1.
    + constructor. auto.
  - apply multi_subs_has_type_empty with (Gamma := Gamma).
    + eauto using G_for_context_2.
    + eauto using G_typing_context_Some_substitution_Some_2.
    + auto.
  - simpl. do 4 eexists. intuition eauto.
    rewrite subs_multi_subs.
    + rewrite subs_multi_subs. 
      * unfold E in *.
        specialize (H1 (Substitution.shadow x v1 (Substitution.delete x gamma1))
                       (Substitution.shadow x v2 (Substitution.delete x gamma2))).
        conclude_using ltac:(auto using extend_delete_satisfies).
        intuition.
      * rewrite Substitution.get_delete_same. auto.
      * intros.
        find_apply_lem_hyp SubstitutionFacts.get_delete_Some.
        find_eapply_lem_hyp G_substitution_Some_typing_context_Some_2; eauto.
        break_exists. intuition. eauto using has_type_empty_not_free.
    + rewrite Substitution.get_delete_same. auto.
    + intros.
      find_apply_lem_hyp SubstitutionFacts.get_delete_Some.
      find_eapply_lem_hyp G_substitution_Some_typing_context_Some_1; eauto.
      break_exists. intuition. eauto using has_type_empty_not_free.
Qed.  

Lemma V_is_value_1 : 
  forall tau x1 x2, 
    V tau x1 x2 -> 
    is_value x1.
Proof.
  destruct tau; simpl; intuition; break_exists.
  - subst. subst. simpl. auto.
  - break_and. subst. simpl. auto.
Qed.

Lemma V_is_value_2 : 
  forall tau x1 x2, 
    V tau x1 x2 -> 
    is_value x2.
Proof.
  destruct tau; simpl; intuition; break_exists.
  - subst. subst. simpl. auto.
  - break_and. subst. simpl. auto.
Qed.

Lemma if_compatability : 
  forall Gamma e1 e1' e2 e2' e3 e3' tau, 
    semantic_relation Gamma e1 e1' TBool -> 
    semantic_relation Gamma e2 e2' tau -> 
    semantic_relation Gamma e3 e3' tau -> 
    semantic_relation Gamma (TIf e1 e2 e3) (TIf e1' e2' e3') tau.
Proof.
  unfold semantic_relation, E.
  intros. simpl.
  repeat match goal with 
  | [ H : forall _ _, _ |- _ ] => 
    specialize (H gamma1 gamma2); concludes
  end.     simpl in *. 
  break_and. break_exists. break_and. break_exists. intuition.
  subst. subst. 
  pose proof step_star_if (multi_subs gamma1 e1) _ (multi_subs gamma1 e2) 
       (multi_subs gamma1 e3) $(eauto)$.
  pose proof step_star_if (multi_subs gamma2 e1') _ (multi_subs gamma2 e2')
       (multi_subs gamma2 e3') $(eauto)$.
  destruct x5.
  - exists x1, x2. intuition.
    + eapply step_star_trans. eauto.
      eapply step_star_step_left. constructor. eauto.
    + eapply step_star_trans. eauto.
      eapply step_star_step_left. constructor. eauto.
  - exists x, x0. intuition.
    + eapply step_star_trans. eauto.
      eapply step_star_step_left. constructor. eauto.
    + eapply step_star_trans. eauto.
      eapply step_star_step_left. constructor. eauto.
Qed.

Lemma app_compatability : 
  forall Gamma e1 e1' e2 e2' tau2 tau, 
    semantic_relation Gamma e1 e1' (TArrow tau2 tau) -> 
    semantic_relation Gamma e2 e2' tau2 -> 
    semantic_relation Gamma (TApp e1 e2) (TApp e1' e2') tau.
Proof.
  unfold semantic_relation, E.
  intros. simpl.
  repeat match goal with 
  | [ H : forall _ _, _ |- _ ] => 
    specialize (H gamma1 gamma2); concludes
  end.     simpl in *. 
  break_and. break_exists. break_and. intuition eauto.
  pose proof app_step_star_1 _ x1 (multi_subs gamma1 e2) $(eauto)$.
  pose proof app_step_star_1 _ x2 (multi_subs gamma2 e2') $(eauto)$.
  break_exists. break_and. subst.
  match goal with 
  | [ H : forall _ _, _ |- _ ] => specialize (H _ _ $(eauto)$)
  end.
  break_exists. break_and. exists x1, x2.
  intuition.
  - eapply step_star_trans. eauto.
    eapply step_star_trans. eauto using app_step_star_2. 
    eapply step_star_step_left. constructor.
    + eauto using V_is_value_1.
    + auto.
  - eapply step_star_trans. eauto.
    eapply step_star_trans. eauto using app_step_star_2. 
    eapply step_star_step_left. constructor.
    + eauto using V_is_value_2.
    + auto.
Qed.

Lemma const_compatability : 
  forall Gamma b, 
    semantic_relation Gamma (TConst b) (TConst b) TBool.
Proof.
  unfold semantic_relation. intros. simpl.
  apply V_implies_E. red. intuition. eauto.
Qed.

Theorem fundamental_property : 
  forall Gamma e tau, 
    has_type Gamma e tau -> 
    semantic_relation Gamma e e tau.
Proof.
  induction 1; intros.
  - auto using const_compatability.
  - auto using var_compatability.
  - auto using if_compatability.
  - auto using abs_compatability.
  - eauto using app_compatability.
Qed.

Lemma semantic_relation_plug : 
  forall C Gamma e1 e2 tau Gamma' tau', 
    has_type Gamma e1 tau -> 
    has_type Gamma e2 tau -> 
    semantic_relation Gamma e1 e2 tau -> 
    context_has_type C Gamma tau Gamma' tau' -> 
    semantic_relation Gamma' (plug e1 C) (plug e2 C) tau'.
Proof.
  induction C; intros; simpl; invc H2.
  - auto.
  - eapply if_compatability; eauto using fundamental_property.
  - eapply if_compatability; eauto using fundamental_property.
  - eapply if_compatability; eauto using fundamental_property.
  - eapply abs_compatability; eauto using CHT_plug.
  - eapply app_compatability; eauto using fundamental_property.
  - eapply app_compatability; eauto using fundamental_property.
Qed.

Lemma G_empty : 
  G TypingContext.empty Substitution.empty Substitution.empty.
Proof.
  unfold G.
  intuition.
  - rewrite TypingContext.get_empty in *. discriminate.
  - rewrite Substitution.get_empty in *. discriminate.
  - rewrite Substitution.get_empty in *. discriminate.
Qed.

Theorem soundness : 
  forall Gamma e1 e2 tau C, 
    has_type Gamma e1 tau -> 
    has_type Gamma e2 tau -> 
    semantic_relation Gamma e1 e2 tau -> 
    context_has_type C Gamma tau TypingContext.empty TBool -> 
    exists b, 
      step_star (plug e1 C) (TConst b) /\
      step_star (plug e2 C) (TConst b).
Proof.
  intros.
  eapply semantic_relation_plug in H1; eauto.
  unfold semantic_relation in *.
  specialize (H1 Substitution.empty Substitution.empty).
  conclude_using ltac:(eauto using G_empty).
  repeat rewrite multi_subs_empty_substitution in *.
  unfold E in *. intuition. 
  break_exists. break_and.
  simpl in *. intuition.
  break_exists. subst. subst. eauto.
Qed.
