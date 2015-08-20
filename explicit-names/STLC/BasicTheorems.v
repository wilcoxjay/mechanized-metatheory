Require Import SyntaxAndSemantics.
Require Import JRWTactics.

Require Import Relations.
Require Import Operators_Properties.

Hint Constructors has_type.

Fixpoint is_free_in (x : name) (e : term) : Prop := 
  match e with 
  | TConst _ => False
  | TVar y => x = y
  | TIf e1 e2 e3 => is_free_in x e1 \/ is_free_in x e2 \/ is_free_in x e3
  | TAbs y tau e => x <> y /\ is_free_in x e
  | TApp e1 e2 => is_free_in x e1 \/ is_free_in x e2
  end.

Lemma has_type_ext : 
  forall Gamma Gamma' e tau, 
    has_type Gamma e tau -> 
    (forall x, is_free_in x e -> TypingContext.get x Gamma = TypingContext.get x Gamma') -> 
    has_type Gamma' e tau.
Proof.
  intros.
  prep_induction H.
  induction H; intros.
  - auto.
  - constructor. now rewrite <- H0 by (simpl; auto).
  - simpl in *. auto 6. 
  - simpl in *. constructor. 
    apply IHhas_type.
    intros. destruct (name_eq_dec x x0). 
    + subst. repeat rewrite TypingContext.get_shadow_same. auto.
    + repeat rewrite TypingContext.get_shadow_diff by auto. auto.
  - simpl in *. firstorder.
Qed.

Lemma subs_free : 
  forall x to e, 
    is_free_in x (subs x to e) -> is_free_in x to.
Proof.
  induction e; simpl; intros.
  - intuition.
  - break_if.
    + auto.
    + simpl in *. congruence.
  - intuition.
  - break_if; simpl in *; intuition.
  - intuition.
Qed.

Lemma has_type_free : 
  forall e Gamma tau x, 
    has_type Gamma e tau -> 
    is_free_in x e -> 
    exists tyx, TypingContext.get x Gamma = Some tyx.
Proof.
  induction e; simpl; intros.
  - intuition.
  - invc H. firstorder.
  - invc H. firstorder.
  - invc H. firstorder.
    eapply_prop_hyp has_type has_type; eauto.
    break_exists_exists. simpl in *. 
    rewrite TypingContext.get_shadow_diff in * by auto. auto.
  - invc H. firstorder.
Qed.

Lemma subs_not_free : 
  forall x to e tau, 
    has_type TypingContext.empty to tau -> 
    is_free_in x (subs x to e) -> False.
Proof.
  intros.
  find_apply_lem_hyp subs_free.
  find_eapply_lem_hyp has_type_free; eauto.
  simpl in *. break_exists. 
  rewrite TypingContext.get_empty in *. discriminate.
Qed.

Lemma weakening_empty : 
  forall Gamma e tau, 
    has_type TypingContext.empty e tau -> 
    has_type Gamma e tau.
Proof.
  intros.
  eapply has_type_ext; eauto.
  intros.
  find_eapply_lem_hyp has_type_free; eauto.
  simpl in *. break_exists. 
  rewrite TypingContext.get_empty in *. discriminate.
Qed.

Lemma canonical_forms_bool : 
  forall e, 
    has_type TypingContext.empty e TBool -> 
    is_value e -> 
    e = TConst true \/ e = TConst false.
Proof.
  intros.
  destruct e; invc H; firstorder.
  destruct b; auto.
Qed.

Lemma canonical_forms_arrow : 
  forall e ty1 ty2, 
    has_type TypingContext.empty e (TArrow ty1 ty2) -> 
    is_value e -> 
    exists x b, e = TAbs x ty1 b.
Proof.
  intros.
  destruct e; invc H; firstorder.
Qed.

Lemma values_are_irreducible : 
  forall e, 
    is_value e -> 
    irreducible e.
Proof.
  unfold irreducible.
  destruct e; simpl; intuition; solve_by_inversion.
Qed.

Lemma irreducible_no_step : 
  forall e e', 
    irreducible e -> 
    step e e' -> 
    False.
Proof.
  unfold irreducible.
  intros. eauto.
Qed.

Lemma step_det : 
  forall e1 e2 e2', 
    step e1 e2 -> 
    step e1 e2' -> 
    e2 = e2'.
Proof.
  intros.
  prep_induction H. 
  induction H; intros;
  match goal with 
  | [ H : step ?x _  |- _ ] => ((is_var x; fail 1) || invc H)
  end; auto; try solve [f_equal; auto]; try solve_by_inversion; 
  try solve [exfalso; eauto using irreducible_no_step, values_are_irreducible].
Qed.

Lemma step_star_left_inv : 
  forall e e', 
    step_star e e' -> 
    e = e' \/ exists e'', step e e'' /\ step_star e'' e'.
Proof.
  unfold step_star.
  intros.
  find_apply_lem_hyp clos_rtn1_rt.
  find_apply_lem_hyp clos_rt_rt1n.
  inversion H.
  - auto.
  - right. subst.
    eexists. intuition eauto.
    find_apply_lem_hyp clos_rt1n_rt.
    find_apply_lem_hyp clos_rt_rtn1.
    auto.
Qed.

Lemma terminates_forward_reduction : 
  forall e e', 
    terminates e -> 
    step e e' -> 
    terminates e'.
Proof.
  unfold terminates.
  intuition. break_exists_exists. intuition.
  find_apply_lem_hyp step_star_left_inv.
  intuition.
  - subst. exfalso. eauto using irreducible_no_step.
  - break_exists. intuition.
    match goal with 
    | [ H : step ?e ?x, H' : step ?e ?y |- _ ] => assert (x = y) by eauto using step_det
    end.
    subst. 
    auto.
Qed.

Lemma step_star_step_left : 
  forall e e' e'', 
    step e e' -> 
    step_star e' e'' -> 
    step_star e e''.
Proof.
  unfold step_star.
  intros.
  eapply clos_rt_rtn1.
  eapply rt_trans. 
  - eauto using rt_step. 
  - eauto using clos_rtn1_rt.
Qed.

Lemma terminates_backward_reduction : 
  forall e e', 
    terminates e' -> 
    step e e' -> 
    terminates e.
Proof.
  unfold terminates.
  intros. break_exists_exists. 
  intuition.
  eauto using step_star_step_left.
Qed.

Lemma step_star_trans : 
  forall e e' e'', 
    step_star e e' -> 
    step_star e' e'' ->
    step_star e e''.
Proof.
  unfold step_star. intros.
  apply clos_rt_rtn1.
  eapply rt_trans; eauto using clos_rtn1_rt.
Qed.

Lemma app_step_star_1 : 
  forall e1 e1' e2, 
    step_star e1 e1' -> 
    step_star (TApp e1 e2)
              (TApp e1' e2).
Proof.
  induction 1; intros.
  - constructor.
  - eapply step_star_trans; eauto.
    eapply step_star_step_left. 
    + eapply step_app1; eauto. 
    + constructor.
Qed.

Lemma app_step_star_2 : 
  forall x tau e1 e2 e2', 
    step_star e2 e2' -> 
    step_star (TApp (TAbs x tau e1) e2)
              (TApp (TAbs x tau e1) e2').
Proof.
  induction 1; intros.
  - constructor.
  - eapply step_star_trans; eauto.
    eapply step_star_step_left. 
    + eapply step_app2; eauto. firstorder.
    + constructor.
Qed.

Lemma step_star_if : 
  forall e1 e1' e2 e3, 
    step_star e1 e1' -> 
    step_star (TIf e1 e2 e3) (TIf e1' e2 e3).
Proof.
  induction 1; intros.
  - constructor.
  - eapply step_star_trans; eauto.
    eapply step_star_step_left. 
    + apply step_if_step; eauto.
    + constructor.
Qed.

Lemma subs_not_free_same : 
  forall x to e, 
    (is_free_in x e -> False) -> 
    subs x to e = e.
Proof.
  induction e; simpl; intros.
  - auto.
  - break_if; congruence.
  - f_equal; firstorder.
  - break_if; auto.
    f_equal; firstorder.
  - f_equal; firstorder.
Qed.

Lemma const_terminates : 
  forall b, 
    terminates (TConst b).
Proof.
  unfold terminates.
  intros. exists (TConst b). intuition.
  - red. intros. solve_by_inversion.
  - red. constructor.
Qed.

Lemma lambda_terminates : 
  forall x tau e, 
    terminates (TAbs x tau e).
Proof.
  unfold terminates.
  intros.
  exists (TAbs x tau e).
  intuition.
  - red. intros. invc H.
  - constructor.
Qed.

Lemma step_star_left_ind : 
  forall (P : term -> term -> Prop),
    (forall x, P x x) -> 
    (forall x y z, step x y -> step_star y z -> P y z -> P x z) -> 
    forall x a, step_star x a -> P x a.
Proof.
  unfold step_star.
  intros.
  find_apply_lem_hyp clos_rtn1_rt.
  find_apply_lem_hyp clos_rt_rt1n.
  eapply clos_refl_trans_1n_ind; eauto.
  intros.
  eapply H0; eauto.
  eauto using clos_rt1n_rt, clos_rt_rtn1.
Qed.

Lemma step_star_if_inv : 
  forall e1 e2 e3 e', 
    step_star (TIf e1 e2 e3) e' -> 
    irreducible e' -> 
    exists e1', 
      step_star e1 e1' /\
      irreducible e1' /\
      step_star (TIf e1' e2 e3) e'.
Proof.
  intros.
  prep_induction H.
  induction H using step_star_left_ind; intros; subst.
  - exists e1. intuition; try solve [constructor].
    unfold irreducible in *.
    intros.
    eapply H0. econstructor. eauto.
  - inv H.
    + eexists. intuition.
      * constructor.
      * apply values_are_irreducible. simpl. auto.
      * eauto using step_star_step_left. 
    + eexists. intuition.
      * constructor.
      * apply values_are_irreducible. simpl. auto.
      * eauto using step_star_step_left. 
    + specialize (IHstep_star _ _ _ $(auto)$ $(eauto)$).
      break_exists_exists. intuition eauto using step_star_step_left. 
Qed.

Lemma step_star_TConst : 
  forall b e, 
    step_star (TConst b) e -> 
    e = TConst b.
Proof.
  intros.
  find_apply_lem_hyp step_star_left_inv. intuition.
  break_exists. intuition. solve_by_inversion.
Qed.

Lemma step_star_TAbs : 
  forall x tau e e', 
    step_star (TAbs x tau e) e' -> 
    e' = TAbs x tau e.
Proof.
  intros.
  find_apply_lem_hyp step_star_left_inv.
  firstorder.
  solve_by_inversion.
Qed.

Lemma step_star_value : 
  forall v e', 
    is_value v -> 
    step_star v e' -> 
    v = e'.
Proof.
  destruct v; simpl; intuition.
  - symmetry. auto using step_star_TConst.
  - symmetry. auto using step_star_TAbs.
Qed.

Lemma step_star_app_inv_1 : 
  forall e1 e2 e', 
    step_star (TApp e1 e2) e' -> 
    irreducible e' -> 
    exists e1', 
      step_star e1 e1' /\ irreducible e1' /\ step_star (TApp e1' e2) e'.
Proof.
  intros.
  prep_induction H.
  induction H using step_star_left_ind; intros; subst.
  - exists e1. intuition; try solve [constructor].
    unfold irreducible in *.
    intros.
    eapply H0. econstructor. eauto.
  - inv H.
    + eexists. intuition.
      * constructor.
      * apply values_are_irreducible. simpl. auto.
      * eauto using step_star_step_left.
    + specialize (IHstep_star _ _ $(auto)$ $(eauto)$).
      break_exists_exists. intuition eauto using step_star_step_left. 
    + specialize (IHstep_star _ _ $(auto)$ $(eauto)$).
      break_exists_exists. intuition.
      match goal with 
      | [ H : is_value _ |- _ ] => eapply step_star_value in H; eauto
      end.
      subst.
      eauto using step_star_step_left. 
Qed.

Lemma step_star_app_inv_2 : 
  forall e1 e2 e', 
    step_star (TApp e1 e2) e' -> 
    is_value e1 -> 
    irreducible e' -> 
    exists e2', 
      step_star e2 e2' /\ irreducible e2' /\ step_star (TApp e1 e2') e'.
Proof.
  intros.
  prep_induction H.
  induction H using step_star_left_ind; intros; subst.
  - exists e2. intuition; try solve [constructor].
    unfold irreducible in *.
    intros.
    eapply H1. eapply step_app2; eauto.
  - inv H.
    + eexists. intuition.
      * constructor.
      * apply values_are_irreducible. simpl. auto.
      * eauto using step_star_step_left.
    + exfalso. eauto using irreducible_no_step, values_are_irreducible.
    + specialize (IHstep_star e1 e2' $(auto)$ $(auto)$ $(auto)$).
      break_exists_exists. intuition.
      eauto using step_star_step_left. 
Qed.

Lemma inhabited : 
  forall tau (x : name), 
  exists e, 
    has_type TypingContext.empty e tau.
Proof.
  intros. induction tau.
  - exists (TConst true). auto.
  - break_exists_name e2. 
    break_exists_name e1.
    exists (TAbs x tau1 e2).
    constructor.
    eauto using weakening_empty.
Qed.

Lemma has_type_empty_not_free : 
  forall tau e x, 
    has_type TypingContext.empty e tau -> 
    is_free_in x e -> False.
Proof.
  intros.
  find_eapply_lem_hyp has_type_free; eauto.
  break_exists. rewrite TypingContext.get_empty in *. discriminate.
Qed.
