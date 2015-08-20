Require Import Arith.
Require Import Omega.
Require Import List.
Import ListNotations.

Require Import Relations.
Require Import Operators_Properties.

Require Import JRWTactics.

Definition name : Type := nat.
Definition name_eq_dec := eq_nat_dec.

Inductive type : Type :=
| TBool : type
| TArrow : type -> type -> type.

Inductive term : Type :=
| TConst : bool -> term
| TVar : name -> term
| TIf : term -> term -> term -> term
| TAbs : type -> term -> term
| TApp : term -> term -> term.

Fixpoint shift_up (d c : nat) (e : term) : term :=
  match e with
  | TConst _ => e
  | TVar x => if lt_dec x c then e else TVar (d + x)
  | TIf e1 e2 e3 => TIf (shift_up d c e1) (shift_up d c e2) (shift_up d c e3)
  | TAbs tau e => TAbs tau (shift_up d (1 + c) e)
  | TApp e1 e2 => TApp (shift_up d c e1) (shift_up d c e2)
  end.

Fixpoint shift_down (d c : nat) (e : term) : term :=
  match e with
  | TConst _ => e
  | TVar x => if lt_dec x c then e else TVar (x - d)
  | TIf e1 e2 e3 => TIf (shift_down d c e1) (shift_down d c e2) (shift_down d c e3)
  | TAbs tau e => TAbs tau (shift_down d (1 + c) e)
  | TApp e1 e2 => TApp (shift_down d c e1) (shift_down d c e2)
  end.

Fixpoint at_least (d c : nat) (e : term) : Prop :=
  match e with
  | TConst _ => True
  | TVar x => x < c \/ d <= x
  | TIf e1 e2 e3 => at_least d c e1 /\ at_least d c e2 /\ at_least d c e3
  | TAbs tau e => at_least (1 + d) (1 + c) e
  | TApp e1 e2 => at_least d c e1 /\ at_least d c e2
  end.

Fixpoint subs (from : nat) (to : term) (e : term) : term :=
  match e with
  | TConst _ => e
  | TVar x => if name_eq_dec from x then to else e
  | TIf e1 e2 e3 => TIf (subs from to e1) (subs from to e2) (subs from to e3)
  | TAbs tau e => TAbs tau (subs (1 + from) (shift_up 1 0 to) e)
  | TApp e1 e2 => TApp (subs from to e1) (subs from to e2)
  end.

Definition context := list type.
Definition lookup (x : name) (Gamma : context) : option type := nth_error Gamma x.
Definition extend (tau : type) (Gamma : context) : context := tau :: Gamma.
Definition empty : context := [].

Inductive has_type : context -> term -> type -> Prop :=
| HT_const : forall Gamma b, has_type Gamma (TConst b) TBool
| HT_var : forall Gamma x tau, lookup x Gamma = Some tau -> has_type Gamma (TVar x) tau
| HT_if : forall Gamma e1 e2 e3 tau,
    has_type Gamma e1 TBool ->
    has_type Gamma e2 tau ->
    has_type Gamma e3 tau ->
    has_type Gamma (TIf e1 e2 e3) tau
| HT_abs : forall Gamma tau2 tau e,
    has_type (extend tau2 Gamma) e tau ->
    has_type Gamma (TAbs tau2 e) (TArrow tau2 tau)
| HT_app : forall Gamma tau2 tau e1 e2,
    has_type Gamma e1 (TArrow tau2 tau) ->
    has_type Gamma e2 tau2 ->
    has_type Gamma (TApp e1 e2) tau.

Fixpoint is_free_in (x : name) (e : term) : Prop :=
  match e with
  | TConst _ => False
  | TVar y => if name_eq_dec x y then True else False
  | TIf e1 e2 e3 => is_free_in x e1 \/ is_free_in x e2 \/ is_free_in x e3
  | TAbs tau e => is_free_in (1 + x) e
  | TApp e1 e2 => is_free_in x e1 \/ is_free_in x e2
  end.

Hint Constructors has_type.

Lemma has_type_ext :
  forall Gamma Gamma' e tau,
    has_type Gamma e tau ->
    (forall x, is_free_in x e -> lookup x Gamma = lookup x Gamma') ->
    has_type Gamma' e tau.
Proof.
  intros.
  prep_induction H.
  induction H; intros.
  - auto.
  - specialize (H0 x). simpl in *. break_if; try congruence.
    concludes. find_rewrite. auto.
  - simpl in *. constructor; firstorder.
  - simpl in *. constructor. eapply IHhas_type.
    intros. destruct x; simpl; auto.
  - simpl in *. econstructor; eauto.
Qed.

Lemma has_type_is_free_in :
  forall x Gamma e tau,
    has_type Gamma e tau ->
    is_free_in x e ->
    exists taux, lookup x Gamma = Some taux.
Proof.
  intros.
  prep_induction H.
  induction H; simpl; intuition.
  - break_if.
    + subst. eauto.
    + intuition.
  - firstorder.
Qed.

Lemma lookup_empty :
  forall x,
    lookup x empty = None.
Proof.
  destruct x; auto.
Qed.

Lemma weakening_empty :
  forall e tau Gamma,
    has_type empty e tau ->
    has_type Gamma e tau.
Proof.
  intros.
  apply has_type_ext with (Gamma := empty); auto.
  intros.
  find_eapply_lem_hyp has_type_is_free_in; eauto.
  break_exists.
  rewrite lookup_empty in *. discriminate.
Qed.

Lemma lookup_x_lt :
  forall x Gamma tau,
    lookup x Gamma = Some tau ->
    x < length Gamma.
Proof.
  induction x; simpl; intros.
  - break_match; simpl.
    + discriminate.
    + omega.
  - break_match; simpl.
    + discriminate.
    + apply lt_n_S. eauto.
Qed.

Lemma length_extend :
  forall Gamma tau,
    length (extend tau Gamma) = S (length Gamma).
Proof.
  induction Gamma; simpl; intros; auto.
Qed.

Lemma shift_up_has_type :
  forall Gamma e tau d c,
    has_type Gamma e tau ->
    length Gamma <= c ->
    has_type Gamma (shift_up d c e) tau.
Proof.
  intros.
  prep_induction H.
  induction H; intros; simpl.
  - auto.
  - break_if.
    + auto.
    + find_apply_lem_hyp lookup_x_lt. omega.
  - auto.
  - constructor. eapply IHhas_type. rewrite length_extend. omega.
  - eauto.
Qed.

Lemma shift_down_has_type :
  forall Gamma e tau d c,
    has_type Gamma e tau ->
    length Gamma <= c ->
    has_type Gamma (shift_down d c e) tau.
Proof.
  intros.
  prep_induction H.
  induction H; intros; simpl.
  - auto.
  - break_if.
    + auto.
    + find_apply_lem_hyp lookup_x_lt. omega.
  - auto.
  - constructor. eapply IHhas_type. rewrite length_extend. omega.
  - eauto.
Qed.

Lemma substitution :
  forall e x to tau taux Gamma,
    has_type empty to taux ->
    lookup x Gamma = Some taux ->
    has_type Gamma e tau ->
    has_type Gamma (subs x to e) tau.
Proof.
  induction e; intros; simpl.
  - auto.
  - break_if.
    + subst. invc H1. apply weakening_empty. congruence.
    + auto.
  - invc H1. eauto.
  - invc H1. constructor. eapply IHe; eauto.
    apply shift_up_has_type; auto.
  - invc H1. eauto.
Qed.

Lemma shift_up_free :
  forall e x d c,
    is_free_in (d + x) (shift_up d c e) ->
    c <= x ->
    is_free_in x e.
Proof.
  induction e; simpl; firstorder.
  - repeat (break_if; simpl in * ); intuition.
  - eapply IHe with (c := S c) (d := d).
    + rewrite <- plus_n_Sm. auto.
    + omega.
Qed.

Lemma subs_free :
  forall e x to,
    is_free_in x (subs x to e) ->
    is_free_in x to.
Proof.
  induction e; simpl; intuition.
  - break_if.
    + auto.
    + simpl in *. break_if; intuition.
  - eapply IHe in H.
    eapply shift_up_free with (d := 1) (c := 0); auto.
    omega.
Qed.

Definition is_value (e : term) : Prop :=
  match e with
  | TConst _ => True
  | TAbs _ _ => True
  | _ => False
  end.

Inductive step : term -> term -> Prop :=
| step_if_true :
    forall e2 e3,
      step (TIf (TConst true) e2 e3) e2
| step_if_false :
    forall e2 e3,
      step (TIf (TConst false) e2 e3) e3
| step_if_step :
    forall e1 e1' e2 e3,
      step e1 e1' ->
      step (TIf e1 e2 e3) (TIf e1' e2 e3)
| step_beta :
    forall tau e1 e2,
      is_value e2 ->
      step (TApp (TAbs tau e1) e2) (shift_down 1 0 (subs 0 e2 e1))
| step_app1 :
    forall e1 e1' e2,
      step e1 e1' ->
      step (TApp e1 e2) (TApp e1' e2)
| step_app2 :
    forall e1 e2 e2',
      is_value e1 ->
      step e2 e2' ->
      step (TApp e1 e2) (TApp e1 e2').

Definition step_star : term -> term -> Prop := clos_refl_trans_n1 _ step.

Theorem preservation :
  forall e e',
    step e e' ->
    forall tau,
      has_type empty e tau ->
      has_type empty e' tau.
Proof.
  induction 1; intros.
  - invc H. auto.
  - invc H. auto.
  - invc H0. auto.
  - invc H0. invc H4.
    eapply shift_down_has_type; auto.
    eapply substitution with (x := 0) in H2; eauto.
    eapply has_type_ext; eauto.
    intros.
    destruct x.
    + apply subs_free in H0.
      find_eapply_lem_hyp has_type_is_free_in; eauto.
      break_exists. discriminate.
    + simpl. rewrite lookup_empty. auto.
  - invc H0. eauto.
  - invc H1. eauto.
Qed.

Lemma canonical_forms_bool :
  forall e,
    has_type empty e TBool ->
    is_value e ->
    exists b, e = TConst b.
Proof.
  destruct e; simpl; intuition eauto.
  invc H.
Qed.

Hint Constructors step.

Lemma canonical_forms_arrow :
  forall e tau1 tau2,
    has_type empty e (TArrow tau1 tau2) ->
    is_value e ->
    exists e', e = TAbs tau1 e'.
Proof.
  destruct e; simpl; intuition.
  - invc H.
  - invc H. eauto.
Qed.

Theorem progress :
  forall e tau,
    has_type empty e tau ->
    is_value e \/ exists e', step e e'.
Proof.
  induction e; intros.
  - simpl. auto.
  - invc H. rewrite lookup_empty in *. discriminate.
  - invc H.
    copy_apply IHe1 H4.
    intuition.
    + find_eapply_lem_hyp canonical_forms_bool; auto.
      break_exists. subst.
      destruct x; eauto.
    + break_exists. eauto.
  - simpl. auto.
  - invc H.
    copy_apply IHe1 H3.
    intuition.
    + find_eapply_lem_hyp canonical_forms_arrow; eauto.
      break_exists. subst.
      copy_apply IHe2 H5.
      intuition.
      * eauto.
      * break_exists. right. eexists. apply step_app2; eauto. simpl. auto.
    + break_exists. eauto.
Qed.
