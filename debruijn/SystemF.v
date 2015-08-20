Require Import Arith.
Require Import Omega.
Require Import List.
Import ListNotations.
Require Import Relations.
Require Import Operators_Properties.

Require Import JRWTactics.

Set Firstorder Solver (try congruence; eauto).

Definition name : Type := nat.
Definition name_eq_dec := eq_nat_dec.

Definition type_name : Type := nat.
Definition type_name_eq_dec := eq_nat_dec.

Inductive type : Type :=
| TyBool : type
| TyVar : type_name -> type
| TyArrow : type -> type -> type
| TyForall : type -> type.

Inductive term : Type :=
| TConst : bool -> term
| TVar : name -> term
| TIf : term -> term -> term -> term
| TAbs : type -> term -> term
| TApp : term -> term -> term
| TTyAbs : term -> term
| TTyApp : term -> type -> term.


Definition kinding_context := list unit.
Definition kinding_context_lookup (x : type_name) (Delta : kinding_context) : option unit := nth_error Delta x.
Definition kinding_context_extend (Delta : kinding_context) : kinding_context := tt :: Delta.
Definition kinding_context_empty : kinding_context := [].

Inductive well_kinded : kinding_context -> type -> Prop :=
| WK_var : forall Delta alpha u,
    kinding_context_lookup alpha Delta = Some u ->
    well_kinded Delta (TyVar alpha)
| WK_bool : forall Delta, well_kinded Delta TyBool
| WK_arrow : forall Delta tau1 tau2,
    well_kinded Delta tau1 ->
    well_kinded Delta tau2 ->
    well_kinded Delta (TyArrow tau1 tau2)
| WK_forall : forall Delta tau,
    well_kinded (kinding_context_extend Delta) tau ->
    well_kinded Delta (TyForall tau).

Definition typing_context := list type.
Definition typing_context_lookup (x : name) (Gamma : typing_context) : option type := nth_error Gamma x.
Definition typing_context_extend (tau : type) (Gamma : typing_context) : typing_context := tau :: Gamma.
Definition typing_context_empty : typing_context := [].

Fixpoint ty_shift_up (d c : nat) (tau : type) : type :=
  match tau with
  | TyBool => tau
  | TyVar alpha => if lt_dec alpha c then tau else TyVar (d + alpha)
  | TyArrow tau1 tau2 => TyArrow (ty_shift_up d c tau1) (ty_shift_up d c tau2)
  | TyForall tau' => TyForall (ty_shift_up d (1 + c) tau')
  end.

Fixpoint ty_shift_down (d c : nat) (tau : type) : type :=
  match tau with
  | TyBool => tau
  | TyVar alpha => if lt_dec alpha c then tau else TyVar (alpha - d)
  | TyArrow tau1 tau2 => TyArrow (ty_shift_down d c tau1) (ty_shift_down d c tau2)
  | TyForall tau' => TyForall (ty_shift_down d (1 + c) tau')
  end.

Fixpoint ty_subs_ty (from : nat) (to : type) (tau : type) : type :=
  match tau with
  | TyBool => tau
  | TyVar alpha => if name_eq_dec from alpha then to else tau
  | TyArrow tau1 tau2 => TyArrow (ty_subs_ty from to tau1) (ty_subs_ty from to tau2)
  | TyForall tau' => TyForall (ty_subs_ty (1 + from) (ty_shift_up 1 0 to) tau')
  end.

Fixpoint ty_subs_exp (from : nat) (to : type) (e : term) : term :=
  match e with
  | TConst _ => e
  | TVar _ => e
  | TIf e1 e2 e3 => TIf (ty_subs_exp from to e1) (ty_subs_exp from to e2) (ty_subs_exp from to e3)
  | TAbs tau e' => TAbs (ty_subs_ty from to tau) (ty_subs_exp from to e')
  | TApp e1 e2 => TApp (ty_subs_exp from to e1) (ty_subs_exp from to e2)
  | TTyAbs e' => TTyAbs (ty_subs_exp (1 + from) (ty_shift_up 1 0 to) e')
  | TTyApp e1 tau => TTyApp (ty_subs_exp from to e1) (ty_subs_ty from to tau)
  end.

Fixpoint ty_shift_up_exp (d c : nat) (e : term) : term :=
  match e with
  | TConst _ => e
  | TVar _ => e
  | TIf e1 e2 e3 => TIf (ty_shift_up_exp d c e1) (ty_shift_up_exp d c e2) (ty_shift_up_exp d c e3)
  | TAbs tau e' => TAbs (ty_shift_up d c tau) (ty_shift_up_exp d c e')
  | TApp e1 e2 => TApp (ty_shift_up_exp d c e1) (ty_shift_up_exp d c e2)
  | TTyAbs e' => TTyAbs (ty_shift_up_exp d (1 + c) e')
  | TTyApp e1 tau => TTyApp (ty_shift_up_exp d c e1) (ty_shift_up d c tau)
  end.

Fixpoint ty_shift_down_exp (d c : nat) (e : term) : term :=
  match e with
  | TConst _ => e
  | TVar _ => e
  | TIf e1 e2 e3 => TIf (ty_shift_down_exp d c e1) (ty_shift_down_exp d c e2) (ty_shift_down_exp d c e3)
  | TAbs tau e' => TAbs (ty_shift_down d c tau) (ty_shift_down_exp d c e')
  | TApp e1 e2 => TApp (ty_shift_down_exp d c e1) (ty_shift_down_exp d c e2)
  | TTyAbs e' => TTyAbs (ty_shift_down_exp d (1 + c) e')
  | TTyApp e1 tau => TTyApp (ty_shift_down_exp d c e1) (ty_shift_down d c tau)
  end.

Inductive has_type : kinding_context -> typing_context -> term -> type -> Prop :=
| HTConst : forall Delta Gamma b, has_type Delta Gamma (TConst b) TyBool
| HTVar : forall Delta Gamma x tau,
    typing_context_lookup x Gamma = Some tau ->
    has_type Delta Gamma (TVar x) tau
| HTIf : forall Delta Gamma e1 e2 e3 tau,
    has_type Delta Gamma e1 TyBool ->
    has_type Delta Gamma e2 tau ->
    has_type Delta Gamma e3 tau ->
    has_type Delta Gamma (TIf e1 e2 e3) tau
| HTAbs : forall Delta Gamma tyx e tau,
    well_kinded Delta tyx ->
    has_type Delta (typing_context_extend tyx Gamma) e tau ->
    has_type Delta Gamma (TAbs tyx e) (TyArrow tyx tau)
| HTApp : forall Delta Gamma e1 e2 ty2 tau,
    has_type Delta Gamma e1 (TyArrow ty2 tau) ->
    has_type Delta Gamma e2 ty2 ->
    has_type Delta Gamma (TApp e1 e2) tau
| HTTTyAbs : forall Delta Gamma e tau,
    has_type (kinding_context_extend Delta) (map (ty_shift_up 1 0) Gamma) e tau ->
    has_type Delta Gamma (TTyAbs e) (TyForall tau)
| HTTyApp : forall Delta Gamma e1 tau1 tau2,
    has_type Delta Gamma e1 (TyForall tau1) ->
    well_kinded Delta tau2 ->
    has_type Delta Gamma (TTyApp e1 tau2) (ty_shift_down 1 0 (ty_subs_ty 0 (ty_shift_up 1 0 tau2) tau1)).

Definition is_value (e : term) : Prop :=
  match e with
  | TConst _ => True
  | TAbs _ _ => True
  | TTyAbs _ => True
  | _ => False
  end.

Fixpoint shift_up (d c : nat) (e : term) : term :=
  match e with
  | TConst _ => e
  | TVar x => if lt_dec x c then e else TVar (d + x)
  | TIf e1 e2 e3 => TIf (shift_up d c e1) (shift_up d c e2) (shift_up d c e3)
  | TAbs tau e => TAbs tau (shift_up d (1 + c) e)
  | TApp e1 e2 => TApp (shift_up d c e1) (shift_up d c e2)
  | TTyAbs e' => TTyAbs (shift_up d c e')
  | TTyApp e' tau => TTyApp (shift_up d c e') tau
  end.

Fixpoint shift_down (d c : nat) (e : term) : term :=
  match e with
  | TConst _ => e
  | TVar x => if lt_dec x c then e else TVar (x - d)
  | TIf e1 e2 e3 => TIf (shift_down d c e1) (shift_down d c e2) (shift_down d c e3)
  | TAbs tau e => TAbs tau (shift_down d (1 + c) e)
  | TApp e1 e2 => TApp (shift_down d c e1) (shift_down d c e2)
  | TTyAbs e' => TTyAbs (shift_down d c e')
  | TTyApp e' tau => TTyApp (shift_down d c e') tau
  end.

Fixpoint subs (from : nat) (to : term) (e : term) : term :=
  match e with
  | TConst _ => e
  | TVar x => if name_eq_dec from x then to else e
  | TIf e1 e2 e3 => TIf (subs from to e1) (subs from to e2) (subs from to e3)
  | TAbs tau e => TAbs tau (subs (1 + from) (shift_up 1 0 to) e)
  | TApp e1 e2 => TApp (subs from to e1) (subs from to e2)
  | TTyAbs e' => TTyAbs (subs from to e')
  | TTyApp e' tau => TTyApp (subs from to e') tau
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
      step (TApp e1 e2) (TApp e1 e2')
| step_ty_beta :
    forall e tau,
      step (TTyApp (TTyAbs e) tau) (ty_shift_down_exp 1 0 (ty_subs_exp 0 tau e))
| step_ty_app :
    forall e e' tau,
      step e e' ->
      step (TTyApp e tau) (TTyApp e' tau).

Hint Constructors has_type.

Fixpoint is_free_in (x : name) (e : term) : Prop :=
  match e with
  | TConst _ => False
  | TVar y => if name_eq_dec x y then True else False
  | TIf e1 e2 e3 => is_free_in x e1 \/ is_free_in x e2 \/ is_free_in x e3
  | TAbs tau e => is_free_in (1 + x) e
  | TApp e1 e2 => is_free_in x e1 \/ is_free_in x e2
  | TTyAbs e' => is_free_in x e'
  | TTyApp e' tau => is_free_in x e'
  end.

Fixpoint is_free_in_ty (alpha : type_name) (tau : type) : Prop :=
  match tau with
  | TyBool => False
  | TyVar beta => alpha = beta
  | TyArrow tau1 tau2 => is_free_in_ty alpha tau1 \/ is_free_in_ty alpha tau2
  | TyForall tau' => is_free_in_ty (1 + alpha) tau'
  end.

Lemma well_kinded_ext :
  forall Delta Delta' tau,
    well_kinded Delta tau ->
    (forall alpha, is_free_in_ty alpha tau -> kinding_context_lookup alpha Delta = kinding_context_lookup alpha Delta') ->
    well_kinded Delta' tau.
Proof.
  intros.
  prep_induction H.
  induction H; intros.
  - econstructor. rewrite <- H0; eauto. simpl. auto.
  - constructor.
  - simpl in *. constructor; firstorder.
  - simpl in *. constructor. eapply IHwell_kinded.
    intros. destruct alpha; simpl; auto.
Qed.

Fixpoint ty_is_free_in (alpha : type_name) (e : term) : Prop :=
  match e with
  | TConst _ => False
  | TVar _ => False
  | TIf e1 e2 e3 => ty_is_free_in alpha e1 \/ ty_is_free_in alpha e2 \/ ty_is_free_in alpha e3
  | TAbs tau e' => is_free_in_ty alpha tau \/ ty_is_free_in alpha e'
  | TApp e1 e2 => ty_is_free_in alpha e1 \/ ty_is_free_in alpha e2
  | TTyAbs e' => ty_is_free_in (1 + alpha) e'
  | TTyApp e' tau => is_free_in_ty alpha tau \/ ty_is_free_in alpha e'
  end.

Lemma typing_context_lookup_map :
  forall (f : type -> type) x Gamma tau,
    typing_context_lookup x Gamma = Some tau ->
    typing_context_lookup x (map f Gamma) = Some (f tau).
Proof.
  induction x; intros; simpl in *; destruct Gamma; try discriminate; simpl; auto.
  invc H. auto.
Qed.

Lemma typing_context_lookup_map_inv :
  forall (f : type -> type) x Gamma sigma,
    typing_context_lookup x (map f Gamma) = Some sigma ->
    exists tau, typing_context_lookup x Gamma = Some tau /\ sigma = f tau.
Proof.
  induction x; intros; simpl in *; destruct Gamma; simpl in *; try discriminate; auto.
  invc H. eauto.
Qed.

Lemma has_type_ext :
  forall Delta Delta' Gamma Gamma' e tau,
    has_type Delta Gamma e tau ->
    (forall x, is_free_in x e -> typing_context_lookup x Gamma = typing_context_lookup x Gamma') ->
    (forall alpha, ty_is_free_in alpha e -> kinding_context_lookup alpha Delta = kinding_context_lookup alpha Delta') ->
    has_type Delta' Gamma' e tau.
Proof.
  intros.
  prep_induction H.
  induction H; intros.
  - auto.
  - specialize (H0 x). simpl in *. break_if; try congruence.
    concludes. find_rewrite. auto.
  - simpl in *. constructor; firstorder.
  - simpl in *. constructor.
    + eapply well_kinded_ext; eauto.
    + eapply IHhas_type.
      * intros. destruct x; simpl; auto.
      * auto.
  - simpl in *. econstructor.
    + eapply IHhas_type1; eauto.
    + eapply IHhas_type2; eauto.
  - simpl in *. constructor. apply IHhas_type.
    + intros. destruct (typing_context_lookup x (map (ty_shift_up 1 0) Gamma)) eqn:?.
      * find_apply_lem_hyp typing_context_lookup_map_inv.
        break_exists_name tau'. break_and.
        erewrite typing_context_lookup_map with (tau := tau'); try congruence.
        find_higher_order_rewrite; auto.
      * { destruct (typing_context_lookup x (map (ty_shift_up 1 0) Gamma')) eqn:?; auto.
          find_apply_lem_hyp typing_context_lookup_map_inv.
          break_exists_name tau'. break_and.
          erewrite typing_context_lookup_map with (tau := tau') in *; try congruence.
          find_higher_order_rewrite; auto.
        }
    + intros. destruct alpha; simpl; auto.
  - simpl in *. constructor.
    + auto.
    + eapply well_kinded_ext; eauto.
Qed.

Lemma has_type_is_free_in :
  forall x Delta Gamma e tau,
    has_type Delta Gamma e tau ->
    is_free_in x e ->
    exists taux, typing_context_lookup x Gamma = Some taux.
Proof.
  intros.
  prep_induction H.
  induction H; simpl; intuition.
  - break_if.
    + subst. eauto.
    + intuition.
  - firstorder.
  - find_apply_hyp_hyp. break_exists.
    find_apply_lem_hyp typing_context_lookup_map_inv.
    break_exists_exists. intuition.
Qed.

Lemma well_kinded_is_free_in_ty :
  forall Delta tau alpha,
    well_kinded Delta tau ->
    is_free_in_ty alpha tau ->
    kinding_context_lookup alpha Delta = Some tt.
Proof.
  intros.
  prep_induction H.
  induction H; simpl; intuition.
  - destruct u. subst. auto.
  - find_apply_hyp_hyp. simpl in *. auto.
Qed.

Lemma has_type_ty_is_free_in :
  forall alpha Delta Gamma e tau,
    has_type Delta Gamma e tau ->
    ty_is_free_in alpha e ->
    kinding_context_lookup alpha Delta = Some tt.
Proof.
  intros.
  prep_induction H.
  induction H; simpl; intuition eauto using well_kinded_is_free_in_ty.
  find_apply_hyp_hyp. simpl in *. auto.
Qed.

Lemma typing_context_lookup_empty :
  forall x,
    typing_context_lookup x typing_context_empty = None.
Proof.
  destruct x; auto.
Qed.

Lemma kinding_context_lookup_empty :
  forall alpha,
    kinding_context_lookup alpha kinding_context_empty = None.
Proof.
  destruct alpha; auto.
Qed.

Lemma well_kinded_empty_no_free :
  forall tau alpha,
    well_kinded kinding_context_empty tau ->
    is_free_in_ty alpha tau -> False.
Proof.
  intros.
  find_eapply_lem_hyp well_kinded_is_free_in_ty; eauto.
  rewrite kinding_context_lookup_empty in *. discriminate.
Qed.

Lemma weakening_empty :
  forall e tau Delta Gamma,
    has_type kinding_context_empty typing_context_empty e tau ->
    has_type Delta Gamma e tau.
Proof.
  intros.
  eapply has_type_ext; eauto.
  - intros.
    find_eapply_lem_hyp has_type_is_free_in; eauto.
    break_exists.
    rewrite typing_context_lookup_empty in *. discriminate.
  - intros.
    find_eapply_lem_hyp has_type_ty_is_free_in; eauto.
    rewrite kinding_context_lookup_empty in *. discriminate.
Qed.

Lemma lookup_x_lt :
  forall x Gamma tau,
    typing_context_lookup x Gamma = Some tau ->
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
    length (typing_context_extend tau Gamma) = S (length Gamma).
Proof.
  induction Gamma; simpl; intros; auto.
Qed.

Lemma shift_up_has_type :
  forall e Delta Gamma tau d c,
    has_type Delta Gamma e tau ->
    length Gamma <= c ->
    has_type Delta Gamma (shift_up d c e) tau.
Proof.
  induction e; intros.
  - simpl. auto.
  - simpl. break_if.
    + auto.
    + invc H. find_apply_lem_hyp lookup_x_lt. omega.
  - simpl. invc H. auto.
  - simpl. invc H. constructor; auto.
    eapply IHe; auto. rewrite length_extend. omega.
  - simpl. invc H. eauto.
  - simpl. invc H. constructor. eapply IHe; auto. rewrite map_length. auto.
  - cbn [shift_up]. invc H. auto.
Qed.

Lemma shift_down_has_type :
  forall e Delta Gamma tau d c,
    has_type Delta Gamma e tau ->
    length Gamma <= c ->
    has_type Delta Gamma (shift_down d c e) tau.
Proof.
  induction e; intros.
  - simpl. auto.
  - simpl. break_if.
    + auto.
    + invc H. find_apply_lem_hyp lookup_x_lt. omega.
  - simpl. invc H. auto.
  - simpl. invc H. constructor; auto.
    eapply IHe; auto. rewrite length_extend. omega.
  - simpl. invc H. eauto.
  - simpl. invc H. constructor. eapply IHe; auto. rewrite map_length. auto.
  - cbn [shift_down]. invc H. auto.
Qed.

Lemma ty_shift_up_no_free_nop :
  forall tau d c,
    (forall alpha, c <= alpha -> is_free_in_ty alpha tau -> False) ->
    ty_shift_up d c tau = tau.
Proof.
  induction tau; intros; simpl.
  - auto.
  - break_if; auto.
    exfalso. apply H with (alpha := t).
    + omega.
    + simpl. auto.
  - simpl in *. f_equal; firstorder.
  - simpl in *. f_equal. eapply IHtau. intros. destruct alpha; try omega.
    apply H with (alpha := alpha); auto. omega.
Qed.

Lemma ty_shift_down_no_free_nop :
  forall tau d c,
    (forall alpha, c <= alpha -> is_free_in_ty alpha tau -> False) ->
    ty_shift_down d c tau = tau.
Proof.
  induction tau; intros; simpl.
  - auto.
  - break_if; auto.
    exfalso. apply H with (alpha := t).
    + omega.
    + simpl. auto.
  - simpl in *. f_equal; firstorder.
  - simpl in *. f_equal. eapply IHtau. intros. destruct alpha; try omega.
    apply H with (alpha := alpha); auto. omega.
Qed.

Fixpoint kinding_context_extend_n (n : nat) (Delta : kinding_context) : kinding_context :=
  match n with
  | 0 => Delta
  | S n' => kinding_context_extend (kinding_context_extend_n n' Delta)
  end.

Fixpoint kinding_context_append (Delta Delta' : kinding_context) : kinding_context :=
  match Delta with
  | [] => Delta'
  | u :: Delta0 => u :: kinding_context_append Delta0 Delta'
  end.

Lemma kinding_context_lookup_append_first :
  forall alpha Delta Delta',
    alpha < length Delta ->
    kinding_context_lookup alpha (kinding_context_append Delta Delta') =
    kinding_context_lookup alpha Delta.
Proof.
  induction alpha; intros; simpl; destruct Delta; simpl in *; auto with *; omega.
Qed.

Lemma kinding_context_lookup_append_second :
  forall Delta Delta' alpha,
    kinding_context_lookup (length Delta + alpha) (kinding_context_append Delta Delta') =
    kinding_context_lookup alpha Delta'.
Proof.
  induction Delta; intros; simpl in *; auto.
Qed.

Lemma kinding_context_lookup_extend_n_second :
  forall n x Delta,
    kinding_context_lookup (n + x) (kinding_context_extend_n n Delta) = kinding_context_lookup x Delta.
Proof.
  induction n; auto.
Qed.

Lemma extend_append :
  forall Delta Delta',
    kinding_context_extend (kinding_context_append Delta Delta') =
    kinding_context_append (kinding_context_extend Delta) Delta'.
Proof.
  induction Delta; auto.
Qed.

Hint Constructors well_kinded.

Lemma ty_shift_up_well_kinded_shift :
  forall tau d c Delta Delta',
    c = length Delta ->
    well_kinded (kinding_context_append Delta Delta') tau ->
    well_kinded (kinding_context_append Delta (kinding_context_extend_n d Delta')) (ty_shift_up d c tau).
Proof.
  induction tau; simpl; intros.
  - constructor.
  - invc H0.
    break_if.
    + econstructor. rewrite kinding_context_lookup_append_first in * by auto. eauto.
    + apply WK_var with (u := u).
      find_apply_lem_hyp Nat.nlt_ge.
      find_apply_lem_hyp Nat.le_exists_sub. break_exists. break_and.
      subst.
      replace (d + (x + length Delta)) with (length Delta + (d + x)) by omega.
      rewrite kinding_context_lookup_append_second.
      rewrite plus_comm in * |-.
      rewrite kinding_context_lookup_append_second in *.
      rewrite kinding_context_lookup_extend_n_second. auto.
  - invc H0. constructor; auto.
  - invc H0. constructor.
    rewrite extend_append. eapply IHtau; auto.
Qed.

Corollary ty_shift_up_well_kinded_shift_1_0 :
  forall tau Delta,
    well_kinded Delta tau ->
    well_kinded (kinding_context_extend Delta) (ty_shift_up 1 0 tau).
Proof.
  intros.
  pose proof ty_shift_up_well_kinded_shift tau 1 0 kinding_context_empty Delta.
  auto.
Qed.


Lemma ty_shift_down_well_kinded_shift :
  forall tau d c Delta Delta',
    c = length Delta ->
    well_kinded (kinding_context_append Delta (kinding_context_extend_n d Delta')) tau ->
    (forall alpha, is_free_in_ty alpha tau -> c <= alpha < c + d -> False) ->
    well_kinded (kinding_context_append Delta Delta') (ty_shift_down d c tau).
Proof.
  induction tau; simpl; intros.
  - constructor.
  - invc H0.
    break_if.
    + econstructor. rewrite kinding_context_lookup_append_first in * by auto. eauto.
    + destruct u. apply WK_var with (u := tt).
      find_apply_lem_hyp Nat.nlt_ge.
      find_apply_lem_hyp Nat.le_exists_sub. break_exists. break_and. subst.
      specialize (H1 (x + length Delta)). concludes.
      assert (x >= d) by omega.
      find_apply_lem_hyp Nat.le_exists_sub. break_exists. break_and. subst.
      replace (x0 + d + length Delta) with (d + (x0 + length Delta)) by omega.
      rewrite minus_plus in *.
      rewrite plus_comm.
      replace (x0 + d + length Delta) with (length Delta + (d + x0)) in * by omega.
      rewrite kinding_context_lookup_append_second in *.
      rewrite kinding_context_lookup_extend_n_second in *.
      auto.
  - invc H0. constructor; eauto.
  - invc H0. constructor.
    rewrite extend_append. eapply IHtau; auto.
    intros. destruct alpha; try omega. eapply H1; eauto. omega.
Qed.

Corollary ty_shift_down_well_kinded_shift_1_0 :
  forall Delta tau,
    well_kinded (kinding_context_extend Delta) tau ->
    (is_free_in_ty 0 tau -> False) ->
    well_kinded Delta (ty_shift_down 1 0 tau).
Proof.
  intros.
  eapply ty_shift_down_well_kinded_shift with (Delta := kinding_context_empty); auto.

  intros. destruct alpha; try omega. auto.
Qed.

Lemma ty_subs_ty_well_kinded :
  forall tau Delta alpha to,
    well_kinded Delta to ->
    well_kinded Delta tau ->
    well_kinded Delta (ty_subs_ty alpha to tau).
Proof.
  induction tau; simpl; intros.
  - auto.
  - break_if; auto.
  - invc H0. constructor; auto.
  - invc H0. constructor. eapply IHtau; auto.
    auto using ty_shift_up_well_kinded_shift_1_0.
Qed.

Lemma ty_shift_up_free :
  forall tau d c alpha,
    is_free_in_ty (d + alpha) (ty_shift_up d c tau) ->
    c <= alpha ->
    is_free_in_ty alpha tau.
Proof.
  induction tau; simpl; intuition eauto.
  - break_if.
    + simpl in *. omega.
    + simpl in *. eauto using plus_reg_l.
  - rewrite plus_n_Sm in *. eapply IHtau; eauto. omega.
Qed.

Lemma ty_subs_ty_is_free_in_ty :
  forall tau alpha to,
    is_free_in_ty alpha (ty_subs_ty alpha to tau) -> is_free_in_ty alpha to.
Proof.
  induction tau; simpl; intuition.
  - break_if.
    + auto.
    + simpl in *. congruence.
  - eapply IHtau in H.
    eapply ty_shift_up_free with (d := 1); eauto. omega.
Qed.

Lemma ty_shift_up_free_inv :
  forall tau alpha d c,
    is_free_in_ty alpha (ty_shift_up d c tau) ->
    (alpha < c /\ is_free_in_ty alpha tau) \/
    (c + d <= alpha /\ is_free_in_ty (alpha - d) tau).
Proof.
  induction tau; simpl; intuition.
  - break_if; simpl in *.
    + intuition.
    + right. intuition. symmetry. auto using plus_minus.
  - find_apply_hyp_hyp. intuition.
  - find_apply_hyp_hyp. intuition.
  - find_apply_hyp_hyp. intuition.
    right. intuition.
    rewrite minus_Sn_m; auto.
    omega.
Qed.

Lemma has_type_well_kinded :
  forall Delta Gamma e tau,
    has_type Delta Gamma e tau ->
    (forall x taux, typing_context_lookup x Gamma = Some taux -> well_kinded Delta taux) ->
    well_kinded Delta tau.
Proof.
  induction 1; eauto; intros.
  - constructor; auto. eapply IHhas_type. intros.
    destruct x; simpl in *.
    + solve_by_inversion.
    + eauto.
  - repeat concludes. solve_by_inversion.
  - constructor. eapply IHhas_type. intros.
    find_apply_lem_hyp typing_context_lookup_map_inv.
    firstorder. subst. eauto using ty_shift_up_well_kinded_shift_1_0.
  - concludes. invc IHhas_type.
    apply ty_shift_down_well_kinded_shift_1_0.
    + apply ty_subs_ty_well_kinded; auto.
      apply ty_shift_up_well_kinded_shift_1_0; auto.
    + intro. find_apply_lem_hyp ty_subs_ty_is_free_in_ty.
      find_apply_lem_hyp ty_shift_up_free_inv. intuition.
Qed.

Lemma substitution :
  forall e x to tau taux Gamma Delta,
    has_type kinding_context_empty typing_context_empty to taux ->
    typing_context_lookup x Gamma = Some taux ->
    has_type Delta Gamma e tau ->
    has_type Delta Gamma (subs x to e) tau.
Proof.
  induction e; intros; simpl.
  - auto.
  - break_if.
    + subst. invc H1. apply weakening_empty. congruence.
    + auto.
  - invc H1. eauto.
  - invc H1. constructor; auto.
    eapply IHe; eauto.
    apply shift_up_has_type; auto.
  - invc H1. eauto.
  - invc H1. constructor. eapply IHe; eauto.
    erewrite <- ty_shift_up_no_free_nop with (tau := taux).
    + eauto using typing_context_lookup_map.
    + intros.
      match goal with
      | [ H : has_type _ _ _ taux |- _ ] =>
        apply has_type_well_kinded in H
      end.
      * eauto using well_kinded_empty_no_free.
      * intros. rewrite typing_context_lookup_empty in *. discriminate.
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

Lemma extend_map :
  forall (f : type -> type) Gamma tau,
    typing_context_extend (f tau) (map f Gamma) =
    map f (typing_context_extend tau Gamma).
Proof.
  auto.
Qed.


Lemma well_kinded_weakening_empty :
  forall Delta tau,
    well_kinded kinding_context_empty tau ->
    well_kinded Delta tau.
Proof.
  intros.
  eapply well_kinded_ext; eauto.
  intros. exfalso. eauto using well_kinded_empty_no_free.
Qed.

Ltac eq_apply H :=
  match type of H with
  | ?F ?X1 ?X2 ?X3 ?X4 =>
    match goal with
    | [ |- ?F ?Y1 ?Y2 ?Y3 ?Y4 ] =>
      replace Y1 with X1; [
          replace Y2 with X2; [
            replace Y3 with X3; [
              replace Y4 with X4; [apply H|auto]|auto]|auto]|auto]
    end
  end.

Lemma ty_subs_ty_shift_up :
  forall tau alpha to d c,
    (forall beta, is_free_in_ty beta to -> False) ->
    c <= alpha ->
    ty_subs_ty (d + alpha) to (ty_shift_up d c tau) =
    ty_shift_up d c (ty_subs_ty alpha to tau).
Proof.
  induction tau; simpl; intros.
  - auto.
  - repeat (break_if; simpl); try omega; auto.
    now rewrite ty_shift_up_no_free_nop by eauto.
  - f_equal; auto.
  - f_equal. rewrite ty_shift_up_no_free_nop by eauto.
    rewrite plus_n_Sm. rewrite IHtau; auto with *.
Qed.

Lemma ty_subs_ty_shift_down :
  forall tau alpha to d c,
    (forall beta, is_free_in_ty beta to -> False) ->
    (forall beta, is_free_in_ty beta tau -> c <= beta -> d <= beta) ->
    c <= alpha ->
    ty_subs_ty alpha to (ty_shift_down d c tau) =
    ty_shift_down d c (ty_subs_ty (d + alpha) to tau).
Proof.
  induction tau; simpl; intros.
  - auto.
  - repeat (break_if; simpl); try omega; auto.
    + now rewrite ty_shift_down_no_free_nop by eauto.
    + subst. rewrite le_plus_minus_r in * by auto with *. congruence.
  - f_equal; auto.
  - f_equal. rewrite ty_shift_up_no_free_nop by eauto.
    rewrite plus_n_Sm. rewrite IHtau; auto with *.
    intros.
    destruct beta; try omega.
    destruct d; try omega.
    auto with *.
Qed.

Lemma ty_shift_down_up :
  forall tau d c d' c',
    (forall alpha, is_free_in_ty alpha tau -> c' <= alpha -> c + d' <= alpha) ->
    c <= c' ->
    ty_shift_up d c (ty_shift_down d' c' tau) =
    ty_shift_down d' (c' + d) (ty_shift_up d c tau).
Proof.
  induction tau; simpl; intros.
  - auto.
  - specialize (H t). repeat concludes.
    repeat (break_if; simpl); auto; try omega.
    repeat find_apply_lem_hyp not_lt. unfold ge in *. repeat concludes.
    rewrite Nat.add_sub_assoc; auto with *.
  - f_equal; auto.
  - f_equal. apply IHtau; try omega; intros; destruct alpha; try omega.
    apply le_n_S. apply H; auto with *.
Qed.

Lemma ty_subs_ty_shift_down' :
  forall tau alpha to d c,
    (forall beta, is_free_in_ty beta tau -> c <= beta -> c + d <= beta) ->
    alpha < c ->
    ty_subs_ty alpha (ty_shift_down d c to) (ty_shift_down d c tau) =
    ty_shift_down d c (ty_subs_ty alpha to tau).
Proof.
  induction tau; simpl; intros.
  - auto.
  - repeat (break_if; simpl); try omega; auto.
    repeat find_apply_lem_hyp not_lt.
    subst.
    specialize (H t). concludes. concludes.
    omega.
  - f_equal; auto.
  - f_equal. rewrite ty_shift_down_up.
    + rewrite plus_comm with (n := c).
      rewrite IHtau; auto.
      * intros. destruct beta; try omega. simpl. auto with *.
      (** intros. find_apply_lem_hyp ty_shift_up_free_inv.
        intuition.
        destruct beta; try omega.
        simpl in *. rewrite <- minus_n_O  in *.
        auto with *. *)
      * omega.
    + intros. admit.
    + omega.
Admitted.

Lemma ty_subs_ty_no_free_nop :
  forall tau alpha to,
    (is_free_in_ty alpha tau -> False) ->
    ty_subs_ty alpha to tau = tau.
Proof.
  induction tau; simpl; intros; auto using f_equal, f_equal2.
  break_if; auto.
  exfalso. auto.
Qed.

Lemma ty_subs_ty_ty_subs_ty :
  forall tau alpha beta toa tob,
    alpha <> beta ->
    (forall gamma, is_free_in_ty gamma toa -> False) ->
    ty_subs_ty alpha toa (ty_subs_ty beta tob tau) =
    ty_subs_ty beta (ty_subs_ty alpha toa tob) (ty_subs_ty alpha toa tau).
Proof.
  induction tau; simpl; intros.
  - auto.
  - repeat (break_if; simpl in * ); try congruence.
    subst. rewrite ty_subs_ty_no_free_nop; eauto.
  - f_equal; auto.
  - f_equal. rewrite IHtau; auto.
    * f_equal.
      { rewrite ty_subs_ty_shift_up with (d := 1); auto with *.
        - now rewrite ty_shift_up_no_free_nop with (tau := toa) by eauto.
        - intros. find_apply_lem_hyp ty_shift_up_free_inv. intuition eauto.
      }
    * intros.
      find_apply_lem_hyp ty_shift_up_free_inv. intuition eauto.
Qed.


Lemma ty_subs_has_type :
  forall Gamma Delta alpha to e tau,
    has_type Delta Gamma e tau ->
    well_kinded kinding_context_empty to ->
    has_type Delta (map (ty_subs_ty alpha to) Gamma) (ty_subs_exp alpha to e) (ty_subs_ty alpha to tau).
Proof.
  intros.
  assert (forall alpha, is_free_in_ty alpha to -> False) by eauto using well_kinded_empty_no_free.
  prep_induction H.
  induction H; simpl; intros.
  - auto.
  - constructor. find_eapply_lem_hyp typing_context_lookup_map; eauto.
  - eauto.
  - constructor.
    + apply ty_subs_ty_well_kinded; auto.
      auto using well_kinded_weakening_empty.
    + rewrite extend_map. auto.
  - eauto.
  - constructor. specialize (IHhas_type (S alpha) to).
    repeat concludes.
    rewrite ty_shift_up_no_free_nop by eauto.
    eq_apply IHhas_type.
    repeat rewrite map_map.
    apply map_ext.
    intros.
    now rewrite ty_subs_ty_shift_up with (d := 1) by eauto with *.
  - specialize (IHhas_type alpha to). repeat concludes.
    simpl in *.
    match goal with
    | [ |- ?F _ _ _ ?tau ] =>
      match type of tau with
      | ?T => evar (x : T);
          let x' := eval unfold x in x in
              clear x; replace tau with x'
      end
    end.
    econstructor.
    + eauto.
    + apply ty_subs_ty_well_kinded; auto using well_kinded_weakening_empty.
    + rewrite ty_shift_up_no_free_nop with (tau := to) by eauto.
      rewrite ty_subs_ty_shift_down; auto with *.
      * f_equal. rewrite <- ty_subs_ty_shift_up by auto with *.
        rewrite ty_subs_ty_ty_subs_ty with (toa := to); auto.
      * intros. destruct beta; try omega.
        find_apply_lem_hyp ty_subs_ty_is_free_in_ty.
        find_apply_lem_hyp ty_shift_up_free_inv. intuition.
Qed.

Ltac forward' H :=
  let H' := fresh in
  match type of H with
  | ?P -> _ => assert P as H'; [| specialize (H H'); clear H']
  end.

Lemma typing_context_lookup_map_ext_eq :
  forall x Gamma f f',
    (forall y, typing_context_lookup x Gamma = Some y ->
          f y = f' y) ->
    typing_context_lookup x (map f Gamma) =
    typing_context_lookup x (map f' Gamma).
Proof.
  induction x; simpl; intros; repeat break_match; simpl in *; try congruence; repeat find_inversion;
  auto using f_equal.
Qed.

Lemma ty_shift_down_down :
  forall tau d c d' c',
    ty_shift_down d c (ty_shift_down d' c' tau) =
    ty_shift_down d' (c' - d) (ty_shift_down d c tau).
Proof.
  induction tau; simpl; intros.
  - auto.
  -
Admitted.

Lemma ty_shift_down_has_type :
  forall Delta' Delta Gamma e tau d c,
    has_type (kinding_context_append Delta' (kinding_context_extend_n d Delta)) Gamma e tau ->
    length Delta' = c ->
    (forall alpha, ty_is_free_in alpha e -> c <= alpha < c + d -> False) ->
    (forall x taux alpha,
        typing_context_lookup x Gamma = Some taux ->
        is_free_in_ty alpha taux ->
        c <= alpha < c + d -> False) ->
    has_type (kinding_context_append Delta' Delta)
             (map (ty_shift_down d c) Gamma)
             (ty_shift_down_exp d c e)
             (ty_shift_down d c tau).
Proof.
  intros.
  prep_induction H.
  induction H; simpl; intros; subst.
  - auto.
  - auto using typing_context_lookup_map.
  - constructor; firstorder.
  - constructor.
    + apply ty_shift_down_well_kinded_shift; firstorder.
    + apply IHhas_type; firstorder.
      destruct x; simpl in *.
      * invc H1. eauto.
      * eauto.
  - econstructor; eauto.
  - constructor.
    eapply has_type_ext.
    apply IHhas_type with (Delta'0 := (kinding_context_extend Delta')) (Delta := Delta0); auto.
    + intros. destruct alpha; try omega. eauto with *.
    + intros. destruct alpha; try omega.
      find_apply_lem_hyp typing_context_lookup_map_inv. break_exists. break_and.
      subst taux.
      find_apply_lem_hyp ty_shift_up_free_inv. intuition.
      simpl in *. rewrite <- minus_n_O in *.
      eapply H2; eauto. omega.
    + intros. repeat rewrite map_map.
      apply typing_context_lookup_map_ext_eq.
      intros.
      rewrite ty_shift_down_up; auto with *.
      * f_equal. omega.
      * intros. destruct (le_dec d alpha); auto.
        find_apply_lem_hyp not_le.
        exfalso. eauto with *.
    + intros. rewrite extend_append. auto.
  - specialize (IHhas_type Delta' Delta0 d (length Delta')).
    concludes.
    conclude_using firstorder.
    concludes.
    concludes.
    simpl in *.
    eapply HTTyApp in IHhas_type.
    eq_apply IHhas_type.
    * { rewrite ty_shift_down_up.
        - rewrite Nat.add_1_r.
          rewrite ty_subs_ty_shift_down'.
          + rewrite ty_shift_down_down.
            simpl. now rewrite <- minus_n_O.
          + admit.
          + omega.
        - intros. destruct (lt_dec alpha (length Delta' + d)).
          + exfalso. eauto.
          + find_apply_lem_hyp not_lt. unfold ge in *. omega.
        - omega.
      }
    * apply ty_shift_down_well_kinded_shift; auto.
      firstorder.
Admitted.

Lemma ty_subs_exp_ty_is_free_in :
  forall e alpha tau,
    ty_is_free_in alpha (ty_subs_exp alpha tau e) ->
    is_free_in_ty alpha tau.
Proof.
  induction e; simpl; intuition.
  - eauto using ty_subs_ty_is_free_in_ty.
  - apply IHe in H. find_apply_lem_hyp ty_shift_up_free_inv.
    intuition; try omega.
    simpl in *. rewrite <- minus_n_O in *.
    auto.
  - eauto using ty_subs_ty_is_free_in_ty.
Qed.

Theorem preservation :
  forall e e',
    step e e' ->
    forall tau,
      has_type kinding_context_empty typing_context_empty e tau ->
      has_type kinding_context_empty typing_context_empty e' tau.
Proof.
  induction 1; intros.
  - invc H. auto.
  - invc H. auto.
  - invc H0. auto.
  - invc H0. invc H5. apply shift_down_has_type.
    + eapply substitution with (x := 0) in H9; eauto.
      eapply has_type_ext; eauto.
      intros. destruct x.
      * apply subs_free in H0.
        find_eapply_lem_hyp has_type_is_free_in; eauto.
        break_exists. discriminate.
      * simpl. rewrite typing_context_lookup_empty. auto.
    + simpl. auto.
  - invc H0. eauto.
  - invc H1. eauto.
  - invc H. invc H4.
    eapply ty_shift_down_has_type with (Delta' := kinding_context_empty) (Gamma := typing_context_empty); auto.
    + simpl in *.
      rewrite ty_shift_up_no_free_nop.
      apply ty_subs_has_type with (Gamma := typing_context_empty); auto.
      eauto using well_kinded_empty_no_free.
    + intros. destruct alpha; try omega.
      find_apply_lem_hyp ty_subs_exp_ty_is_free_in.
      eauto using well_kinded_empty_no_free.
    + intros. destruct alpha; try omega.
      rewrite typing_context_lookup_empty in *. discriminate.
  - invc H0. eauto.
Qed.
