Require Import List.
Import ListNotations.

Require Import JRWTactics.

Require Import EQ ANY MAP.

Set Firstorder Solver (subst; eauto).

Module alist (K : EQ) (V : ANY) : MAP with Definition key := K.t with Definition value := V.t.
  Definition key := K.t.
  Definition value := V.t.

  Definition t := list (key * value).

  Definition empty : t := nil.

  Fixpoint alist_get (k : key) (m : t) : option value  := 
    match m with
    | [] => None
    | (k1,v1) :: m' => if K.t_eq_dec k k1 then Some v1 else alist_get k m'
    end.

  Definition get := alist_get.


  Definition shadow (k : key) (v : value) (m : t) : t := (k,v) :: m.


  Fixpoint alist_delete (k : key) (m : t) : t := 
    match m with 
    | [] => m
    | (k1,v1) :: m' => if K.t_eq_dec k k1 then alist_delete k m' else (k1,v1) :: alist_delete k m'
    end.

  Definition delete := alist_delete.

  Lemma alist_get_delete_same : 
    forall k a, 
      alist_get k (alist_delete k a) = None.
  Proof.
    induction a; simpl; intros.
    - auto.
    - repeat (break_match; simpl); subst; congruence.
  Qed.

  Lemma alist_get_delete_diff : 
    forall k k' a, 
      k <> k' -> 
      alist_get k' (alist_delete k a) = alist_get k' a.
  Proof.
    induction a; simpl; intros.
    - auto.
    - repeat (break_match; simpl); subst; auto; congruence.
  Qed.

  Lemma alist_get_shadow_same : 
    forall k v a, 
      alist_get k (shadow k v a) = Some v.
  Proof.
    intros.
    simpl. break_if; congruence.
  Qed.

  Lemma alist_get_shadow_diff : 
    forall k k' v a, 
      k <> k' -> 
      alist_get k' (shadow k v a) = alist_get k' a.
  Proof.
    intros.
    simpl. break_if; congruence.
  Qed.

  Lemma get_empty : 
    forall k, 
      get k empty = None.
  Proof.
    auto.
  Qed.

  Lemma delete_shadow_same : 
    forall k v m, 
      alist_delete k (shadow k v m) = alist_delete k m.
  Proof.
    intros.
    simpl. break_if; congruence.
  Qed.

  Lemma delete_shadow_diff : 
    forall k' k v m, 
      k <> k' -> 
      alist_delete k' (shadow k v m) = shadow k v (alist_delete k' m).
  Proof.
    intros.
    simpl. break_if; try congruence.
    auto.
  Qed.

  Lemma delete_empty : 
    forall k, 
      alist_delete k empty = empty. 
  Proof.
    auto.
  Qed.

  Definition get_shadow_same := alist_get_shadow_same.
  Definition get_shadow_diff := alist_get_shadow_diff.

  Definition get_delete_same := alist_get_delete_same.
  Definition get_delete_diff := alist_get_delete_diff.
End alist.
