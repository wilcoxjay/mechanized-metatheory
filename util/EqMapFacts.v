Require Import MAP.
Require Import EQ.
Require Import ANY.

Module EqMapFacts (K : EQ) (V : ANY) (M : MAP with Definition key := K.t with Definition value := V.t).
  Lemma get_delete_Some : 
    forall k k' v m, 
      M.get k' (M.delete k m) = Some v -> 
      M.get k' m = Some v.
  Proof.
    intros.
    destruct (K.t_eq_dec k k').
    - subst. rewrite M.get_delete_same in *. discriminate.
    - rewrite M.get_delete_diff in * by auto. auto.
  Qed.
End EqMapFacts.
