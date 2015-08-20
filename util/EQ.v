Module Type EQ.
  Parameter t : Type.
  Axiom t_eq_dec : forall x y : t, {x = y} + {x <> y}.
End EQ.

Require Import Arith.

Module Instances.
  Module NatEq : EQ with Definition t := nat.
    Definition t := nat.
    Definition t_eq_dec := eq_nat_dec.
  End NatEq.
End Instances.