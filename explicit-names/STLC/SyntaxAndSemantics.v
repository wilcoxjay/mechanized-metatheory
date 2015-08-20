Require Import EQ ANY.
Require Import Alist.

Require Import Relations.
Require Import Operators_Properties.

Declare Module Name : EQ.

Definition name := Name.t.
Definition name_eq_dec := Name.t_eq_dec.

Inductive type : Type :=
| TBool : type
| TArrow : type -> type -> type.

Inductive term : Type :=
| TConst : bool -> term
| TVar : name -> term
| TIf : term -> term -> term -> term 
| TAbs : name -> type -> term -> term
| TApp : term -> term -> term.

Module TypeAny.
  Definition t := type.
End TypeAny.

Module TypingContext := alist Name TypeAny.

Definition typing_context := TypingContext.t.

Inductive has_type : typing_context -> term -> type -> Prop := 
| HTConst : forall Gamma b, has_type Gamma (TConst b) TBool
| HTVar : forall Gamma x tau, 
    TypingContext.get x Gamma = Some tau -> 
    has_type Gamma (TVar x) tau
| HTIf : forall Gamma e1 e2 e3 tau, 
    has_type Gamma e1 TBool -> 
    has_type Gamma e2 tau -> 
    has_type Gamma e3 tau -> 
    has_type Gamma (TIf e1 e2 e3) tau
| HTAbs : forall Gamma x tyx e tau, 
    has_type (TypingContext.shadow x tyx Gamma) e tau -> 
    has_type Gamma (TAbs x tyx e) (TArrow tyx tau)
| HTApp : forall Gamma e1 e2 ty2 tau, 
    has_type Gamma e1 (TArrow ty2 tau) -> 
    has_type Gamma e2 ty2 -> 
    has_type Gamma (TApp e1 e2) tau.

Fixpoint subs (from : name) (to : term) (e : term) : term :=
  match e with 
  | TConst _ => e
  | TVar y => if name_eq_dec from y then to else e
  | TIf e1 e2 e3 => TIf (subs from to e1)
                       (subs from to e2)
                       (subs from to e3)
  | TAbs y tau e' => if name_eq_dec from y then e else TAbs y tau (subs from to e')
  | TApp e1 e2 => TApp (subs from to e1) (subs from to e2)
  end.

Definition is_value (e : term) : Prop := 
  match e with 
  | TConst _ => True
  | TAbs _ _ _ => True
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
    forall x tau e1 e2, 
      is_value e2 -> 
      step (TApp (TAbs x tau e1) e2) (subs x e2 e1)
| step_app1 : 
    forall e1 e1' e2, 
      step e1 e1' -> 
      step (TApp e1 e2) (TApp e1' e2)
| step_app2 : 
    forall e1 e2 e2', 
      is_value e1 -> 
      step e2 e2' -> 
      step (TApp e1 e2) (TApp e1 e2').

Definition step_star := clos_refl_trans_n1 term step.
Definition irreducible (e : term) : Prop := forall e', step e e' -> False.
Definition terminates (e : term) : Prop := exists v, irreducible v /\ step_star e v.