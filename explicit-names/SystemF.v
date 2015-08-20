Require Import JRWTactics.

Require Import Relations.
Require Import Operators_Properties.

Require Import EQ ANY MAP.
Require Import EqMapFacts.
Require Import Alist.

Declare Module Name : EQ.
Declare Module TypeName : EQ.

Definition name := Name.t.
Definition name_eq_dec := Name.t_eq_dec.

Definition type_name := TypeName.t.
Definition type_name_eq_dec := TypeName.t_eq_dec.

Inductive type : Type :=
| TyVar : type_name -> type
| TyBool : type
| TyArrow : type -> type -> type
| TyForall : type_name -> type -> type.
(*  | TyExists : name -> type -> type. *)

Inductive term : Type :=
| TConst : bool -> term
| TVar : name -> term
| TIf : term -> term -> term -> term 
| TAbs : name -> type -> term -> term
| TApp : term -> term -> term 
| TTyAbs : type_name -> term -> term
| TTyApp : term -> type -> term.

Module UnitAny.
  Definition t := unit.
End UnitAny.

Module KindingContext := alist TypeName UnitAny.

Definition kinding_context := KindingContext.t.

Module TypeAny.
  Definition t := type.
End TypeAny.

Module TypingContext := alist Name TypeAny.

Definition typing_context := TypingContext.t.

Inductive well_kinded : kinding_context -> type -> Prop := 
| WK_var : forall Delta alpha u, 
    KindingContext.get alpha Delta = Some u -> 
    well_kinded Delta (TyVar alpha)
| WK_bool : forall Delta, well_kinded Delta TyBool
| WK_arrow : forall Delta tau1 tau2, 
    well_kinded Delta tau1 -> 
    well_kinded Delta tau2 -> 
    well_kinded Delta (TyArrow tau1 tau2)
| WK_forall : forall Delta alpha tau, 
    well_kinded (KindingContext.shadow alpha tt Delta) tau -> 
    well_kinded Delta (TyForall alpha tau).

Inductive has_type : kinding_context -> typing_context -> term -> type -> Prop := 
| HTConst : forall Delta Gamma b, has_type Delta Gamma (TConst b) TyBool
| HTVar : forall Delta Gamma x tau, 
    TypingContext.get x Gamma = Some tau -> 
    has_type Delta Gamma (TVar x) tau
| HTIf : forall Delta Gamma e1 e2 e3 tau, 
    has_type Delta Gamma e1 TyBool -> 
    has_type Delta Gamma e2 tau -> 
    has_type Delta Gamma e3 tau -> 
    has_type Delta Gamma (TIf e1 e2 e3) tau
| HTAbs : forall Delta Gamma x tyx e tau, 
    well_kinded Delta tyx -> 
    has_type Delta (TypingContext.shadow x tyx Gamma) e tau -> 
    has_type Delta Gamma (TAbs x tyx e) (TyArrow tyx tau)
| HTApp : forall Delta Gamma e1 e2 ty2 tau, 
    has_type Delta Gamma e1 (TyArrow ty2 tau) -> 
    has_type Delta Gamma e2 ty2 -> 
    has_type Delta Gamma (TApp e1 e2) tau
| HTTTyAbs : forall Delta Gamma alpha e tau, 
    has_type (KindingContext.shadow alpha tt Delta) Gamma e tau -> 
    has_type Delta Gamma e (TyForall alpha tau)
 .
(*
| HTTyApp : forall Delta Gamma e1 tau1 tau2, 
    has_type Delta Gamma e1 (TyForall alpha tau1) -> 
    well_kinded Delta tau2 -> 
    has_type Delta Gamma (TTyApp e1 tau2) (ty_subs alpha tau2

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

*)
