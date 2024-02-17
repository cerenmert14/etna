 
From QuickChick Require Import QuickChick. Import QcNotation.
From Coq Require Import Bool ZArith List. Import ListNotations.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import MonadNotation.

From PropLang Require Import PropLang.
From STLCProplang Require Import Impl Spec.
Local Open Scope prop_scope.

Derive (Arbitrary) for Typ.
Derive (Arbitrary) for Expr.


Inductive bind : Ctx -> nat -> Typ -> Prop :=
| BindNow   : forall tau env, bind (tau :: env) 0 tau
| BindLater : forall tau tau' x env,
    bind env x tau -> bind (tau' :: env) (S x) tau.
Inductive typing (G : Ctx) : Expr -> Typ -> Prop :=
| TyVar :
    forall x T,
      bind G x T ->
      typing G (Var x) T
| TyBool :
    forall b,
      typing G (Bool b) TBool
| TyAbs :
    forall e T1 T2,
      typing (T1 :: G) e T2 ->
      typing G (Abs T1 e) (TFun T1 T2)
| TyApp :
    forall e1 e2 T1 T2,
      typing G e1 (TFun T1 T2) ->
      typing G e2 T1 ->
      typing G (App e1 e2) T2.


#[export] Instance dec_type (t1 t2 : Typ) : Dec (t1 = t2).
Proof. dec_eq. Defined.
Derive Arbitrary for Typ.
Derive ArbitrarySizedSuchThat for (fun x => bind env x tau).
Derive ArbitrarySizedSuchThat for (fun t => typing env t tau).

Definition gTypedExpr G T sz :=
  @arbitrarySizeST _ (fun e => typing G e T) _ sz.


Definition gSized := 
    typ <- arbitrary ;;
    gTypedExpr [] typ 5.


#[local] Instance dec_eq_expr : Dec_Eq Expr.
Proof. dec_eq. Defined.
    
Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

(* --------------------- Tests --------------------- *)

Definition prop_SinglePreserve   :=
	ForAllMaybe "e" (fun tt => gSized) (fun tt e => gSized) (fun tt => shrink) (fun tt => show) (
  Implies (Expr · ∅) "isJust (mt e)" (fun '(e, tt) => isJust (mt e)) (
	Check (Expr · ∅)
	(fun '(e, tt) => 
    match (mt e) with
    | None => false
    | Some t' => mtypeCheck (pstep e) t'
    end
  ))).

Definition test_prop_SinglePreserve := (runLoop number_of_trials prop_SinglePreserve).
(*! QuickProp test_prop_SinglePreserve. *)

Definition prop_MultiPreserve   :=
	ForAllMaybe "e" (fun tt => gSized) (fun tt e => gSized) (fun tt => shrink) (fun tt => show) (
  Implies (Expr · ∅) "isJust (mt e)" (fun '(e, tt) => isJust (mt e)) (
	Check (Expr · ∅)
	(fun '(e, tt) => 
    match (mt e) with
    | None => false
    | Some t' => mtypeCheck (multistep 40 pstep e) t'
    end
  ))).

Definition test_prop_MultiPreserve := (runLoop number_of_trials prop_MultiPreserve).
(*! QuickProp test_prop_MultiPreserve. *)
