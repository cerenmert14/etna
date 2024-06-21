 
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


#[local] Instance dec_eq_expr : Dec_Eq Expr.
Proof. dec_eq. Defined.
    
Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

(* --------------------- Tests --------------------- *)

Definition prop_SinglePreserve   :=
	ForAllMaybe "e" (fun _ => arbitrary) (fun _ e => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Expr · ∅) (fun '(e, _) => isJust (mt e)) (
	Check (Expr · ∅)
	(fun '(e, _) => 
    match (mt e) with
    | None => false
    | Some t' => mtypeCheck (pstep e) t'
    end
  ))).

Definition test_prop_SinglePreserve := (runLoop number_of_trials prop_SinglePreserve).
(*! QuickProp test_prop_SinglePreserve. *)

Definition prop_MultiPreserve   :=
	ForAllMaybe "e" (fun _ => arbitrary) (fun _ e => arbitrary) (fun _ => shrink) (fun _ => show) (
  Implies (Expr · ∅) (fun '(e, _) => isJust (mt e)) (
	Check (Expr · ∅)
	(fun '(e, _) => 
    match (mt e) with
    | None => false
    | Some t' => mtypeCheck (multistep 40 pstep e) t'
    end
  ))).

Definition test_prop_MultiPreserve := (runLoop number_of_trials prop_MultiPreserve).
(*! QuickProp test_prop_MultiPreserve. *)
