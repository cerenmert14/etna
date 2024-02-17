


Require Import ZArith.
From QuickChick Require Import QuickChick.
From ExtLib Require Import Monad.
From ExtLib.Data.Monads Require Import OptionMonad.
Import QcNotation.
Import MonadNotation.
From Coq Require Import List.
Import ListNotations.

From RBTProplang Require Import Impl Spec.
From PropLang Require Import PropLang.

Local Open Scope prop_scope.
Open Scope Z_scope.

Derive (Shrink) for Tree.
Definition genZ := choose (-20, 20).

Fixpoint gen_kvs (s : nat) : G (list (Z * Z)) :=
  match s with
  | O => ret []
  | S s' => k <- genZ;;
           v <- arbitrary;;
           kvs <- gen_kvs s';;
           ret ((k, v) :: kvs)
  end.

Definition blacken_ (t: Tree) : Tree :=
    match t with
    | E => E
    | (T _ a x vx b) => T B a x vx b
    end.

Definition balance_ (col: Color) (tl: Tree) (key: Z) (val: Z) (tr: Tree) : Tree :=
    match col, tl, key, val, tr with
    | B, (T R (T R a x vx b) y vy c), z, vz, d => T R (T B a x vx b) y vy (T B c z vz d)
    | B, (T R a x vx (T R b y vy c)), z, vz, d => T R (T B a x vx b) y vy (T B c z vz d)
    | B, a, x, vx, (T R (T R b y vy c) z vz d) => T R (T B a x vx b) y vy (T B c z vz d)
    | B, a, x, vx, (T R b y vy (T R c z vz d)) => T R (T B a x vx b) y vy (T B c z vz d)
    | rb, a, x, vx, b => T rb a x vx b
    end.


Fixpoint insert_ (key: Z) (val: Z) (t: Tree) : Tree :=
    let fix ins (x: Z) (vx: Z) (s: Tree) : Tree :=
    match x, vx, s with
    | x, vx, E => 
    T R E x vx E
    | x, vx, (T rb a y vy b) =>
    if x <?? y then balance_ rb (ins x vx a) y vy b
    else if y <?? x then balance_ rb a y vy (ins x vx b)
    else T rb a y vx b
    end
    in blacken_ (ins key val t).

Definition gen_tree (s : nat) : G Tree :=
    sz <- choose(1, s)%nat;;
    kvs <- gen_kvs sz;;
    ret (fold_right (fun '(k, v) t => insert_ k v t) E kvs).

Definition bespoke :=
    gen_tree 20.
    
#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.
    

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

(* --------------------- Tests --------------------- *)

Definition prop_InsertValid :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isRBT t" (fun '(t, tt) => isRBT t) (
	ForAll "k" (fun tt => genZ) (fun tt k => genZ) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (Z · (Z · (Tree · ∅)))
	(fun '(v, (k, (t, tt))) => (isRBT (insert k v t))))))).

Definition test_prop_InsertValid := (runLoop number_of_trials prop_InsertValid).
(*! QuickProp test_prop_InsertValid. *)

Definition prop_DeleteValid :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isRBT t" (fun '(t, tt) => isRBT t) (
	ForAll "k" (fun tt => genZ) (fun tt n => genZ) (fun tt => shrink) (fun tt => show) (
	Check (Z · (Tree · ∅))
	(fun '(k, (t, tt)) => (match delete k t with
						   | None => false
						   | Some t' => isRBT t'
							end))))).

Definition test_prop_DeleteValid := (runLoop number_of_trials prop_DeleteValid).
(*! QuickProp test_prop_DeleteValid. *)

Definition prop_InsertPost :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isRBT t" (fun '(t, tt) => isRBT t) (
	ForAll "k" (fun tt => genZ) (fun tt k => genZ) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => genZ) (fun tt k' => genZ) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (Z · (Z · (Z · (Tree · ∅))))
	(fun '(v, (k', (k, (t, tt)))) => (let v' := find k' (insert k v t) in
										if k =? k' then v' ==? Some v 
										else v' ==? find k' t))))))).

Definition test_prop_InsertPost := (runLoop number_of_trials prop_InsertPost).
(*! QuickProp test_prop_InsertPost. *)

Definition prop_DeletePost :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isRBT t" (fun '(t, tt) => isRBT t) (
	ForAll "k" (fun tt => genZ) (fun tt t => genZ) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => genZ) (fun tt n => genZ) (fun tt => shrink) (fun tt => show) (
	Check (Z · (Z · (Tree · ∅)))
	(fun '(k', (k, (t, tt))) => (t' <- delete k t ;;
								 find k' t' ==? if k =? k' then None else find k' t)))))).

Definition test_prop_DeletePost := (runLoop number_of_trials prop_DeletePost).
(*! QuickProp test_prop_DeletePost. *)


Definition prop_InsertModel :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isRBT t" (fun '(t, tt) => isRBT t) (
	ForAll "k" (fun tt => genZ) (fun tt t => genZ) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (Z · (Z · (Tree · ∅)))
	(fun '(v, (k, (t, tt))) => ((toList (insert k v t) = L_insert (k, v) (deleteKey k (toList t)))?)))))).

Definition test_prop_InsertModel := (runLoop number_of_trials prop_InsertModel).
(*! QuickProp test_prop_InsertModel. *)

Definition prop_DeleteModel :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isRBT t" (fun '(t, tt) => isRBT t) (
	ForAll "k" (fun tt => genZ) (fun tt t => genZ) (fun tt => shrink) (fun tt => show) (
	Check (Z · (Tree · ∅))
	(fun '(k, (t, tt)) => ( match delete k t with
							| None => false
							| Some t' => (toList t' = deleteKey k (toList t))?
							end))))).

Definition test_prop_DeleteModel := (runLoop number_of_trials prop_DeleteModel).
(*! QuickProp test_prop_DeleteModel. *)

Definition prop_InsertInsert :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isRBT t" (fun '(t, tt) => isRBT t) (
	ForAll "k" (fun tt => genZ) (fun tt t => genZ) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => genZ) (fun tt n => genZ) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v'" (fun tt => arbitrary) (fun tt v' => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (Z · (Z · (Z · (Z · (Tree · ∅)))))
	(fun '(v', (v, (k', (k, (t, tt))))) => ((toList (insert k v (insert k' v' t))
    ==? toList(if k =? k' then insert k v t else insert k' v' (insert k v t))))))))))).

Definition test_prop_InsertInsert := (runLoop number_of_trials prop_InsertInsert).
(*! QuickProp test_prop_InsertInsert. *)


Definition prop_InsertDelete :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isRBT t" (fun '(t, tt) => isRBT t) (
	ForAll "k" (fun tt => genZ) (fun tt k => genZ) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => genZ) (fun tt k' => genZ) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (Z · (Z · (Z · (Tree · ∅))))
	(fun '(v, (k', (k, (t, tt)))) => (
		match (delete k' t) with
		| None => false
		| Some t' =>
			match delete k' (insert k v t) with
			| None => false
			| Some t'' =>
				toList(insert k v t') ==? toList(if k =? k' then insert k v t else t'')
			end
		end))))))).

Definition test_prop_InsertDelete := (runLoop number_of_trials prop_InsertDelete).
(*! QuickProp test_prop_InsertDelete. *)

Definition prop_DeleteInsert :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isRBT t" (fun '(t, tt) => isRBT t) (
	ForAll "k" (fun tt => genZ) (fun tt t => genZ) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => genZ) (fun tt n => genZ) (fun tt => shrink) (fun tt => show) (
	ForAll "v'" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (Z · (Z · (Z · (Tree · ∅))))
	(fun '(v', (k', (k, (t, tt)))) => (
		match delete k (insert k' v' t) with
		| None => false
		| Some t' =>
		  match delete k t with
		  | None => false
		  | Some t'' =>
			let t''' := insert k' v' t'' in
			toList t' ==? toList (if k =? k' then t'' else t''')
		  end
		end
	))))))).

Definition test_prop_DeleteInsert := (runLoop number_of_trials prop_DeleteInsert).
(*! QuickProp test_prop_DeleteInsert. *)

Definition prop_DeleteDelete :=
	ForAll "t" (fun tt => bespoke) (fun tt t => bespoke) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) "isRBT t" (fun '(t, tt) => isRBT t) (
	ForAll "k" (fun tt => arbitrary) (fun tt t => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (Z · (Z · (Tree · ∅)))
	(fun '(k', (k, (t, tt))) => (
		match delete k' t with
		| None => false
		| Some t' =>
		  match delete k t' with
		  | None => false
		  | Some t'' =>
			match delete k t with
			| None => false
			| Some t1' =>
			  match delete k' t1' with
			  | None => false
			  | Some t1'' =>
				toList t'' ==? toList t1''
			  end
			end
		  end
		end
	)))))).

Definition test_prop_DeleteDelete := (runLoop number_of_trials prop_DeleteDelete).
(*! QuickProp test_prop_DeleteDelete. *)