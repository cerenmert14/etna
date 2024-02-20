From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Set Warnings "-extraction-opaque-accessed,-extraction".

Require Import List ZArith.
Import ListNotations.
Import MonadNotation.

From BSTProplang Require Import Impl.
From BSTProplang Require Import Spec.
From PropLang Require Import PropLang.

Local Open Scope nat.
Local Open Scope prop_scope.


Inductive between : nat -> nat -> nat -> Prop :=
| between_n : forall n m, le n m -> between n (S n) (S (S m))
| between_S : forall n m o, between n m o -> between n (S m) (S o).

Derive DecOpt for (le x y).
Derive ArbitrarySizedSuchThat for (fun x => le y x).

Derive ArbitrarySizedSuchThat for (fun x => between lo x hi).
Derive DecOpt for (between lo x hi).

Inductive bst : nat -> nat -> Tree -> Prop :=
| bst_leaf : forall lo hi, bst lo hi E
| bst_node : forall lo hi k v l r,
    between lo k hi ->
    bst lo k l -> bst k hi r ->
    bst lo hi (T l k v r).

Derive ArbitrarySizedSuchThat for (fun t => bst lo hi t).
Derive DecOpt for (bst lo hi t).


Definition spec_derived := (@arbitrarySizeST _ (fun t => bst 0 100 t) _ 10).
Derive (Shrink, Show) for Tree.

#[local] Instance dec_eq_tree : Dec_Eq Tree.
Proof. dec_eq. Defined.

Axiom number_of_trials : nat.
Extract Constant number_of_trials => "max_int".

Definition prop_InsertValid   :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(v, (k, (t, tt))) => (isBST (insert k v t))))))).

Definition test_prop_InsertValid := (runLoop number_of_trials prop_InsertValid).

(*! QuickProp test_prop_InsertValid. *)

Definition prop_DeleteValid   :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (Tree · ∅))
	(fun '(k, (t, tt)) => (isBST (delete k t)))))).

Definition test_prop_DeleteValid := (runLoop number_of_trials prop_DeleteValid).

(*! QuickProp test_prop_DeleteValid. *)

Definition prop_UnionValid :=
	ForAllMaybe "t1" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t1, tt) => isBST t1) (
	ForAllMaybe "t2" (fun tt => spec_derived) (fun tt n => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) (fun '(t2, _) => isBST t2) (
	Check (Tree · (Tree · ∅))
	(fun '(t2, (t1, tt)) => (isBST (union t1 t2))))))).

Definition test_prop_UnionValid := (runLoop number_of_trials prop_UnionValid).
(*! QuickProp test_prop_UnionValid. *)

Definition prop_InsertPost :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => arbitrary) (fun tt k' => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v, (k', (k, (t, tt)))) => ((find k' (insert k v t) = if k =? k' then Some v else find k' t)?))))))).

Definition test_prop_InsertPost := (runLoop number_of_trials prop_InsertPost).
(*! QuickProp test_prop_InsertPost. *)


Definition prop_DeletePost :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt t => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(k', (k, (t, tt))) => ((find k' (delete k t) = if k =? k' then None else find k' t)?)))))).

Definition test_prop_DeletePost := (runLoop number_of_trials prop_DeletePost).
(*! QuickProp test_prop_DeletePost. *)

Definition prop_UnionPost :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAllMaybe "t'" (fun tt => spec_derived) (fun tt t' => spec_derived) (fun tt => shrink) (fun tt => show) (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (Tree · (Tree · ∅)))
	(fun '(k, (t', (t, tt))) => (let lhs := find k (union t t') in
									match (find k t) with
									| Some rhs => (lhs = (Some rhs))?
									| None => match (find k t') with
											| Some rhs => (lhs = (Some rhs))?
											| None => (lhs = None)?
											end
									end)))))).

Definition test_prop_UnionPost := (runLoop number_of_trials prop_UnionPost).
(*! QuickProp test_prop_UnionPost. *)

Definition prop_InsertModel :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt t => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(v, (k, (t, tt))) => ((toList (insert k v t) = L_insert (k, v) (deleteKey k (toList t)))?)))))).

Definition test_prop_InsertModel := (runLoop number_of_trials prop_InsertModel).
(*! QuickProp test_prop_InsertModel. *)

Definition prop_DeleteModel :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt t => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (Tree · ∅))
	(fun '(k, (t, tt)) => ((toList (delete k t) = deleteKey k (toList t))?))))).

Definition test_prop_DeleteModel := (runLoop number_of_trials prop_DeleteModel).
(*! QuickProp test_prop_DeleteModel. *)

Definition prop_UnionModel :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAllMaybe "t'" (fun tt => spec_derived) (fun tt t' => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	Check (Tree · (Tree · ∅))
	(fun '(t', (t, tt)) => ((toList (union t t') = L_sort (L_unionBy (fun x y => x) (toList t) (toList t')))?)))))).

Definition test_prop_UnionModel := (runLoop number_of_trials prop_UnionModel).
(*! QuickProp test_prop_UnionModel. *)

Definition prop_InsertInsert :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt t => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v'" (fun tt => arbitrary) (fun tt v' => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (nat · (nat · (Tree · ∅)))))
	(fun '(v', (v, (k', (k, (t, tt))))) => (insert k v (insert k' v' t) =|= if k =? k' then insert k v t else insert k' v' (insert k v t))))))))).

Definition test_prop_InsertInsert := (runLoop number_of_trials prop_InsertInsert).
(*! QuickProp test_prop_InsertInsert. *)

Definition prop_InsertDelete :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => arbitrary) (fun tt k' => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v, (k', (k, (t, tt)))) => ((insert k v (delete k' t) =|= if k =? k' then insert k v t else delete k' (insert k v t))))))))).

Definition test_prop_InsertDelete := (runLoop number_of_trials prop_InsertDelete).
(*! QuickProp test_prop_InsertDelete. *)

Definition prop_InsertUnion :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAllMaybe "t'" (fun tt => spec_derived) (fun tt t' => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (Tree · (Tree · ∅))))
	(fun '(v, (k, (t', (t, tt)))) => (insert k v (union t t') =|= union (insert k v t) t')))))))).

Definition test_prop_InsertUnion := (runLoop number_of_trials prop_InsertUnion).
(*! QuickProp test_prop_InsertUnion. *)

Definition prop_DeleteInsert :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt t => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v'" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (nat · (Tree · ∅))))
	(fun '(v', (k', (k, (t, tt)))) => (delete k (insert k' v' t) =|= if k =? k' then delete k t else insert k' v' (delete k t)))))))).

Definition test_prop_DeleteInsert := (runLoop number_of_trials prop_DeleteInsert).
(*! QuickProp test_prop_DeleteInsert. *)

Definition prop_DeleteDelete :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAll "k" (fun tt => arbitrary) (fun tt t => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "k'" (fun tt => arbitrary) (fun tt n => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (Tree · ∅)))
	(fun '(k', (k, (t, tt))) => ((delete k (delete k' t) =|= delete k' (delete k t)))))))).

Definition test_prop_DeleteDelete := (runLoop number_of_trials prop_DeleteDelete).
(*! QuickProp test_prop_DeleteDelete. *)

Definition prop_DeleteUnion :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAllMaybe "t'" (fun tt => spec_derived) (fun tt t' => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (Tree · (Tree · ∅)))
	(fun '(k, (t', (t, tt))) => (delete k (union t t') =|= union (delete k t) (delete k t')))))))).

Definition test_prop_DeleteUnion := (runLoop number_of_trials prop_DeleteUnion).
(*! QuickProp test_prop_DeleteUnion. *)

Definition prop_UnionDeleteInsert :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	ForAllMaybe "t'" (fun tt => spec_derived) (fun tt t' => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) (fun '(t', _) => isBST t') (
	ForAll "k" (fun tt => arbitrary) (fun tt k => arbitrary) (fun tt => shrink) (fun tt => show) (
	ForAll "v" (fun tt => arbitrary) (fun tt v => arbitrary) (fun tt => shrink) (fun tt => show) (
	Check (nat · (nat · (Tree · (Tree · ∅))))
	(fun '(v, (k, (t', (t, tt)))) => ((union (delete k t) (insert k v t') =|= insert k v (union t t')))))))))).

Definition test_prop_UnionDeleteInsert := (runLoop number_of_trials prop_UnionDeleteInsert).
(*! QuickProp test_prop_UnionDeleteInsert. *)

Definition prop_UnionUnionIdem :=
	ForAllMaybe "t" (fun tt => spec_derived) (fun tt t => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t, tt) => isBST t) (
	Check (Tree · ∅)
	(fun '(t, tt) => (union t t =|= t)))).

Definition test_prop_UnionUnionIdem := (runLoop number_of_trials prop_UnionUnionIdem).
(*! QuickProp test_prop_UnionUnionIdem. *)

Definition prop_UnionUnionAssoc :=
	ForAllMaybe "t1" (fun tt => spec_derived) (fun tt t1 => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · ∅) (fun '(t1, tt) => isBST t1) (
	ForAllMaybe "t2" (fun tt => spec_derived) (fun tt t2 => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) (fun '(t2, _) => isBST t2) (
	ForAllMaybe "t3" (fun tt => spec_derived) (fun tt t3 => spec_derived) (fun tt => shrink) (fun tt => show) (
	Implies (Tree · _) (fun '(t3, _) => isBST t3) (
	Check (Tree · (Tree · (Tree · ∅)))
	(fun '(t3, (t2, (t1, tt))) => (union (union t1 t2) t3 =|= union t1 (union t2 t3))))))))).

Definition test_prop_UnionUnionAssoc := (runLoop number_of_trials prop_UnionUnionAssoc).
(*! QuickProp test_prop_UnionUnionAssoc. *)

