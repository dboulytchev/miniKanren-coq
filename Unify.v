Require Export List.
Import ListNotations.
Require Export Arith.
Require Export Omega.
Require Export FMapAVL.
Require Export Coq.Structures.OrderedTypeEx.

Inductive Term : Type :=
| V : nat -> Term
| C : nat -> list Term -> Term.

Module S := FMapAVL.Make (Nat_as_OT).

Definition Subst: Type := S.t Term.

Definition empty : Subst := S.empty Term.

Definition find k (m: Subst) := S.find k m.

Definition update (k: nat) (v: Term) (m: Subst) :=
  S.add k v m.

Notation "s [ k <- v ]" := (update k v s) (at level 0).
Reserved Notation "t \ s" (at level 0).

Fixpoint apply (s: Subst) (t: Term) : Term := 
  match t with
  | V v    => match find v s with
              | None   => V v
              | Some t => t
              end
  | C c ts => C c (map (fun t => t \ s) ts)
  end
where "t \ s" := (apply s t).

(*
-- Unification
unify :: Maybe Sigma -> Ts -> Ts -> Maybe Sigma 
unify Nothing _ _ = Nothing
unify st@(Just subst) u v = 
  unify' (walk u subst) (walk v subst)  where
    unify' (V u) (V v) | u == v = Just subst
    unify' (V u) _              = Just $ (u, v) : subst
    unify' _ (V v)              = Just $ (v, u) : subst
    unify' (C a as) (C b bs) | a == b && length as == length bs = 
      foldl (\ st (u, v) -> unify st u v) st $ zip as bs
    unify' _ _ = Nothing
    walk x@(V v) s =
      case lookup v s of
        Nothing -> x
        Just t  -> walk t s
    walk u     _ = u
*)

Print well_founded.
Print Acc.
Check Fix.

Definition sizeOrder (s1 s2 : Subst) := S.cardinal s1 < S.cardinal s2.

Hint Constructors Acc.

Lemma sizeOrder_wf': forall (size: nat) (s: Subst), S.cardinal s < size -> Acc sizeOrder s.
  unfold sizeOrder. induction size.  
    intros. inversion H.
    intros. constructor. intros. apply IHsize. omega.
Defined.
 
Theorem sizeOrder_wf: well_founded sizeOrder.
  red; intro; eapply sizeOrder_wf'; eauto.
Defined.

Lemma remove_wf: forall (s: Subst) (n: nat) (t: Term),
  find n s = Some t -> sizeOrder (S.remove n s) s.
  intros. red. 


Fixpoint walk (t: Term) (s: Subst) : Term :=
  match t with
  | V n => match find n s with
           | None   => V n
           | Some t => walk t (S.remove n s)
           end
  | t => t
  end.
  


Example ex1: find 3 (empty [1 <- V 2][3 <- V 4]) = Some (V 4).
Proof. reflexivity. Qed.

Example ex2: find 5 (empty [1 <- V 2][3 <- V 4]) = None.
Proof. reflexivity. Qed.



