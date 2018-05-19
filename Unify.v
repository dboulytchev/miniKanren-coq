Require Import List.
Import ListNotations.
Require Import Arith.
Require Import Omega.

(************************* Terms *************************)
(* Name of entities *)
Definition name := nat.

(* Term type *) 
Inductive term : Set :=
(* a variable           *) | Var : name -> term
(* a constant           *) | Cst : name -> term
(* a binary constructor *) | Con : name -> term -> term -> term.

(* Set union on lists *)
Definition union (l1 l2 : list name) : list name := nodup eq_nat_dec (l1 ++ l2).

(* Some lemmas for lists as sets *)
Lemma union_NoDup: forall (l1 l2 : list name), NoDup (union l1 l2).
Proof. admit. Admitted.

Lemma union_In: forall (l1 l2 : list name) (n : name), In n (union l1 l2) <-> In n l1 \/ In n l2.
Proof. admit. Admitted.
                       
Lemma lt_length:
  forall (l1 l2 : list name),
    NoDup l1 -> NoDup l2 -> (forall n, In n l1 -> In n l2) -> (exists n, In n l2 /\ ~ (In n l1)) -> length l1 < length l2.
Proof. admit. Admitted.
    
(* Free variables *)
Fixpoint fv (t : term) : list name :=
  match t with
  | Var x     => [x]
  | Cst _     => []
  | Con _ x y => union (fv x) (fv y)
  end.

(* fv returns NoDup *)
Lemma fv_NoDup: forall t,  NoDup (fv t).
Proof. admit. Admitted.

(* Occurs property *)
Fixpoint occurs (n : name) (t : term) : bool :=
  if find (fun x => if eq_nat_dec x n then true else false) (fv t)
  then true
  else false.

(* In follows from occurs *)
Lemma occurs_In: forall t n, occurs n t = true <-> In n (fv t).
Proof. admit. Admitted.
  
(******************** Substitutions **********************)
(* Substitution *)
Definition subst : Type := list (name * term).

(* Substitution domain *)
Fixpoint domain (s : subst) : list name := map (@fst name term) s.
  
(* Substitution image *)
Fixpoint image (s : subst) (n : name) : option term :=
  match s with
  | [] => None
  | (m, t) :: tl => if eq_nat_dec m n then Some t else image tl n
  end.

(* Substitution application *)
Fixpoint apply (s : subst) (t : term) : term :=
  match t with
  | Cst _     => t
  | Var n     => match image s n with None => t | Some t' => t' end
  | Con n l r => Con n (apply s l) (apply s r)
  end.

(* Free variables in the result of substitution application *)
Lemma apply_fv: forall t s n m,  In m (fv (apply [(n, s)] t)) -> In m (fv s) \/ In m (fv t).
Proof. admit. Admitted.

(* Generality *)
Definition more_general (m s : subst) : Prop :=
  exists (s' : subst), forall (t : term), apply s t = apply s' (apply m t).

(* Unification property *)
Definition unifier (s : subst) (t1 t2 : term) : Prop := apply s t1 = apply s t2.

(* MGU *)
Definition mgu (m : subst) (t1 t2 : term) : Prop :=
  unifier m t1 t2 /\ forall (s : subst), unifier s t1 t2 -> more_general m s.

(*
(******************** Well-formed Substitutions ***********)
(* Substitution welformedness *)
Definition subst_wf (s : subst) : Prop :=
  forall (m n : name), forall (t : term), In m (domain s) -> image s n = Some t -> occurs m t = false.

(* Well-formed substitution *)
Definition swbst := {s : subst | subst_wf s}.

(* Coercion *)
Definition coerce (T : Type) (P : subst -> T) (s: swbst) : T :=
  match s with exist l _ => P l end.
             
(* Empty well-formed substitution *)
Definition empty : subst := [].
(*
Proof.
  exists []. unfold subst_wf. intros. simpl in H. inversion H.
Qed.
*)
(* Extending a well-fromed substitution *)
Definition extend (b : subst) (n : name) (t : term) := (n, apply b t) :: b.

(* Singleton substitution *)
Definition trivial (n : name) (t : term) : subst := extend empty n t.
(*
(* Singleton well-formed substitution construction *)
Definition trivial (n : name) (t : term) : option swbst.
Proof.
  remember (occurs n t). destruct b.
  * exact None.
  * remember [(n, t)]. assert (A: image l n = Some t). rewrite Heql. simpl.
    destruct (eq_nat_dec n n). auto. exfalso. auto. refine (Some _). exists l.
    rewrite Heql. unfold subst_wf. intros. simpl in H.
    destruct (eq_nat_dec n n0). inversion H. subst. auto. inversion H.
Qed.
 *)
*)
Inductive outcome : Set :=
| Fail
| Fine
| Subst : forall (n: name) (t: term), outcome.  

Definition create (n: name) (t: term) : outcome :=
  if occurs n t then Fail else Subst n t.

(* Find a difference in a couple of terms and try to make a unification step *)
Fixpoint unification_step (t1 t2 : term) : outcome :=
  match (t1, t2) with
  | (Cst n1      , Cst n2      ) => if eq_nat_dec n1 n2 then Fine else Fail 
  | (Con n1 l1 r1, Con n2 l2 r2) => if eq_nat_dec n1 n2
                                    then
                                      match unification_step l1 l2 with
                                      | Fail => Fail
                                      | Fine => unification_step r1 r2
                                      | res  => res
                                      end
                                    else Fail
  | (Var n1      , Var n2      ) => if eq_nat_dec n1 n2 then Fine else create n1 t2
  | (Var n1      , _           ) => create n1 t2
  | (_           , Var n2      ) => create n2 t1
  | (_           , _           ) => Fail
  end.

Definition unification_step_ok t1 t2 n s := unification_step t1 t2 = Subst n s.

Lemma unification_step_fv: forall t1 t2 s n ,
    unification_step_ok t1 t2 n s -> (forall m, In m (fv s) -> In m (fv t1) \/ In m (fv t2)).
Proof. admit. Admitted. 

Lemma unification_step_subst_wf:
  forall t1 t2 s n, unification_step_ok t1 t2 n s -> ~ In n (fv s).
Proof. admit. Admitted.

Lemma unification_step_subst_occurs:
  forall t1 t2 s n, unification_step_ok t1 t2 n s -> In n (fv t1) \/ In n (fv t2).
Proof. admit. Admitted.

Lemma unification_step_subst_elims: forall s t n, In n (fv (apply [(n, s)] t)) -> In n (fv s).
Proof. admit. Admitted.
  
Lemma unification_step_decreases_fv:
  forall t1 t2 s n,
    unification_step_ok t1 t2 n s ->
    length (union (fv (apply [(n, s)] t1)) (fv (apply [(n, s)] t2))) < length (union (fv t1) (fv t2)).
Proof.
  intros t1 t2 s n USok. 
  apply lt_length; try apply union_NoDup.
  * intros n0 InH. apply union_In in InH. inversion_clear InH.
    + apply apply_fv in H. inversion_clear H.
      - apply unification_step_fv with (m:=n0) in USok.
        { apply union_In. auto. }
        auto.
      - apply union_In. left. auto.
    + apply apply_fv in H. inversion_clear H.
      - apply unification_step_fv with (m:=n0) in USok.
        { apply union_In. auto. }
        auto.
      - apply union_In. right. auto.
  * exists n. split.
    + apply unification_step_subst_occurs in USok. apply union_In. auto.
    + unfold not. intro H. apply union_In in H. inversion_clear H as [H0 | H0];
      apply unification_step_subst_elims in H0;
      apply unification_step_subst_wf in USok; auto.
Qed.
      