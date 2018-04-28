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

(* Occurs property *)
Fixpoint occurs (n : name) (t : term) : bool :=
  match t with
  | Var n1    => if eq_nat_dec n1 n then true else false
  | Con _ l r => orb (occurs n l) (occurs n r)
  | _         => false
  end.

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

(* Generality *)
Definition more_general (m s : subst) : Prop :=
  exists (s' : subst), forall (t : term), apply s t = apply s' (apply m t).

(* Unification property *)
Definition unifier (s : subst) (t1 t2 : term) : Prop := apply s t1 = apply s t2.

(* MGU *)
Definition mgu (m : subst) (t1 t2 : term) : Prop :=
  unifier m t1 t2 /\ forall (s : subst), unifier s t1 t2 -> more_general m s.

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

Inductive outcome : Set :=
| Fail
| Fine
| Subst : forall (n: name) (t: term), outcome.  

Definition create (n: name) (t: term) : outcome :=
  if occurs n t then Fail else Subst n t.
(*.
  remember (occurs n t). destruct b.
  * exact Fail.
  * symmetry in Heqb. exact (Subst n t Heqb).
Defined.
  *)         
(* Find a difference in a couple of terms and try to make a unification step *)
Fixpoint delta (t1 t2 : term) : outcome :=
  match (t1, t2) with
  | (Cst n1      , Cst n2      ) => if eq_nat_dec n1 n2 then Fine else Fail 
  | (Con n1 l1 r1, Con n2 l2 r2) => if eq_nat_dec n1 n2
                                    then
                                      match delta l1 l2 with
                                      | Fail => Fail
                                      | Fine => delta r1 r2
                                      | res  => res
                                      end
                                    else Fail
  | (Var n1      , Var n2      ) => if eq_nat_dec n1 n2 then Fine else create n1 t2
  | (Var n1      , _           ) => create n1 t2
  | (_           , Var n2      ) => create n2 t1
  | (_           , _           ) => Fail
  end.

(* A distance between terms *)
Fixpoint distance (t1 t2 : term) : nat :=
  match (t1, t2) with
  | (Cst n1      , Cst n2      ) => if eq_nat_dec n1 n2 then 0 else 1 
  | (Con n1 l1 r1, Con n2 l2 r2) => if eq_nat_dec n1 n2
                                    then distance l1 l2 + distance r1 r2
                                    else 1
  | (Var n1      , Var n2      ) => if eq_nat_dec n1 n2 then 0 else 1
  | (_           , _           ) => 1
  end.

Lemma apply_eq: forall (t1 t2 : term) (n : name), occurs n t1 = false -> apply [(n, t2)] t1 = t1.
Proof. admit. Admitted.

Lemma apply_empty: forall (t1 : term), apply [] t1 = t1.
Proof. admit. Admitted.

Lemma distance_eq_zero: forall (t : term), distance t t = 0.
Proof. admit. Admitted.
                       
Lemma distance_decrease:
  forall (t1 t2 t: term) (n: name),
    delta t1 t2 = Subst n t -> distance t1 t2 > distance (apply (trivial n t) t1) (apply (trivial n t) t2).
Proof.
  intros. induction t1.
  * unfold delta in H. unfold create in H. destruct t2. destruct (eq_nat_dec n0 n1). inversion H.
    destruct (occurs n0 (Var n1)). inversion H. inversion H. subst. unfold trivial. unfold empty. unfold extend. unfold apply.
    simpl. destruct (eq_nat_dec n n1). rewrite e in n2. exfalso. auto. destruct (eq_nat_dec n n). unfold distance.
    destruct (eq_nat_dec n1 n1). omega. exfalso. auto. exfalso. auto.
    unfold occurs in H. inversion H.  unfold trivial. unfold empty. unfold extend. unfold apply.
    simpl. destruct (eq_nat_dec n n). simpl. destruct (eq_nat_dec n1 n1). omega. exfalso. auto. exfalso. auto.
    destruct (occurs n0 (Con n1 t2_1 t2_2)) eqn:D. inversion H. inversion H. unfold trivial. unfold empty. unfold extend.
    apply apply_eq with (t2:=apply [] (Con n1 t2_1 t2_2)) in D. subst n0. rewrite D. rewrite apply_empty.
    unfold apply. unfold image. destruct (eq_nat_dec n n). rewrite distance_eq_zero. unfold distance. omega. exfalso. auto.
  * admit.
  * 
    