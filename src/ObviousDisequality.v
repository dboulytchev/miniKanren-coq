Add LoadPath "~/JB/minikanren-coq/src/".

Require Import List.
Import ListNotations.
(*Require Import Coq.Lists.ListSet.*)
Require Import Extraction.

Require Import Unify.
Require Import MiniKanrenSyntaxDiseq.
Require Import Stream.
Require Import DenotationalSemDiseq.
Require Import OperationalSemDiseq.
Require Import OpSemDiseqSoundness.
Require Import OpSemCompletenessDiseq.


Module ObviousConstraintStore <: ConstraintStoreSig.

Definition constraint_store (s : subst) : Set := list (term * term).

Definition init_cs : constraint_store empty_subst := [].

Inductive add_constraint : forall (s : subst), constraint_store s -> term -> term -> option (constraint_store s) -> Set :=
| acC : forall s cs t1 t2, add_constraint s cs t1 t2 (Some ((t1, t2) :: cs)).

Lemma add_constraint_exists :
  forall (s : subst) (cs : constraint_store s) (t1 t2 : term),
    {r : option (constraint_store s) & add_constraint s cs t1 t2 r}.
Proof. intros. eexists. econstructor. Qed.

Lemma add_constraint_unique :
  forall (s : subst) (cs : constraint_store s) (t1 t2 : term) (r r' : option (constraint_store s)),
    add_constraint s cs t1 t2 r -> add_constraint s cs t1 t2 r' -> r = r'.
Proof. intros. good_inversion H. good_inversion H0. simpl_existT_cs_same.

Parameter upd_cs : forall (s : subst), constraint_store s -> forall (d : subst), option (constraint_store (compose s d)) -> Set.

Parameter upd_cs_exists :
  forall (s : subst) (cs : constraint_store s) (d : subst),
    {r : option (constraint_store (compose s d)) & upd_cs s cs d r}.

Parameter upd_cs_unique :
  forall (s : subst) (cs : constraint_store s) (d : subst) (r r' : option (constraint_store (compose s d))),
    upd_cs s cs d r -> upd_cs s cs d r' -> r = r'.

Parameter in_denotational_sem_cs : forall (s : subst), constraint_store s -> repr_fun -> Prop.

Notation "[| s , cs , f |]" := (in_denotational_sem_cs s cs f) (at level 0).

Axiom init_condition : forall f, [| empty_subst , init_cs , f |].

Axiom add_constraint_fail_condition :
  forall (s : subst) (cs : constraint_store s) (t1 t2 : term),
    add_constraint s cs t1 t2 None ->
    forall f, ~ ([| s , cs  , f |] /\ [ s , f ] /\ (~ gt_eq (apply_repr_fun f t1) (apply_repr_fun f t2))).

Axiom add_constraint_success_condition :
  forall (s : subst) (cs cs' : constraint_store s) (t1 t2 : term),
    add_constraint s cs t1 t2 (Some cs') ->
    forall f, [| s , cs' , f |] /\ [ s , f ] <->
              [| s , cs  , f |] /\ [ s , f ] /\ (~ gt_eq (apply_repr_fun f t1) (apply_repr_fun f t2)).

Axiom upd_cs_fail_condition :
  forall (s : subst) (cs : constraint_store s) (d : subst),
    upd_cs s cs d None -> forall f, ~ ([| s , cs , f |] /\ [ compose s d , f ]).

Axiom upd_cs_success_condition :
  forall (s : subst) (cs : constraint_store s) (d : subst) (cs' : constraint_store (compose s d)),
    upd_cs s cs d (Some cs') ->
    forall f, [| compose s d , cs' , f |] /\ [ compose s d , f ] <->
              [| s           , cs  , f |] /\ [ compose s d , f ].

End ObviousConstraintStore.



Module Type ConstraintStoreSig.

Parameter constraint_store : subst -> Set.

Parameter init_cs : constraint_store empty_subst.

Parameter add_constraint : forall (s : subst), constraint_store s -> term -> term -> option (constraint_store s) -> Set.

Parameter add_constraint_exists :
  forall (s : subst) (cs : constraint_store s) (t1 t2 : term),
    {r : option (constraint_store s) & add_constraint s cs t1 t2 r}.

Parameter add_constraint_unique :
  forall (s : subst) (cs : constraint_store s) (t1 t2 : term) (r r' : option (constraint_store s)),
    add_constraint s cs t1 t2 r -> add_constraint s cs t1 t2 r' -> r = r'.

Parameter upd_cs : forall (s : subst), constraint_store s -> forall (d : subst), option (constraint_store (compose s d)) -> Set.

Parameter upd_cs_exists :
  forall (s : subst) (cs : constraint_store s) (d : subst),
    {r : option (constraint_store (compose s d)) & upd_cs s cs d r}.

Parameter upd_cs_unique :
  forall (s : subst) (cs : constraint_store s) (d : subst) (r r' : option (constraint_store (compose s d))),
    upd_cs s cs d r -> upd_cs s cs d r' -> r = r'.

Parameter in_denotational_sem_cs : forall (s : subst), constraint_store s -> repr_fun -> Prop.

Notation "[| s , cs , f |]" := (in_denotational_sem_cs s cs f) (at level 0).

Axiom init_condition : forall f, [| empty_subst , init_cs , f |].

Axiom add_constraint_fail_condition :
  forall (s : subst) (cs : constraint_store s) (t1 t2 : term),
    add_constraint s cs t1 t2 None ->
    forall f, ~ ([| s , cs  , f |] /\ [ s , f ] /\ (~ gt_eq (apply_repr_fun f t1) (apply_repr_fun f t2))).

Axiom add_constraint_success_condition :
  forall (s : subst) (cs cs' : constraint_store s) (t1 t2 : term),
    add_constraint s cs t1 t2 (Some cs') ->
    forall f, [| s , cs' , f |] /\ [ s , f ] <->
              [| s , cs  , f |] /\ [ s , f ] /\ (~ gt_eq (apply_repr_fun f t1) (apply_repr_fun f t2)).

Axiom upd_cs_fail_condition :
  forall (s : subst) (cs : constraint_store s) (d : subst),
    upd_cs s cs d None -> forall f, ~ ([| s , cs , f |] /\ [ compose s d , f ]).

Axiom upd_cs_success_condition :
  forall (s : subst) (cs : constraint_store s) (d : subst) (cs' : constraint_store (compose s d)),
    upd_cs s cs d (Some cs') ->
    forall f, [| compose s d , cs' , f |] /\ [ compose s d , f ] <->
              [| s           , cs  , f |] /\ [ compose s d , f ].

End ConstraintStoreSig.
