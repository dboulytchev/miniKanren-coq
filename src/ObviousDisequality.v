Require Import List.
Import ListNotations.
(*Require Import Coq.Lists.ListSet.*)
Require Import Extraction.

Require Import Unify.
Require Import MiniKanrenSyntax.
Require Import Stream.
Require Import DenotationalSem.
Require Import OperationalSem.
Require Import OpSemSoundness.
Require Import OpSemCompleteness.


Module ObviousConstraintStore <: ConstraintStoreSig.

Definition constraint_store (s : subst) : Set := list (term * term).

Definition init_cs : constraint_store empty_subst := [].

Inductive add_constraint_ind_def : forall (s : subst), constraint_store s -> term -> term -> option (constraint_store s) -> Set :=
| acC : forall s cs t1 t2, add_constraint_ind_def s cs t1 t2 (Some ((t1, t2) :: cs)).

Definition add_constraint := add_constraint_ind_def.

Lemma add_constraint_exists :
  forall (s : subst) (cs : constraint_store s) (t1 t2 : term),
    {r : option (constraint_store s) & add_constraint s cs t1 t2 r}.
Proof. intros. eexists. econstructor. Qed.

Lemma add_constraint_unique :
  forall (s : subst) (cs : constraint_store s) (t1 t2 : term) (r r' : option (constraint_store s)),
    add_constraint s cs t1 t2 r -> add_constraint s cs t1 t2 r' -> r = r'.
Proof. intros. good_inversion H. good_inversion H0. simpl_existT_cs_same. reflexivity. Qed.

Inductive upd_cs_ind_def : forall (s : subst), constraint_store s -> forall (d : subst), option (constraint_store (compose s d)) -> Set :=
| uC : forall s cs d, upd_cs_ind_def s cs d (Some cs).

Definition upd_cs := upd_cs_ind_def.

Lemma upd_cs_exists :
  forall (s : subst) (cs : constraint_store s) (d : subst),
    {r : option (constraint_store (compose s d)) & upd_cs s cs d r}.
Proof. intros. eexists. econstructor. Qed.

Lemma upd_cs_unique :
  forall (s : subst) (cs : constraint_store s) (d : subst) (r r' : option (constraint_store (compose s d))),
    upd_cs s cs d r -> upd_cs s cs d r' -> r = r'.
Proof. intros. good_inversion H. good_inversion H0. simpl_existT_cs_same. reflexivity. Qed.

Definition in_denotational_sem_cs (s : subst) (cs : constraint_store s) (f : repr_fun) :=
  forall (t1 t2 : term), In (t1, t2) cs -> ~ gt_eq (apply_repr_fun f t1) (apply_repr_fun f t2).

Notation "[| s , cs , f |]" := (in_denotational_sem_cs s cs f) (at level 0).

Lemma init_condition : forall f, [| empty_subst , init_cs , f |].
Proof. unfold in_denotational_sem_cs. contradiction. Qed.

Lemma add_constraint_fail_condition :
  forall (s : subst) (cs : constraint_store s) (t1 t2 : term),
    add_constraint s cs t1 t2 None ->
    forall f, ~ ([| s , cs  , f |] /\ [ s , f ] /\ [| Disunify t1 t2 , f |]).
Proof. intros. inversion H. Qed.

Lemma add_constraint_success_condition :
  forall (s : subst) (cs cs' : constraint_store s) (t1 t2 : term),
    add_constraint s cs t1 t2 (Some cs') ->
    forall f, [| s , cs' , f |] /\ [ s , f ] <->
              [| s , cs  , f |] /\ [ s , f ] /\ [| Disunify t1 t2 , f |].
Proof.
  unfold in_denotational_sem_cs. intros.
  good_inversion H. simpl_existT_cs_same. good_inversion H4. split.
  { intros [DSCS DSS]. split; try split; intros; auto.
    { apply DSCS. right. auto. }
    { constructor. apply DSCS. left. auto. }  }
  { intros [DSCS [DSS DSG]]. good_inversion DSG. split; auto. intros.
    destruct H; auto. good_inversion H; auto. }
Qed.

Lemma upd_cs_fail_condition :
  forall (s : subst) (cs : constraint_store s) (d : subst),
    upd_cs s cs d None -> forall f, ~ ([| s , cs , f |] /\ [ compose s d , f ]).
Proof. intros. inversion H. Qed.

Lemma upd_cs_success_condition :
  forall (s : subst) (cs : constraint_store s) (d : subst) (cs' : constraint_store (compose s d)),
    upd_cs s cs d (Some cs') ->
    forall f, [| compose s d , cs' , f |] /\ [ compose s d , f ] <->
              [| s           , cs  , f |] /\ [ compose s d , f ].
Proof.
  unfold in_denotational_sem_cs. intros. good_inversion H. simpl_existT_cs_same.
  good_inversion H3. reflexivity.
Qed.

End ObviousConstraintStore.


Module OperationalSemObviousCS := OperationalSemAbstr ObviousConstraintStore.

Module OperationalSemObviousCSSoundness := OperationalSemSoundnessAbstr ObviousConstraintStore.

Module OperationalSemObviousCSCompleteness := OperationalSemCompletenessAbstr ObviousConstraintStore.

Import OperationalSemObviousCS.

Extraction Language Haskell.

Extraction "extracted/obvious_diseq_interpreter.hs" op_sem_exists.


