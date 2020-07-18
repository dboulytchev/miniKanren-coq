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

Definition constraint_store : Set := list (term * term).


Definition in_denotational_sem_cs (s : subst) (cs : constraint_store) (f : repr_fun) :=
  forall (t1 t2 : term), In (t1, t2) cs -> ~ gt_eq (apply_repr_fun f t1) (apply_repr_fun f t2).

Notation "[| s , cs , f |]" := (in_denotational_sem_cs s cs f) (at level 0).


Definition wf_cs (s : subst) (cs : constraint_store) : Prop := True.


Definition init_cs : constraint_store := [].

Lemma wf_init_cs : wf_cs empty_subst init_cs.
Proof. apply I. Qed.


Inductive add_constraint_ind_def : subst -> constraint_store -> term -> term -> option constraint_store -> Prop :=
| acC : forall s cs t1 t2, add_constraint_ind_def s cs t1 t2 (Some ((t1, t2) :: cs)).

Definition add_constraint := add_constraint_ind_def.

Lemma add_constraint_exists :
  forall (s : subst) (cs : constraint_store) (t1 t2 : term),
    {r : option constraint_store & add_constraint s cs t1 t2 r}.
Proof. intros. eexists. econstructor. Qed.

Lemma add_constraint_unique :
  forall (s : subst) (cs : constraint_store) (t1 t2 : term) (r r' : option constraint_store),
    add_constraint s cs t1 t2 r -> add_constraint s cs t1 t2 r' -> r = r'.
Proof. intros. good_inversion H. good_inversion H0. reflexivity. Qed.

Lemma add_constraint_wf_preservation :
  forall (s : subst) (cs : constraint_store) (t1 t2 : term) (cs' : constraint_store),
    narrowing_subst s ->
    add_constraint s cs t1 t2 (Some cs') ->
    wf_cs s cs ->
    wf_cs s cs'.
Proof. intros. apply I. Qed.


Inductive upd_cs_ind_def : subst -> constraint_store -> subst -> option constraint_store -> Prop :=
| uC : forall s cs d, upd_cs_ind_def s cs d (Some cs).

Definition upd_cs := upd_cs_ind_def.

Lemma upd_cs_exists :
  forall (s : subst) (cs : constraint_store) (d : subst),
    {r : option constraint_store & upd_cs s cs d r}.
Proof. intros. eexists. econstructor. Qed.

Lemma upd_cs_unique :
  forall (s : subst) (cs : constraint_store) (d : subst) (r r' : option (constraint_store)),
    upd_cs s cs d r -> upd_cs s cs d r' -> r = r'.
Proof. intros. good_inversion H. good_inversion H0. reflexivity. Qed.

Lemma upd_cs_wf_preservation :
  forall (s : subst) (cs : constraint_store) (d : subst) (cs' : constraint_store),
    narrowing_subst s ->
    narrowing_subst d ->
    extending_subst s d ->
    upd_cs s cs d (Some cs') ->
    wf_cs s cs ->
    wf_cs (compose s d) cs'.
Proof. intros. apply I. Qed.


Lemma init_condition : forall f, [| empty_subst , init_cs , f |].
Proof. unfold in_denotational_sem_cs. contradiction. Qed.

Lemma add_constraint_fail_condition :
  forall (s : subst) (cs : constraint_store) (t1 t2 : term),
    wf_cs s cs ->
    add_constraint s cs t1 t2 None ->
    forall f, ~ ([| s , cs  , f |] /\ [ s , f ] /\ [| Disunify t1 t2 , f |]).
Proof. intros. inversion H0. Qed.

Lemma add_constraint_success_condition :
  forall (s : subst) (cs cs' : constraint_store) (t1 t2 : term),
    wf_cs s cs ->
    add_constraint s cs t1 t2 (Some cs') ->
    forall f, [| s , cs' , f |] /\ [ s , f ] <->
              [| s , cs  , f |] /\ [ s , f ] /\ [| Disunify t1 t2 , f |].
Proof.
  unfold in_denotational_sem_cs. intros.
  good_inversion H0. split.
  { intros [DSCS DSS]. split; try split; intros; auto.
    { apply DSCS. right. auto. }
    { constructor. apply DSCS. left. auto. }  }
  { intros [DSCS [DSS DSG]]. good_inversion DSG. split; auto. intros.
    destruct H0; auto. good_inversion H0; auto. }
Qed.

Lemma upd_cs_fail_condition :
  forall (s : subst) (cs : constraint_store) (d : subst),
    wf_cs s cs ->
    upd_cs s cs d None -> forall f, ~ ([| s , cs , f |] /\ [ compose s d , f ]).
Proof. intros. inversion H0. Qed.

Lemma upd_cs_success_condition :
  forall (s : subst) (cs : constraint_store) (d : subst) (cs' : constraint_store),
    wf_cs s cs ->
    upd_cs s cs d (Some cs') ->
    forall f, [| compose s d , cs' , f |] /\ [ compose s d , f ] <->
              [| s           , cs  , f |] /\ [ compose s d , f ].
Proof.
  unfold in_denotational_sem_cs. intros. good_inversion H0. reflexivity.
Qed.

End ObviousConstraintStore.


Module OperationalSemObviousCS := OperationalSemAbstr ObviousConstraintStore.

Module OperationalSemObviousCSSoundness := OperationalSemSoundnessAbstr ObviousConstraintStore.

Module OperationalSemObviousCSCompleteness := OperationalSemCompletenessAbstr ObviousConstraintStore.

Import OperationalSemObviousCS.

Extraction Language Haskell.

Extraction "extracted/obvious_diseq_interpreter.hs" op_sem_exists initial_state.


