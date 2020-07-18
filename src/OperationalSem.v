Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Program.Equality.
Require Import Omega.

Require Import Unify.
Require Import MiniKanrenSyntax.
Require Import Stream.
Require Import DenotationalSem.

Definition narrowing_subst (s : subst) : Prop := forall x, in_subst_vran s x ->  ~ in_subst_dom s x.

Definition extending_subst (s w : subst) : Prop :=
  (forall x, in_subst_dom w x -> ~ in_subst_dom s x) /\
  (forall x, in_subst_vran w x -> ~ in_subst_dom s x).

Definition nodup_dom (s : subst) : Prop := NoDup (map fst s).

Lemma apply_subst_FV_stronger
      (x : name)
      (t : term)
      (s : subst)
      (X_FV : In x (fv_term (apply_subst s t))) :
      (In x (fv_term t) /\ image s x = None) \/ in_subst_vran s x.
Proof.
  induction t; try contradiction.
  { simpl in X_FV. destruct (image s n) eqn:EQ.
    { right. red. exists n. exists t. auto. }
    { left. split; auto. destruct X_FV; try contradiction. subst. auto. } }
  { simpl in X_FV. apply (set_union_elim name_eq_dec) in X_FV. destruct X_FV.
    { apply IHt1 in H. destruct H.
      { destruct H. left. split; auto. apply (set_union_intro name_eq_dec). left. auto. }
      { right. auto. } }
    { apply IHt2 in H. destruct H.
      { destruct H. left. split; auto. apply (set_union_intro name_eq_dec). right. auto. }
      { right. auto. } } }
Qed.

Lemma compose_vran_stronger
      (s d : subst)
      (y : name)
      (IN_VRAN_COMP : in_subst_vran (compose s d) y) :
      (in_subst_vran s y /\ ~ in_subst_dom d y) \/ in_subst_vran d y.
Proof.
  destruct IN_VRAN_COMP as [x [t [IN_IMAGE IN_FV]]].
  assert (GEN : (exists t0, image s x = Some t0 /\ In y (fv_term t0) /\ ~ in_subst_dom d y) \/ in_subst_vran d y).
  { induction s.
    { right. red. eauto. }
    { destruct a. simpl in IN_IMAGE. simpl. destruct (Nat.eq_dec n x).
      { inversion IN_IMAGE. subst. apply apply_subst_FV_stronger in IN_FV.
        destruct IN_FV; auto. destruct H. left. exists t0. split; try split; auto.
        intro C. destruct C. rewrite H0 in H1. good_inversion H1. }
      { apply IHs in IN_IMAGE. destruct IN_IMAGE; auto. } } }
  destruct GEN.
  { left. destruct H as [t0 [IMG [IN_VRAN NIN_DOM]]]. split; eauto. red. eauto. }
  { right. auto. }
Qed.

Lemma compose_narrowing_extending
      (s d : subst)
      (NAR_s : narrowing_subst s)
      (NAR_d : narrowing_subst d)
      (EXT : extending_subst s d) :
      narrowing_subst (compose s d).
Proof.
  red in NAR_s. red in NAR_d. red in EXT. destruct EXT as [EXT_DOM EXT_VRAN].
  red. intros x IN_VRAN_COMP IN_DOM_COMP. apply compose_dom in IN_DOM_COMP.
  apply compose_vran_stronger in IN_VRAN_COMP. destruct IN_DOM_COMP; destruct IN_VRAN_COMP.
  { destruct H0. apply NAR_s in H0. auto. }
  { apply EXT_VRAN in H0. auto. }
  { destruct H0. auto. }
  { apply NAR_d in H0. auto. }
Qed.

Lemma in_fst_dom
      (s : subst)
      (n : name)
      (IN : In n (map fst s)) :
      in_subst_dom s n.
Proof.
  revert IN. induction s; try contradiction.
  intros. red. destruct a. simpl in IN. simpl. destruct (Nat.eq_dec n0 n); subst.
  { eexists; eauto. }
  { destruct IN; try contradiction. apply IHs in H. auto. }
Qed.

Lemma mgu_nodup_dom
      (t1 t2 : term)
      (m : subst)
      (MGU : mgu t1 t2 (Some m)) :
      nodup_dom m.
Proof.
  remember (Some m) as r eqn:EQ. revert EQ. revert m.
  induction MGU; intros m EQ; good_inversion EQ.
  { constructor. }
  { specialize (IHMGU r eq_refl).
    unfold compose. simpl. constructor; auto. simpl. intro C.
    apply in_fst_dom in C. eapply mgu_dom in MGU; eauto. destruct MGU.
    all: eapply unification_step_subst_elims in H; eauto; eapply unification_step_subst_wf; eauto. }
Qed.


Lemma in_apply_narrowing_FV
      (s : subst)
      (NAR : narrowing_subst s)
      (n : name)
      (t : term)
      (IN_ts : In n (fv_term (apply_subst s t))) :
      ~ in_subst_dom s n.
Proof.
  apply apply_subst_FV_stronger in IN_ts. destruct IN_ts.
  { destruct H. intro C. destruct C. rewrite H1 in H0. good_inversion H0. }
  { auto. }
Qed.

Lemma mgu_is_extending
      (s : subst)
      (NAR : narrowing_subst s)
      (t1 t2 : term)
      (m : subst)
      (MGU : mgu (apply_subst s t1) (apply_subst s t2) (Some m)) :
      extending_subst s m.
Proof.
  red. specialize (mgu_dom _ _ _ MGU). intros IN_DOM_TERMS.
  specialize (mgu_vran _ _ _ MGU). intros IN_VRAN_TERMS.
  split.
  { intros. apply IN_DOM_TERMS in H. destruct H; eapply in_apply_narrowing_FV; eauto. }
  { intros. apply IN_VRAN_TERMS in H. destruct H; eapply in_apply_narrowing_FV; eauto. }
Qed.


Lemma mgu_is_narrowing
      (t1 t2 : term)
      (m : subst)
      (MGU : mgu t1 t2 (Some m)) :
      narrowing_subst m.
Proof.
  remember (Some m) as r eqn:EQ. revert EQ. revert m.
  induction MGU; intros m EQ; good_inversion EQ.
  { red. intros. destruct H as [y [t [IMG _]]]. good_inversion IMG. }
  { specialize (IHMGU r eq_refl). red.
    intros. apply compose_vran_stronger in H. intro DOM. apply compose_dom in DOM.
    destruct H; destruct DOM. 
    { destruct H. destruct H0. destruct H as [y [ty [IMG_RAN IN_RAN]]].
      simpl in H0. destruct (Nat.eq_dec n x); good_inversion H0.
      simpl in IMG_RAN. destruct (Nat.eq_dec x y); good_inversion IMG_RAN.
      eapply unification_step_subst_wf; eauto. }
    { destruct H. auto. }
    { destruct H0. simpl in H0. destruct (Nat.eq_dec n x); good_inversion H0.
      eapply mgu_vran in H; eauto. destruct H; apply unification_step_subst_elims in H;
      eapply unification_step_subst_wf; eauto. }
    { apply IHMGU in H. auto. } }
Qed.

Module Type ConstraintStoreSig.

Parameter constraint_store : Set.


Parameter in_denotational_sem_cs : subst -> constraint_store -> repr_fun -> Prop.

Notation "[| s , cs , f |]" := (in_denotational_sem_cs s cs f) (at level 0).


Parameter wf_cs : subst -> constraint_store -> Prop.


Parameter init_cs : constraint_store.

Axiom wf_init_cs : wf_cs empty_subst init_cs.


Parameter add_constraint : subst -> constraint_store -> term -> term -> option constraint_store -> Prop.

Axiom add_constraint_exists :
  forall (s : subst) (cs : constraint_store) (t1 t2 : term),
    {r : option constraint_store & add_constraint s cs t1 t2 r}.

Axiom add_constraint_unique :
  forall (s : subst) (cs : constraint_store) (t1 t2 : term) (r r' : option constraint_store),
    add_constraint s cs t1 t2 r -> add_constraint s cs t1 t2 r' -> r = r'.

Axiom add_constraint_wf_preservation :
  forall (s : subst) (cs : constraint_store) (t1 t2 : term) (cs' : constraint_store),
    narrowing_subst s ->
    add_constraint s cs t1 t2 (Some cs') ->
    wf_cs s cs ->
    wf_cs s cs'.


Parameter upd_cs : subst -> constraint_store -> subst -> option constraint_store -> Prop.

Axiom upd_cs_exists :
  forall (s : subst) (cs : constraint_store) (d : subst),
    {r : option constraint_store & upd_cs s cs d r}.

Axiom upd_cs_unique :
  forall (s : subst) (cs : constraint_store) (d : subst) (r r' : option constraint_store),
    upd_cs s cs d r -> upd_cs s cs d r' -> r = r'.

Axiom upd_cs_wf_preservation :
  forall (s : subst) (cs : constraint_store) (d : subst) (cs' : constraint_store),
    narrowing_subst s ->
    narrowing_subst d ->
    extending_subst s d ->
    upd_cs s cs d (Some cs') ->
    wf_cs s cs ->
    wf_cs (compose s d) cs'.


Axiom init_condition : forall f, [| empty_subst , init_cs , f |].

Axiom add_constraint_fail_condition :
  forall (s : subst) (cs : constraint_store) (t1 t2 : term),
    wf_cs s cs ->
    add_constraint s cs t1 t2 None ->
    forall f, ~ ([| s , cs  , f |] /\ [ s , f ] /\ [| Disunify t1 t2 , f |]).

Axiom add_constraint_success_condition :
  forall (s : subst) (cs cs' : constraint_store) (t1 t2 : term),
    wf_cs s cs ->
    add_constraint s cs t1 t2 (Some cs') ->
    forall f, [| s , cs' , f |] /\ [ s , f ] <->
              [| s , cs  , f |] /\ [ s , f ] /\ [| Disunify t1 t2 , f |].

Axiom upd_cs_fail_condition :
  forall (s : subst) (cs : constraint_store) (d : subst),
    wf_cs s cs ->
    upd_cs s cs d None -> forall f, ~ ([| s , cs , f |] /\ [ compose s d , f ]).

Axiom upd_cs_success_condition :
  forall (s : subst) (cs : constraint_store) (d : subst) (cs' : constraint_store),
    wf_cs s cs ->
    upd_cs s cs d (Some cs') ->
    forall f, [| compose s d , cs' , f |] /\ [ compose s d , f ] <->
              [| s           , cs  , f |] /\ [ compose s d , f ].

End ConstraintStoreSig.


Module OperationalSemAbstr (ConstraintStore : ConstraintStoreSig).

Import ConstraintStore.

(* Partial state *) 
Inductive state' : Set :=
| Leaf : goal -> subst -> constraint_store -> nat -> state'
| Sum  : state' -> state' -> state'
| Prod : state' -> goal   -> state'.

(* Complete state *)
Inductive state : Set :=
(* end of evaluation *) | Stop  : state
(* a partial state   *) | State : state' -> state.

Inductive is_fv_of_state' : name -> state' -> Prop :=
| isfvst'Leaf  : forall x g s cs n  (X_FV_G : is_fv_of_goal x g),
                                    is_fv_of_state' x (Leaf g s cs n)
| isfvst'SumL  : forall x st'1 st'2 (X_FV : is_fv_of_state' x st'1),
                                    is_fv_of_state' x (Sum st'1 st'2)
| isfvst'SumR  : forall x st'1 st'2 (X_FV : is_fv_of_state' x st'2),
                                    is_fv_of_state' x (Sum st'1 st'2)
| isfvst'ProdL : forall x st' g     (X_FV : is_fv_of_state' x st'),
                                    is_fv_of_state' x (Prod st' g)
| isfvst'ProdR : forall x st' g     (X_FV : is_fv_of_goal x g),
                                    is_fv_of_state' x (Prod st' g).

Hint Constructors is_fv_of_state' : core.

Inductive is_fv_of_state : name -> state -> Prop :=
| isfvstC : forall x st' (X_FV_ST' : is_fv_of_state' x st'),
                         is_fv_of_state x (State st').

Hint Constructors is_fv_of_state : core.

Inductive is_counter_of_state' : nat -> state' -> Prop :=
| iscst'Leaf  : forall g s cs n,   is_counter_of_state' n (Leaf g s cs n)
| iscst'SumL  : forall n st'1 st'2 (ISC : is_counter_of_state' n st'1),
                                   is_counter_of_state' n (Sum st'1 st'2)
| iscst'SumR  : forall n st'1 st'2 (ISC : is_counter_of_state' n st'2),
                                   is_counter_of_state' n (Sum st'1 st'2)
| iscst'Prod  : forall n st' g     (ISC : is_counter_of_state' n st'),
                                   is_counter_of_state' n (Prod st' g).

Hint Constructors is_counter_of_state' : core.

Inductive well_formed_state' : state' -> Prop :=
| wfLeaf : forall g s cs frn
           (DOM_LT_COUNTER  : forall x (X_IN_DOM : in_subst_dom s x), x < frn)
           (VRAN_LT_COUNTER : forall x (X_IN_VRAN : in_subst_vran s x), x < frn)
           (FV_LT_COUNTER   : forall x (X_FV : is_fv_of_goal x g), x < frn)
           (DS_LT_COUNTER   : forall (f f' : repr_fun)
                                     (REQ_ff' : forall x, x < frn -> gt_eq (f x) (f' x)),
                                     [ s , f ] /\ [| s , cs , f |] <-> [ s , f' ] /\ [| s , cs , f' |])
           (NAR             : narrowing_subst s)
           (WF_CS           : wf_cs s cs),
           well_formed_state' (Leaf g s cs frn)
| wfSum  : forall st'1 st'2 (WF_L : well_formed_state' st'1)
                            (WF_R : well_formed_state' st'2),
                            well_formed_state' (Sum st'1 st'2)
| wfProd : forall st' g     (WF_L : well_formed_state' st')
                            (FV_LT_COUNTER : forall x frn (FRN_COUNTER : is_counter_of_state' frn st')
                                                          (X_FV : is_fv_of_goal x g),
                                                          x < frn),
                            well_formed_state' (Prod st' g).

Hint Constructors well_formed_state' : core.

Fixpoint first_nats (k : nat) : list nat :=
  match k with
  | 0   => []
  | S n => n :: first_nats n
  end.

Lemma first_nats_less (n k : nat) (H : In n (first_nats k)) : n < k.
Proof.
  induction k.
  { inversion H. }
  { inversion H. { omega. } { apply IHk in H0. omega. } }
Qed.

Definition initial_state
           (g   : goal)
           (k   : nat) :
           state' :=
           (Leaf g empty_subst init_cs k).

Lemma well_formed_initial_state
      (g   : goal)
      (k   : nat)
      (HC  : closed_goal_in_context (first_nats k) g) :
      well_formed_state' (initial_state g k).
Proof.
  constructor.
  { intros. good_inversion X_IN_DOM. good_inversion H. }
  { intros. good_inversion X_IN_VRAN. destruct H as [t0 [H0 _]]. good_inversion H0. }
  { red in HC. intros. apply first_nats_less; auto. }
  { intros. split; split.
    { apply empty_subst_ds. }
    { apply init_condition. }
    { apply empty_subst_ds. }
    { apply init_condition. } }
  { red. intros. red in H. destruct H as [y [t [C _]]].
    good_inversion C. }
  { apply wf_init_cs. }
Qed.


Inductive well_formed_state : state -> Prop :=
| wfEmpty    : well_formed_state Stop
| wfNonEmpty : forall st' (wfState : well_formed_state' st'),
                          well_formed_state (State st').

Hint Constructors well_formed_state : core.

(* Labels *)
Inductive label : Set :=
(* nothing                                       *) | Step   : label
(* answer: (subst, first free semantic variable) *) | Answer : subst -> constraint_store -> nat -> label.

(* Transitions *)
Inductive eval_step : state' -> label -> state -> Prop :=
| esFail         : forall           s cs       n, eval_step (Leaf Fail s cs n) Step Stop
| esCut          : forall           s cs       n, eval_step (Leaf Cut s cs n)  (Answer s cs n) Stop                             (* cuts are ignored in interliving search *)
| esUnifyFail    : forall t1 t2     s cs       n  (MGU : mgu (apply_subst s t1) (apply_subst s t2) None),
                                                  eval_step (Leaf (Unify t1 t2) s cs n) Step Stop
| esUnifyUpdFail : forall t1 t2     s cs d     n  (MGU : mgu (apply_subst s t1) (apply_subst s t2) (Some d))
                                                  (UPD_CS : upd_cs s cs d None),
                                                  eval_step (Leaf (Unify t1 t2) s cs n) Step Stop
| esUnifySuccess : forall t1 t2     s cs d cs' n  (MGU : mgu (apply_subst s t1) (apply_subst s t2) (Some d))
                                                  (UPD_CS : upd_cs s cs d (Some cs')),
                                                  eval_step (Leaf (Unify t1 t2) s cs n) (Answer (compose s d) cs' n) Stop
| esDisunifyFail : forall t1 t2     s cs       n  (ADD_C : add_constraint s cs t1 t2 None),
                                                  eval_step (Leaf (Disunify t1 t2) s cs n) Step Stop
| esDisunifySuccess : forall t1 t2     s cs cs' n  (ADD_C : add_constraint s cs t1 t2 (Some cs')),
                                                   eval_step (Leaf (Disunify t1 t2) s cs n) (Answer s cs' n) Stop
| esDisj         : forall g1 g2     s cs       n, eval_step (Leaf (Disj g1 g2) s cs n)   Step (State (Sum (Leaf g1 s cs n) (Leaf g2 s cs n)))
| esConj         : forall g1 g2     s cs       n, eval_step (Leaf (Conj g1 g2) s cs n)   Step (State (Prod (Leaf g1 s cs n) g2))
| esFresh        : forall fg        s cs       n, eval_step (Leaf (Fresh fg) s cs n)     Step (State (Leaf (fg n) s cs (S n)))
| esInvoke       : forall r arg     s cs       n, eval_step (Leaf (Invoke r arg) s cs n) Step (State (Leaf (proj1_sig (MiniKanrenSyntax.Prog r) arg) s cs n))
| esSumE         : forall st1 st2        l        (STEP_L : eval_step st1 l  Stop),
                                                  eval_step (Sum st1 st2) l (State st2)
| esSumNE        : forall st1 st1' st2   l        (STEP_L : eval_step st1 l (State st1')),
                                                  eval_step (Sum st1 st2) l (State (Sum st2 st1'))
| esProdSE       : forall st g                    (STEP_L : eval_step st Step Stop),
                                                  eval_step (Prod st g) Step Stop
| esProdAE       : forall st g s cs n             (STEP_L : eval_step st (Answer s cs n) Stop),
                                                  eval_step (Prod st g) Step (State (Leaf g s cs n))
| esProdSNE      : forall st g        st'         (STEP_L : eval_step st Step (State st')),
                                                  eval_step (Prod st g) Step (State (Prod st' g))
| esProdANE      : forall st g s cs n st'         (STEP_L : eval_step st (Answer s cs n) (State st')),
                                                  eval_step (Prod st g) Step (State (Sum (Leaf g s cs n) (Prod st' g))).

Hint Constructors eval_step : core.

Lemma counter_in_answer
      (st' : state')
      (s : subst)
      (cs : constraint_store)
      (n : nat)
      (st : state)
      (EV : eval_step st' (Answer s cs n) st) :
      is_counter_of_state' n st'.
Proof.
  remember (Answer s cs n). induction EV; good_inversion Heql; auto.
Qed.

Lemma counter_in_next_state
      (n : nat)
      (st' st'_next : state')
      (l : label)
      (EV : eval_step st' l (State st'_next))
      (ISC_NEXT :  is_counter_of_state' n st'_next) :
      exists n', n' <= n /\ is_counter_of_state' n' st'.
Proof.
  remember (State st'_next) as st.
  revert Heqst ISC_NEXT. revert st'_next.
  induction EV; intros; good_inversion Heqst.
  { exists n. split.
    { constructor. }
    { good_inversion ISC_NEXT; good_inversion ISC; auto. } }
  { exists n. split.
    { constructor. }
    { good_inversion ISC_NEXT; good_inversion ISC; auto. } }
  { good_inversion ISC_NEXT. exists n0. split.
    { repeat constructor. }
    { auto. } }
  { exists n. split.
    { constructor. }
    { good_inversion ISC_NEXT; auto. } }
  { exists n. split.
    { constructor. }
    { auto. } }
  { specialize (IHEV st1' eq_refl). good_inversion ISC_NEXT.
    { exists n. split.
      { constructor. }
      { auto. } }
    { apply IHEV in ISC. destruct ISC as [n' [LE ISC]].
      exists n'; auto. } }
  { good_inversion ISC_NEXT. exists n0.
    eapply counter_in_answer in EV. split; auto. }
  { specialize (IHEV st' eq_refl). good_inversion ISC_NEXT.
    apply IHEV in ISC. destruct ISC as [n' [LE ISC]].
    exists n'; auto. }
  { specialize (IHEV st' eq_refl). good_inversion ISC_NEXT.
    { good_inversion ISC. exists n0.
      eapply counter_in_answer in EV. split; auto. }
    { good_inversion ISC. apply IHEV in ISC0.
      destruct ISC0 as [n' [LE ISC]]. exists n'; auto. } }
Qed.

Lemma well_formed_subst_in_answer
      (st' : state')
      (s : subst)
      (cs : constraint_store)
      (n : nat)
      (st : state)
      (EV : eval_step st' (Answer s cs n) st)
      (WF : well_formed_state' st') :
      (forall x, in_subst_dom s x -> x < n) /\ (forall x, in_subst_vran s x -> x < n).
Proof.
  remember (Answer s cs n). induction EV; good_inversion Heql; good_inversion WF; auto.
  assert (FV_LT_N_1 : forall x, In x (fv_term (apply_subst s0 t1)) -> x < n).
  { clear MGU UPD_CS. intros. induction t1.
    { simpl in H. destruct (image s0 n0) eqn:eq; auto.
      apply VRAN_LT_COUNTER. red. eauto. }
    { good_inversion H. }
    { simpl in H. apply (set_union_elim name_eq_dec) in H. destruct H.
      { apply IHt1_1; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyL. simpl.
        apply set_union_intro. left. auto. }
      { apply IHt1_2; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyL. simpl.
        apply set_union_intro. right. auto. } } }
  assert (FV_LT_N_2 : forall x, In x (fv_term (apply_subst s0 t2)) -> x < n).
  { clear MGU UPD_CS. intros. induction t2.
    { simpl in H. destruct (image s0 n0) eqn:eq; auto.
      apply VRAN_LT_COUNTER. red. eauto. }
    { good_inversion H. }
    { simpl in H. apply (set_union_elim name_eq_dec) in H. destruct H.
      { apply IHt2_1; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyR. simpl.
        apply set_union_intro. left. auto. }
      { apply IHt2_2; auto. intros. apply FV_LT_COUNTER.
        good_inversion X_FV; auto. apply fvUnifyR. simpl.
        apply set_union_intro. right. auto. } } }
  specialize (mgu_dom _ _ _ MGU). intro S'_DOM.
  specialize (mgu_vran _ _ _ MGU). intro S'_VRAN.
  split.
  { intros. apply compose_dom in H. destruct H; auto.
    apply S'_DOM in H. destruct H; auto. }
  { intros. apply compose_vran in H. destruct H; auto.
    apply S'_VRAN in H. destruct H; auto. }
Qed.

Lemma well_formed_ds_in_answer
      (st' : state')
      (s : subst)
      (cs : constraint_store)
      (n : nat)
      (st : state)
      (EV : eval_step st' (Answer s cs n) st)
      (WF : well_formed_state' st')
      (f f' : repr_fun)
      (REQ_ff' : forall x, x < n -> gt_eq (f x) (f' x)) :
      [ s , f ] /\ [| s , cs , f |] <-> [ s , f' ] /\ [| s , cs , f' |].
Proof.
  assert (AND_IFF_SPLIT : forall A B C D, (A <-> C) -> (B <-> D) -> (A /\ B <-> C /\ D)).
  { intros. split; split; auto; destruct H1; destruct H0; destruct H; auto. }
  remember (Answer s cs n). induction EV; good_inversion Heql; good_inversion WF; auto; specialize (DS_LT_COUNTER f f' REQ_ff').
  { rewrite and_comm.
    eapply iff_trans. 2: apply and_comm.
    rewrite (upd_cs_success_condition _ _ _ _ WF_CS UPD_CS).
    rewrite (upd_cs_success_condition _ _ _ _ WF_CS UPD_CS).
    rewrite (denotational_sem_uni _ _ _ _ MGU f).
    rewrite (denotational_sem_uni _ _ _ _ MGU f').
    rewrite <- and_assoc. rewrite <- and_assoc.
    apply AND_IFF_SPLIT.
    { rewrite and_comm. rewrite DS_LT_COUNTER. apply and_comm. }
    { split; intros.
      { etransitivity. etransitivity.
        2: apply H.
        { apply apply_repr_fun_fv. intros. symmetry. apply REQ_ff'. auto. }
        { apply apply_repr_fun_fv. intros. apply REQ_ff'. auto. } }
      { etransitivity. etransitivity.
        2: apply H.
        { apply apply_repr_fun_fv. intros. apply REQ_ff'. auto. }
        { apply apply_repr_fun_fv. intros. symmetry. apply REQ_ff'. auto. } } } }
  { rewrite and_comm.
    eapply iff_trans. 2: apply and_comm.
    rewrite (add_constraint_success_condition _ _ _ _ _ WF_CS ADD_C).
    rewrite (add_constraint_success_condition _ _ _ _ _ WF_CS ADD_C).
    rewrite <- and_assoc. rewrite <- and_assoc.
    apply AND_IFF_SPLIT.
    { rewrite and_comm. rewrite DS_LT_COUNTER. apply and_comm. }
    { split; intros DSG; good_inversion DSG; constructor; intro C; apply DISUNI.
      { etransitivity. etransitivity.
        2: apply C.
        { apply apply_repr_fun_fv. intros. apply REQ_ff'. auto. }
        { apply apply_repr_fun_fv. intros. symmetry. apply REQ_ff'. auto. } }
      { etransitivity. etransitivity.
        2: apply C.
        { apply apply_repr_fun_fv. intros. symmetry. apply REQ_ff'. auto. }
        { apply apply_repr_fun_fv. intros. apply REQ_ff'. auto. } } } }
Qed.

Lemma narrowing_subst_in_answer
      (st' : state')
      (s : subst)
      (cs : constraint_store)
      (n : nat)
      (st : state)
      (EV : eval_step st' (Answer s cs n) st)
      (WF : well_formed_state' st') :
      narrowing_subst s.
Proof.
  remember (Answer s cs n). induction EV; good_inversion Heql; good_inversion WF; auto.
  apply compose_narrowing_extending; auto.
  { eapply mgu_is_narrowing; eauto. }
  { eapply mgu_is_extending; eauto. }
Qed.


Lemma wf_cs_in_answer
      (st' : state')
      (s : subst)
      (cs : constraint_store)
      (n : nat)
      (st : state)
      (EV : eval_step st' (Answer s cs n) st)
      (WF : well_formed_state' st') :
      wf_cs s cs.
Proof.
  remember (Answer s cs n). induction EV; good_inversion Heql; good_inversion WF; auto.
  { eapply upd_cs_wf_preservation; eauto.
    { eapply mgu_is_narrowing; eauto. }
    { eapply mgu_is_extending; eauto. } }
  { eapply add_constraint_wf_preservation; eauto. }
Qed.

Lemma well_formedness_preservation
      (st' : state')
      (l : label)
      (st : state)
      (EV : eval_step st' l st)
      (WF : well_formed_state' st') :
      well_formed_state st.
Proof.
  intros. induction EV; good_inversion WF; auto.
  { constructor. auto. }
  { constructor. constructor; auto.
    intros. good_inversion FRN_COUNTER. subst. auto. }
  { constructor. constructor; auto.
    1-2: intros; eapply lt_trans; eauto.
    intros. destruct (eq_nat_dec n x).
    { omega. }
    { apply Nat.lt_lt_succ_r. apply FV_LT_COUNTER. econstructor; eauto. } }
  { constructor. constructor; auto.
    specialize (proj2_sig (MiniKanrenSyntax.Prog r)). intro CC.
    simpl in CC. destruct CC as [CL _]. red in CL. red in CL. auto. }
  { specialize (IHEV WF_L).
    good_inversion IHEV. auto. }
  { constructor. constructor; auto.
    6: eapply wf_cs_in_answer; eauto.
    5: eapply narrowing_subst_in_answer; eauto.
    4: eapply well_formed_ds_in_answer; eauto.
    1-2: apply well_formed_subst_in_answer in EV; destruct EV; auto.
    intros. apply FV_LT_COUNTER; auto. eapply counter_in_answer; eauto. }
  { specialize (IHEV WF_L). good_inversion IHEV.
    constructor. constructor; auto. intros.
    eapply counter_in_next_state in EV; eauto.
    destruct EV as [frn' [LE ISC]]. eapply lt_le_trans.
    2: eauto.
    auto. }
  { specialize (IHEV WF_L). good_inversion IHEV.
    constructor. constructor.
    { constructor.
      6: eapply wf_cs_in_answer; eauto.
      5: eapply narrowing_subst_in_answer; eauto.
      4: eapply well_formed_ds_in_answer; eauto.
      1-2: apply well_formed_subst_in_answer in EV; destruct EV; auto.
      intros. apply FV_LT_COUNTER; auto.
      eapply counter_in_answer; eauto. }
    { constructor; auto. intros.
      eapply counter_in_next_state in EV; eauto.
      destruct EV as [frn' [Le ISC]]. eapply lt_le_trans.
      2: eauto.
      auto. } }
Qed.

Lemma eval_step_exists
      (st' : state') :
      {l : label & {st : state & eval_step st' l st}}.
Proof.
  induction st'.
  { destruct g.
    1-2,5-8: repeat eexists; econstructor.
    { assert ({r & mgu (apply_subst s t) (apply_subst s t0) r}).
      { apply mgu_exists. }
      destruct H. destruct x.
      { assert ({r & upd_cs s c s0 r}).
        { apply upd_cs_exists. }
        destruct H. destruct x.
        all: repeat eexists; eauto. }
      { repeat eexists; eauto. } }
    { assert ({r & add_constraint s c t t0 r}).
      { apply add_constraint_exists. }
      destruct H. destruct x.
      all: repeat eexists; eauto. } }
  { destruct IHst'1 as [l1 [st1 IH1]]. destruct st1.
    all: repeat eexists; eauto. }
  { destruct IHst' as [l [st IH]]. destruct st; destruct l.
    all: repeat eexists; eauto. }
Qed.

Lemma eval_step_unique
      (st' : state')
      (l1 l2 : label)
      (st1 st2 : state)
      (STEP_1 : eval_step st' l1 st1)
      (STEP_2 : eval_step st' l2 st2) :
      l1 = l2 /\ st1 = st2.
Proof.
  revert STEP_1 STEP_2. revert l1 l2 st1 st2. induction st'.
  { intros. destruct g; good_inversion STEP_1; good_inversion STEP_2; auto.
    { assert (C : None = Some d).
      { eapply mgu_unique; eassumption. }
      inversion C. }
    { assert (EQ : Some d = Some d0).
      { eapply mgu_unique; eassumption. }
      good_inversion EQ.
      assert (C : None = Some cs').
      { eapply upd_cs_unique; eassumption. }
      inversion C. }
    { assert (C : None = Some d).
      { eapply mgu_unique; eassumption. }
      inversion C. }
    { assert (EQ : Some d = Some d0).
      { eapply mgu_unique; eassumption. }
      good_inversion EQ.
      assert (C : None = Some cs').
      { eapply upd_cs_unique; eassumption. }
      inversion C. }
    { assert (EQ : Some d = Some d0).
      { eapply mgu_unique; eassumption. }
      good_inversion EQ.
      assert (C : Some cs' = Some cs'0).
      { eapply upd_cs_unique; eassumption. }
      inversion C. auto. }
    { assert (C : None = Some cs').
      { eapply add_constraint_unique; eassumption. }
      inversion C. }
    { assert (C : None = Some cs').
      { eapply add_constraint_unique; eassumption. }
      inversion C. }
    { assert (C : Some cs' = Some cs'0).
      { eapply add_constraint_unique; eassumption. }
      inversion C. auto. } }
  { intros. good_inversion STEP_1; good_inversion STEP_2;
    specialize (IHst'1 _ _ _ _ STEP_L STEP_L0); inversion IHst'1;
    inversion H0; subst; auto. }
  { intros. good_inversion STEP_1; good_inversion STEP_2;
    specialize (IHst' _ _ _ _ STEP_L STEP_L0); inversion IHst'; subst;
    inversion H; inversion H0; auto. }
Qed.

(* Traces *)
Definition trace : Set := @stream label.

CoInductive op_sem : state -> trace -> Prop :=
| osStop : op_sem Stop Nil
| osState : forall st' l st t (EV: eval_step st' l st)
                              (OP: op_sem st t),
                              op_sem (State st') (Cons l t).

Hint Constructors op_sem : core.

CoFixpoint trace_from (st : state) : trace :=
  match st with
  | Stop => Nil
  | State st' =>
    match eval_step_exists st' with
    | existT _ l (existT _ st'' ev_st'_st'') =>
      Cons l (trace_from st'')
    end
  end.

Lemma trace_from_correct
      (st : state) :
      op_sem st (trace_from st).
Proof.
  revert st. cofix CIH. destruct st.
  { rewrite helper_eq. simpl. constructor. }
  { rewrite helper_eq. simpl. destruct (eval_step_exists s).
    destruct s0. econstructor; eauto. }
Qed.

Lemma op_sem_exists
      (st : state) :
      {t : trace & op_sem st t}.
Proof.
  eexists. eapply trace_from_correct.
Qed.

Lemma op_sem_unique
      (st : state)
      (t1 t2 : trace)
      (OP_1 : op_sem st t1)
      (OP_2 : op_sem st t2) :
      equal_streams t1 t2.
Proof.
  revert OP_1 OP_2. revert t1 t2 st.
  cofix CIH. intros. inversion OP_1; inversion OP_2;
  rewrite <- H1 in H; inversion H.
  { constructor. }
  { subst.
    specialize (eval_step_unique _ _ _ _ _ EV EV0).
    intros [EQL EQST]. constructor.
    { auto. }
    { subst. eapply CIH; eauto. } }
Qed.

Definition in_denotational_analog (t : trace) (f : repr_fun) : Prop :=
  exists (s : subst) (cs : constraint_store) (n : nat),
    in_stream (Answer s cs n) t /\ [ s ,  f ] /\ [| s , cs , f |].

Notation "{| t , f |}" := (in_denotational_analog t f).

Inductive in_denotational_sem_state' : state' -> repr_fun -> Prop :=
| dsst'Leaf : forall g s cs n f (DSG  : [| g , f |])
                                (DSS  : [ s , f ])
                                (DSCS : [| s , cs , f |]),
                                in_denotational_sem_state' (Leaf g s cs n) f
| dsst'SumL : forall st1' st2' f (DSST' : in_denotational_sem_state' st1' f),
                                 in_denotational_sem_state' (Sum st1' st2') f
| dsst'SumR : forall st1' st2' f (DSST' : in_denotational_sem_state' st2' f),
                                 in_denotational_sem_state' (Sum st1' st2') f
| dsst'Prod : forall st' g f (DSG : [| g , f |])
                             (DSST' : in_denotational_sem_state' st' f),
                             in_denotational_sem_state' (Prod st' g) f.

Hint Constructors in_denotational_sem_state' : core.

Inductive in_denotational_sem_state : state -> repr_fun -> Prop :=
| dsstState : forall st' f (DSST' : in_denotational_sem_state' st' f),
                           in_denotational_sem_state (State st') f.

Hint Constructors in_denotational_sem_state : core.

Lemma counter_in_trace
      (g : goal)
      (s sr : subst)
      (cs : constraint_store)
      (csr : constraint_store)
      (n nr : nat)
      (tr : trace)
      (OP : op_sem (State (Leaf g s cs n)) tr)
      (HIn : in_stream (Answer sr csr nr) tr) :
      n <= nr.
Proof.
  remember (Leaf g s cs n) as st'.
  assert (CNT_GE : forall n', is_counter_of_state' n' st' -> n <= n').
  { intros. subst. good_inversion H. auto. }
  clear Heqst'. revert CNT_GE OP. revert n st'.
  remember (Answer sr csr nr). induction HIn; intros; subst.
  { good_inversion OP. apply counter_in_answer in EV. auto. }
  { good_inversion OP. destruct st.
    { good_inversion OP0. good_inversion HIn. }
    { apply IHHIn with s0; auto. intros.
      specialize (counter_in_next_state _ _ _ _ EV H). intros.
      destruct H0. destruct H0. apply CNT_GE in H1.
      eapply le_trans; eauto. } }
Qed.

Lemma well_formed_subst_in_trace
      (st : state)
      (WF : well_formed_state st)
      (t : trace)
      (OP : op_sem st t)
      (s : subst)
      (cs : constraint_store)
      (n : nat)
      (IS_ANS: in_stream (Answer s cs n) t) :
      (forall x, in_subst_dom s x -> x < n) /\ (forall x, in_subst_vran s x -> x < n).
Proof.
  remember (Answer s cs n). revert WF OP. revert st.
  induction IS_ANS; intros.
  { good_inversion OP. good_inversion WF.
    eapply well_formed_subst_in_answer; eauto. }
  { good_inversion OP. good_inversion WF.
    apply IHIS_ANS with st0; auto.
    eapply well_formedness_preservation; eauto. }
Qed.

Lemma well_formed_ds_in_trace
      (st : state)
      (WF : well_formed_state st)
      (t : trace)
      (OP : op_sem st t)
      (s : subst)
      (cs : constraint_store)
      (n : nat)
      (IS_ANS: in_stream (Answer s cs n) t)
      (f f' : repr_fun)
      (REQ_ff' : forall x, x < n -> gt_eq (f x) (f' x)) :
      [ s , f ] /\ [| s , cs , f |] <-> [ s , f' ] /\ [| s , cs , f' |].
Proof.
  remember (Answer s cs n). revert WF OP. revert st.
  induction IS_ANS; intros.
  { good_inversion OP. good_inversion WF.
    eapply well_formed_ds_in_answer; eauto. }
  { good_inversion OP. good_inversion WF.
    apply IHIS_ANS with st0; auto.
    eapply well_formedness_preservation; eauto. }
Qed.

Lemma narrowing_subst_in_trace
      (st : state)
      (WF : well_formed_state st)
      (t : trace)
      (OP : op_sem st t)
      (s : subst)
      (cs : constraint_store)
      (n : nat)
      (IS_ANS: in_stream (Answer s cs n) t) :
      narrowing_subst s.
Proof.
  remember (Answer s cs n). revert WF OP. revert st.
  induction IS_ANS; intros.
  { good_inversion OP. good_inversion WF.
    eapply narrowing_subst_in_answer; eauto. }
  { good_inversion OP. good_inversion WF.
    apply IHIS_ANS with st0; auto.
    eapply well_formedness_preservation; eauto. }
Qed.

Lemma wf_cs_in_trace
      (st : state)
      (WF : well_formed_state st)
      (t : trace)
      (OP : op_sem st t)
      (s : subst)
      (cs : constraint_store)
      (n : nat)
      (IS_ANS: in_stream (Answer s cs n) t) :
      wf_cs s cs.
Proof.
  remember (Answer s cs n). revert WF OP. revert st.
  induction IS_ANS; intros.
  { good_inversion OP. good_inversion WF.
    eapply wf_cs_in_answer; eauto. }
  { good_inversion OP. good_inversion WF.
    apply IHIS_ANS with st0; auto.
    eapply well_formedness_preservation; eauto. }
Qed.


Lemma sum_op_sem
      (st'1 st'2 : state')
      (t1 t2 t : trace)
      (OP_1 : op_sem (State st'1) t1)
      (OP_2 : op_sem (State st'2) t2)
      (OP_12 : op_sem (State (Sum st'1 st'2)) t) :
      interleave t1 t2 t.
Proof.
  revert OP_1 OP_2 OP_12. revert t1 t2 t st'1 st'2.
  cofix CIH. intros. inversion OP_1. subst. inversion OP_12. subst.
  inversion EV0; subst; specialize (eval_step_unique _ _ _ _ _ EV STEP_L);
  intros [EQL EQST]; subst; constructor.
  { inversion OP. subst. specialize (op_sem_unique _ _ _ OP_2 OP0).
    intro EQS. inversion EQS; subst.
    { constructor. constructor. }
    { constructor. constructor. auto. } }
  { eapply CIH; eassumption. }
Qed.

Lemma prod_op_sem_in
      (st' : state')
      (g : goal)
      (s : subst)
      (cs : constraint_store)
      (n : nat)
      (t1 t2 t : trace)
      (r : label)
      (OP : op_sem (State (Prod st' g)) t)
      (OP1 : op_sem (State st') t1)
      (OP2 : op_sem (State (Leaf g s cs n)) t2)
      (IN_1 : in_stream (Answer s cs n) t1)
      (IN_2 : in_stream r t2) :
      in_stream r t.
Proof.
  revert OP OP1. revert t st'. remember (Answer s cs n) as r1.
  induction IN_1; intros; subst.
  { good_inversion OP1. good_inversion OP.
    good_inversion EV0; specialize (eval_step_unique _ _ _ _ _ EV STEP_L);
    intro eqs; destruct eqs; subst; good_inversion H.
    { constructor. specialize (op_sem_unique _ _ _ OP2 OP1).
      intros. eapply in_equal_streams; eauto. }
    { constructor. specialize (op_sem_exists (State (Leaf g s0 cs0 n0))).
      intro H. destruct H as [t3 OP3].
      specialize (op_sem_exists (State (Prod st'0 g))).
      intro H. destruct H as [t4 OP4].
      specialize (sum_op_sem _ _ _ _ _ OP3 OP4 OP1).
      intro interH. eapply interleave_in in interH.
      eapply interH. left. specialize (op_sem_unique _ _ _ OP2 OP3).
      intros. eapply in_equal_streams; eauto. } }
  { specialize (IHIN_1 eq_refl).
    good_inversion OP1. good_inversion OP.
    good_inversion EV0; specialize (eval_step_unique _ _ _ _ _ EV STEP_L);
    intro eqs; destruct eqs; subst.
    1-2: good_inversion OP0; good_inversion IN_1.
    { constructor. eapply IHIN_1; eauto. }
    { constructor. specialize (op_sem_exists (State (Leaf g s0 cs0 n0))).
      intro H. destruct H as [t3 OP3].
      specialize (op_sem_exists (State (Prod st'0 g))).
      intro H. destruct H as [t4 OP4].
      specialize (sum_op_sem _ _ _ _ _ OP3 OP4 OP1).
      intro interH. eapply interleave_in in interH.
      eapply interH. right. eapply IHIN_1; eauto. } }
Qed.

End OperationalSemAbstr.
