Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Extraction.

Require Import Unification.
Require Import Streams.
Require Import LanguageSLD.
Require Import DenotationalSemSLD.


(************************* States *************************)

Inductive cutting_mark : Set :=
| StopCutting : cutting_mark
| KeepCutting : cutting_mark.

Inductive nt_state : Set :=
| Leaf : goal -> subst -> nat -> nt_state
| Sum  : cutting_mark -> nt_state -> nt_state -> nt_state
| Prod : nt_state -> goal   -> nt_state.

Inductive state : Set :=
| Stop  : state
| NTState : nt_state -> state.

Inductive is_fv_of_nt_state : name -> nt_state -> Prop :=
| isfvnstLeaf  : forall x g s n     (X_FV_G : is_fv_of_goal x g),
                                    is_fv_of_nt_state x (Leaf g s n)
| isfvnstSumL  : forall x m nst1 nst2 (X_FV : is_fv_of_nt_state x nst1),
                                    is_fv_of_nt_state x (Sum m nst1 nst2)
| isfvnstSumR  : forall x m nst1 nst2 (X_FV : is_fv_of_nt_state x nst2),
                                    is_fv_of_nt_state x (Sum m nst1 nst2)
| isfvnstProdL : forall x nst g     (X_FV : is_fv_of_nt_state x nst),
                                    is_fv_of_nt_state x (Prod nst g)
| isfvnstProdR : forall x nst g     (X_FV : is_fv_of_goal x g),
                                    is_fv_of_nt_state x (Prod nst g).

Hint Constructors is_fv_of_nt_state : core.

Inductive is_fv_of_state : name -> state -> Prop :=
| isfvstC : forall x nst (X_FV_NT_ST : is_fv_of_nt_state x nst),
                         is_fv_of_state x (NTState nst).

Hint Constructors is_fv_of_state : core.

Inductive is_counter_of_nt_state : nat -> nt_state -> Prop :=
| iscnstLeaf  : forall g s n,      is_counter_of_nt_state n (Leaf g s n)
| iscnstSumL  : forall n m nst1 nst2 (ISC : is_counter_of_nt_state n nst1),
                                   is_counter_of_nt_state n (Sum m nst1 nst2)
| iscnstSumR  : forall n m nst1 nst2 (ISC : is_counter_of_nt_state n nst2),
                                   is_counter_of_nt_state n (Sum m nst1 nst2)
| iscnstProd  : forall n nst g     (ISC : is_counter_of_nt_state n nst),
                                   is_counter_of_nt_state n (Prod nst g).

Hint Constructors is_counter_of_nt_state : core.

Inductive well_formed_nt_state : nt_state -> Prop :=
| wfLeaf : forall g s frn
           (DOM_LT_COUNTER  : forall x (X_IN_DOM : in_subst_dom s x), x < frn)
           (VRAN_LT_COUNTER : forall x (X_IN_VRAN : in_subst_vran s x), x < frn)
           (FV_LT_COUNTER   : forall x (X_FV : is_fv_of_goal x g), x < frn),
           well_formed_nt_state (Leaf g s frn)
| wfSum  : forall m nst1 nst2 (WF_L : well_formed_nt_state nst1)
                            (WF_R : well_formed_nt_state nst2),
                            well_formed_nt_state (Sum m nst1 nst2)
| wfProd : forall nst g     (WF_L : well_formed_nt_state nst)
                            (FV_LT_COUNTER : forall x frn (FRN_COUNTER : is_counter_of_nt_state frn nst)
                                                          (X_FV : is_fv_of_goal x g),
                                                          x < frn),
                            well_formed_nt_state (Prod nst g).

Hint Constructors well_formed_nt_state : core.

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

Lemma well_formed_initial_state
      (g   : goal)
      (k   : nat)
      (HC  : closed_goal_in_context (first_nats k) g) :
      well_formed_nt_state (Leaf g empty_subst k).
Proof.
  constructor.
  { intros. good_inversion X_IN_DOM. good_inversion H. }
  { intros. good_inversion X_IN_VRAN. destruct H as [t0 [H0 _]]. good_inversion H0. }
  { red in HC. intros. apply first_nats_less; auto. }
Qed.


Inductive well_formed_state : state -> Prop :=
| wfTerminal    : well_formed_state Stop
| wfNonTerminal : forall nst (wfState : well_formed_nt_state nst),
                             well_formed_state (NTState nst).

Hint Constructors well_formed_state : core.



(************************** LTS ***************************)
(* Labels *)
Inductive label : Set :=
| Step   : label
| Answer : subst -> nat -> label.

(* Cutting signal *)
Inductive cut_signal : Set :=
| NoCutting  : cut_signal
| YesCutting : cut_signal.

(* Transitions *)
Inductive eval_step : nt_state -> label -> cut_signal -> state -> Prop :=
| esFail         : forall s n, eval_step (Leaf Fail s n) Step NoCutting Stop
| esCut          : forall s n, eval_step (Leaf Cut s n) (Answer s n) YesCutting Stop
| esUnifyFail    : forall t1 t2 s   n (MGU : mgu (apply_subst s t1) (apply_subst s t2) None),
                                      eval_step (Leaf (Unify t1 t2) s n) Step NoCutting Stop
| esUnifySuccess : forall t1 t2 s d n (MGU : mgu (apply_subst s t1) (apply_subst s t2) (Some d)),
                                      eval_step (Leaf (Unify t1 t2) s n) (Answer (compose s d) n) NoCutting Stop
| esDisj         : forall g1 g2 s n, eval_step (Leaf (Disj g1 g2) s n)   Step NoCutting (NTState (Sum StopCutting (Leaf g1 s n) (Leaf g2 s n)))
| esConj         : forall g1 g2 s n, eval_step (Leaf (Conj g1 g2) s n)   Step NoCutting (NTState (Prod (Leaf g1 s n) g2))
| esFresh        : forall fg    s n, eval_step (Leaf (Fresh fg) s n)     Step NoCutting (NTState (Leaf (fg n) s (S n)))
| esInvoke       : forall r arg s n, eval_step (Leaf (Invoke r arg) s n) Step NoCutting (NTState (Leaf (proj1_sig (LanguageSLD.Prog r) arg) s n))
| esSumE         : forall m nst1       nst2 l (STEP_L : eval_step nst1 l NoCutting Stop),
                                              eval_step (Sum m nst1 nst2) l NoCutting (NTState nst2)
| esSumECS       : forall nst1         nst2 l (STEP_L : eval_step nst1 l YesCutting Stop),
                                              eval_step (Sum StopCutting nst1 nst2) l NoCutting Stop
| esSumECK       : forall nst1         nst2 l (STEP_L : eval_step nst1 l YesCutting Stop),
                                              eval_step (Sum KeepCutting nst1 nst2) l YesCutting Stop
| esSumNE        : forall m nst1 nst1' nst2 l (STEP_L : eval_step nst1 l NoCutting (NTState nst1')),
                                              eval_step (Sum m nst1 nst2) l NoCutting (NTState (Sum m nst1' nst2))
| esSumNECS      : forall nst1 nst1' nst2   l (STEP_L : eval_step nst1 l YesCutting (NTState nst1')),
                                              eval_step (Sum StopCutting nst1 nst2) l NoCutting (NTState nst1')
| esSumNECK      : forall nst1 nst1' nst2   l (STEP_L : eval_step nst1 l YesCutting (NTState nst1')),
                                              eval_step (Sum KeepCutting nst1 nst2) l YesCutting (NTState nst1')
| esProdSE       : forall nst g     cs      (STEP_L : eval_step nst Step cs Stop),
                                            eval_step (Prod nst g) Step cs Stop
| esProdAE       : forall nst g s n cs      (STEP_L : eval_step nst (Answer s n) cs Stop),
                                            eval_step (Prod nst g) Step cs (NTState (Leaf g s n))
| esProdSNE      : forall nst g     cs nst' (STEP_L : eval_step nst Step cs (NTState nst')),
                                            eval_step (Prod nst g) Step cs (NTState (Prod nst' g))
| esProdANE      : forall nst g s n cs nst' (STEP_L : eval_step nst (Answer s n) cs (NTState nst')),
                                            eval_step (Prod nst g) Step cs (NTState (Sum KeepCutting (Leaf g s n) (Prod nst' g))).

Hint Constructors eval_step : core.

Lemma counter_in_answer
      (nst : nt_state)
      (s : subst)
      (n : nat)
      (cs : cut_signal)
      (st : state)
      (EV : eval_step nst (Answer s n) cs st) :
      is_counter_of_nt_state n nst.
Proof.
  remember (Answer s n). induction EV; good_inversion Heql; auto.
Qed.

Lemma counter_in_next_state
      (n : nat)
      (nst nst_next : nt_state)
      (l : label)
      (cs : cut_signal)
      (EV : eval_step nst l cs (NTState nst_next))
      (ISC_NEXT :  is_counter_of_nt_state n nst_next) :
      exists n', n' <= n /\ is_counter_of_nt_state n' nst.
Proof.
  remember (NTState nst_next) as st.
  revert Heqst ISC_NEXT. revert nst_next.
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
  { specialize (IHEV nst1' eq_refl). good_inversion ISC_NEXT.
    { apply IHEV in ISC. destruct ISC as [n' [LE ISC]].
      exists n'; auto. } 
    { exists n. split.
      { constructor. }
      { auto. } } }
  { destruct (IHEV nst_next eq_refl ISC_NEXT) as [n' [LE ISC]].
    exists n'; auto. }
  { destruct (IHEV nst_next eq_refl ISC_NEXT) as [n' [LE ISC]].
    exists n'; auto. }
  { good_inversion ISC_NEXT. exists n0.
    eapply counter_in_answer in EV. split; auto. }
  { specialize (IHEV nst' eq_refl). good_inversion ISC_NEXT.
    apply IHEV in ISC. destruct ISC as [n' [LE ISC]].
    exists n'; auto. }
  { specialize (IHEV nst' eq_refl). good_inversion ISC_NEXT.
    { good_inversion ISC. exists n0.
      eapply counter_in_answer in EV. split; auto. }
    { good_inversion ISC. apply IHEV in ISC0.
      destruct ISC0 as [n' [LE ISC]]. exists n'; auto. } }
  
Qed.

Lemma well_formed_subst_in_answer
      (nst : nt_state)
      (s : subst)
      (n : nat)
      (cs : cut_signal)
      (st : state)
      (EV : eval_step nst (Answer s n) cs st)
      (WF : well_formed_nt_state nst) :
      (forall x, in_subst_dom s x -> x < n) /\ (forall x, in_subst_vran s x -> x < n).
Proof.
  remember (Answer s n). induction EV; good_inversion Heql; good_inversion WF; auto.
  assert (FV_LT_N_1 : forall x, In x (fv_term (apply_subst s0 t1)) -> x < n).
  { clear MGU. clear d. intros. induction t1.
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
  { clear MGU. clear d. intros. induction t2.
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

Lemma well_formedness_preservation
      (nst : nt_state)
      (l : label)
      (cs : cut_signal)
      (st : state)
      (EV : eval_step nst l cs st)
      (WF : well_formed_nt_state nst) :
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
    specialize (proj2_sig (LanguageSLD.Prog r)). intro CC.
    simpl in CC. destruct CC as [CL _]. red in CL. red in CL. auto. }
  { specialize (IHEV WF_L).
    good_inversion IHEV. auto. }
  { constructor. constructor; auto.
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
      (nst : nt_state) :
      {l : label & {cs : cut_signal & {st : state & eval_step nst l cs st}}}.
Proof.
  induction nst.
  { destruct g.
    1-2,4-7: repeat eexists; econstructor.
    { assert ({r & mgu (apply_subst s t) (apply_subst s t0) r}).
      { apply mgu_result_exists. }
      destruct H. destruct x.
      { repeat eexists; eauto. }
      { repeat eexists; eauto. } } }
  { destruct IHnst1 as [l1 [cs [st1 IH1]]].
    destruct st1; destruct cs; destruct c.
    all: repeat eexists; eauto. }
  { destruct IHnst as [l [cs [st IH]]]. destruct st; destruct l.
    all: repeat eexists; eauto. }
Defined.

Lemma eval_step_unique
      (nst : nt_state)
      (l1 l2 : label)
      (cs1 cs2 : cut_signal)
      (st1 st2 : state)
      (STEP_1 : eval_step nst l1 cs1 st1)
      (STEP_2 : eval_step nst l2 cs2 st2) :
      l1 = l2 /\ cs1 = cs2 /\ st1 = st2.
Proof.
  revert STEP_1 STEP_2. revert l1 l2 cs1 cs2 st1 st2. induction nst.
  { intros. destruct g; good_inversion STEP_1; good_inversion STEP_2; auto.
    { assert (C : None = Some d).
      { eapply mgu_result_unique; eassumption. }
      inversion C. }
    { assert (C : None = Some d).
      { eapply mgu_result_unique; eassumption. }
      inversion C. }
    { assert (EQ : Some d = Some d0).
      { eapply mgu_result_unique; eassumption. }
      good_inversion EQ. auto. } }
  { intros. good_inversion STEP_1; good_inversion STEP_2;
    destruct (IHnst1 _ _ _ _ _ _ STEP_L STEP_L0) as [EQL [EQCS EQST]];
    inversion EQCS; inversion EQST; subst; auto. }
  { intros. good_inversion STEP_1; good_inversion STEP_2;
    destruct (IHnst _ _ _ _ _ _ STEP_L STEP_L0)as [EQL [EQCS EQST]];
    inversion EQL; inversion EQCS; inversion EQST; auto. }
Qed.



(***************** Operational Semantics ******************)

Definition trace : Set := @stream label.

CoInductive op_sem : state -> trace -> Prop :=
| osStop : op_sem Stop Nil
| osNTState : forall nst l cs st t (EV: eval_step nst l cs st)
                                   (OP: op_sem st t),
                                   op_sem (NTState nst) (Cons l t).

Hint Constructors op_sem : core.

CoFixpoint trace_from (st : state) : trace :=
  match st with
  | Stop => Nil
  | NTState nst =>
    match eval_step_exists nst with
    | existT _ l (existT _ _ (existT _ nst' ev_nst_nst')) =>
      Cons l (trace_from nst')
    end
  end.

Lemma trace_from_correct
      (st : state) :
      op_sem st (trace_from st).
Proof.
  revert st. cofix CIH. destruct st.
  { rewrite helper_eq. simpl. constructor. }
  { rewrite helper_eq. simpl.
    destruct (eval_step_exists n) as [l [cs [st EV]]].
    econstructor; eauto. }
Qed.

Lemma op_sem_exists
      (st : state) :
      {t : trace & op_sem st t}.
Proof.
  eexists. eapply trace_from_correct.
Defined.

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
    destruct (eval_step_unique _ _ _ _ _ _ _ EV EV0) as [EQL [EQCS EQST]].
    constructor.
    { auto. }
    { subst. eapply CIH; eauto. } }
Qed.

Definition in_denotational_analog (t : trace) (f : repr_fun) : Prop :=
  exists (s : subst) (n : nat),
    in_stream (Answer s n) t /\ [ s ,  f ].

Notation "{| t , f |}" := (in_denotational_analog t f).

Extraction Language Haskell.

Extraction "extracted/sld_interpreter.hs" op_sem_exists.
