Section Stream.

  Context {A : Set}.

  CoInductive stream : Set :=
  | Nil : stream
  | Cons : A -> stream -> stream.

  Definition helper (s : stream) : stream :=
    match s with
    | Nil => Nil
    | Cons h t => Cons h t
    end.

  Lemma helper_eq
        (s : stream) :
        s = helper s.
  Proof. destruct s; reflexivity. Qed.

  CoInductive equal_streams : stream -> stream -> Prop :=
  | eqsNil  :                    equal_streams Nil Nil
  | eqsCons : forall h1 h2 t1 t2 (EQH : h1 = h2)
                                 (EQT : equal_streams t1 t2),
                                 equal_streams (Cons h1 t1) (Cons h2 t2).

  Lemma equal_streams_symmetry
        (s1 s2 : stream)
        (EQS : equal_streams s1 s2) :
        equal_streams s2 s1.
  Proof.
    revert EQS. revert s1 s2.
    cofix CIH. intros. inversion EQS; subst.
    { constructor. }
    { constructor. reflexivity. auto. }
  Qed.

  Inductive in_stream : A -> stream -> Prop :=
  | inHead : forall x t,  in_stream x (Cons x t)
  | inTail : forall x h t (IN : in_stream x t),
                          in_stream x (Cons h t).

  Hint Constructors in_stream : core.

  Lemma in_equal_streams
        (s1 s2 : stream)
        (EQS : equal_streams s1 s2)
        (x : A)
        (X_IN : in_stream x s1) :
        in_stream x s2.
  Proof.
    revert EQS. revert s2.
    induction X_IN; intros; inversion_clear EQS; subst.
    { constructor. }
    { constructor. eapply IHX_IN. assumption. }
  Qed.

  Inductive finite : stream -> Prop :=
  | fNil  :            finite Nil
  | fCons : forall h t (FIN : finite t),
                       finite (Cons h t).

  Hint Constructors finite : core.

  CoInductive interleave : stream -> stream -> stream -> Prop :=
  | interNil  : forall s s'     (EQS : equal_streams s s'),
                                interleave Nil s s'
  | interCons : forall h t s rs (INTER : interleave s t rs),
                                interleave (Cons h t) s (Cons h rs).

  Lemma interleave_in_1
        (s1 s2 s : stream)
        (INTER : interleave s1 s2 s)
        (x : A)
        (X_IN : in_stream x s) :
        in_stream x s1 \/ in_stream x s2.
  Proof.
    revert INTER. revert s1 s2. induction X_IN; intros.
    { inversion INTER.
      { right. inversion EQS. subst. constructor. }
      { left. constructor. } }
    { inversion INTER; subst.
      { right. inversion EQS; subst. constructor.
        apply equal_streams_symmetry in EQT.
        eapply in_equal_streams; eauto. }
      { specialize (IHX_IN _ _ INTER0). destruct IHX_IN.
        { auto. }
        { left. constructor. auto. } } }
  Qed.

  Lemma interleave_in_2
        (s1 s2 s : stream)
        (INTER : interleave s1 s2 s)
        (x : A)
        (X_IN_12 : in_stream x s1 \/ in_stream x s2) :
        in_stream x s.
  Proof.
    destruct X_IN_12.
    { revert INTER. revert s2 s. induction H.
      { intros. inversion_clear INTER; subst. constructor. }
      { intros. inversion_clear INTER; subst. constructor.
        inversion_clear INTER0; subst.
        { eapply in_equal_streams; eauto. }
        { constructor. eauto. } } }
    { revert INTER. revert s1 s. induction H.
      { intros. inversion INTER; subst.
        { eapply in_equal_streams; eauto. }
        { constructor. inversion INTER0; subst. auto. } }
      { intros. inversion INTER; subst.
        { eapply in_equal_streams; eauto. }
        { inversion INTER0; subst. constructor. constructor. eapply IHin_stream. eauto. } } }
  Qed.

  Lemma interleave_in
        (s1 s2 s : stream)
        (INTER : interleave s1 s2 s)
        (x : A) :
        in_stream x s <-> in_stream x s1 \/ in_stream x s2.
  Proof.
    intros. split.
    { apply interleave_in_1. auto. }
    { apply interleave_in_2. auto. }
  Qed.

  Lemma equal_streams_finite
        (s1 s2 : stream)
        (EQS : equal_streams s1 s2)
        (FIN_1 : finite s1) :
        finite s2.
  Proof.
    revert EQS. revert s2.
    induction FIN_1; intros; inversion EQS; subst; auto.
  Qed.

  Lemma interleave_finite_1
        (s s1 s2 : stream)
        (INTER : interleave s1 s2 s)
        (FIN : finite s) :
        finite s1 /\ finite s2.
  Proof.
    revert INTER. revert s1 s2. induction FIN.
    { intros. inversion INTER; subst. inversion EQS. auto. }
    { intros. inversion INTER; subst.
      { inversion EQS; subst. split; auto. constructor.
        apply equal_streams_symmetry in EQT. eapply equal_streams_finite; eauto. }
      { apply IHFIN in INTER0. destruct INTER0. auto. } }
  Qed.

  Lemma interleave_finite_2
        (s s1 s2 : stream)
        (INTER : interleave s1 s2 s)
        (FIN_1 : finite s1)
        (FIN_2 : finite s2) :
        finite s.
  Proof.
    revert INTER FIN_2. revert s s2. induction FIN_1.
    { intros. inversion INTER. eapply equal_streams_finite; eauto. }
    { intros. inversion INTER; subst. constructor. inversion INTER0; subst.
      { eapply equal_streams_finite; eauto. }
      { inversion FIN_2; subst. constructor. eapply IHFIN_1; eauto. } }
  Qed.

  Lemma interleave_finite
        (s1 s2 s : stream)
        (INTER : interleave s1 s2 s) :
        finite s <-> finite s1 /\ finite s2.
  Proof.
    intros. split.
    { intro. eapply interleave_finite_1; eauto. }
    { intro. destruct H. eapply interleave_finite_2; eauto. }
  Qed.

End Stream.

Section Test.

  CoFixpoint nats (n : nat) : stream := Cons n (nats (S n)).

  Definition true_false : stream := Cons true (Cons false Nil).

  Lemma true_false_fin : finite true_false.
  Proof.
    repeat constructor.
  Qed.

  Lemma nats_not_fin
        (n : nat) :
        ~ finite (nats n).
  Proof.
    intro C. remember (nats n).
    revert Heqs. revert n.
    induction C.
    { intros. rewrite helper_eq in Heqs. simpl in Heqs. inversion Heqs. }
    { intros. apply IHC with (S n). rewrite helper_eq in Heqs. simpl in Heqs.
      inversion Heqs. reflexivity. }
  Qed.

  Lemma nats_contain_all_nats
        (n : nat) :
        in_stream n (nats 0).
  Proof.
    induction n.
    { rewrite helper_eq. constructor. }
    { remember (nats 0). remember 0. clear Heqn0.
      revert Heqs. revert n0. induction IHn.
      { intros. rewrite helper_eq in Heqs. inversion Heqs.
        constructor. rewrite helper_eq. constructor. }
      { intros. constructor. rewrite helper_eq in Heqs.
        inversion Heqs; subst. eapply IHIHn. reflexivity. } }
  Qed.

End Test.
