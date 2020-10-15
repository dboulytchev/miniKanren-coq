Require Import List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Coq.Program.Equality.
Require Import Omega.
Require Import Extraction.

Require Import Unification.
Require Import Streams.
Require Import Language.
Require Import DenotationalSem.
Require Import OperationalSem.

(******************************** States ****************************)

(* Non-terminal state *)
Inductive nt_state : Set :=
    Leaf : forall (theta : subst) (i : nat) (r : list (name * term)), nt_state
  | Sum  : forall (left right : nt_state), nt_state.

(* State *)
Inductive state : Set :=
  Stop    : state
| NTState : forall (st : nt_state), state.

(* Functions on states *)
Fixpoint union (x y : state) : state :=
  match x with
  | Stop       => y
  | NTState sx => match y with
                  | Stop       => x
                  | NTState sy => NTState (Sum sx sy)
                  end
  end.

(* The context is represented as a list zipper *)
Definition context : Set := (list (name * term) * list (name * term)).

Fixpoint push_nt (ctx : context) (st : nt_state) : nt_state :=
  match st with
  | Sum l r        => Sum (push_nt ctx l) (push_nt ctx r)
  | Leaf theta i r => Leaf theta i (concat [fst ctx; r; snd ctx])
  end.

Definition push (ctx : context) (st : state) : state :=
  match st with
  | Stop => Stop
  | NTState st => NTState (push_nt ctx st)
  end.

(* Free variables of nt_state *)
Inductive is_fv_of_nt_state : name -> nt_state -> Prop :=
| isfvnstLeaf  : forall x theta i r
                        (X_FV_R    : Exists (fun p => In x (fv_term (snd p))) r)
                        (X_IN_DOM  : in_subst_dom theta x)
                        (X_IN_VRAN : in_subst_vran theta x), is_fv_of_nt_state x (Leaf theta i r)
| isfvnstSumL  : forall x nst1 nst2 (X_FV : is_fv_of_nt_state x nst1),
                                    is_fv_of_nt_state x (Sum nst1 nst2)
| isfvnstSumR  : forall x nst1 nst2 (X_FV : is_fv_of_nt_state x nst2),
                                    is_fv_of_nt_state x (Sum nst1 nst2).

Hint Constructors is_fv_of_nt_state : core.

Inductive is_fv_of_state : name -> state -> Prop :=
| isfvstC : forall x nst (X_FV_NT_ST : is_fv_of_nt_state x nst),
                         is_fv_of_state x (NTState nst).

Hint Constructors is_fv_of_state : core.

Inductive is_counter_of_nt_state : nat -> nt_state -> Prop :=
| iscnstLeaf  : forall theta i r, is_counter_of_nt_state i (Leaf theta i r)
| iscnstSumL  : forall n nst1 nst2 (ISC : is_counter_of_nt_state n nst1),
                                   is_counter_of_nt_state n (Sum nst1 nst2)
| iscnstSumR  : forall n nst1 nst2 (ISC : is_counter_of_nt_state n nst2),
                                   is_counter_of_nt_state n (Sum nst1 nst2).

Hint Constructors is_counter_of_nt_state : core.

Inductive well_formed_nt_state : nt_state -> Prop :=
| wfLeaf : forall theta r frn
           (DOM_LT_COUNTER  : forall x (X_IN_DOM  : in_subst_dom theta x), x < frn)
           (VRAN_LT_COUNTER : forall x (X_IN_VRAN : in_subst_vran theta x), x < frn)
           (FV_LT_COUNTER   : forall x (X_FV      : Exists (fun p => In x (fv_term (snd p))) r), x < frn),
           well_formed_nt_state (Leaf theta frn r) 
| wfSum  : forall nst1 nst2 (WF_L : well_formed_nt_state nst1)
                            (WF_R : well_formed_nt_state nst2),
                            well_formed_nt_state (Sum nst1 nst2).

Hint Constructors well_formed_nt_state : core.

(*********************** One-step unfolding *************************)

Reserved Notation "st |- g ~~> st'" (at level 0).

Inductive os_eval : state -> goal -> state -> Prop :=
  osEnd       : forall g,  Stop |- g ~~> Stop
| osUnifyFail : forall theta i r t1 t2
                        (MGU : mgu (apply_subst theta t1) (apply_subst theta t2) None),
    (NTState (Leaf theta i r)) |- Unify t1 t2 ~~> Stop
| osUnifySucc : forall theta theta' i r t1 t2
                        (MGU : mgu (apply_subst theta t1) (apply_subst theta t2) (Some theta')),
    (NTState (Leaf theta i r)) |- Unify t1 t2 ~~> (NTState (Leaf (compose theta theta') i r))
| osApp       : forall theta i r rel t,
    (NTState (Leaf theta i r)) |- Invoke rel t ~~> (NTState (Leaf theta i (concat [r; [(rel, t)]])))
| osFresh     : forall theta r i g st (H : (NTState (Leaf theta (S i) r)) |- g i ~~> st),
    (NTState (Leaf theta i r)) |- Fresh g ~~> st
| osDisjGoal  : forall theta r i g1 g2 st1 st2
                        (H1 : (NTState (Leaf theta i r)) |- g1 ~~> st1)
                        (H1 : (NTState (Leaf theta i r)) |- g2 ~~> st2),
    (NTState (Leaf theta i r)) |- Disj g1 g2 ~~> (union st1 st2)
| osDisjState : forall st1 st2 st3 st4 g
                        (H1 : (NTState st1) |- g ~~> st3)
                        (H2 : (NTState st2) |- g ~~> st4), 
    (NTState (Sum st1 st2)) |- g ~~> (union st3 st4)
| osConj      : forall theta i r g1 g2 st st'
                        (H1 : (NTState (Leaf theta i r)) |- g1 ~~> st)
                        (H2 : st |- g2 ~~> st'),
    (NTState (Leaf theta i r)) |- Conj g1 g2 ~~> st'
where "st |- g ~~> st'" := (os_eval st g st').

Inductive unfold : subst -> nat -> name -> term -> state -> Prop :=
  ufIntro : forall theta i rel term st
                    (H : (NTState (Leaf theta i [])) |- (proj1_sig (Language.Prog rel) term) ~~> st),
    unfold theta i rel term st.

(******************* Angelic semantics itself ***********************)

Inductive label : Set :=
  Step   : label
| Answer : subst -> label.

Inductive selected_app : list (name * term) -> ((name * term) * context) -> Prop :=
  saBase : forall p, selected_app [p] (p, ([], []))
| saHead : forall p ps, selected_app (p :: ps) (p, ([], ps))
| saTail : forall h ps p ps1 ps2 (H : selected_app ps (p, (ps1, ps2))),
    selected_app (h :: ps) (p, (h :: ps1, ps2)).
  
Reserved Notation "st -- l --> st'" (at level 0).

Inductive ang_eval : state -> label -> state -> Prop :=
  angAnswer     : forall theta i, (NTState (Leaf theta i [])) -- (Answer theta) --> Stop
| angConjUnfold : forall theta i r name term ctx st 
                         (Hs : selected_app r ((name, term), ctx))
                         (H  : unfold theta i name term st),
    (NTState (Leaf theta i r)) -- Step --> (push ctx st)
| angDisj       : forall st1 st2 lab (H : (NTState st1) -- lab --> Stop),
    (NTState (Sum st1 st2)) -- lab --> (NTState st2)
| angDisjStep   : forall st1 st2 lab st' (H : (NTState st1) -- lab --> (NTState st')),
    (NTState (Sum st1 st2)) -- lab --> (NTState (Sum st2 st'))
  where "st -- l --> st'" := (ang_eval st l st').

  
