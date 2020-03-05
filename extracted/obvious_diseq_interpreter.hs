module Obvious_diseq_interpreter where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

false_rect :: a1
false_rect =
  Prelude.error "absurd case"

false_rec :: a1
false_rec =
  false_rect

eq_rect :: a1 -> a2 -> a1 -> a2
eq_rect _ f _ =
  f

eq_rec :: a1 -> a2 -> a1 -> a2
eq_rec =
  eq_rect

eq_rec_r :: a1 -> a2 -> a1 -> a2
eq_rec_r =
  eq_rec

data Bool =
   True
 | False

orb :: Bool -> Bool -> Bool
orb b1 b2 =
  case b1 of {
   True -> True;
   False -> b2}

data Nat =
   O
 | S Nat

nat_rect :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rect f f0 n =
  case n of {
   O -> f;
   S n0 -> f0 n0 (nat_rect f f0 n0)}

nat_rec :: a1 -> (Nat -> a1 -> a1) -> Nat -> a1
nat_rec =
  nat_rect

data Option a =
   Some a
 | None

data Prod a b =
   Pair a b

fst :: (Prod a1 a2) -> a1
fst p =
  case p of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p =
  case p of {
   Pair _ y -> y}

data List a =
   Nil
 | Cons a (List a)

app :: (List a1) -> (List a1) -> List a1
app l m =
  case l of {
   Nil -> m;
   Cons a l1 -> Cons a (app l1 m)}

type Sig a = a
  -- singleton inductive, whose constructor was exist
  
data SigT a p =
   ExistT a p

proj1_sig :: a1 -> a1
proj1_sig e =
  e

data Sumbool =
   Left
 | Right

acc_rect :: (a1 -> () -> (a1 -> () -> a2) -> a2) -> a1 -> a2
acc_rect f x =
  f x __ (\y _ -> acc_rect f y)

well_founded_induction_type :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
well_founded_induction_type x a =
  acc_rect (\x0 _ x1 -> x x0 x1) a

well_founded_induction :: (a1 -> (a1 -> () -> a2) -> a2) -> a1 -> a2
well_founded_induction =
  well_founded_induction_type

eqb :: Nat -> Nat -> Bool
eqb n m =
  case n of {
   O -> case m of {
         O -> True;
         S _ -> False};
   S n' -> case m of {
            O -> False;
            S m' -> eqb n' m'}}

eq_dec :: Nat -> Nat -> Sumbool
eq_dec n =
  nat_rec (\m -> case m of {
                  O -> Left;
                  S _ -> Right}) (\_ iHn m ->
    case m of {
     O -> Right;
     S m0 -> iHn m0}) n

map :: (a1 -> a2) -> (List a1) -> List a2
map f l =
  case l of {
   Nil -> Nil;
   Cons a t -> Cons (f a) (map f t)}

type Name = Nat

data Term =
   Var Name
 | Cst Name
 | Con Name Term Term

occurs :: Name -> Term -> Bool
occurs n t =
  case t of {
   Var x -> eqb n x;
   Cst _ -> False;
   Con _ l r -> orb (occurs n l) (occurs n r)}

type Subst = List (Prod Name Term)

empty_subst :: Subst
empty_subst =
  Nil

singleton_subst :: Name -> Term -> List (Prod Name Term)
singleton_subst n t =
  Cons (Pair n t) Nil

image :: Subst -> Name -> Option Term
image s n =
  case s of {
   Nil -> None;
   Cons p tl ->
    case p of {
     Pair m t -> case eq_dec m n of {
                  Left -> Some t;
                  Right -> image tl n}}}

apply_subst :: Subst -> Term -> Term
apply_subst s t =
  case t of {
   Var n -> case image s n of {
             Some t' -> t';
             None -> t};
   Cst _ -> t;
   Con n l r -> Con n (apply_subst s l) (apply_subst s r)}

compose :: Subst -> Subst -> Subst
compose s1 s2 =
  app (map (\p -> Pair (fst p) (apply_subst s2 (snd p))) s1) s2

data Unification_step_outcome =
   NonUnifiable
 | Same
 | VarSubst Name Term

create :: Name -> Term -> Unification_step_outcome
create n t =
  case occurs n t of {
   True -> NonUnifiable;
   False -> VarSubst n t}

unification_step :: Term -> Term -> Unification_step_outcome
unification_step t1 t2 =
  case t1 of {
   Var n1 ->
    case t2 of {
     Var n2 -> case eq_dec n1 n2 of {
                Left -> Same;
                Right -> create n1 t2};
     _ -> create n1 t2};
   Cst n1 ->
    case t2 of {
     Var n2 -> create n2 t1;
     Cst n2 -> case eq_dec n1 n2 of {
                Left -> Same;
                Right -> NonUnifiable};
     Con _ _ _ -> NonUnifiable};
   Con n1 l1 r1 ->
    case t2 of {
     Var n2 -> create n2 t1;
     Cst _ -> NonUnifiable;
     Con n2 l2 r2 ->
      case eq_dec n1 n2 of {
       Left ->
        case unification_step l1 l2 of {
         Same -> unification_step r1 r2;
         x -> x};
       Right -> NonUnifiable}}}

data Mgu =
   MguNonUnifiable Term Term
 | MguSame Term Term
 | MguVarSubstNone Term Term Name Term Mgu
 | MguVarSubstSome Term Term Name Term Subst Subst Mgu

mgu_exists :: Term -> Term -> SigT (Option Subst) Mgu
mgu_exists t1 t2 =
  let {
   h = well_founded_induction (\x h ->
         eq_rec_r __ (\h0 ->
           case x of {
            Pair t3 t4 ->
             let {u = unification_step t3 t4} in
             case u of {
              NonUnifiable -> ExistT None (MguNonUnifiable t3 t4);
              Same -> ExistT (Some empty_subst) (MguSame t3 t4);
              VarSubst n t ->
               let {
                h1 = h0 (Pair (apply_subst (singleton_subst n t) t3)
                       (apply_subst (singleton_subst n t) t4))}
               in
               let {h2 = h1 __} in
               case h2 of {
                ExistT x0 m ->
                 case x0 of {
                  Some s -> ExistT (Some (compose (singleton_subst n t) s))
                   (MguVarSubstSome t3 t4 n t s
                   (compose (singleton_subst n t) s) m);
                  None -> ExistT None (MguVarSubstNone t3 t4 n t m)}}}}) __ h)
         (Pair t1 t2)}
  in
  eq_rec_r __ (\h0 -> h0) __ h

data Goal =
   Fail
 | Cut
 | Unify Term Term
 | Disunify Term Term
 | Disj Goal Goal
 | Conj Goal Goal
 | Fresh (Name -> Goal)
 | Invoke Name Term

type Rel = Term -> Goal

type Def = Rel

type Spec = Name -> Def

prog :: Spec
prog =
  Prelude.error "AXIOM TO BE REALIZED"

data Stream a =
   Nil0
 | Cons0 a (Stream a)

helper :: (Stream a1) -> Stream a1
helper s =
  s

type Constraint_store = List (Prod Term Term)

init_cs :: Constraint_store
init_cs =
  Nil

data Add_constraint_ind_def =
   AcC Subst Constraint_store Term Term

type Add_constraint = Add_constraint_ind_def

add_constraint_exists :: Subst -> Constraint_store -> Term -> Term -> SigT
                         (Option Constraint_store) Add_constraint
add_constraint_exists s cs t1 t2 =
  ExistT (Some (Cons (Pair t1 t2) cs)) (AcC s cs t1 t2)

data Upd_cs_ind_def =
   UC Subst Constraint_store Subst

type Upd_cs = Upd_cs_ind_def

upd_cs_exists :: Subst -> Constraint_store -> Subst -> SigT
                 (Option Constraint_store) Upd_cs
upd_cs_exists s cs d =
  ExistT (Some cs) (UC s cs d)

data State' =
   Leaf Goal Subst Constraint_store Nat
 | Sum State' State'
 | Prod0 State' Goal

state'_rect :: (Goal -> Subst -> Constraint_store -> Nat -> a1) -> (State' ->
               a1 -> State' -> a1 -> a1) -> (State' -> a1 -> Goal -> a1) ->
               State' -> a1
state'_rect f f0 f1 s =
  case s of {
   Leaf g s0 c n -> f g s0 c n;
   Sum s0 s1 -> f0 s0 (state'_rect f f0 f1 s0) s1 (state'_rect f f0 f1 s1);
   Prod0 s0 g -> f1 s0 (state'_rect f f0 f1 s0) g}

state'_rec :: (Goal -> Subst -> Constraint_store -> Nat -> a1) -> (State' ->
              a1 -> State' -> a1 -> a1) -> (State' -> a1 -> Goal -> a1) ->
              State' -> a1
state'_rec =
  state'_rect

data State0 =
   Stop
 | State State'

state_rect :: a1 -> (State' -> a1) -> State0 -> a1
state_rect f f0 s =
  case s of {
   Stop -> f;
   State x -> f0 x}

state_rec :: a1 -> (State' -> a1) -> State0 -> a1
state_rec =
  state_rect

data Well_formed_state' =
   WfLeaf Goal Subst Constraint_store Nat
 | WfSum State' State' Well_formed_state' Well_formed_state'
 | WfProd State' Goal Well_formed_state'

well_formed_state'_rect :: (Goal -> Subst -> Constraint_store -> Nat -> () ->
                           () -> () -> () -> a1) -> (State' -> State' ->
                           Well_formed_state' -> a1 -> Well_formed_state' ->
                           a1 -> a1) -> (State' -> Goal -> Well_formed_state'
                           -> a1 -> () -> a1) -> State' -> Well_formed_state'
                           -> a1
well_formed_state'_rect f f0 f1 _ w =
  case w of {
   WfLeaf g s cs frn -> f g s cs frn __ __ __ __;
   WfSum st'1 st'2 wF_L wF_R ->
    f0 st'1 st'2 wF_L (well_formed_state'_rect f f0 f1 st'1 wF_L) wF_R
      (well_formed_state'_rect f f0 f1 st'2 wF_R);
   WfProd st' g wF_L ->
    f1 st' g wF_L (well_formed_state'_rect f f0 f1 st' wF_L) __}

well_formed_state'_rec :: (Goal -> Subst -> Constraint_store -> Nat -> () ->
                          () -> () -> () -> a1) -> (State' -> State' ->
                          Well_formed_state' -> a1 -> Well_formed_state' ->
                          a1 -> a1) -> (State' -> Goal -> Well_formed_state'
                          -> a1 -> () -> a1) -> State' -> Well_formed_state'
                          -> a1
well_formed_state'_rec =
  well_formed_state'_rect

first_nats :: Nat -> List Nat
first_nats k =
  case k of {
   O -> Nil;
   S n -> Cons n (first_nats n)}

well_formed_initial_state :: Goal -> Nat -> Well_formed_state'
well_formed_initial_state g k =
  WfLeaf g empty_subst init_cs k

data Well_formed_state =
   WfEmpty
 | WfNonEmpty State' Well_formed_state'

well_formed_state_rect :: a1 -> (State' -> Well_formed_state' -> a1) ->
                          State0 -> Well_formed_state -> a1
well_formed_state_rect f f0 _ w =
  case w of {
   WfEmpty -> f;
   WfNonEmpty x x0 -> f0 x x0}

well_formed_state_rec :: a1 -> (State' -> Well_formed_state' -> a1) -> State0
                         -> Well_formed_state -> a1
well_formed_state_rec =
  well_formed_state_rect

data Label =
   Step
 | Answer Subst Constraint_store Nat

label_rect :: a1 -> (Subst -> Constraint_store -> Nat -> a1) -> Label -> a1
label_rect f f0 l =
  case l of {
   Step -> f;
   Answer x x0 x1 -> f0 x x0 x1}

label_rec :: a1 -> (Subst -> Constraint_store -> Nat -> a1) -> Label -> a1
label_rec =
  label_rect

data Eval_step =
   EsFail Subst Constraint_store Nat
 | EsCut Subst Constraint_store Nat
 | EsUnifyFail Term Term Subst Constraint_store Nat Mgu
 | EsUnifyUpdFail Term Term Subst Constraint_store Subst Nat Mgu Upd_cs
 | EsUnifySuccess Term Term Subst Constraint_store Subst Constraint_store 
 Nat Mgu Upd_cs
 | EsDisunifyFail Term Term Subst Constraint_store Nat Add_constraint
 | EsDisunifySuccess Term Term Subst Constraint_store Constraint_store 
 Nat Add_constraint
 | EsDisj Goal Goal Subst Constraint_store Nat
 | EsConj Goal Goal Subst Constraint_store Nat
 | EsFresh (Name -> Goal) Subst Constraint_store Nat
 | EsInvoke Name Term Subst Constraint_store Nat
 | EsSumE State' State' Label Eval_step
 | EsSumNE State' State' State' Label Eval_step
 | EsProdSE State' Goal Eval_step
 | EsProdAE State' Goal Subst Constraint_store Nat Eval_step
 | EsProdSNE State' Goal State' Eval_step
 | EsProdANE State' Goal Subst Constraint_store Nat State' Eval_step

eval_step_rect :: (Subst -> Constraint_store -> Nat -> a1) -> (Subst ->
                  Constraint_store -> Nat -> a1) -> (Term -> Term -> Subst ->
                  Constraint_store -> Nat -> Mgu -> a1) -> (Term -> Term ->
                  Subst -> Constraint_store -> Subst -> Nat -> Mgu -> Upd_cs
                  -> a1) -> (Term -> Term -> Subst -> Constraint_store ->
                  Subst -> Constraint_store -> Nat -> Mgu -> Upd_cs -> a1) ->
                  (Term -> Term -> Subst -> Constraint_store -> Nat ->
                  Add_constraint -> a1) -> (Term -> Term -> Subst ->
                  Constraint_store -> Constraint_store -> Nat ->
                  Add_constraint -> a1) -> (Goal -> Goal -> Subst ->
                  Constraint_store -> Nat -> a1) -> (Goal -> Goal -> Subst ->
                  Constraint_store -> Nat -> a1) -> ((Name -> Goal) -> Subst
                  -> Constraint_store -> Nat -> a1) -> (Name -> Term -> Subst
                  -> Constraint_store -> Nat -> a1) -> (State' -> State' ->
                  Label -> Eval_step -> a1 -> a1) -> (State' -> State' ->
                  State' -> Label -> Eval_step -> a1 -> a1) -> (State' ->
                  Goal -> Eval_step -> a1 -> a1) -> (State' -> Goal -> Subst
                  -> Constraint_store -> Nat -> Eval_step -> a1 -> a1) ->
                  (State' -> Goal -> State' -> Eval_step -> a1 -> a1) ->
                  (State' -> Goal -> Subst -> Constraint_store -> Nat ->
                  State' -> Eval_step -> a1 -> a1) -> State' -> Label ->
                  State0 -> Eval_step -> a1
eval_step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15 _ _ _ e =
  case e of {
   EsFail s cs n -> f s cs n;
   EsCut s cs n -> f0 s cs n;
   EsUnifyFail t1 t2 s cs n mGU -> f1 t1 t2 s cs n mGU;
   EsUnifyUpdFail t1 t2 s cs d n mGU uPD_CS -> f2 t1 t2 s cs d n mGU uPD_CS;
   EsUnifySuccess t1 t2 s cs d cs' n mGU uPD_CS ->
    f3 t1 t2 s cs d cs' n mGU uPD_CS;
   EsDisunifyFail t1 t2 s cs n aDD_C -> f4 t1 t2 s cs n aDD_C;
   EsDisunifySuccess t1 t2 s cs cs' n aDD_C -> f5 t1 t2 s cs cs' n aDD_C;
   EsDisj g1 g2 s cs n -> f6 g1 g2 s cs n;
   EsConj g1 g2 s cs n -> f7 g1 g2 s cs n;
   EsFresh fg s cs n -> f8 fg s cs n;
   EsInvoke r arg s cs n -> f9 r arg s cs n;
   EsSumE st1 st2 l sTEP_L ->
    f10 st1 st2 l sTEP_L
      (eval_step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        st1 l Stop sTEP_L);
   EsSumNE st1 st1' st2 l sTEP_L ->
    f11 st1 st1' st2 l sTEP_L
      (eval_step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        st1 l (State st1') sTEP_L);
   EsProdSE st g sTEP_L ->
    f12 st g sTEP_L
      (eval_step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        st Step Stop sTEP_L);
   EsProdAE st g s cs n sTEP_L ->
    f13 st g s cs n sTEP_L
      (eval_step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        st (Answer s cs n) Stop sTEP_L);
   EsProdSNE st g st' sTEP_L ->
    f14 st g st' sTEP_L
      (eval_step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        st Step (State st') sTEP_L);
   EsProdANE st g s cs n st' sTEP_L ->
    f15 st g s cs n st' sTEP_L
      (eval_step_rect f f0 f1 f2 f3 f4 f5 f6 f7 f8 f9 f10 f11 f12 f13 f14 f15
        st (Answer s cs n) (State st') sTEP_L)}

eval_step_rec :: (Subst -> Constraint_store -> Nat -> a1) -> (Subst ->
                 Constraint_store -> Nat -> a1) -> (Term -> Term -> Subst ->
                 Constraint_store -> Nat -> Mgu -> a1) -> (Term -> Term ->
                 Subst -> Constraint_store -> Subst -> Nat -> Mgu -> Upd_cs
                 -> a1) -> (Term -> Term -> Subst -> Constraint_store ->
                 Subst -> Constraint_store -> Nat -> Mgu -> Upd_cs -> a1) ->
                 (Term -> Term -> Subst -> Constraint_store -> Nat ->
                 Add_constraint -> a1) -> (Term -> Term -> Subst ->
                 Constraint_store -> Constraint_store -> Nat ->
                 Add_constraint -> a1) -> (Goal -> Goal -> Subst ->
                 Constraint_store -> Nat -> a1) -> (Goal -> Goal -> Subst ->
                 Constraint_store -> Nat -> a1) -> ((Name -> Goal) -> Subst
                 -> Constraint_store -> Nat -> a1) -> (Name -> Term -> Subst
                 -> Constraint_store -> Nat -> a1) -> (State' -> State' ->
                 Label -> Eval_step -> a1 -> a1) -> (State' -> State' ->
                 State' -> Label -> Eval_step -> a1 -> a1) -> (State' -> Goal
                 -> Eval_step -> a1 -> a1) -> (State' -> Goal -> Subst ->
                 Constraint_store -> Nat -> Eval_step -> a1 -> a1) -> (State'
                 -> Goal -> State' -> Eval_step -> a1 -> a1) -> (State' ->
                 Goal -> Subst -> Constraint_store -> Nat -> State' ->
                 Eval_step -> a1 -> a1) -> State' -> Label -> State0 ->
                 Eval_step -> a1
eval_step_rec =
  eval_step_rect

well_formedness_preservation :: State' -> Label -> State0 -> Eval_step ->
                                Well_formed_state' -> Well_formed_state
well_formedness_preservation st' l st eV wF =
  eval_step_rec (\s cs n wF0 ->
    case wF0 of {
     WfLeaf g s0 cs0 frn ->
      eq_rec_r Fail (\_ ->
        eq_rec_r s (\cs1 _ _ ->
          eq_rec_r n (\_ _ _ _ -> eq_rec_r cs (\_ -> WfEmpty) cs1 __) frn) s0
          cs0) g __ __ __ __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd _ _ wF_L -> false_rec wF_L __}) (\s cs n wF0 ->
    case wF0 of {
     WfLeaf g s0 cs0 frn ->
      eq_rec_r Cut (\_ ->
        eq_rec_r s (\cs1 _ _ ->
          eq_rec_r n (\_ _ _ _ -> eq_rec_r cs (\_ -> WfEmpty) cs1 __) frn) s0
          cs0) g __ __ __ __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd _ _ wF_L -> false_rec wF_L __}) (\t1 t2 s cs n _ wF0 ->
    case wF0 of {
     WfLeaf g s0 cs0 frn ->
      eq_rec_r (Unify t1 t2) (\_ ->
        eq_rec_r s (\cs1 _ _ ->
          eq_rec_r n (\_ _ _ _ -> eq_rec_r cs (\_ -> WfEmpty) cs1 __) frn) s0
          cs0) g __ __ __ __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd _ _ wF_L -> false_rec wF_L __}) (\t1 t2 s cs _ n _ _ wF0 ->
    case wF0 of {
     WfLeaf g s0 cs0 frn ->
      eq_rec_r (Unify t1 t2) (\_ ->
        eq_rec_r s (\cs1 _ _ ->
          eq_rec_r n (\_ _ _ _ -> eq_rec_r cs (\_ -> WfEmpty) cs1 __) frn) s0
          cs0) g __ __ __ __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd _ _ wF_L -> false_rec wF_L __}) (\t1 t2 s cs _ _ n _ _ wF0 ->
    case wF0 of {
     WfLeaf g s0 cs0 frn ->
      eq_rec_r (Unify t1 t2) (\_ ->
        eq_rec_r s (\cs1 _ _ ->
          eq_rec_r n (\_ _ _ _ -> eq_rec_r cs (\_ -> WfEmpty) cs1 __) frn) s0
          cs0) g __ __ __ __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd _ _ wF_L -> false_rec wF_L __}) (\t1 t2 s cs n _ wF0 ->
    case wF0 of {
     WfLeaf g s0 cs0 frn ->
      eq_rec_r (Disunify t1 t2) (\_ ->
        eq_rec_r s (\cs1 _ _ ->
          eq_rec_r n (\_ _ _ _ -> eq_rec_r cs (\_ -> WfEmpty) cs1 __) frn) s0
          cs0) g __ __ __ __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd _ _ wF_L -> false_rec wF_L __}) (\t1 t2 s cs _ n _ wF0 ->
    case wF0 of {
     WfLeaf g s0 cs0 frn ->
      eq_rec_r (Disunify t1 t2) (\_ ->
        eq_rec_r s (\cs1 _ _ ->
          eq_rec_r n (\_ _ _ _ -> eq_rec_r cs (\_ -> WfEmpty) cs1 __) frn) s0
          cs0) g __ __ __ __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd _ _ wF_L -> false_rec wF_L __}) (\g1 g2 s cs n wF0 ->
    case wF0 of {
     WfLeaf g s0 cs0 frn ->
      eq_rec_r (Disj g1 g2) (\_ ->
        eq_rec_r s (\cs1 _ _ ->
          eq_rec_r n (\_ _ _ _ ->
            eq_rec_r cs (\_ -> WfNonEmpty (Sum (Leaf g1 s cs n) (Leaf g2 s cs
              n)) (WfSum (Leaf g1 s cs n) (Leaf g2 s cs n) (WfLeaf g1 s cs n)
              (WfLeaf g2 s cs n))) cs1 __) frn) s0 cs0) g __ __ __ __ __ __
        __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd _ _ wF_L -> false_rec wF_L __}) (\g1 g2 s cs n wF0 ->
    case wF0 of {
     WfLeaf g s0 cs0 frn ->
      eq_rec_r (Conj g1 g2) (\_ ->
        eq_rec_r s (\cs1 _ _ ->
          eq_rec_r n (\_ _ _ _ ->
            eq_rec_r cs (\_ -> WfNonEmpty (Prod0 (Leaf g1 s cs n) g2) (WfProd
              (Leaf g1 s cs n) g2 (WfLeaf g1 s cs n))) cs1 __) frn) s0 cs0) g
        __ __ __ __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd _ _ wF_L -> false_rec wF_L __}) (\fg s cs n wF0 ->
    case wF0 of {
     WfLeaf g s0 cs0 frn ->
      eq_rec_r (Fresh fg) (\_ ->
        eq_rec_r s (\cs1 _ _ ->
          eq_rec_r n (\_ _ _ _ ->
            eq_rec_r cs (\_ -> WfNonEmpty (Leaf (fg n) s cs (S n)) (WfLeaf
              (fg n) s cs (S n))) cs1 __) frn) s0 cs0) g __ __ __ __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd _ _ wF_L -> false_rec wF_L __}) (\r arg s cs n wF0 ->
    case wF0 of {
     WfLeaf g s0 cs0 frn ->
      eq_rec_r (Invoke r arg) (\_ ->
        eq_rec_r s (\cs1 _ _ ->
          eq_rec_r n (\_ _ _ _ ->
            eq_rec_r cs (\_ -> WfNonEmpty (Leaf (proj1_sig (prog r) arg) s cs
              n) (WfLeaf (proj1_sig (prog r) arg) s cs n)) cs1 __) frn) s0
          cs0) g __ __ __ __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd _ _ wF_L -> false_rec wF_L __}) (\st1 st2 _ _ _ wF0 ->
    case wF0 of {
     WfLeaf _ _ _ _ -> false_rec __ __ __ __;
     WfSum st'1 st'2 wF_L wF_R ->
      eq_rec_r st1 (\_ ->
        eq_rec_r st2 (\_ wF_R0 -> WfNonEmpty st2 wF_R0) st'2) st'1 __ wF_L
        wF_R;
     WfProd _ _ wF_L -> false_rec wF_L __}) (\st1 st1' st2 _ _ iHEV wF0 ->
    case wF0 of {
     WfLeaf _ _ _ _ -> false_rec __ __ __ __;
     WfSum st'1 st'2 wF_L wF_R ->
      eq_rec_r st1 (\_ ->
        eq_rec_r st2 (\wF_L0 wF_R0 ->
          let {iHEV0 = iHEV wF_L0} in
          case iHEV0 of {
           WfEmpty -> false_rec;
           WfNonEmpty st'0 wfState ->
            eq_rec_r st1' (\wfState0 -> WfNonEmpty (Sum st2 st1') (WfSum st2
              st1' wF_R0 wfState0)) st'0 wfState}) st'2) st'1 __ wF_L wF_R;
     WfProd _ _ wF_L -> false_rec wF_L __}) (\st0 g _ iHEV wF0 ->
    case wF0 of {
     WfLeaf _ _ _ _ -> false_rec __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd st'0 g0 wF_L ->
      eq_rec_r st0 (\_ -> eq_rec_r g (\wF_L0 _ -> iHEV wF_L0) g0) st'0 __
        wF_L __}) (\st0 g s cs n _ _ wF0 ->
    case wF0 of {
     WfLeaf _ _ _ _ -> false_rec __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd st'0 g0 wF_L ->
      eq_rec_r st0 (\_ ->
        eq_rec_r g (\_ _ -> WfNonEmpty (Leaf g s cs n) (WfLeaf g s cs n)) g0)
        st'0 __ wF_L __}) (\st0 g st'0 _ iHEV wF0 ->
    case wF0 of {
     WfLeaf _ _ _ _ -> false_rec __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd st'1 g0 wF_L ->
      eq_rec_r st0 (\_ ->
        eq_rec_r g (\wF_L0 _ ->
          let {iHEV0 = iHEV wF_L0} in
          case iHEV0 of {
           WfEmpty -> false_rec;
           WfNonEmpty st'2 wfState ->
            eq_rec_r st'0 (\wfState0 -> WfNonEmpty (Prod0 st'0 g) (WfProd
              st'0 g wfState0)) st'2 wfState}) g0) st'1 __ wF_L __})
    (\st0 g s cs n st'0 _ iHEV wF0 ->
    case wF0 of {
     WfLeaf _ _ _ _ -> false_rec __ __ __ __;
     WfSum _ _ wF_L wF_R -> false_rec wF_L wF_R;
     WfProd st'1 g0 wF_L ->
      eq_rec_r st0 (\_ ->
        eq_rec_r g (\wF_L0 _ ->
          let {iHEV0 = iHEV wF_L0} in
          case iHEV0 of {
           WfEmpty -> false_rec;
           WfNonEmpty st'2 wfState ->
            eq_rec_r st'0 (\wfState0 -> WfNonEmpty (Sum (Leaf g s cs n)
              (Prod0 st'0 g)) (WfSum (Leaf g s cs n) (Prod0 st'0 g) (WfLeaf g
              s cs n) (WfProd st'0 g wfState0))) st'2 wfState}) g0) st'1 __
        wF_L __}) st' l st eV wF

eval_step_exists :: State' -> SigT Label (SigT State0 Eval_step)
eval_step_exists st' =
  state'_rec (\g s c n ->
    case g of {
     Fail -> ExistT Step (ExistT Stop (EsFail s c n));
     Cut -> ExistT (Answer s c n) (ExistT Stop (EsCut s c n));
     Unify t t0 ->
      let {h = mgu_exists (apply_subst s t) (apply_subst s t0)} in
      case h of {
       ExistT x m ->
        case x of {
         Some s0 ->
          let {h0 = upd_cs_exists s c s0} in
          case h0 of {
           ExistT x0 u ->
            case x0 of {
             Some c0 -> ExistT (Answer (compose s s0) c0 n) (ExistT Stop
              (EsUnifySuccess t t0 s c s0 c0 n m u));
             None -> ExistT Step (ExistT Stop (EsUnifyUpdFail t t0 s c s0 n m
              u))}};
         None -> ExistT Step (ExistT Stop (EsUnifyFail t t0 s c n m))}};
     Disunify t t0 ->
      let {h = add_constraint_exists s c t t0} in
      case h of {
       ExistT x a ->
        case x of {
         Some c0 -> ExistT (Answer s c0 n) (ExistT Stop (EsDisunifySuccess t
          t0 s c c0 n a));
         None -> ExistT Step (ExistT Stop (EsDisunifyFail t t0 s c n a))}};
     Disj g1 g2 -> ExistT Step (ExistT (State (Sum (Leaf g1 s c n) (Leaf g2 s
      c n))) (EsDisj g1 g2 s c n));
     Conj g1 g2 -> ExistT Step (ExistT (State (Prod0 (Leaf g1 s c n) g2))
      (EsConj g1 g2 s c n));
     Fresh g0 -> ExistT Step (ExistT (State (Leaf (g0 n) s c (S n))) (EsFresh
      g0 s c n));
     Invoke n0 t -> ExistT Step (ExistT (State (Leaf (proj1_sig (prog n0) t)
      s c n)) (EsInvoke n0 t s c n))}) (\st'1 iHst'1 st'2 _ ->
    case iHst'1 of {
     ExistT l1 s ->
      case s of {
       ExistT st1 iH1 ->
        case st1 of {
         Stop -> ExistT l1 (ExistT (State st'2) (EsSumE st'1 st'2 l1 iH1));
         State s0 -> ExistT l1 (ExistT (State (Sum st'2 s0)) (EsSumNE st'1 s0
          st'2 l1 iH1))}}}) (\st'0 iHst' g ->
    case iHst' of {
     ExistT l s ->
      case s of {
       ExistT st iH ->
        case st of {
         Stop ->
          case l of {
           Step -> ExistT Step (ExistT Stop (EsProdSE st'0 g iH));
           Answer s0 c n -> ExistT Step (ExistT (State (Leaf g s0 c n))
            (EsProdAE st'0 g s0 c n iH))};
         State s0 ->
          case l of {
           Step -> ExistT Step (ExistT (State (Prod0 s0 g)) (EsProdSNE st'0 g
            s0 iH));
           Answer s1 c n -> ExistT Step (ExistT (State (Sum (Leaf g s1 c n)
            (Prod0 s0 g))) (EsProdANE st'0 g s1 c n s0 iH))}}}}) st'

type Trace = Stream Label

data Op_sem =
   OsStop
 | OsState State' Label State0 Trace Eval_step Op_sem

trace_from :: State0 -> Trace
trace_from st =
  case st of {
   Stop -> Nil0;
   State st' ->
    case eval_step_exists st' of {
     ExistT l s -> case s of {
                    ExistT st'' _ -> Cons0 l (trace_from st'')}}}

trace_from_correct :: State0 -> Op_sem
trace_from_correct st =
  case st of {
   Stop -> eq_rec_r (helper (trace_from Stop)) OsStop (trace_from Stop);
   State s ->
    eq_rec_r (helper (trace_from (State s)))
      (let {s0 = eval_step_exists s} in
       case s0 of {
        ExistT x s1 ->
         case s1 of {
          ExistT x0 e -> OsState s x x0 (trace_from x0) e
           (trace_from_correct x0)}}) (trace_from (State s))}

op_sem_exists :: State0 -> SigT Trace Op_sem
op_sem_exists st =
  ExistT (trace_from st) (trace_from_correct st)

