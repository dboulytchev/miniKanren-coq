module Interpreter where

import qualified Prelude

__ :: any
__ = Prelude.error "Logical or arity value used"

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
fst p0 =
  case p0 of {
   Pair x _ -> x}

snd :: (Prod a1 a2) -> a2
snd p0 =
  case p0 of {
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
   Cons p0 tl ->
    case p0 of {
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
  app (map (\p0 -> Pair (fst p0) (apply_subst s2 (snd p0))) s1) s2

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
 | Disj Goal Goal
 | Conj Goal Goal
 | Fresh (Name -> Goal)
 | Invoke Name Term

type Rel = Term -> Goal

type Def = Rel

type Spec = Name -> Def

p :: Spec
p =
  Prelude.error "AXIOM TO BE REALIZED"

data Stream a =
   Nil0
 | Cons0 a (Stream a)

helper :: (Stream a1) -> Stream a1
helper s =
  s

data State' =
   Leaf Goal Subst Nat
 | Sum State' State'
 | Prod0 State' Goal

state'_rect :: (Goal -> Subst -> Nat -> a1) -> (State' -> a1 -> State' -> a1
               -> a1) -> (State' -> a1 -> Goal -> a1) -> State' -> a1
state'_rect f f0 f1 s =
  case s of {
   Leaf g s0 n -> f g s0 n;
   Sum s0 s1 -> f0 s0 (state'_rect f f0 f1 s0) s1 (state'_rect f f0 f1 s1);
   Prod0 s0 g -> f1 s0 (state'_rect f f0 f1 s0) g}

state'_rec :: (Goal -> Subst -> Nat -> a1) -> (State' -> a1 -> State' -> a1
              -> a1) -> (State' -> a1 -> Goal -> a1) -> State' -> a1
state'_rec =
  state'_rect

data State0 =
   Stop
 | State State'

data Label =
   Step
 | Answer Subst Nat

data Eval_step =
   EsFail Subst Nat
 | EsCut Subst Nat
 | EsUnifyFail Term Term Subst Nat Mgu
 | EsUnifySuccess Term Term Subst Subst Nat Mgu
 | EsDisj Goal Goal Subst Nat
 | EsConj Goal Goal Subst Nat
 | EsFresh (Name -> Goal) Subst Nat
 | EsInvoke Name Term Subst Nat
 | EsSumE State' State' Label Eval_step
 | EsSumNE State' State' State' Label Eval_step
 | EsProdSE State' Goal Eval_step
 | EsProdAE State' Goal Subst Nat Eval_step
 | EsProdSNE State' Goal State' Eval_step
 | EsProdANE State' Goal Subst Nat State' Eval_step

eval_step_exists :: State' -> SigT Label (SigT State0 Eval_step)
eval_step_exists st' =
  state'_rec (\g s n ->
    case g of {
     Fail -> ExistT Step (ExistT Stop (EsFail s n));
     Cut -> ExistT (Answer s n) (ExistT Stop (EsCut s n));
     Unify t t0 ->
      let {h = mgu_exists (apply_subst s t) (apply_subst s t0)} in
      case h of {
       ExistT x m ->
        case x of {
         Some s0 -> ExistT (Answer (compose s s0) n) (ExistT Stop
          (EsUnifySuccess t t0 s s0 n m));
         None -> ExistT Step (ExistT Stop (EsUnifyFail t t0 s n m))}};
     Disj g1 g2 -> ExistT Step (ExistT (State (Sum (Leaf g1 s n) (Leaf g2 s
      n))) (EsDisj g1 g2 s n));
     Conj g1 g2 -> ExistT Step (ExistT (State (Prod0 (Leaf g1 s n) g2))
      (EsConj g1 g2 s n));
     Fresh g0 -> ExistT Step (ExistT (State (Leaf (g0 n) s (S n))) (EsFresh
      g0 s n));
     Invoke n0 t -> ExistT Step (ExistT (State (Leaf (proj1_sig (p n0) t) s
      n)) (EsInvoke n0 t s n))}) (\st'1 iHst'1 st'2 _ ->
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
           Answer s0 n -> ExistT Step (ExistT (State (Leaf g s0 n)) (EsProdAE
            st'0 g s0 n iH))};
         State s0 ->
          case l of {
           Step -> ExistT Step (ExistT (State (Prod0 s0 g)) (EsProdSNE st'0 g
            s0 iH));
           Answer s1 n -> ExistT Step (ExistT (State (Sum (Leaf g s1 n)
            (Prod0 s0 g))) (EsProdANE st'0 g s1 n s0 iH))}}}}) st'

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

