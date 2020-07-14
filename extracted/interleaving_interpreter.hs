module Interleaving_interpreter where

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

mgu_result_exists :: Term -> Term -> SigT (Option Subst) ()
mgu_result_exists t1 t2 =
  let {
   h = well_founded_induction (\x h ->
         eq_rec_r __ (\h0 ->
           case x of {
            Pair t3 t4 ->
             let {u = unification_step t3 t4} in
             case u of {
              NonUnifiable -> ExistT None __;
              Same -> ExistT (Some empty_subst) __;
              VarSubst n t ->
               let {
                h1 = h0 (Pair (apply_subst (singleton_subst n t) t3)
                       (apply_subst (singleton_subst n t) t4))}
               in
               let {h2 = h1 __} in
               case h2 of {
                ExistT x0 _ ->
                 case x0 of {
                  Some s -> ExistT (Some (compose (singleton_subst n t) s))
                   __;
                  None -> ExistT None __}}}}) __ h) (Pair t1 t2)}
  in
  eq_rec_r __ (\h0 -> h0) __ h

data Stream a =
   Nil0
 | Cons0 a (Stream a)

data Goal =
   Fail
 | Unify Term Term
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

data Nt_state =
   Leaf Goal Subst Nat
 | Sum Nt_state Nt_state
 | Prod0 Nt_state Goal

nt_state_rect :: (Goal -> Subst -> Nat -> a1) -> (Nt_state -> a1 -> Nt_state
                 -> a1 -> a1) -> (Nt_state -> a1 -> Goal -> a1) -> Nt_state
                 -> a1
nt_state_rect f f0 f1 n =
  case n of {
   Leaf g s n0 -> f g s n0;
   Sum n0 n1 ->
    f0 n0 (nt_state_rect f f0 f1 n0) n1 (nt_state_rect f f0 f1 n1);
   Prod0 n0 g -> f1 n0 (nt_state_rect f f0 f1 n0) g}

nt_state_rec :: (Goal -> Subst -> Nat -> a1) -> (Nt_state -> a1 -> Nt_state
                -> a1 -> a1) -> (Nt_state -> a1 -> Goal -> a1) -> Nt_state ->
                a1
nt_state_rec =
  nt_state_rect

data State =
   Stop
 | NTState Nt_state

data Label =
   Step
 | Answer Subst Nat

eval_step_exists :: Nt_state -> SigT Label (SigT State ())
eval_step_exists nst =
  nt_state_rec (\g s n ->
    case g of {
     Fail -> ExistT Step (ExistT Stop __);
     Unify t t0 ->
      let {h = mgu_result_exists (apply_subst s t) (apply_subst s t0)} in
      case h of {
       ExistT x _ ->
        case x of {
         Some s0 -> ExistT (Answer (compose s s0) n) (ExistT Stop __);
         None -> ExistT Step (ExistT Stop __)}};
     Disj g1 g2 -> ExistT Step (ExistT (NTState (Sum (Leaf g1 s n) (Leaf g2 s
      n))) __);
     Conj g1 g2 -> ExistT Step (ExistT (NTState (Prod0 (Leaf g1 s n) g2)) __);
     Fresh g0 -> ExistT Step (ExistT (NTState (Leaf (g0 n) s (S n))) __);
     Invoke n0 t -> ExistT Step (ExistT (NTState (Leaf
      (proj1_sig (prog n0) t) s n)) __)}) (\_ iHnst1 nst2 _ ->
    case iHnst1 of {
     ExistT l1 s ->
      case s of {
       ExistT st1 _ ->
        case st1 of {
         Stop -> ExistT l1 (ExistT (NTState nst2) __);
         NTState n -> ExistT l1 (ExistT (NTState (Sum nst2 n)) __)}}})
    (\_ iHnst g ->
    case iHnst of {
     ExistT l s ->
      case s of {
       ExistT st _ ->
        case st of {
         Stop ->
          case l of {
           Step -> ExistT Step (ExistT Stop __);
           Answer s0 n -> ExistT Step (ExistT (NTState (Leaf g s0 n)) __)};
         NTState n ->
          case l of {
           Step -> ExistT Step (ExistT (NTState (Prod0 n g)) __);
           Answer s0 n0 -> ExistT Step (ExistT (NTState (Sum (Leaf g s0 n0)
            (Prod0 n g))) __)}}}}) nst

type Trace = Stream Label

trace_from :: State -> Trace
trace_from st =
  case st of {
   Stop -> Nil0;
   NTState nst ->
    case eval_step_exists nst of {
     ExistT l s -> case s of {
                    ExistT nst' _ -> Cons0 l (trace_from nst')}}}

op_sem_exists :: State -> SigT Trace ()
op_sem_exists st =
  ExistT (trace_from st) __

