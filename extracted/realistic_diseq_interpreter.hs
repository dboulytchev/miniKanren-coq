module Realistic_diseq_interpreter where

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

list_rect :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rect f f0 l =
  case l of {
   Nil -> f;
   Cons y l0 -> f0 y l0 (list_rect f f0 l0)}

list_rec :: a2 -> (a1 -> (List a1) -> a2 -> a2) -> (List a1) -> a2
list_rec =
  list_rect

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

mgu_exists :: Term -> Term -> SigT (Option Subst) ()
mgu_exists t1 t2 =
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

type Constraint_store = List Subst

init_cs :: Constraint_store
init_cs =
  Nil

add_constraint_exists :: Subst -> Constraint_store -> Term -> Term -> SigT
                         (Option Constraint_store) ()
add_constraint_exists s cs t1 t2 =
  let {mGU_E = mgu_exists (apply_subst s t1) (apply_subst s t2)} in
  case mGU_E of {
   ExistT r _ ->
    case r of {
     Some s0 ->
      case s0 of {
       Nil -> ExistT None __;
       Cons p s1 -> ExistT (Some (Cons (Cons p s1) cs)) __};
     None -> ExistT (Some cs) __}}

list_to_term :: (List Term) -> Term
list_to_term ts =
  case ts of {
   Nil -> Cst O;
   Cons t ts0 -> Con (S O) t (list_to_term ts0)}

upd_constr_exists :: Subst -> Subst -> Subst -> SigT (Option Subst) ()
upd_constr_exists _ w d =
  let {
   mGU_E = mgu_exists
             (list_to_term
               (map fst
                 (map (\p -> Pair (apply_subst d (Var (fst p)))
                   (apply_subst d (snd p))) w)))
             (list_to_term
               (map snd
                 (map (\p -> Pair (apply_subst d (Var (fst p)))
                   (apply_subst d (snd p))) w)))}
  in
  case mGU_E of {
   ExistT r _ -> ExistT r __}

upd_cs_exists :: Subst -> Constraint_store -> Subst -> SigT
                 (Option Constraint_store) ()
upd_cs_exists s cs d =
  list_rec (ExistT (Some Nil) __) (\a _ iHcs ->
    case iHcs of {
     ExistT rcs' _ ->
      let {uPD_C_E = upd_constr_exists s a d} in
      case uPD_C_E of {
       ExistT rw' _ ->
        case rcs' of {
         Some cs' ->
          case rw' of {
           Some w' ->
            case w' of {
             Nil -> ExistT None __;
             Cons p w'0 -> ExistT (Some (Cons (Cons p w'0) cs')) __};
           None -> ExistT (Some cs') __};
         None -> ExistT None __}}}) cs

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

first_nats :: Nat -> List Nat
first_nats k =
  case k of {
   O -> Nil;
   S n -> Cons n (first_nats n)}

initial_state :: Goal -> Nat -> State'
initial_state g k =
  Leaf g empty_subst init_cs k

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

eval_step_exists :: State' -> SigT Label (SigT State0 ())
eval_step_exists st' =
  state'_rec (\g s c n ->
    case g of {
     Fail -> ExistT Step (ExistT Stop __);
     Cut -> ExistT (Answer s c n) (ExistT Stop __);
     Unify t t0 ->
      let {h = mgu_exists (apply_subst s t) (apply_subst s t0)} in
      case h of {
       ExistT x _ ->
        case x of {
         Some s0 ->
          let {h0 = upd_cs_exists s c s0} in
          case h0 of {
           ExistT x0 _ ->
            case x0 of {
             Some c0 -> ExistT (Answer (compose s s0) c0 n) (ExistT Stop __);
             None -> ExistT Step (ExistT Stop __)}};
         None -> ExistT Step (ExistT Stop __)}};
     Disunify t t0 ->
      let {h = add_constraint_exists s c t t0} in
      case h of {
       ExistT x _ ->
        case x of {
         Some c0 -> ExistT (Answer s c0 n) (ExistT Stop __);
         None -> ExistT Step (ExistT Stop __)}};
     Disj g1 g2 -> ExistT Step (ExistT (State (Sum (Leaf g1 s c n) (Leaf g2 s
      c n))) __);
     Conj g1 g2 -> ExistT Step (ExistT (State (Prod0 (Leaf g1 s c n) g2)) __);
     Fresh g0 -> ExistT Step (ExistT (State (Leaf (g0 n) s c (S n))) __);
     Invoke n0 t -> ExistT Step (ExistT (State (Leaf (proj1_sig (prog n0) t)
      s c n)) __)}) (\_ iHst'1 st'2 _ ->
    case iHst'1 of {
     ExistT l1 s ->
      case s of {
       ExistT st1 _ ->
        case st1 of {
         Stop -> ExistT l1 (ExistT (State st'2) __);
         State s0 -> ExistT l1 (ExistT (State (Sum st'2 s0)) __)}}})
    (\_ iHst' g ->
    case iHst' of {
     ExistT l s ->
      case s of {
       ExistT st _ ->
        case st of {
         Stop ->
          case l of {
           Step -> ExistT Step (ExistT Stop __);
           Answer s0 c n -> ExistT Step (ExistT (State (Leaf g s0 c n)) __)};
         State s0 ->
          case l of {
           Step -> ExistT Step (ExistT (State (Prod0 s0 g)) __);
           Answer s1 c n -> ExistT Step (ExistT (State (Sum (Leaf g s1 c n)
            (Prod0 s0 g))) __)}}}}) st'

type Trace = Stream Label

trace_from :: State0 -> Trace
trace_from st =
  case st of {
   Stop -> Nil0;
   State st' ->
    case eval_step_exists st' of {
     ExistT l s -> case s of {
                    ExistT st'' _ -> Cons0 l (trace_from st'')}}}

op_sem_exists :: State0 -> SigT Trace ()
op_sem_exists st =
  ExistT (trace_from st) __

