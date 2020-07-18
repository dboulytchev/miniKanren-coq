module Realistic_diseq_interpreter where

import qualified Prelude as P
import qualified Data.Maybe
import qualified Data.Tuple
import qualified Data.List

__ :: any
__ = P.error "Logical or arity value used"

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






{- Nats and ints -}

int_to_nat :: P.Int -> Nat
int_to_nat n | n P.== 0    = O
             | P.otherwise = S (int_to_nat (n P.- 1))

nat_to_int :: Nat -> P.Int
nat_to_int O = 0
nat_to_int (S n) = (nat_to_int n) P.+ 1

instance P.Show Nat where
  show n = P.show (nat_to_int n)

instance P.Eq Nat where
  a == b = (nat_to_int a) P.== (nat_to_int b)


{- Usual terms and terms -}

data UsualTerm = UVar Name | UCon P.String [UsualTerm]

v i = UVar (int_to_nat i)
c = UCon
cst s = UCon s [] 

constr_names :: [(P.Int, P.String)]
constr_names = 
  [
    (0, "_app"),
    (1, "_nil"),
    (2, "_cons"),

    (3, "z"),
    (4, "s"),
    (5, "nil"),
    (6, "cons")
  ]

constr_name_id :: P.String -> Name
constr_name_id s = int_to_nat (Data.Maybe.fromMaybe (P.error "no such constr name")
                                                    (P.lookup s (P.map Data.Tuple.swap constr_names)))

constr_id_name :: Name -> P.String
constr_id_name n = Data.Maybe.fromMaybe (P.error "no such constr name")
                                        (P.lookup (nat_to_int n) constr_names)

usual_term_to_term :: UsualTerm -> Term
usual_term_to_term (UVar n) = Var n
usual_term_to_term (UCon s uts) = Con (constr_name_id "_app")
                                      (Cst (constr_name_id s))
                                      (usual_list_to_term uts)

usual_list_to_term :: [UsualTerm] -> Term
usual_list_to_term uts = P.foldr (Con (constr_name_id "_cons"))
                                 (Cst (constr_name_id "_nil"))
                                 (P.map usual_term_to_term uts)



instance P.Show Term where
  show (Var n) = "v" P.++ (P.show n)                                  -- result of variable translation
  show (Con _ (Cst n) (Cst _)) = constr_id_name n                     -- result of constant translation
  show (Con _ (Cst n) (Con _ at ats)) = constr_id_name n P.++         -- result of constructor translation
                                        "(" P.++
                                        (P.show at) P.++
                                        (show_arg_terms ats) P.++
                                        ")"

show_arg_terms (Cst _) = ""
show_arg_terms (Con _ t ts) = ", " P.++ (P.show t) P.++ (show_arg_terms ts)


{- Program constructors -}

fail = Fail

infix 4 ===
ut1 === ut2 = Unify (usual_term_to_term ut1) (usual_term_to_term ut2)

infix 4 =/=
ut1 =/= ut2 = Disunify (usual_term_to_term ut1) (usual_term_to_term ut2)

infixr 2 |||
(|||) = Disj

infixr 3 &&&
(&&&) = Conj

fresh fb = Fresh (\x -> fb (UVar x))

invoke r args = Invoke (pred_name_id r) (usual_list_to_term args)

rel0 :: Goal -> Def
rel0 g = \arg ->                (Unify arg (usual_list_to_term [])) &&& g

rel1 :: (UsualTerm -> Goal) -> Def
rel1 gf = \arg ->  fresh (\x -> (Unify arg (usual_list_to_term [x])) &&& gf x)

rel2 :: (UsualTerm -> UsualTerm -> Goal) -> Def
rel2 gf = \arg ->  fresh (\x -> 
                  (fresh (\y -> (Unify arg (usual_list_to_term [x, y])) &&& gf x y)))

rel3 :: (UsualTerm -> UsualTerm -> UsualTerm -> Goal) -> Def
rel3 gf = \arg ->  fresh (\x -> 
                  (fresh (\y ->  
                  (fresh (\z -> (Unify arg (usual_list_to_term [x, y, z])) &&& gf x y z)))))

{- Program (all predicate definitions) and test goals -}

pred_name_id :: P.String -> Name
pred_name_id s = int_to_nat (Data.Maybe.fromMaybe (P.error "no such pred name")
                                                  (P.lookup s (P.map Data.Tuple.swap pred_names)))

pred_id_name :: Name -> P.String
pred_id_name n = Data.Maybe.fromMaybe (P.error "no such pred name")
                                      (P.lookup (nat_to_int n) pred_names)

pred_names :: [(P.Int, P.String)]
pred_names = 
  [
    (0, "zeroeso"),
    (1, "appendo"),
    (2, "reverso"),
    (3, "neq_any_nat_from_o"),
    (4, "neq_any_nat_o"),
    (5, "not_elem_o"),
    (6, "delete_o")
  ]

pseudo_p :: P.String -> Def
pseudo_p "zeroeso" = rel1 (\x -> invoke "zeroeso" [x] ||| x === cst "z")
pseudo_p "appendo" = rel3 (\a b ab -> (a === cst "nil" &&& b === ab) |||
                                       fresh (\h  ->
                                      (fresh (\t  ->
                                      (fresh (\tb -> a  === c "cons" [h, t]  &&&
                                                     ab === c "cons" [h, tb] &&&
                                                     invoke "appendo" [t, b, tb]))))))
pseudo_p "reverso" = rel2 (\a ar -> (a === cst "nil" &&& ar === cst "nil") |||
                                     fresh (\h  ->
                                    (fresh (\t  ->
                                    (fresh (\tr -> a  === c "cons" [h, t]   &&&
                                                   invoke "reverso" [t, tr] &&&
                                                   invoke "appendo" [tr, c "cons" [h, cst "nil"], ar]))))))
pseudo_p "neq_any_nat_from_o" = rel2 (\n x -> n =/= x &&& invoke "neq_any_nat_from_o" [c "s" [n], x])
pseudo_p "neq_any_nat_o" = rel1 (\x -> invoke "neq_any_nat_from_o" [cst "z", x])
pseudo_p "not_elem_o" = rel2 (\x l -> (l === cst "nil") |||
                                       fresh (\h  ->
                                      (fresh (\t  -> l === c "cons" [h, t]  &&&
                                                     h =/= x &&&
                                                     invoke "not_elem_o" [x, t]))))
pseudo_p "delete_o" = rel3 (\x l rl -> (l === cst "nil" &&& rl === cst "nil") |||
                                        fresh (\t -> l  === c "cons" [x, t]  &&&
                                                     invoke "delete_o" [x, t, rl]) |||
                                        fresh (\h  ->
                                       (fresh (\t  ->
                                       (fresh (\rt -> l  === c "cons" [h, t]  &&&
                                                      h  =/= x &&&
                                                      rl === c "cons" [h, rt] &&&
                                                      invoke "delete_o" [x, t, rt]))))))
pseudo_p _ = \arg -> fail

prog :: Spec
prog = \r_id -> pseudo_p (pred_id_name r_id)


itut :: P.Int -> UsualTerm
itut n | n P.== 0    = cst "z"
       | P.otherwise = c "s" [itut (n P.- 1)]


ultut :: [UsualTerm] -> UsualTerm
ultut uts = P.foldr (\x y -> c "cons" [x, y]) (cst "nil") uts

goal0 = invoke "zeroeso" [v 0] -- should give infinite stream
goal1 = invoke "appendo" [ultut [itut 0, itut 1], ultut [itut 2, itut 3], v 0]
goal2 = invoke "appendo" [v 0, v 1, ultut [itut 0, itut 1, itut 2]]
goal3 = invoke "reverso" [ultut [itut 0, itut 1, itut 2], v 0]
goal4 = invoke "reverso" [v 0, v 0] -- should give infinite stream

goal5 = invoke "neq_any_nat_o" [itut 3] -- should diverge
goal6 = invoke "not_elem_o" [v 0, ultut [itut 0, itut 1, itut 2]]
goal7 = invoke "delete_o" [itut 0, ultut [itut 0, itut 2, itut 0, itut 1, itut 0], v 0] &&& invoke "not_elem_o" [itut 0, v 0]
goal8 = invoke "delete_o" [itut 0, v 0, ultut [itut 2, itut 1]] -- should give infinite stream



{- Interpretation -}

instance (P.Show a, P.Show b) => P.Show (Prod a b) where
  show (Pair x v) = P.show x P.++ " -> " P.++ P.show v

listToPList :: List a -> [a]
listToPList Nil = []
listToPList (Cons h t) = h : listToPList t

instance P.Show a => P.Show (List a) where
  show l = P.show (listToPList l)

streamToList :: Stream a -> [a]
streamToList Nil0         = []
streamToList (Cons0 x xs) = x : streamToList xs

takeValsOnFVs :: P.Int -> Subst -> [Term]
takeValsOnFVs n s = P.map (\i -> apply_subst s (Var (int_to_nat i))) (P.init [0..n])

interpret :: P.Int -> Goal -> [([Term], Constraint_store)]
interpret n g = let (ExistT t _) = op_sem_exists (State (initial_state g (int_to_nat n)))
                in P.map (\(Answer s cs _) -> (takeValsOnFVs n s, cs))
                         (P.filter answersOnly (streamToList t))
  where
    answersOnly Step = P.False
    answersOnly (Answer _ _ _) = P.True


{- newtype ConstraintBinding = ConstraintBinding (Prod Name Term)

instance P.Show ConstraintBinding where
  show (ConstraintBinding (Pair n v)) = "v" P.++ P.show n P.++ " =/= " P.++ P.show v

show_constraint :: Subst -> P.String
show_constraint s = P.show P.$ P.map ConstraintBinding P.$ listToPList s -}



interpretAndPrint :: P.Int -> Goal -> P.IO ()
interpretAndPrint n g =
  P.mapM_
    (\(ans, cs) -> do
      P.putStr (P.show ans)
      P.putStr "\nwith\n"
      P.mapM_ (\c -> P.putStrLn ("not " P.++ P.show c)) (listToPList cs)
      P.putStr ";\n\n")
    (interpret n g)

interpretAndPrintFirstK :: P.Int -> P.Int -> Goal -> P.IO ()
interpretAndPrintFirstK k n g =
  P.mapM_
    (\(ans, cs) -> do
      P.putStr (P.show ans)
      P.putStr "\nwith\n"
      P.mapM_ (\c -> P.putStrLn ("not " P.++ P.show c)) (listToPList cs)
      P.putStr ";\n\n")
    (P.take k (interpret n g))

