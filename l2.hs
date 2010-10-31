{-# LANGUAGE ViewPatterns, FlexibleInstances #-}
module Main where

import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad.Reader

data Var = Name String Int -- a_i
    deriving (Eq,Ord)

mkName = flip Name 0
instance Show Var where
    show (Name a i) = a ++ show i

data Term1 = Var Var | App Term1 Term1 | Lam Var Term1
data Val1 =  V Var | L Var Val1 | A Val1 Val1

instance Show Term1 where
    show (Var v) = show v
    show (App t1 t2) = concat [show t1, "@" ,show t2]
    show (Lam v t) = concat ["\\",show v,".",show t]

fv (Var a) = S.singleton a
fv (App (fv -> s1) (fv -> s2)) = s1 `S.union` s2
fv (Lam a (fv ->s)) = a `S.delete` s

isVal (Var _ ) = True
isVal (Lam _ t) = isVal t
isVal (App (App t1 t2) t3) = all isVal [t1,t2,t3]
isVal (App (Var _) t) = isVal t
isVal _ = False

-- [b/t]  s
subst b t (Var a)| a == b = t
subst b t (Var a)  = Var a
subst b t (App (subst b t ->t1) (subst b t ->t2))= App t1 t2
subst b _ t@(Lam a _ ) | b == a = t
subst b t (Lam a u) = Lam a' $ subst b t u'  where
   Name n c = a
   (a',u') =
       let (f,x) = occ a t
           uniq_t_v = flip bump' b $ bump a x
           (f',x') = occ uniq_t_v u
           a_uniq = if f' then bump uniq_t_v x' else uniq_t_v
       in if f then (a_uniq,subst a (Var a') u) else (a,u)
   occ a = S.fold (\a' (f',a'')-> (f' || a' == a ,maxVar a'' a')) (False,Name "" 0) . fv
   bump (Name name k) (Name _ j) = Name name $ succ $ max k j
   bump' v@(Name n _) v1@(Name n' _) = if v == v1 then bump v v1 else v
   maxVar v@(Name _ x) v1@(Name _ x1) = if x > x1 then v else v1

betaRed :: Term1 -> Term1
betaRed (Var a) = Var a
betaRed (Lam a t) = Lam a $ betaRed t
betaRed (App (betaRed -> Lam a u) t) = betaRed (subst a t u)
betaRed (App t1 t2 ) | isVal t1 = App t1 $ betaRed t2
betaRed (App (betaRed -> a)  s) = App a s

betaNorm :: Term1 -> Val1
betaNorm t = case betaRed t of
               t | isVal t-> toVal t
               t  -> betaNorm t
    where
      toVal (Var a) = V a
      toVal (Lam a t) = L a $ toVal t
      toVal (App t1 t2) = A (toVal t1) (toVal t2)


data Term2 = Var2 Integer | App2 Term2 Term2 | Lam2 Term2
    deriving Show
data Val2 = V2 Integer | L2 Term2 | A2 Val2 Term2
    deriving Show

shift :: Integer -> Integer -> Term2 -> Term2
shift d c (Var2 k) | k < c = Var2 k
shift d c (Var2 k) = Var2 $ k + d
shift d c (App2 (shift d c -> t1) (shift d c -> t2)) = App2 t1 t2
shift d c (Lam2 (shift d (c+1) -> t1)) = Lam2 t1

subst2 (Var2 k) j u | k ==j = u
subst2 (Var2 k) _ _ = Var2 k
subst2 (App2 t1 t2) j u = App2 (subst2 t1 j u) (subst2 t2 j u)
subst2 (Lam2 t) j u = subst2 t (j+1) $ shift 1 0 u

betaRed2 (Var2 a) = Var2 a
betaRed2 (Lam2 t) = Lam2 t
betaRed2 (App2 (betaRed2 -> Lam2 u) t) = betaRed2 $ shift (-1) 0 $ subst2 u 0 $ shift 1 0 t
betaRed2 (App2 (betaRed2 -> a)  s) = App2 a s


betaNorm2 :: Term2 -> Val2
betaNorm2 = either betaNorm2 id .toVal . betaRed2
    where
      toVal (Var2 a) = Right $ V2 a
      toVal (Lam2 t) = Right $ L2 t
      toVal t@(App2 (Lam2 _) _) = Left t
      toVal t@(App2 t1 t2) = either (const (Left t)) (\t' -> Right $ A2 t' t2) $ toVal t1
--      toVal t = Left t
{-
moze kiedy indziej?
-- see `I'm not a numberm: I'm free variable` by McBride and McKinna
data Term3 = Free Name2 | Bound Int | App Term3 Term3 | Lam Term3 Scope
    deriving (Eq,Show)
newtype Scope = Scope Term3
-}
type Name = Var
data Term3 = Var3 Name | App3 Term3 Term3 | Lam3 Name Term3 | Z | S Term3 | Case Term3 Term3 (Name,Term3) | Fix Name Term3
data Value = N Int | Fun (Value -> Value)
type Env = Name -> Value
type Intepreter = ReaderT Env Maybe

instance Eq Value where
    (N x) == (N y) = x == y

instance Show Value where
    show (N n)= show n
    show _ = "<function>"


data StackType = Either Term3 Value
type Stack = [StackType]
type Machine = Either (Term3,Stack) (Stack,Term3)

evalStack (Var3 v,s) = Right (s,Var3 v)
evalStack (Lam3 v t,s) = Right (s,Lam3 v t)
evalStack (App3 t1 t2,s) = Left (t1,Left t2:s)

evalStack' (Left t:s,v0) = Left (t1,Right v:s)
evalStack  (


suck (N i) = return $ N $ i + 1
suck _ = fail "not integer"
app (Fun f) x = f x

eval :: Term3 -> Intepreter Value
eval Z  = return $ N 0
eval (S n) = suck =<< eval n
eval (Var3 n )  = ($n) `fmap` ask
eval (App3 t1 t2) = do
  f <- eval t1
  arg <- eval t2
  return $ f `app` arg
eval (Lam3 x t) = do
  env <- ask
  return $ Fun $ \val -> maybe (error "Error!") id .
      flip runReaderT (\y -> if y == x then val else env y) $ eval t
eval (Case t1 t2 (v,t3)) = do
  N n <- eval t1
  case n of
    0 -> eval t2
    _ -> local (\r -> \x -> if x == v then N $ n -1 else r x) $ eval t3
eval (Fix n t) = mfix $ \val -> local (\r -> \x -> if x == n then val else r x) $ eval t

interp = interp' (error "unbuod variable")
interp' env = maybe (error "another error") id . flip runReaderT env . eval
--tests

x = mkName "x"
y = mkName "y"
z = mkName "z"
f = mkName "f"
g = mkName "g"
h = mkName "h"

test =
  let
    cataName = mkName "cata"
    addName  = mkName "add"
    mulName = mkName "mul"
    cata = Lam3 f $ Lam3 g $ Fix h $  Lam3 x $ Case (Var3 x) (Var3 g) (y,App3 (Var3 f) (App3 (Var3 h) (Var3 y)))
    add = Lam3 x $ Lam3 y $ App3 (App3 (App3 (Var3 cataName) (Lam3 z $ S (Var3 z)) ) (Var3 y)) (Var3 x)
    mul = Lam3 x $ Lam3 y $ App3 (App3 (App3 (Var3 cataName) (Lam3 z $ App3 (App3 (Var3 addName) (Var3 y)) (Var3 z)) ) Z) (Var3 x)
    fac = Fix f $ Lam3 x $ Case (Var3 x) (S Z) (y,App3 (App3 (Var3 mulName) (Var3 x)) (App3 (Var3 f) (Var3 y)))
    cataFun = interp cata
    addFun = interp' env' add
    mulFun = interp' env'' mul
    env' = \x -> if x == cataName then cataFun else error ("unbound var")
    env'' = \x -> if x == addName then addFun else env' x
    env''' = \x -> if x == mulName then mulFun else env'' x
  in
    interp' env''' fac

