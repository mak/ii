{-# LANGUAGE ViewPatterns, NoMonomorphismRestriction, OverloadedStrings #-}
module Main where

import GHC.Exts
import Data.Set (Set)
import qualified Data.Set as S
import Data.Map (Map)
import qualified Data.Map as M
import Control.Arrow (Arrow(..))
import Control.Monad.Reader
import Control.Monad.State
import Data.Char (chr)
import Data.List (findIndex)


data Var = Name String Integer -- a_i
    deriving (Eq,Ord)


mkName = flip Name 0
instance Show Var where
    show (Name a i) = a ++ show i

instance IsString Var where
    fromString = mkName

instance IsString Term1 where
    fromString = Var . mkName

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
   (a',u') =
       let (f,x) = occ fv a t
           uniq_t_v = flip bump' b $ bump a x
           (f',x') = occ fv uniq_t_v u
           a_uniq = if f' then bump uniq_t_v x' else uniq_t_v
       in if f then (a_uniq,subst a (Var a') u) else (a,u)

occ fv a = S.fold (\a' (f',a'')-> (f' || a' == a ,maxVar a'' a')) (False,Name "" 0) . fv
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

shift :: Integer -> Integer -> Term2 -> Term2
shift d c (Var2 k) | k < c = Var2 k
shift d c (Var2 k) = Var2 $ k + d
shift d c (App2 (shift d c -> t1) (shift d c -> t2)) = App2 t1 t2
shift d c (Lam2 (shift d (c+1) -> t1)) = Lam2 t1

subst2 (Var2 k) j u | k ==j = u
subst2 (Var2 k) _ _ = Var2 k
subst2 (App2 t1 t2) j u = App2 (subst2 t1 j u) (subst2 t2 j u)
subst2 (Lam2 t) j u = subst2 t (j+1) $ shift 1 0 u

kervine (App2 t1 t2) s = (t1,t2:s)
kervine (Lam2 t) (u:s) = (t',s) where
  t' = shift (-1) 0 $ subst2 t 0 $ shift 1 0 u

kervineStar = go . flip (,) [] where
    go (uncurry kervine -> (Lam2 t,[])) = Lam2 t
    go (uncurry kervine -> (Var2 n,s)) = foldl App2 (Var2 n) s
    go (uncurry kervine -> (t,s)) = go (t,s)


toDeBrujin ctx = flip evalState (reverse ctx) . go where
    go (Var v) = maybe (error $ "unboud variable:" ++ show v) (return . Var2 . toEnum ) . findIndex (==v) =<< get
    go (App t1 t2) = App2 `fmap` go t1 `ap` go t2
    go (Lam v t) = Lam2 `fmap` (modify (v:) >> go t)


fromDeBrujin = flip evalState 0 . go where
    mkName  = uncurry (flip Name) . second (return . chr . fromEnum . (97+)) .  (`quotRem` 26)
    go (Var2 i) = return . Var $ mkName i
    go (App2 t1 t2) = App `fmap` go t1 `ap` go t2
    go (Lam2 t) = do
      t' <- go t
      i <- get
      modify succ
      return $ Lam (mkName i) t'

type Name = Var
data Term3 = Var3 Name | App3 Term3 Term3 | Lam3 Name Term3 | Z | S Term3 | Case Term3 Term3 (Name,Term3) | Fix Name Term3
    deriving Show
data Value = N Int | Fun (Value -> Value)
type Env = Name -> Value
type Intepreter = ReaderT Env Maybe

instance Eq Value where
    (N x) == (N y) = x == y

instance Show Value where
    show (N n)= show n
    show _ = "<function>"

fv3 Z = S.empty
fv3 (S n) = fv3 n
fv3 (Var3 a) = S.singleton a
fv3 (App3 (fv3 -> s1) (fv3 -> s2)) = s1 `S.union` s2
fv3 (Lam3 a (fv3 ->s)) = a `S.delete` s
fv3 (Fix a (fv3 ->s)) = a `S.delete` s
fv3 (Case (fv3 -> s1) (fv3 -> s2) (second fv3 -> (a,s3))) = s1 `S.union` s2 `S.union` (a `S.delete` s3)


-- [b/t]  s
subst3 b s = subst3' b s where
    fvs = fv3 s
    subst3' b t (Var3 a)| a == b = t
    subst3' b t (Var3 a)  = Var3 a
    subst3' _ _ Z = Z
    subst3' b t (S n) = S $ subst3' b t n
    subst3' b t (App3 (subst3' b t ->t1) (subst3' b t ->t2))= App3 t1 t2
    subst3' b _ t@(Lam3 a _ ) | b == a = t
    subst3' b _ t@(Fix a _) | b == a = t
    subst3' b _ t@(Case _ _ (a,_)) | b == a = t
    subst3' b t (Lam3 a u) = Lam3 a' $ subst3' b t u'  where
         (a',u') = reName3 fvs a t u b
    subst3' b t (Fix a u) = Fix a' $ subst3' b t u' where
         (a',u') = reName3 fvs a t u b
    subst3' b t (Case (subst3' b t ->t1) (subst3' b t -> t2) (a,t3)) = Case t1 t2 $ (a',subst3' b t u') where
         (a',u') = reName3 fvs a t t3 b

reName3 fvt a t u b = (a',u') where
    (a',u') =
       let (f,x) = occ (const fvt) a t
           uniq_t_v = flip bump' b $ bump a x
           (f',x') = occ fv3 uniq_t_v u
           a_uniq = if f' then bump uniq_t_v x' else uniq_t_v
       in if f then (a_uniq,subst3 a (Var3 a') u) else (a,u)

isNum Z = True
isNum (S n) = isNum n
isNum _ = False

isVal3 (Var3 _) = True
isVal3 (Lam3 _ _) = True
isVal3 (App3 (App3 t1 t2) t3) = all isVal3 [t1,t2,t3]
isVal3 (App3 (Var3 _) t) = isVal3 t
isVal3 _ = False

betaEval3 (Var3 v) = Var3 v
betaEval3 (Lam3 v t) = Lam3 v t
betaEval3 Z = Z
betaEval3 (S (betaEval3 -> n)) | isNum n = S n
betaEval3 (App3 (betaEval3 -> Lam3 v u) (betaEval3 -> w)) = betaEval3 $ subst3 v w u
betaEval3 (App3 (betaEval3 -> v) (betaEval3 -> w)) | not $ isNum v = App3 v w
betaEval3 (Case (betaEval3 -> Z) t _ ) = betaEval3 t
betaEval3 (Case (betaEval3 -> S n) _ (v,t) ) = betaEval3 $ subst3 v n t
betaEval3 (Fix v t) = let a =  betaEval3 $ subst3 v a  t in a

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

instance IsString Term3 where
    fromString = Var3 . mkName

cata = Lam3 "f" $ Lam3 "g" $ Fix "h" $  Lam3 "x" $ Case "x" "g" ("y",App3 "f" (App3 "h" "y"))
add = Lam3 "n" $ Lam3 "m" $ App3 (App3 (App3 "cata" (Lam3 "z" $ S "z" ) ) "m") "n"
mul = Lam3 "x" $ Lam3 "y" $ App3 (App3 (App3 "cata" (Lam3 "z" $ App3 (App3 "add" "y") "z") ) Z) "x"
fac = Fix "f" $ Lam3 "x" $ Case "x" (S Z) ("y",App3 (App3 "mul" "x") (App3 "f" "y"))

add' = App3 (Lam3 "cata" add) cata
mul' = App3 (Lam3 "cata" (App3 (Lam3 "add" mul) add')) cata
fac' = App3 (Lam3 "mul" fac) mul'

fromInt 0 = Z
fromInt n = S $ fromInt $ n -1

test1 x y = betaEval3 $ App3 (App3 add' (fromInt x)) (fromInt y)
test2 x y = betaEval3 $ App3 (App3 mul' (fromInt x)) (fromInt y)
test3 = betaEval3 . App3 fac' . fromInt

test =
  let
    cataFun = interp cata
    addFun = interp' env' add
    mulFun = interp' env'' mul
    env' = \x -> if x == "cata" then cataFun else error ("unbound var: " ++ show x )
    env'' = \x -> if x == "add" then addFun else env' x
    env''' = \x -> if x == "mul" then mulFun else env'' x
  in
    interp' env''' fac

