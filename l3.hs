-- {-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE
   OverloadedStrings
  ,NoMonomorphismRestriction
  #-}

import GHC.Exts
import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative

import Data.Map (Map)


data Var = Name String Integer -- a_i
    deriving (Eq,Ord)

mkName = flip Name 0
instance Show Var where
    show (Name a i) = a ++ show i

instance IsString Var where
    fromString = mkName

instance IsString Term where
    fromString = Var . mkName


type Label =  Either Int String

data Term = Var Var
          | App Term Term
          | Lam Var Term
          | Fix Term
          | Ann Term Type
          | Rec [(String,Term)]
          | Proj Label Term
--          | Var [Term]
          | Unit
          | Nil Type
          | Cons Type Term Term
          | Head Type Term
          | Tail Type Term
          | IsNil Type Term
          | T
          | F
          | If Term Term Term
          | Z
          | S Term
          | Term :+: Term
          | IsZ Term
          | Eq Term Term
          | P Term
    deriving (Eq,Show)

data Type = TUnit
          | TRec [(String,Type)]
--          | TVariant [Type]
          | TList Type
          | TNat
          | TBool
          | TAbs Type Type
          | TVar Int
    deriving (Eq,Show)


data Value = VNat Int
           | VBool Bool
           | VUnit
           | VTuple [Value]
--           | VVarinat Int [Val]
           | VAbs Value Value
           | VList Type Value Value
    deriving (Eq,Show)


type EnvT = (Var -> Type)
type Env  = (Var -> Term)

type Typer = ReaderT EnvT (State Int) Type


newTVar = modify (+1) >> TVar <$> get

unify TNat TNat   = True
unify TBool TBool = True
unify TUnit TUnit = True
unify (TRec ts) (TRec ts1) = and $ zipWith unify (map snd ts) (map snd ts1)
unify (TList t) (TList t1) = unify t t1
unify (TAbs t t1) (TAbs t' t1') = unify t1 t1' && unify t t'
unify (TVar _) _  = True
unify _  _ = False

typeOf :: Term -> Typer
typeOf Unit = return TUnit
typeOf T = return TBool
typeOf F = return TBool
typeOf Z = return TNat
typeOf (Var v) = ($v) <$> ask
typeOf (S t) = do
  TNat <- typeOf t
  return TNat
typeOf (P t) = do
  TNat <- typeOf t
  return TNat
typeOf (If t1 t2 t3) = do
  TBool <- typeOf t1
  ty2 <- typeOf t2
  ty3 <- typeOf t3
  if ty2 == ty3 then return ty2 else fail ("type mismatch: " ++ show ty3 ++ " and  "++ show ty2)
typeOf (t1 :+: t2) = do
  TNat <- typeOf t1
  TNat <- typeOf t2
  return TNat
typeOf (IsZ t) = do
  TNat <- typeOf t
  return TBool
typeOf (Nil t) = return t
typeOf (Rec t) = let (ls,tys) = unzip t
                 in (TRec . zip ls) <$> (mapM typeOf tys)
typeOf (Proj l t) = do
  TRec ts <- typeOf t
  return $ project l ts
typeOf (Ann t ty) = do
  ty1 <- typeOf t
  if ty == ty1 then return ty else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOf (App t1 t2) = do
  ty <- typeOf t2
  TAbs ty1 ty2 <- typeOf t1
  if unify ty ty1 then return ty2 else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOf (Cons ty t1 ts) = do
  ty1 <- typeOf t1
  TList ty2 <- typeOf ts
  if ty1 == ty2 && ty1 == ty then return (TList ty) else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1 ++ " and " ++ show ty2)
typeOf (Head ty t) = do
  TList ty1 <- typeOf t
  if ty == ty1 then return ty else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOf (Tail ty t) = do
  TList ty1 <- typeOf t
  if ty == ty1 then return (TList ty) else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOf (IsNil ty t) = do
  TList ty1 <- typeOf t
  if ty == ty1 then return TBool else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOf (Lam v t) = do
  tv <- newTVar
  ty <- local (\r x -> if x == v then  tv else r x) $ typeOf t
  return $ TAbs tv ty
typeOf (Fix t) = do
  TAbs ty ty1  <- typeOf t
  if ty == ty1 then return ty else  fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOf (Eq t1 t2) = do
  ty1 <- typeOf t1
  ty2 <- typeOf t2
  if ty1 == ty2 && canEq ty1 && canEq ty2 then return ty1 else fail ("type mismatch: " ++ show ty1 ++ " and  "++ show ty2)

canEq TNat  = True
canEq TBool = True
canEq (TRec ts) = all (canEq.snd) ts
canEq (TList t) = canEq t
canEq _ = False

isNum Z = True
isNum (S n) = isNum n
isNum _ = False

isBool F = True
isBool T = True
isBool _ = False


project = either (\i -> snd . (!!i)) (\l ->  maybe (error $ "unknown label: " ++ show l) id. lookup l)

isVal = undefined

type Evaluator = ReaderT Env Maybe Term

evalStep :: Term -> Evaluator
evalStep Z = fail "value"
evalStep T = fail "value"
evalStep F = fail "value"
evalStep (Var _) = fail "value"
evalStep (S n) | isNum n  = fail "value"
evalStep (S e) = S <$> evalStep e
evalStep (P Z) = return Z
evalStep (P (S e)) | isNum e = return e
evalStep (P e) = P <$> evalStep e
evalStep (If T e _ ) = return e
evalStep (If F _ e  ) = return e
evalStep (If eb e1 e2 ) = evalStep eb >>= \b -> return (If b e1 e2)
evalStep (IsZ Z) = return T
evalStep (IsZ (S e )) | isNum e  = return F
evalStep (IsZ e) | isNum e = IsZ <$> evalStep e
evalStep (Z :+: n) | isNum n = return n
evalStep (S n1 :+: n2) | isNum n1 && isNum n2 = return $ S $ n1 :+: n2
evalStep (n :+: e) | isNum n = (n :+:) <$>  evalStep e
evalStep (e1 :+: e2) = (:+: e2) <$> evalStep e1
evalStep (Eq Z Z ) = return T
evalStep (Eq Z n ) | isNum n = return F
evalStep (Eq n Z ) | isNum n = return F
evalStep (Eq T T ) = return T
evalStep (Eq F T ) = return F
evalStep (Eq T F ) = return T
{- w zasadzie zle, duze kroki wyszly
evalStep (Eq (Cons t x xs)  (Cons t1 y ys)) =
    let Just eqFun = lookup t eqDict
    in if eqFun x y then return T else Eq xs ys
-}
evalStep (Eq b e) | isBool b = Eq b <$> evalStep e
evalStep (Eq e1 e2) = flip Eq e2 <$> evalStep e1
evalStep (App (Lam v t) v1)  = local (\r x -> if x == v then v1 else r x) $ evalStep t
evalStep a@(Fix (Lam v t)) = local (\r x -> if x == v then a else r x) $ evalStep t
evalStep (Fix t) = Fix <$> evalStep t
evalStep (App t1 t2) | isVal t1 = App t1 <$> evalStep t2
evalStep (App t1 t2) = flip App t2 <$> evalStep t1
evalStep (IsNil _ (Nil _)) = return T
evalStep (IsNil _ (Cons _ _ _)) = return F
evalStep (IsNil ty t) = IsNil ty <$> evalStep t
evalStep (Cons ty t ts) | isVal t = Cons ty t <$> evalStep ts
evalStep (Cons ty t ts) = (\v -> Cons ty v ts) <$> evalStep t
evalStep (Head _ (Cons _ v _)) = return v
evalStep (Head ty t) = Head ty <$> evalStep t
evalStep (Tail _ (Cons _ _ t)) = return t
evalStep (Tail ty t) = Tail ty <$> evalStep t
evalStep (Ann t ty) = flip Ann ty <$> evalStep t
evalStep (Proj l (Rec ts)) = return $ project l ts
evalStep (Proj l t) = Proj l <$> evalStep t
-- nie ma sensu przy takiej reprezentacji
-- rozwazac ewaluacji po koleji kazdej wsporzednej
evalStep (Rec ts) = let (ls,ts') = unzip ts
                    in (Rec . zip ls) <$> mapM evalStep ts'


evalStarM t =  (evalStep t >>= evalStarM) `mplus` return t

evalStar = maybe toValue  (err "hun unevalueted term: ")  . flip runReaderT  (err "unbound variable: ") . evalStarM
    where toValue :: Term -> Value
          toValue = undefined
          err msg = error . (msg ++) . show
