{-# LANGUAGE
   OverloadedStrings
  ,NoMonomorphismRestriction
  ,ViewPatterns
  ,TypeFamilies
  #-}


import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative hiding ((<|>))
import Data.Map (Map)



type Location = Int
type Pat = Maybe String
data Term = Var String
          | App Term Term
          | Lam Pat Term
          | Fix Term
          | Unit
          | Nil Type
          | Cons Type Term Term
          | Head Type Term
          | Tail Type Term
          | IsNil Type Term
          | Z
          | S Term
          | Ref Term
          | Ass Term Term
          | Loc Location
          | Deref Term
  deriving (Show,Eq)


data Type = TUnit
          | TList Type
          | TNat
          | TAbs Type Type
          | TVar Int
          | TRef Type
    deriving (Eq,Show)


data Value = VNat Int
           | VUnit
           | VAbs Pat Value
           | VCons Type Value Value
           | VNil Type
    deriving (Eq,Show)


type EnvT = (String -> Type)
type Env  = (String -> Term)

type Typer = ReaderT EnvT (State Int) Type

newTVar = modify (+1) >> TVar <$> get

unify TNat TNat   = True
unify TUnit TUnit = True
unify (TList t) (TList t1) = unify t t1
unify (TAbs t t1) (TAbs t' t1') = unify t1 t1' && unify t t'
unify (TVar _) _  = True
unify _  _ = False


typeOfM :: Term -> Typer
typeOfM Unit = return TUnit
typeOfM Z = return TNat
typeOfM (Var v) = ($v) <$> ask
typeOfM (S t) = do
  TNat <- typeOfM t
  return TNat
typeOfM (Nil t) = return t
typeOfM (App t1 t2) = do
  ty <- typeOfM t2
  TAbs ty1 ty2 <- typeOfM t1
  if unify ty ty1 then return ty2 else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOfM (Cons ty t1 ts) = do
  ty1 <- typeOfM t1
  TList ty2 <- typeOfM ts
  if ty1 == ty2 && ty1 == ty then return (TList ty) else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1 ++ " and " ++ show ty2)
typeOfM (Head ty t) = do
  TList ty1 <- typeOfM t
  if ty == ty1 then return ty else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOfM (Tail ty t) = do
  TList ty1 <- typeOfM t
  if ty == ty1 then return (TList ty) else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOfM (Lam (Just v) t) = do
  tv <- newTVar
  ty <- local (\r x -> if x == v then  tv else r x) $ typeOfM t
  return $ TAbs tv ty
typeOfM (Lam Nothing t) = TAbs TUnit <$> typeOfM t
typeOfM (Fix t) = do
  TAbs ty ty1  <- typeOfM t
  if ty == ty1 then return ty else  fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOfM (Ref t) = TRef <$> typeOfM t
typeOfM (Ass t1 t2) = do
  TRef ty <- typeOfM t1
  ty' <- typeOfM t1
  if ty' == ty then return TUnit else  fail ("type mismatch: " ++ show ty ++ " and  "++ show ty')
typeOfM (Deref t) = do
  TRef ty <- typeOfM t
  return ty

typeOf = flip evalState 0 . flip runReaderT (error . ("unbind type variable: " ++) . show ) . typeOfM

isNum Z = True
isNum (S n) = isNum n
isNum _ = False


isVal Z = True
isVal (S v) = isVal v
isVal Unit = True
isVal (Nil _ ) = True
isVal (Cons  _ v vs) = isVal v && isVal vs
isVal (Lam _ _) = True
isVal (Loc _) = True

data Memory = Memory { alloc     :: Term -> (Memory -> (Location,Memory))
                     , replace   :: Location -> Term -> (Memory -> Memory)
                     , deref     :: Location -> (Memory -> Term)
                     , memory    :: Map Location Term
                     }
type Evaluator = ReaderT Env (StateT Memory Maybe) Term

evalStep :: Term -> Evaluator
evalStep Z = fail "value"
evalStep (Var _) = fail "value"
evalStep (S n) | isNum n  = fail "value"
evalStep Unit = fail "value"
evalStep (Lam _ _) = fail "value"
evalStep (S e) = S <$> evalStep e
evalStep (App t1 t2) | isVal t1 = App t1 <$> evalStep t2
evalStep (App (Lam (Just v) t) v1)  = local (\r x -> if x == v then v1 else r x) $ evalStep t
evalStep (App (Lam Nothing t) v1)  =  evalStep t
evalStep (App t1 t2) = flip App t2 <$> evalStep t1
evalStep a@(Fix (Lam (Just v) t)) = local (\r x -> if x == v then a else r x) $ evalStep t
evalStep (Fix t) = Fix <$> evalStep t
evalStep (Cons ty t ts) | isVal t = Cons ty t <$> evalStep ts
evalStep (Cons ty t ts) = (\v -> Cons ty v ts) <$> evalStep t
evalStep (Head _ (Cons _ v _)) = return v
evalStep (Head ty t) = Head ty <$> evalStep t
evalStep (Tail _ (Cons _ _ t)) = return t
evalStep (Tail ty t) = Tail ty <$> evalStep t
evalStep (Ref v) | isVal v = do
  mem <- get
  let fAlloc = alloc mem
      (l,mem') = fAlloc v mem
  put mem'
  return $ Loc l
evalStep (Ref t) = Ref <$> evalStep t
evalStep (Deref (Loc l)) = (\m -> (deref m) l m) <$> get
evalStep (Deref t) = Deref <$> evalStep t
evalStep (Ass (Loc l) v) | isVal v = modify (\m -> replace m l v m) >> return Unit
evalStep (Ass v t) | isVal v = Ass v <$> evalStep t
evalStep (Ass t1 t2) = flip Ass t2 <$> evalStep t1

toValue Z = VNat 0
toValue (S (toValue -> VNat n)) = VNat $ n + 1
toValue Unit = VUnit
toValue (Nil t ) = VNil t
toValue (Cons t v vs) = VCons t (toValue v) $ toValue vs
toValue (Lam v t) = VAbs v (toValue t)

emptyMemory :: Memory
emptyMemory = undefined

evalStar = maybe ( error "huh imposible happens")  toValue . flip evalStateT emptyMemory. flip runReaderT  (err "unbound variable: ") . evalStarM
    where
      err msg = error . (msg ++) . show
      evalStarM t =  (evalStep t >>= evalStarM) `mplus` return t
