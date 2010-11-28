{-# LANGUAGE
   OverloadedStrings
  ,NoMonomorphismRestriction
  ,ViewPatterns
  ,TypeFamilies
  #-}


import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative hiding ((<|>))
import Data.IntMap (IntMap)
import Data.Array

import Data.List (union)

first f = \(x,y) -> (f x,y)

--type Location = Int
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
          | Null
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


type Location = Int

data Memory = M { memory :: Array Location Term
                , freeCell :: [Location]
                }


alloc v (M m []) = error "memory exhausted"
alloc v (M m (fc:fcs)) = (fc,M (m // [(fc,v)]) fcs)
deref l (M m _) = m ! l
update v l (M m fcs) = M (m // [(l,v)]) fcs


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
  let (l,mem') = alloc v mem
  put mem'
  return $ Loc l
evalStep (Ref t) = Ref <$> evalStep t
evalStep (Deref (Loc l)) = deref l  <$> get
evalStep (Deref t) = Deref <$> evalStep t
evalStep (Ass (Loc l) v) | isVal v = modify (update v l  ) >> return Unit
evalStep (Ass v t) | isVal v = Ass v <$> evalStep t
evalStep (Ass t1 t2) = flip Ass t2 <$> evalStep t1

toValue Z = VNat 0
toValue (S (toValue -> VNat n)) = VNat $ n + 1
toValue Unit = VUnit
toValue (Nil t ) = VNil t
toValue (Cons t v vs) = VCons t (toValue v) $ toValue vs
toValue (Lam v t) = VAbs v (toValue t)


emptyMemory = M (listArray (1,200) (replicate 200 Null)) [1..200]


evalStar = maybe ( error "huh imposible happens")  toValue . flip evalStateT emptyMemory. flip runReaderT  (err "unbound variable: ") . evalStarM
    where
      err msg = error . (msg ++) . show
      evalStarM t =  (evalStep t >>= (gc >=> evalStarM)  ) `mplus` return t


locations (Var v)  = locations . ($v) =<< ask
locations (App t1 t2) = union <$> locations t1 <*> locations t2
locations (Lam _ t) = locations t
locations (Fix t) = locations t
locations Unit = return []
locations (Nil _) = return []
locations (Cons _ t1 t2) = union <$> locations t1 <*> locations t2
locations (Head _ t)  = locations t
locations (Tail _ t)  = locations t
locations  Z = return []
locations (S t) = locations t
locations (Ref t) = locations t
locations ( Ass t1 t2) = union <$> locations t1 <*> locations t2
locations ( Loc l ) = return  [l]
locations (Deref t) = locations t

instance Monad m => Applicative ( ReaderT r m) where
    (<*>) = ap
    pure = return


gc t =  do
  mem <- memory <$> get
  let r = \l -> locations t >>= \ls -> reach mem ls l
  ret <-  foldM (\(a,fc) e@(l,t') -> r l >>= \b -> return (if b then (e:a,fc) else ((l,Null):a,l:fc))) ([],[]) $ assocs mem
  put $ uncurry M . first (array (1,200) . reverse) $ ret
  return t
      where
        reach mem ls l = (l `elem` ls ||) <$> foldM (\f l' -> (f || ) <$> (locations (mem ! l') >>= \ls' -> reach mem ls' l )) False ls

