-- {-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE
  NoMonomorphismRestriction
  ,OverloadedStrings
  ,ViewPatterns
  ,BangPatterns
  #-}

import Control.Monad.Reader hiding (join)
--import Control.Monad.State hiding (join)
import Control.Monad hiding (join)

import Control.Applicative
import Data.Function
import Data.List
import GHC.Exts
import Debug.Trace
import Control.Arrow

type Label =  String
data Var = Name String Integer -- a_i
    deriving (Eq,Ord)

mkName = flip Name 0
instance Show Var where
    show (Name a i) = a ++ if i == 0 then "" else show i

instance Applicative ( Reader r) where
    (<*>) = ap
    pure = return


instance IsString Var where
    fromString = mkName

instance IsString Term where
    fromString = Var . mkName

data Term = Var Var
          | App Term Term
          | Lam Var Type Term
          | Fix Term
          | Rec [(String,Term)]
          | Proj Label Term
          | String String
          | Len Term
          | Concat Term Term
          | T
          | F
          | If Term Term Term
          | Z
          | S Term
          | Comp Comp Term Term
          | P Term
--          | Tagged Type Term
    deriving (Show,Eq)

data Comp = Lt | Eq deriving (Eq,Show)

data Type = TRec [(String,Type)]
          | TString
          | TNat
          | TBool
          | TAbs Type Type
     deriving (Eq,Show)
{-
subtypeInc TBool TNat = Just $ \x -> case x of
                                      T -> S Z
                                      F -> Z
subtypeInc TBool TString = Just $ String . show
subtypeInc TNat  TString = Just $ String . show
subtypeInc (TAbs t s) (TAbs t1 s1) = do
  f <- subtypeInc t1 t
  f2 <- subtypeInc s s1
  return $ \(Lam x t) -> Lam x $ f2 $ replace f x t
subtypeInc (TRec ts) (TRec ss) = do
  perm <- find ((==ss).map snd) permutations $ zip [1..] ts
  let sigma _ [] = []
      sigma n (x:xs) = maybe (error "imposible") ((:sigma (n+1) xs) . snd) $ find ((==n).fst) pem
      foo n t = maybe (error "imposible") (subtypeInc t  . snd ) $ find ((==n).fst) perm
  f <- zipWithM foo [1..] ts
  return $ \(Rec ts) -> sigma 1 $ map f ts
-}

sortRec = sortBy (compare `on` fst)
err msg = error . (msg ++ ) . show

subtypeInc TBool TNat = True
subtypeInc TBool TString = True
subtypeInc TNat TString = True
subtypeInc (TAbs t s) (TAbs t1 s1) = subtypeInc t1 t && subtypeInc s s1
subtypeInc (TRec ts) (TRec ss) = all (\(l,t) -> maybe False (subtypeInc t) $ lookup l ts) ss
subtypeInc t1 t2 | t1 == t2 = True
subtypeInc _ _ = False




intersectWithM p f l1 l2 = sequence [ f a b | a <- l1, b <- l2, p a b]

foo f = \(l,x) (_,y) -> ((,) l <$> f x y)

join :: Type -> Type -> Maybe Type
join (TAbs t s) (TAbs t1 s1) = TAbs <$> meet t t1 <*> join s s1
join (TRec ts ) (TRec ss) = TRec <$> intersectWithM ((==) `on` fst) (foo join ) ts ss
join t1 t2  | subtypeInc t1 t2 = return t2
join t1 t2  | subtypeInc t2 t1 = return t1
join  _ _ = Nothing

meet (TAbs t s) (TAbs t1 s1) = TAbs <$> join t t1 <*> meet s s1
meet (TRec ts ) (TRec ss)    =TRec <$> ( ++ (ts \\ ss) ++ ( ss \\ ts)) <$>  intersectWithM ((==) `on` fst) (foo meet) ts ss
meet t1 t2  | subtypeInc t1 t2 = return t1
meet t1 t2  | subtypeInc t2 t1 = return t2
meet _ _ = Nothing

project l = maybe (err "unknown label: " l) id. lookup l
subtypeM ty t = do
  ty' <- typeOfM t
  return $ if subtypeInc ty' ty then ty else error ("can't cast " ++ show ty' ++ " to " ++ show ty)

typeOfM T = return TBool
typeOfM F = return TBool
typeOfM Z = return TNat
typeOfM (String s)   = return TString
typeOfM (Concat t1 t2)  = subtypeM TString t1 >> subtypeM TString t2 >> return TString
typeOfM (Len t) = subtypeM TString t >> return TNat
typeOfM (Var v) = ($v) <$> ask
typeOfM (S t) = subtypeM TNat t
typeOfM (P t) = subtypeM TNat t
typeOfM (If t1 t2 t3) = do
  !ty <- subtypeM TBool t1 --ewentualnie ;]
  ty2 <- typeOfM t2
  ty3 <- typeOfM t3
  case join ty2 ty3 of
    Just ty -> return ty
    _       -> fail ("type mismatch: " ++ show ty3 ++ " and  "++ show ty2)
typeOfM (Rec t) = let (ls,tys) = unzip t
                  in (TRec . zip ls) <$> (mapM typeOfM tys)
typeOfM (Proj l t) = do
  TRec ts <- typeOfM t
  return $ project l ts
typeOfM (App t1 t2) = do
  ty <- typeOfM t2
  TAbs ty1 ty2 <- typeOfM t1
  if subtypeInc ty ty1 then return ty2 else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOfM (Lam v ty1 t) = do
  ty <- local (\r x -> if x == v then  ty1 else r x) $ typeOfM t
  return $ TAbs ty1 ty
typeOfM (Fix t) = do
  TAbs ty ty1  <- typeOfM t
  if ty == ty1 then return ty else  fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOfM (Comp cmp t1 t2) = do
  ty1 <- typeOfM t1
  ty2 <- subtypeM ty1 t2
  if  canCmp ty1 then return TBool else fail ("can't compare: " ++ show ty1 )


typeOf env =  flip runReader env . typeOfM
typeOf' = typeOf (err "unbind type variable: " )


canCmp TNat      = True
canCmp TBool     = True
canCmp TString   = True
canCmp (TRec ts) = all (canCmp . snd) ts
canCmp _         = False

-- te same typy
isPrim = canCmp

type Env = Var -> Term

evalM :: Term -> Reader Env Term
evalM Z = return Z
evalM T = return T
evalM F = return F
evalM l@(Lam _ _ _ ) = return l
-- evalM (Tagged ty t) = cast ty <$> evalM t
evalM s@(String _) = return s
evalM (Var v) = evalM . ($v) =<< ask
evalM (Len s) = mkLen <$> evalM s
evalM (Concat s1 s2) = mkConcat <$> evalM s1 <*> evalM s2
evalM (S n)   = (S . cast TNat) <$> evalM n
evalM (P n)   = (mkP . cast TNat) <$> evalM n
evalM (App t1 t2) = do
  Lam x ty t <- evalM t1
  v <- evalM t2
  local (\r y -> if x == y then {- Tagged ty -} v else r y) $ evalM t
evalM (If t1 t2 t3)  = mkIf <$> evalM t1 <*> evalM t2 <*> evalM t3
evalM (Fix t) = mkFix =<< evalM t
evalM (Rec ts) = Rec <$> mapM (\(l,t) -> ((,) l) <$> evalM t) ts
evalM (Proj l t) = mkProj l <$> evalM t
evalM (Comp cmp t1 t2) = mkCmp cmp <$> evalM t1 <*> evalM t2

mkIf T t _ = t
mkIf F _ t = t
mkLen (cast TString -> String s) = toNat $ length s
mkFix a@(Lam x ty t) = local (\r y -> if x == y then {-Tagged ty $-} Fix a else r y) $ evalM t
mkP (S n) = n
mkConcat (cast TString -> String s1) (cast TString -> String s2) = String $ s1 ++ s2
mkProj l (Rec ts) = maybe (error "imposible") snd . find ((==l).fst) $ ts
mkProj l t = error $ show t
mkCmp Eq t1 t2 = case (t1,t2) of
                   (Z,Z) -> T
                   (Z,F) -> F
                   (F,Z) -> T
                   (S Z,T) -> T
                   (T,S Z) -> T
                   (T,T) -> T
                   (F,F) -> T
                   (S n,S m) -> mkCmp Eq n m
--                   (Rec ts,Rec ss) -> all (==T) $ zipWith (mkCmp Eq) ts ss
                   (String s1,String s2) -> if s1 == s2 then T else F
                   (_,_) -> F
mkCmp Lt t1 t2 = case (t1,t2) of
                   (F,T)   -> T
                   (Z,T)   -> T
                   (Z,S _) -> T
                   (T,S n) -> mkCmp Lt Z n
                   (S n,S m) -> mkCmp Lt n m
--                   (Rec ts,Rec ss) -> all (==T) $ zipWith (mkCmp Lt) ts ss
                   (String s1,String s2) -> if s1 < s2 then T else F
                   (_,_) -> F

toNat 0 = Z
toNat n = S $ toNat $ n -1

cast TNat Z = Z
cast TNat (S n) = S $ cast TNat n
cast TNat T = S Z
cast TNat F = Z
cast TString s@(String _) = s
cast TString T = String "true"
cast TString F = String "false"
cast TString Z = String "Z"
cast TString (S (cast TString -> String s)) = String $ "S " ++ s
--cast (TRec _) r@(Rec _) = r -- jest ok...
cast _ _ = error "i can't do it"


eval env =  flip runReader env . evalM
eval' = eval (err "unbind type variable: " )

coSubtypeM ty t = do
  (ty',t') <- coTypeOfM t
  case subTypeCo ty ty of
    Just f -> return (ty, f t)
    _      -> error ("can't cast " ++ show ty' ++ " to " ++ show ty)

subTypeCo TBool TNat = Just $ \b -> case b of
                                      T -> S Z
                                      F -> Z
subTypeCo TBool TString = return $ String . show
subTypeCo TNat TString = return $ String . show
subTypeCo (TAbs t s) (TAbs t1 s1) = do
  f <- subTypeCo t1 t
  f2 <- subTypeCo s s1
  return $ \(Lam x ty t) -> Lam x ty (App (Lam x t1 (f2 t)) (f $ Var x))

subTypeCo (TRec ts) (TRec ss) = do
  fs <- mapM (\(l,t) -> maybe Nothing (subTypeCo t) $ lookup l ts) ss
  return $ \(Rec ts) -> Rec $ undefined
subTypeCo t1 t2 | t1 == t2 = return id
subTypeCo _ _ = Nothing

type EnvT = Var -> Type

coTypeOfM :: Term -> Reader EnvT (Type,Term)
coTypeOfM T = return (TBool,T)
coTypeOfM F = return (TBool,F)
coTypeOfM Z = return (TNat,Z)
coTypeOfM s@(String _ )   = return (TString,s)
coTypeOfM (Concat t1 t2)  = do
  (_,t1') <- coSubtypeM TString t1
  (_,t2') <- coSubtypeM TString t2
  return (TString,Concat t1' t2')
coTypeOfM (Len t) = ((,) TNat . Len . snd ) <$> coSubtypeM TString t
coTypeOfM (Var v) = (flip (,) (Var v) . ($v)) <$> ask
coTypeOfM (S t) = ((,) TNat . S . snd ) <$> coSubtypeM TNat t
coTypeOfM (P t) = ((,) TNat . P . snd ) <$> coSubtypeM TNat t
{-
coTypeOfM (If t1 t2 t3) = do
  !ty <- coSubtypeM TBool t1 --ewentualnie ;]
  ty2 <- coTypeOfM t2
  ty3 <- coTypeOfM t3
  case join ty2 ty3 of
    Just ty -> return ty
    _       -> fail ("type mismatch: " ++ show ty3 ++ " and  "++ show ty2)
-} -- musze pomyslec
coTypeOfM a@(Rec t) =
    let (ls,tys) = unzip t
    in (((TRec . zip ls)*** (Rec . zip ls)) . unzip) <$> mapM coTypeOfM tys
coTypeOfM (Proj l t) = do
  (TRec ts,t') <- coTypeOfM t
  return (project l ts,Proj l t')
coTypeOfM (App t1 t2) = do
  (ty,t2') <- coTypeOfM t2
  (TAbs ty1 ty2,t1') <- coTypeOfM t1
  case  subTypeCo ty ty1 of
    Just f -> return (ty2,App t1' (f t2'))
    Nothing ->  fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
coTypeOfM (Lam v ty1 t) = (TAbs ty1 *** Lam v ty1) <$> (local (\r x -> if x == v then  ty1 else r x) $ coTypeOfM t)
coTypeOfM (Fix t) = do
  (TAbs ty ty1,t')  <- coTypeOfM t
  if ty == ty1 then return (ty,t') else  fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
coTypeOfM (Comp cmp t1 t2) = do
  (ty1,t1') <- coTypeOfM t1
  (ty2,t2') <- coSubtypeM ty1 t2
  if  canCmp ty1 then return (TBool,Comp cmp t1' t2') else fail ("can't compare: " ++ show ty1 )
