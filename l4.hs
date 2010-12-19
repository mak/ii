-- {-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE
  NoMonomorphismRestriction
  ,OverloadedStrings
  ,ViewPatterns
  #-}

import Control.Monad.Reader hiding (join)
--import Control.Monad.State hiding (join)
import Control.Monad hiding (join)
import Control.Applicative
import Data.Function
import Data.List
import GHC.Exts

type Label =  String
data Var = Name String Integer -- a_i
    deriving (Eq,Ord)

mkName = flip Name 0
instance Show Var where
    show (Name a i) = a ++ if i == 0 then "" else show i

instance Monad m => Applicative ( ReaderT r m) where
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
          | Tagged Type Term
    deriving (Show,Eq)

data Comp = Le | Eq deriving (Eq,Show)

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
subtypeInc (TRec ts) (TRec ss) = isPrefixOf sts sss && (and $ zipWith (subtypeInc `on` snd) sts sss) where
    sts = sortRec ts
    sss = sortRec ss
subtypeInc t1 t2 | t1 == t2 = True
subtypeInc _ _ = False


join :: Type -> Type -> Maybe Type
join (TAbs t s) (TAbs t1 s1) = TAbs <$> meet t t1 <*> join s s1
join (TRec ts ) (TRec ss) = TRec <$> zipWithM (\(l,t1)(_,t2) -> ((,) l) <$> join t1 t2) (sortRec ts) (sortRec ss)
join t1 t2  | subtypeInc t1 t2 = return t2
join t1 t2  | subtypeInc t2 t1 = return t1
join  _ _ = Nothing

meet (TAbs t s) (TAbs t1 s1) = TAbs <$> join t t1 <*> meet s s1
meet (TRec ts ) (TRec ss)    =TRec <$> ( ++ (ts \\ ss) ++ ( ss \\ ts)) <$>  zipWithM (\(l,t1)(_,t2) -> ((,) l)<$>meet t1 t2 ) (sortRec ts) (sortRec ss)
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
  TBool <- typeOfM t1
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

eval Z = return Z
eval T = return T
eval F = return F
eval l@(Lam _ _ _ ) = return l
eval (Tagged ty t) = cast ty <$> eval t
eval s@(String _) = return s
eval (Var v) = ($v) <$> ask
eval (Len s) = mkLen <$> eval s
eval (Concat s1 s2) = mkConcat <$> eval s1 <*> eval s2
eval (S n)   = (S . cast TNat) <$> eval n
eval (P n)   = (mkP . cast TNat) <$> eval n
eval (App t1 t2) = do
  Lam x ty t <- eval t1
  v <- eval t2
  local (\r y -> if x == y then Tagged ty v else r y) $ eval t
eval (If t1 t2 t3)  = mkIf <$> eval t1 <*> eval t2 <*> eval t3
eval (Fix t) = mkFix =<< eval t
eval (Rec ts) = Rec <$> mapM (\(l,t) -> ((,) l) <$> eval t) ts
eval (Proj l t) = mkProj l <$> eval t

mkIf T t _ = t
mkIf F _ t = t
mkLen (cast TString -> String s) = toNat $ length s
mkFix a@(Lam x ty t) = local (\r y -> if x == y then Tagged ty $ Fix a else r y) $ eval t
mkP (S n) = n
mkConcat (cast TString -> String s1) (cast TString -> String s2) = String $ s1 ++ s2
mkProj l (Rec ts) = maybe (error "imposible") snd . find ((==l).fst) $ ts

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
cast _ _ = error "not implemented yet"