-- {-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE
  NoMonomorphismRestriction
  ,ViewPatterns
  #-}

import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative hiding ((<|>))

import Text.Parsec hiding (State)
import Text.Parsec.String (parseFromFile)
import Text.Parsec.Expr
import Text.Parsec.Token hiding (reservedOp,reserved,parens,angles,brackets,braces, identifier,commaSep,natural)
import Text.Parsec.Language
import qualified Text.Parsec.Token as PTok


import qualified Data.Set as S
import Data.Monoid
import Data.Char (isDigit)
import System.Console.Haskeline
import Data.Array
import Data.List (union)

import Debug.Trace

data Var = Name String Integer -- a_i
    deriving (Eq,Ord)

mkName = flip Name 0
instance Show Var where
    show (Name a i) = a ++ if i == 0 then "" else show i

instance Monad m => Applicative ( ReaderT r m) where
    (<*>) = ap
    pure = return


type Label =  Either Int String

data Pat = PVar Var Type | PUnit
    deriving Eq

instance Show Pat where
    showsPrec n (PVar v t) = showParen (n > 0) $ showsPrec n v . showChar ':' . showsPrec n t
    showsPrec _ PUnit = showString "()"


showLabel n (Left i) = showsPrec n i
showLabel _ (Right s) = showString s

type Location = Int

data Term = Var Var
          | App Term Term
          | Lam Pat Term
          | Fix Term
          | Ann Term Type
          | Rec [(String,Term)]
          | Proj Label Term
          | Unit
          | Nil Type
          | Cons Term Term
          | Head Term
          | Tail Term
          | IsNil Term
          | T
          | F
          | If Term Term Term
          | Z
          | S Term
          | Term :+: Term
          | IsZ Term
          | Eq Term Term
          | P Term
          | Inj Label Term Type
          | Case Term [(String,(Var,Term))]
-- zad2
          | Ref Term
          | Ass Term Term

          | Loc Location
          | Deref Term
          | Null

    deriving Eq

showParens s = showChar '(' . s . showChar ')'
showBraces s = showChar '{' . s . showChar '}'
showAngles s = showChar '<' . s . showChar '>'
showBrackets s = showChar '[' . s . showChar ']'

instance Show Term  where
   showsPrec _ (Var v) = shows v
   showsPrec _ Z = shows 0
   showsPrec _ T = showString "true"
   showsPrec _ F = showString "false"
   showsPrec _ Unit = showString "()"
   showsPrec _ Null = showString "nil"
   showsPrec n (App t s) = showParen (n >= 11) $
      showsPrec 1 t  .  showChar ' ' . showsPrec 11 s
   showsPrec n (Lam x t) = showParen (n >0) $
      showChar '\\' . shows x .
      showChar '.' . shows t
   showsPrec n (Fix t) = showParen (n > 0) $ showString "fix " . showsPrec n t
   showsPrec n (Ref t) = showParen (n > 0) $ showString "ref " . showsPrec n t
   showsPrec n (Proj l t) = showParen (n > 0) $ showsPrec n t . showChar '.' . showLabel n l
   showsPrec n (Rec [("1",t),("2",s)]) = showParen (n > 0) $
        showParens (showsPrec 1 t  .  showString " , "  .  showsPrec n s)
   showsPrec n (IsZ t) = showParen (n > 0) $ showString "zero? " . showsPrec n t
   showsPrec n (P t) = showParen (n > 0) $ showString "pred " . showsPrec n t
   showsPrec n (S m) | isNum m = let (VNat k) = toValue $ S m in showsPrec n k
   showsPrec n (S t) = showParen (n > 0) $ showString "succ " . showsPrec n t
   showsPrec n (If t1 t2 t3) = showParen (n > 0) $
        showString "if " . showsPrec n t1 . showString " then " . showsPrec n t2
        . showString " else " . showsPrec n t3
   showsPrec n (t1 :+: t2) = showParen (n > 0) $ showsPrec n t1 . showString " + " . showsPrec n t2
   showsPrec n (Eq t1 t2) = showParen (n > 0) $ showsPrec n t1 . showString " == " . showsPrec n t2
   showsPrec _ (Nil _) = showString "[]"
   showsPrec n (Ann t ty) = showParen (n > 0) $ showsPrec n t . showString " : " . showsPrec n ty
   showsPrec n (Cons t ts) =  showParen (n > 0) $ showsPrec n t  . showString " :: " . showsPrec n ts
   showsPrec n (Tail t ) = showParen (n > 0) $ showString "tail " .  showsPrec n t
   showsPrec n (Head t ) = showParen (n > 0) $ showString "head " .  showsPrec n t
   showsPrec n (IsNil t) = showParen (n > 0) $ showString "null? " .  showsPrec n t
   showsPrec n (Loc l) = showParen (n > 0) $ showString "loc: " . showsPrec n l
   showsPrec n (Ass t1 t2 ) = showParen (n > 0) $ showsPrec n t1 . showString " := " . showsPrec n t2
   showsPrec n (Deref t) =  showParen (n > 0) $ showChar '!' .  showsPrec n t



instance Show Type  where
   showList = flip $ foldr (\x -> showsPrec 1 x  .  showChar ' ')
   showsPrec _ TNat = showString "Nat"
   showsPrec _ TBool = showString "Bool"
   showsPrec _ TUnit = showString " () "
   showsPrec n (TRef t) = showParen (n > 0) $ showString "Ref " . showsPrec n t
--   showsPrec _ (TyVar v) = showV v
   showsPrec n (TAbs t s) = showParen (n > 0) $
        showsPrec 1 t  .  showString " -> "   .  shows s
   showsPrec n (TList t) = showParen (n > 0)  $
        showChar '[' . showsPrec n t . showChar ']'
   showsPrec n (TRec [("1",t),("2",s)]) = showParen (n > 0) $
        showsPrec 1 t  .  showString " * "  .  shows s
   -- showsPrec n (TRec ts) | and $ all (first (all isDigit)) ts = showParen (n>0) $
   -- showString "( " . (foldr (\fs s -> fs .  showString ","  .  s) (showString " )")  $ map (showsPrec n) $ map fst ts)
   -- showsPrec n (TRec ts) = showParen (n>0) showString "{" . (foldr (\(n,t) ->
   --    showString n . showString " = " . showsPrec n t .  showString ","  .)  (showString " }") ts)
   showsPrec n (TVariant [("1",t),("2",s)]) = showParen (n > 0) $
        showsPrec 1 t  .  showString " + "  .  shows s

data Type = TUnit
          | TRec [(String,Type)]
          | TVariant [(String,Type)]
          | TList Type
          | TNat
          | TBool
          | TAbs Type Type
          | TVar Int
-- zad2
          | TRef Type
    deriving Eq


data Value = VNat Int
           | VBool Bool
           | VUnit
           | VRec [(String,Value)]
           | VInj Label Value Type
           | VAbs Pat Value
           | VCons Value Value
           | VNil Type
-- zad2
           | VLoc Location
    deriving (Eq,Show)


type EnvT = (Var -> Type)
type Env  = (Var -> Maybe Term)

type Typer = Reader EnvT  Type

typeOfM :: Term -> Typer
typeOfM Unit = return TUnit
typeOfM T = return TBool
typeOfM F = return TBool
typeOfM Z = return TNat
typeOfM (Var v) = ($v) <$> ask
typeOfM (S t) = do
  TNat <- typeOfM t
  return TNat
typeOfM (P t) = do
  TNat <- typeOfM t
  return TNat
typeOfM (If t1 t2 t3) = do
  TBool <- typeOfM t1
  ty2 <- typeOfM t2
  ty3 <- typeOfM t3
  if ty2 == ty3 then return ty2 else fail ("type mismatch: " ++ show ty3 ++ " and  "++ show ty2)
typeOfM (t1 :+: t2) = do
  TNat <- typeOfM t1
  TNat <- typeOfM t2
  return TNat
typeOfM (IsZ t) = do
  TNat <- typeOfM t
  return TBool
typeOfM (Nil t) = return t
typeOfM (Rec t) = let (ls,tys) = unzip t
                 in (TRec . zip ls) <$> (mapM typeOfM tys)
typeOfM (Proj l t) = do
  TRec ts <- typeOfM t
  return $ project l ts
typeOfM (Ann t ty) = do
  ty1 <- typeOfM t
  if ty == ty1 then return ty else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOfM (App t1 t2) = do
  ty <- typeOfM t2
  TAbs ty1 ty2 <- typeOfM t1
  if ty == ty1 then return ty2 else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOfM (Cons t1 ts) = do
  ty1 <- typeOfM t1
  TList ty2 <- typeOfM ts
  if ty1 == ty2  then return (TList ty1) else fail ("type mismatch: " ++ show ty1 ++ " and " ++ show ty2)
typeOfM (Head t) = do
  TList ty <- typeOfM t
  return ty
typeOfM (Tail t) = do
  ty@(TList _)<- typeOfM t
  return ty
typeOfM (IsNil t) = do
  TList ty <- typeOfM t
  return TBool
typeOfM (Lam (PVar v ty1 ) t) = do
  ty <- local (\r x -> if x == v then  ty1 else r x) $ typeOfM t
  return $ TAbs ty1 ty
typeOfM (Lam PUnit t) = TAbs TUnit <$> typeOfM t
typeOfM (Fix t) = do
  TAbs ty ty1  <- typeOfM t
  if ty == ty1 then return ty else  fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOfM (Eq t1 t2) = do
  ty1 <- typeOfM t1
  ty2 <- typeOfM t2
  if ty1 == ty2 && canEq ty1 && canEq ty2 then return ty1 else fail ("type mismatch: " ++ show ty1 ++ " and  "++ show ty2)
typeOfM (Inj l t typ@(TVariant tys)) = do
  ty <- typeOfM t
  let ty1 = project l tys
  if ty == ty1 then return typ else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOfM (Case t alts) = do
  TVariant (ty:tys) <- typeOfM t
  let reduce = flip . flip foldM
  reduce (snd ty) tys $ \u (s,ty') -> do
     let (_,t') = project (Right s) alts
     ty'' <- typeOfM t'
     if ty'' == ty' && ty' == u then return u else fail ("type mismatch: " ++ show ty'' ++ " or  "++ show ty'' ++ " and " ++ show u)
-- zad2
typeOfM (Ref t) = TRef <$> typeOfM t
typeOfM (Ass t1 t2) = do
  TRef ty <- typeOfM t1
  ty' <- typeOfM t2
  if ty' == ty then return TUnit else  fail ("type mismatch: " ++ show ty ++ " and  "++ show ty')
typeOfM (Deref t) = do
  TRef ty <- typeOfM t
  return ty

typeOf env =  flip runReader env . typeOfM
typeOf' = typeOf (err "unbind type variable: " )

canEq TNat  = True
canEq TBool = True
canEq (TRec ts) = all (canEq.snd) ts
canEq (TList t) = canEq t
canEq _ = False


fv (Var v)  = S.singleton v
fv (App t1 t2) = fv t1 `S.union` fv t2
fv (Lam (PVar v _ ) t) = v `S.delete` fv t
fv (Lam PUnit t) =  fv t
fv (Fix t) = fv t
fv Unit = S.empty
fv (Nil _) = S.empty
fv (Cons  t1 t2) = fv t1 `S.union` fv t2
fv (Head  t)  = fv t
fv (Tail  t)  = fv t
fv  Z = S.empty
fv (S t) = fv t
fv (Ref t) = fv t
fv ( Ass t1 t2) =fv t1 `S.union` fv t2
fv ( Loc _ ) = S.empty
fv (Deref t) = fv t
fv (Ann t _) = fv t
fv (Rec ts)   = mconcat $ map (fv . snd) ts
fv (Proj _ t) = fv t
fv (Eq t1 t2) = fv t1 `S.union` fv t2
fv (Inj _ t _ ) = fv t
fv (IsZ t) = fv t
fv (t1 :+: t2) = fv t1 `S.union` fv t2
fv (If t1 t2 t3) = mconcat $ map fv [t1,t2,t3]
fv (P t) = fv t
fv (IsNil  t) = fv t
fv (Case t alt) = fv t `S.union` (mconcat $ map (uncurry S.delete . second fv . snd ) alt)
fv T = S.empty
fv F = S.empty
fv t = err "wtf: "  t


subst b s = subst'  where
    fvs = fv s
    subst' (Var a)| a == b = s
    subst' (Var a)  = Var a
    subst'  Z = Z
    subst' (S n) = S $ subst' n
    subst' (App (subst'-> t1) (subst' -> t2))= App t1 t2
    subst' (Ann t ty) = Ann (subst' t) ty
    subst' (Proj l t) = Proj l $ subst' t
    subst'  Unit = Unit
    subst'  t@(Nil _) =t
    subst'  (Cons t ts) = Cons (subst' t) (subst' ts)
    subst' (Head  t) = Head  $ subst' t
    subst' (Tail  t) = Tail  $ subst' t
    subst' (IsNil  t) = IsNil $ subst' t
    subst'  T = T
    subst'  F = F
    subst' (If t1 t2 t3) = If (subst' t1) (subst' t2) (subst' t3)
    subst' (t :+: t1) = subst' t :+: subst' t1
    subst' ( IsZ t) = IsZ $  subst' t
    subst' (Eq t1 t2) = Eq (subst' t1) (subst' t2)
    subst' (P t ) = P $ subst' t
    subst' (Inj l t ty) = Inj l (subst' t) ty
-- zad2
    subst' (Ref t) = Ref $ subst' t
    subst' (Ass t1 t2) = Ass (subst' t1) (subst' t2)
    subst' l@(Loc _) = l
    subst' (Deref t) = Deref $ subst' t
    subst' (Rec rec) = Rec $ map (second subst') rec
    subst' (Fix t)   = Fix $ subst' t
    subst' (Lam PUnit t) = subst' t
-- lambda..
    subst' (Case t alts) = Case (subst' t) $ map substAlt alts
    subst' t@(Lam (PVar a _ ) _ ) | b == a = t
    subst' (Lam (PVar a ty ) u) = Lam (PVar a' ty) $ subst' u'  where
         (a',u') = reName fvs a s u b
    substAlt a@(_,(v,_)) | v == b = a
    substAlt (l,(v,t)) = let (v',t') = reName fvs v s t b in (l,(v',subst' t'))

reName fvt a t u b = (a',u') where
    (a',u') =
       let (f,x) = occ (const fvt) a t
           uniq_t_v = flip bump' b $ bump a x
           (f',x') = occ fv uniq_t_v u
           a_uniq = if f' then bump uniq_t_v x' else uniq_t_v
       in if f then (a_uniq,subst a (Var a') u) else (a,u)

occ fv a = S.fold (\a' (f',a'')-> (f' || a' == a ,maxVar a'' a')) (False,Name "" 0) . fv
bump (Name name k) (Name _ j) = Name name $ succ $ max k j
bump' v@(Name _ _) v1@(Name _ _) = if v == v1 then bump v v1 else v
maxVar v@(Name _ x) v1@(Name _ x1) = if x > x1 then v else v1


isNum Z = True
isNum (S n) = isNum n
isNum _ = False

isBool F = True
isBool T = True
isBool _ = False

-- for products/tuples && for sums/variants
project = either (\i -> snd . (!!(i-1))) (\l ->  maybe (err "unknown label: " l) id. lookup l)


second f = \(x,y) -> (x,f y)
first f = \(x,y) -> (f x, y)

isVal Z = True
isVal (S v) = isVal v
isVal T = True
isVal F = True
isVal Unit = True
isVal (Nil _ ) = True
isVal (Lam _ _) = True
isVal (Rec rs) = all (isVal . snd) rs
isVal (Cons  v vs) = isVal v && isVal vs
isVal (Inj _ v _ ) = isVal v
isVal (Loc _) = True
isVal _ = False


toValue Z = VNat 0
toValue (S (toValue -> VNat n)) = VNat $ n + 1
toValue T = VBool True
toValue F = VBool False
toValue Unit = VUnit
toValue (Nil t ) = VNil t
toValue (Lam v t) = VAbs v (toValue t)
toValue (Rec rs) = VRec $ map (second toValue) rs
toValue (Cons v vs) = VCons  (toValue v) $ toValue vs
toValue (Inj l v t ) = VInj l (toValue v) t
toValue e = err "not a value: " e


data Memory = M { memory :: Array Location Term
                , freeCell :: [Location]
                , used :: Int
                }


alloc _ (M _ [] _ ) = error "memory exhausted"
alloc v (M m (fc:fcs) n) = (fc,M (m // [(fc,v)]) fcs $ n - 1)
deref l (M m _ _ ) = m ! l
update v l (M m fcs n) = M (m // [(l,v)]) fcs n

type Evaluator = ReaderT Env (StateT Memory Maybe) Term

evalStepOrNot t= evalStep t `mplus` return t

evalStep :: Term -> Evaluator
evalStep Z = fail "value"
evalStep T = fail "value"
evalStep F = fail "value"
evalStep (Var v) = maybe (err "unbound variable: " v) pure . ($v) =<< ask
evalStep (S n) | isNum n  = fail "value"
evalStep Unit = fail "value"
evalStep (Lam _ _) = fail "value"
evalStep (Nil _) = fail "value"
evalStep t@(Cons _ _) | isVal t = fail "value"
evalStep (S e) = S <$> evalStepOrNot e
evalStep (P Z) = return Z
evalStep (P (S e)) | isNum e = return e
evalStep (P e) = P <$> evalStepOrNot e
evalStep (If T e _ ) = return e
evalStep (If F _ e  ) = return e
evalStep (If eb e1 e2 ) =  evalStepOrNot eb >>= \b -> return (If b e1 e2)
evalStep (IsZ Z) = return T
evalStep (IsZ (S _ )) = return F
evalStep (IsZ e) =  IsZ <$> evalStepOrNot e
evalStep (Z :+: n) | isNum n = return n
evalStep (S n1 :+: n2) | isNum n1 && isNum n2 = return $ S $ n1 :+: n2
evalStep (n :+: e) | isNum n = (n :+:) <$>  evalStepOrNot e
evalStep (e1 :+: e2) = (:+: e2) <$> evalStepOrNot e1
evalStep (Eq Z Z ) = return T
evalStep (Eq Z n ) | isNum n = return F
evalStep (Eq n Z ) | isNum n = return F
evalStep (Eq T T ) = return T
evalStep (Eq F T ) = return F
evalStep (Eq T F ) = return T
evalStep (Eq (S n1) (S n2)) = return $ Eq n1 n2
{- w zasadzie zle, duze kroki wyszly
evalStep (Eq (Cons t x xs)  (Cons t1 y ys)) =
    let Just eqFun = lookup t eqDict
    in if eqFun x y then return T else Eq xs ys
-}

evalStep (Eq b e) | isVal b = Eq b <$> evalStepOrNot e
evalStep (Eq e1 e2) =  flip Eq e2 <$> evalStepOrNot e1
evalStep (App (Lam (PVar v _ ) t) v1) | isVal v1 =   return $ subst v v1 t
evalStep (App (Lam PUnit t) v1) | isVal v1  =  evalStepOrNot t
evalStep (App t1 t2) | isVal t1 =   App t1 <$> evalStepOrNot t2
evalStep (App t1 t2) =   flip App t2 <$> evalStepOrNot t1
evalStep a@(Fix (Lam (PVar v _ ) t)) =  return $ subst v a t
evalStep (Fix t) = Fix <$> evalStepOrNot t
evalStep (IsNil  (Nil _)) = return T
evalStep (IsNil  (Cons _ _)) = return F
evalStep (IsNil t) = IsNil  <$> evalStepOrNot t
evalStep (Cons t ts) | isVal t = Cons  t <$> evalStepOrNot ts
evalStep (Cons t ts) = flip Cons ts <$> evalStepOrNot t
evalStep (Head (Cons  v _)) = return v
evalStep (Head t) = Head  <$> evalStepOrNot t
evalStep (Tail  (Cons  _ t)) = return t
evalStep (Tail  t) = Tail  <$> evalStepOrNot t
evalStep (Ann t ty) = flip Ann ty <$> evalStepOrNot t
evalStep (Proj l (Rec ts)) = return $ project l ts
evalStep (Proj l t) = Proj l <$> evalStepOrNot t
evalStep (Rec ts) = let (ls,ts') = unzip ts
                        evalList [] = pure []
                        evalList (x:xs) | isVal x = (x:) <$>  evalList  xs
                        evalList (x:xs) = (:xs) <$> evalStepOrNot x
                    in (Rec . zip ls) <$> evalList ts'
evalStep (Case (Inj l v1 _) alt ) = do
     let (x,t1) = project l alt
     return $ subst x v1 t1
evalStep (Case t alt) = flip Case alt <$> evalStepOrNot t
evalStep (Inj l t ty) = (\v -> Inj l v ty) <$> evalStepOrNot t
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
evalStep e = err "imposible redex: "  e


emptyMemory = M (listArray (1,200) (replicate 200 Null)) [1..200] 200

evalStar' = evalStar (const Nothing)
evalStar env = flip evalStateT emptyMemory .  flip runReaderT  env . evalStarM
    where
      evalStarM t =  {-trace (show t ++ " ==>* ") $-} (evalStep t >>= evalStarM) `mplus` return t


evalStarGC' = evalStarGC (const Nothing)
evalStarGC env = flip evalStateT emptyMemory . flip runReaderT env . evalStarM
    where
      evalStarM t = {- trace (show t ++ " gc==>* ") -}  (evalStep t >>= \t -> gc t >> evalStarM t ) `mplus` return t


locations T = return []
locations F = return []
locations (Var v)  = maybe (return []) locations . ($v) =<< ask
locations (App t1 t2) = union <$> locations t1 <*> locations t2
locations (Lam _ t) = locations t
locations (Fix t) = locations t
locations Unit = return []
locations (Nil _) = return []
locations (Cons t1 t2) = union <$> locations t1 <*> locations t2
locations (Head  t)  = locations t
locations (Tail  t)  = locations t
locations  Z = return []
locations (S t) = locations t
locations (Ref t) = locations t
locations ( Ass t1 t2) = union <$> locations t1 <*> locations t2
locations ( Loc l ) = return  [l]
locations (Deref t) = locations t
locations (Ann t _) = locations t
locations (Rec ts)   = mconcat <$> mapM (locations . snd) ts
locations (Proj _ t) = locations t
locations (Eq t1 t2) = union <$> locations t1 <*> locations t2
locations (Inj _ t _ ) = locations t
locations (IsZ t) = locations t
locations (t1 :+: t2) = union <$> locations t1 <*> locations t2
locations (If t1 t2 t3) = mconcat <$> mapM locations [t1,t2,t3]
locations (P t) = locations t
locations (IsNil t) = locations t
locations (Case t alts) = union <$> locations t <*> (mconcat <$> mapM (locations . snd . snd ) alts)

gc t =  do
  mem <- memory <$> get
  n <- used <$> get
  let r = \l -> locations t >>= \ls -> reach mem ls l
  when (n <= 20) $  do
          (l,fc) <-  foldM (\(a,fc) e@(l,_) -> r l >>= \b -> return (if b then (e:a,fc) else ((l,Null):a,l:fc))) ([],[]) $ assocs mem
          put $ M (array (1,200) . reverse$l) fc (length fc)
      where
        reach mem ls l = (l `elem` ls ||) <$> foldM (\f l' -> (f || ) <$> (locations (mem ! l') >>= \ls' -> reach mem ls' l )) False ls


langDef = haskellStyle
          { reservedNames = [ "let","letrec","fun","in"
                            , "inl","inr","inj","case","of"
                            , "if","then","else","fix","true"
                            ,"false","nil","head","tail","null?"
                            ,"Nat","Bool","zero","ref","Ref"]
          , reservedOpNames = ["::","\\",";","=",".","+","succ","=="
                              ,"pred","zero?","=>","->","()",":","!",":="]
          }

lang = makeTokenParser langDef
ident = PTok.identifier lang
reserved = PTok.reserved lang
reservedOp = PTok.reservedOp lang
parens = PTok.parens lang
angles = PTok.angles  lang
brackets = PTok.brackets  lang
braces = PTok.braces lang
commaSep = PTok.commaSep lang
natural = PTok.natural lang

pTypeP = choice [try$parens pType,pNat,pBool,pTList,pTRec,pTUnit,pTTuple,pTRef,pTVariants] where
    pNat = const TNat <$> reserved "Nat"
    pBool = const TBool <$> reserved "Bool"
    pTList = TList <$> brackets pType
    pTUnit = const TUnit <$> reservedOp "()"
    pTRec = TRec <$> (braces .  commaSep $  (,) <$> ident <*> ( reservedOp ":" >>  pType))
    pTTuple = (TRec .  zip (map show [1..]) )  <$> (parens . commaSep $ pType)
    pTRef  = const TRef <$> reserved "Ref" <*> pType
    pTVariants = TVariant <$> (angles $ commaSep $ (,) <$> (either show id <$> pLabel) <*> (reservedOp ":" >> pType))

pType = buildExpressionParser [[tyOp "->" AssocRight, tyOp "*" AssocLeft, tyOp "+" AssocLeft]] 	pTypeP
tyOp s assoc = Infix ( do
    reservedOp s
    return $ case s of
	      "->" -> \t1 t2 -> TAbs t1  t2
	      "+"  -> \t1 t2 -> TVariant [("1",t1),("2",t2)]
	      "*"  -> \t1 t2 -> TRec  [("1",t1),("2",t2)]) assoc


pVar = mkName <$> ident  where
    mkName s = let (l,s') = span isDigit $ reverse s
               in Name (reverse s') $ if l == [] then 0 else read $ reverse l

pRecord = Rec <$> (braces .  commaSep $ (,) <$>  (ident <* reservedOp "=")  <*> pTerm)
pTuple = try$(Rec .  zip (map show [1..]) )  <$> (parens . commaSep $ pTerm)

pList = pNil <|> try pCons  where
    pNil = const Nil <$> reserved "nil" <*> (reservedOp ":" >> pType)
    pCons = Cons  <$> (pPrim <* reservedOp "::") <*>  pTerm

pHead = const Head  <$> reserved "head" <*> pTerm
pTail = const Tail  <$> reserved "tail" <*> pTerm
pNull = const IsNil <$> reserved "null?" <*> pTerm

pLabel = (Left . fromEnum) <$> natural <|> Right <$> ident

pProj = try$flip Proj <$> pPrim <*> (reservedOp "." >> pLabel )


pInj =  uncurry Inj <$> (angles $ (,) <$> pLabel <*> (reservedOp "=" >> pTerm)) <*> (reservedOp ":" >> pType)
pInr =  Inj (Left 2) <$> (reserved "inr"  >> pTerm) <*> (reservedOp ":" >> pType)
pInl =  Inj (Left 1) <$> (reserved "inl" >> pTerm) <*> (reservedOp ":" >> pType)

pCase = Case <$> (reserved "case" *> pTerm <* reserved "of") <*> (many1 $ curry assocl <$> (angles $ (,) <$> ident <*> (reservedOp "=" >> pVar))
                                                                                       <*> (reservedOp "=>" >> pTerm))
    where assocl ((a,b),c) = (a,(b,c))

pLam = Lam <$> (const PVar <$> reservedOp "\\" <*> pVar <*> (reservedOp ":" *> pType) ) <*> (reservedOp "." >> pTerm)

pPrim = choice [try$parens pTerm
               ,pRecord, pTuple
               ,const T <$> reserved "true", const F <$> reserved "false"
               ,const Z <$> reserved "zero",Var <$> pVar]
pLet =  mkLet <$> (reserved "let" >> pVar ) <*> (reservedOp ":" >> pType)
              <*> (reservedOp "=" >> pTerm) <*> (reserved "in"  >> pTerm) where
    mkLet v ty t1 t2 = App (Lam (PVar v ty ) t2) t1
pLetRec = mkLetRec <$> (reserved "letrec" >> pVar) <*> (reservedOp ":" >> pType)
                   <*> (reservedOp "=" >> pTerm) <*> (reserved "in"  >> pTerm) where
    mkLetRec v ty t1 t2 = App (Lam (PVar v ty) t2) (Fix (Lam (PVar v ty) t1))

pSeq = try (mkSeq <$> pPrim <*> (reservedOp ";" >> pTerm)) where
    mkSeq t1 t2 = App (Lam PUnit t2) t1

pRef = const Ref <$> reserved "ref" <*> pTerm
pAss = try (Ass <$> pPrim <*> (reserved ":=" >> pTerm))
pDeref = const Deref <$> reservedOp "!" <*> pTerm

runPp p = parse (PTok.whiteSpace lang  >> p) ""



pTerm = choice [ try$const Unit <$> reservedOp "()" , pLam
               , try pLet, pLetRec, pList
               , pCase, pInl, pInr, pInj
               , pList, pHead, pNull, pTail
               , pRef,pDeref,pAss
               , pProj, pExpr
               ]
expr' = choice [pNat,pPred, pSucc,pIsZ, pIf,pPrim] where
    pNat = toNat <$> natural
    pIsZ = IsZ  <$> (reserved "zero?"  *> pTerm)
    pIf = If <$> (reserved "if" *> pTerm) <*> (reserved "then" *> pTerm) <*> (reserved "else" *> pTerm)
    pSucc = S <$> (reserved "succ" *> pTerm)
    pPred = P <$> (reserved "pred" *> pTerm)
    toNat 0 = Z
    toNat n = S $ toNat $ pred n

pExpr = buildExpressionParser [
        [Infix (pure App) AssocLeft],
        [Infix (reserved "+" *>  pure (:+:)) AssocLeft ],
        [Infix (reserved "==" *>  pure Eq) AssocNone ]
       ] expr'

pDec = (,) <$> ident <*> (reserved "=" *> pTerm)

err :: Show a => String -> a -> b
err msg = error . (msg ++ ) . show

parser' = either (err "parse error: ") id . runPp pDec
parser = either (err "parse error: ") id . runPp pTerm

mkF  n t = \x -> if x == mkName n then Just t else  Nothing
combEnv f g = \x ->  maybe (g x) Just $ f x
combEnvT f g = \x ->  maybe (g x) id $ f x

type ReplState = (EnvT,Env,Bool)

emptyState :: ReplState
emptyState = (err "unbound type variable: ",const Nothing,False)

repl :: StateT ReplState (InputT IO) ()
repl = do
  inp <- lift $ getInputLine "> "
  (envT,env,gc) <- get
  let eval = if gc then evalStarGC else evalStar
  case inp of
    Nothing -> return ()
    Just ":q" -> return ()
    Just ":gc" -> if gc then
                      put (envT,env,False) >> lift (outputStrLn "gc off")
                  else
                      put (envT,env,True) >> lift (outputStrLn "gc on")
    Just (':':'l':' ':file)  -> do
             decs <- either (err "parse error: ") id  <$> (liftIO $ parseFromFile (PTok.whiteSpace lang >> pDec `endBy1` semi lang) file )
             forM_ decs $ \(n,t) ->  addToEnv n t
    Just (':':'t':' ':rest)  -> let t = parser rest in lift $ outputStrLn $ show t ++ " : " ++  show (typeOf envT $ t)
  --  Just (':':'e':rest)   -> lift $ outputStrLn $ show $ env $ parser rest
    Just (':':'a':' ':rest)  -> uncurry addToEnv $ parser' rest
    Just exp -> lift . outputStrLn . show $ eval env $ parser exp
  repl
      where
        addToEnv n t =  do
            (envT,env,gc) <- get
            let ty = typeOf envT t
                envT' = combEnvT (mkF n ty) envT
                env'  = combEnv (mkF n t) env
            put (envT',env',gc) >> lift (outputStrLn (n ++ " = " ++ show t ++ " : " ++ show ty))

main = runInputT defaultSettings $ runStateT repl emptyState


-- raise e ->^{e} ..
-- s1;s1

-- wyjatki:
-- przeliczalny zbior wyjatkow,
-- zglaszenie wyjatkow `raise e` gdzie e jest jakims wyjatkiem
-- oblusga wyjatkow, f `catch` (\e -> g)
-- typy: przegladamy funkcje, w jej typie umieszczamy informacje o potencjalnych wyjatkach
-- tj szukamy wyrazen typu `raise e` i tworzymy krotke/liste potencjalnych wyjatkow
-- z listy wyjatkow usuwamy wszystkie zlapane wyjatki
