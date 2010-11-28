-- {-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE
   OverloadedStrings
  ,NoMonomorphismRestriction
  ,ViewPatterns
  ,TypeFamilies
  #-}

-- import GHC.Exts
import Control.Monad.Reader
import Control.Monad.State
import Control.Applicative hiding ((<|>))
import Data.Map (Map)

import Text.Parsec hiding (State)
import Text.Parsec.Expr
import Text.Parsec.Token hiding (reservedOp,reserved,parens,angles,brackets,braces, identifier,commaSep,natural)
import Text.Parsec.Language
import qualified Text.Parsec.Token as PTok


{-
data Var = Name String Integer -- a_i
    deriving (Eq,Ord)

mkName = flip Name 0
instance Show Var where
    show (Name a i) = a ++ show i

instance IsString Var where
    fromString = mkName

instance IsString Term where
    fromString = Var . mkName
-}

type Label =  Either Int String

data Pat = PVar String | PUnit
    deriving (Eq,Show)

data Term = Var String
          | App Term Term
          | Lam Pat Term
          | Fix Term
          | Ann Term Type
          | Rec [(String,Term)]
          | Proj Label Term
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
          | Inj Label Term Type
          | Case Term [(String,(String,Term))]
    deriving (Eq,Show)

data Type = TUnit
          | TRec [(String,Type)]
          | TVariant [(String,Type)]
          | TList Type
          | TNat
          | TBool
          | TAbs Type Type
          | TVar Int
    deriving (Eq,Show)


data Value = VNat Int
           | VBool Bool
           | VUnit
           | VRec [(String,Value)]
           | VInj Label Value Type
           | VAbs Pat Value
           | VCons Type Value Value
           | VNil Type
    deriving (Eq,Show)


type EnvT = (String -> Type)
type Env  = (String -> Term)

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
typeOfM (IsNil ty t) = do
  TList ty1 <- typeOfM t
  if ty == ty1 then return TBool else fail ("type mismatch: " ++ show ty ++ " and  "++ show ty1)
typeOfM (Lam (PVar v) t) = do
  tv <- newTVar
  ty <- local (\r x -> if x == v then  tv else r x) $ typeOfM t
  return $ TAbs tv ty
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

typeOf = flip evalState 0 . flip runReaderT (error . ("unbind type variable: " ++) . show ) . typeOfM

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

-- for products/tuples && for sums/variants
project = either (\i -> snd . (!!i)) (\l ->  maybe (error $ "unknown label: " ++ show l) id. lookup l)


second f = \(x,y) -> (x,f y)

isVal Z = True
isVal (S v) = isVal v
isVal T = True
isVal F = True
isVal Unit = True
isVal (Nil _ ) = True
isVal (Lam _ _) = True
isVal (Rec rs) = all (isVal . snd) rs
isVal (Cons _ v vs) = isVal v && isVal vs
isVal (Inj _ v _ ) = isVal v


toValue Z = VNat 0
toValue (S (toValue -> VNat n)) = VNat $ n + 1
toValue T = VBool True
toValue F = VBool False
toValue Unit = VUnit
toValue (Nil t ) = VNil t
toValue (Lam v t) = VAbs v (toValue t)
toValue (Rec rs) = VRec $ map (second toValue) rs
toValue (Cons t v vs) = VCons t (toValue v) $ toValue vs
toValue (Inj l v t ) = VInj l (toValue v) t


type Evaluator = ReaderT Env Maybe Term

evalStep :: Term -> Evaluator
evalStep Z = fail "value"
evalStep T = fail "value"
evalStep F = fail "value"
evalStep (Var _) = fail "value"
evalStep (S n) | isNum n  = fail "value"
evalStep Unit = fail "value"
evalStep (Lam _ _) = fail "value"
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

evalStep (App t1 t2) | isVal t1 = App t1 <$> evalStep t2
evalStep (App (Lam (PVar v) t) v1)  = local (\r x -> if x == v then v1 else r x) $ evalStep t
evalStep (App (Lam PUnit t) v1)  =  evalStep t
evalStep (App t1 t2) = flip App t2 <$> evalStep t1
evalStep a@(Fix (Lam (PVar v) t)) = local (\r x -> if x == v then a else r x) $ evalStep t
evalStep (Fix t) = Fix <$> evalStep t
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
evalStep (Case (Inj l t _) alt ) =
    let (v,t1) = project l alt
    in local (\r x -> if x == v then t else r x) $ evalStep t1
evalStep (Case t alt) = flip Case alt <$> evalStep t
evalStep (Inj l t ty) = (\v -> Inj l v ty) <$> evalStep t

evalStar = maybe ( error "huh imposible happens")  toValue . flip runReaderT  (err "unbound variable: ") . evalStarM
    where
          err msg = error . (msg ++) . show
          evalStarM t =  (evalStep t >>= evalStarM) `mplus` return t


langDef = haskellStyle
          { reservedNames = [ "let","letrec","fun","in"
                            , "inl","inr","inj","case","of"
                            , "if","then","else","fix","true"
                            ,"false","nil","head","tail","null"
                            ,"Nat","Bool","zero"]
          , reservedOpNames = ["::","\\",";","=",".","+","succ","=="
                              ,"pred","zero?","=>","->","()",":"]
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

pTypeP = choice [try$parens pType,pNat,pBool,pTList,pTRec,pTUnit,pTTuple,pTVariants] where
    pNat = const TNat <$> reserved "Nat"
    pBool = const TBool <$> reserved "Bool"
    pTList = TList <$> brackets pType
    pTUnit = const TUnit <$> reservedOp "()"
    pTRec = TRec <$> (braces .  commaSep $  (,) <$> ident <*> ( reservedOp ":" >>  pType))
    pTTuple = (TRec .  zip (map show [1..]) )  <$> (parens . commaSep $ pType)
    pTVariants = TVariant <$> (angles $ commaSep $ (,) <$> (either show id <$> pLabel) <*> (reservedOp ":" >> pType))

pType = buildExpressionParser [[tyOp "->" AssocRight, tyOp "*" AssocLeft, tyOp "+" AssocLeft]] 	pTypeP
tyOp s assoc = Infix ( do
    reservedOp s
    return $ case s of
	      "->" -> \t1 t2 -> TAbs t1  t2
	      "+"  -> \t1 t2 -> TVariant [("1",t1),("2",t2)]
	      "*"  -> \t1 t2 -> TRec  [("1",t1),("2",t2)]) assoc


getType (Nil t) = t
getType (Cons t _ _) = t

pRecord = Rec <$> (braces .  commaSep $ (,) <$>  (ident <* reservedOp "=")  <*> pTerm)
pTuple = try$(Rec .  zip (map show [1..]) )  <$> (parens . commaSep $ pTerm)

pList = pNil <|> pCons  where
    pNil = const Nil <$> reserved "nil" <*> (reservedOp ":" >> pType)
    pCons = try $ (\x xs -> Cons (getType xs) x  xs) <$> (pPrim <* reservedOp "::") <*>  pList

pHead = (\_ xs -> Head (getType xs) xs) <$> reserved "head" <*> pList
pTail = (\_ xs -> Tail (getType xs) xs) <$> reserved "tail" <*> pList
pNull = (\_ xs -> IsNil (getType xs) xs) <$> reserved "null" <*> pList

pLabel = (Left . fromEnum) <$> natural <|> Right <$> ident

pProj = try$flip Proj <$> pPrim <*> (reservedOp "." >> pLabel )


pInj =  uncurry Inj <$> (angles $ (,) <$> pLabel <*> (reservedOp "=" >> pTerm)) <*> (reservedOp ":" >> pType)
pInr =  Inj (Left 2) <$> (reserved "inr"  >> pTerm) <*> (reservedOp ":" >> pType)
pInl =  Inj (Left 1) <$> (reserved "inl" >> pTerm) <*> (reservedOp ":" >> pType)
pCase = Case <$> (reserved "case" *> pTerm <* reserved "of") <*> (many1 $ curry assocl <$> (angles $ (,) <$> ident <*> (reservedOp "=" >> ident))
                                                                                       <*> (reservedOp "=>" >> pTerm))
    where assocl ((a,b),c) = (a,(b,c))

pLam = Lam <$> (const PVar <$> reservedOp "\\" <*> ident ) <*> (reservedOp "." >> pTerm)
pApp = App <$> pPrim <*> pPrim
pPrim = choice [try$parens pTerm
               ,pRecord, pTuple
               ,const T <$> reserved "true", const F <$> reserved "false"
               ,const Z <$> reserved "zero",Var <$> ident]
pLet =  mkLet <$> (reserved "let" >> ident) <*> (reservedOp "=" >> pTerm) <*> (reserved "in"  >> pTerm) where
    mkLet v t1 t2 = App (Lam (PVar v) t2) t1
pLetRec = mkLetRec <$> (reserved "letrec" >> ident) <*> (reservedOp "=" >> pTerm) <*> (reserved "in"  >> pTerm) where
    mkLetRec v t1 t2 = App (Lam (PVar v) t2) (Fix (Lam (PVar v) t1))

pSeq = mkSeq <$> pTerm <*> (reservedOp ";" >> pTerm) where
    mkSeq t1 t2 = App (Lam PUnit t2) t1

runPp p = parse p ""


pTerm = choice [ try$const Unit <$> reservedOp "()" , try pLam, try pApp
               , try pLet, pLetRec
               , pCase, pInl, pInr, pInj
               , pList, pHead, pNull, pTail
               , pProj, pExpr
               ]
expr' = choice [pNat,pPred, pIsZ, pIf,pPrim] where
    pNat = toNat <$> natural
    pIsZ = IsZ  <$> (reserved "zero?"  *> pTerm)
    pIf = If <$> (reserved "if" *> pTerm) <*> (reserved "then" *> pTerm) <*> (reserved "else" *> pTerm)
    pSucc = S <$> (reserved "succ" *> pTerm)
    pPred = P <$> (reserved "pred" *> pTerm)
    toNat 0 = Z
    toNat n = S $ toNat $ pred n

pExpr = buildExpressionParser [
        [Infix (reserved "+" *>  pure (:+:)) AssocLeft ],
        [Infix (reserved "==" *>  pure Eq) AssocNone ]
       ] expr'




-- class Memory m where
--     data Mem :: *
--     data Address :: *
--     alloc :: Mem -> a -> Mem
--     (!) :: Mem -> Address -> a
-- --    (:=) :: Address -> a -> (Memory -> ())




