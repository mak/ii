-- {-# OPTIONS_GHC -Wall #-}

{-# LANGUAGE
  NoMonomorphismRestriction
  #-}

import Control.Monad.Reader
import Control.Monad.State

type ClassName  = Name
type MethodName = Name
type TermName   = Name
type FieldName  = Name

type Field = (ClassName,FieldName)
data Class = Class { cname    :: ClassName
                   , csuper   :: ClassName
                   , cconstr  :: Const
                   , cfields :: [Field]
                   , cmethods :: [MDecl]
                   }

data Const = Cons { cnsname   :: ClassName
                  , superArgs :: [Field]
                  , thisArgs  :: [Field]
                  , superInit :: [FieldName]
                  , thisInit  :: [(FieldName,FieldName)]
                  }

data MDecl = MDecl { mname :: MethodName
                   , margs :: [(ClassName,TermName)]
                   , mbody_ :: Term
                   , mresType :: ClassName
                   }

data Term = Var TermName
          | Field Term FiledName | Method Term MethodName [Term]
          | New ClassName [Term] | Cast ClassName Term
data Value = VNew ClassName [Value]

data Type = ClassType ClassName  | Arr [ClassName] ClassName

findMethod m = find ((==m) . mname ) . cmethods
findField  f vs = maybe (error "bum" ) (return . (!!vs)) $ findIndex (==f)

fields c= go . ($c) =<< ask where
    go (Class {name = n}) | n == "Object" = return []
    go c = return $ cfields c ++ fields (csuper c))

mtype m c = go . ($c) =<< ask  where
    go c | Just mdec <- findMethod m = return $ Arr (map ClassType $margs mdec) (ClassType $ mresType mdec)
    go c = mtype $ csuper c

mbody m c= go . ($c) =<< ask  where
    go c | Just mdec <- findMethod m = return (map snd (margs mdec),mbody_ mdec)
    go c = mbody m $ csuper c

subtype c e | c == "Object" = return False
subtype c e | c == e = return True
subtype c e =  go . ($c) =<< ask where
    go c | e == csuper c = return True
    go c  = subtype (csuper c) e

deType (ClassType cn) = cn

typeOf (Var x) = ($x) =<< get
typeOf (Field t f) = do
  c0 <- deType <$> typeOf t
  fs <- fields c0
  (ClassType . fst) <$> findField f fs fs
typeOf (Method t mn ts) = do
  tys <- map deType <$> mapM typeOf ts
  c0  <- deType <$> typeOf t
  Arr ds ty <- mtype m c0
  f <- and <$> zipWithM (uncurry subtype) (zip tys ds)
  if f then return (ClassType ty) else error "blad"
typeOf (New cn ts) = do
  tys <- map deType <$> mapM typeOf ts
  fs <- map snd <$>fields cn
  f <- and <$> zipWithM (uncurry subtype) (zip tys fs)
  if f then return (ClassType cn) else error "blad"
typeOf (Cast cn t) = do
  dn <- deType <$> typeOf t
  f <- subtype dn cn
  f' <- subtype cn dn
  if f || (f' && cn /= dn) then
      return (ClassType cn)
   else  error "blad"

typeOfMethod cn md = do
  env = foldr (\(t,x) y -> \v -> if v == x then t else y v)
              (\x -> if x == "this" then ClassType cl else  error "unboud varible")
              $ margs md
  e0 <- evalStateT (typeOf $ mbody_ md) env
  f  <- subtype e0 (mresType md)
  cl <- ($cn) <$> ask
  f' <- override m (csuper cl) (Arr (map fst $ margs md) (mresType md))
  return $ if f && f' then Just cn else Nothing

typeOfClass cd = do
  fs <- fields (csupercd)
  Just _ <- sequence <$> mapM (typeOfMethod (cname cd)) (cmethods cd)
  let cstr = cconstr cd
      f1 = superInit cstr == map fst (superArgs cstr) &&  fs == superArgs cstr
      f2 = and $ zipWith (\(_,fa) (tf,if) -> fa == tf && tf == if) (thisArgs cstr) (thisInit cstr)
  return $ if f1 && f2 then Just (cname cd) else Nothing



isVal (New _ vs) = all isVal vs
isVal _ = False


evalList [] = pure []
evalList (x:xs) | isVal x = (x:) <$>  evalList  xs
evalList (x:xs) = (:xs) <$> evalStepOrNot x

evalStepOrNot t= evalStep t `mplus` return t

evalStep (New cn vs) | all isVal vs = fail "value"
evalStep (Field (New cn vs) f) | all isVal vs = (findField vs .  map snd) <$> fields cn
evalStep (Cast dn a@(New cn vs)) | all isVal vs = do { f <- subtype cn dn; if f then return a else error "cant cast this"}
evalStep (Method v mn ts) | isVal v = Method v mn  <$> evalStepOrNot t
evalStep (Method t mn ts) = (\v -> Method v mn ts) <$> evalList ts
evalStep (New cn ts)  = New cn <$> evalList ts
evalStep (Cast c t) = Cast c <$> evalStep t
evalStep (Field t f) = flip Field f <$> evalStepOrNot t

