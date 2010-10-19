{-# LANGUAGE ViewPatterns, FlexibleInstances #-}
module Main where

import Data.Function
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Control.Applicative
import Control.Monad(ap,forever)
import Control.Arrow
import Data.Char

data Exp = T | F | If Exp Exp Exp | Z | S Exp | Exp :+: Exp | IsZ Exp | Eq Exp Exp | P Exp
         deriving (Eq,Show)
data Value = N Int | B Bool
           deriving Show

data T = Natural | Boolean deriving (Eq,Show)
newtype Type = Maybe T



isNum Z = True
isNum (S n) = isNum n
isNum _ = False

isBool F = True
isBool T = True
isBool _ = False


evalStep Z = Nothing
evalStep T = Nothing
evalStep F = Nothing
evalStep (S n) | isNum n  = pure $ S n
evalStep (S e) = S <$> evalStep e
evalStep (P Z) = pure Z
evalStep (P (S e)) | isNum e = pure e
evalStep (P e) = P <$> evalStep e
evalStep (If T e _ ) = pure e
evalStep (If F _ e  ) = pure e
evalStep (If eb e1 e2 ) = evalStep eb >>= \b -> pure (If b e1 e2)
evalStep (IsZ Z) = pure T
evalStep (IsZ (S e )) | isNum e  = pure F
evalStep (IsZ e) | isNum e = IsZ <$> evalStep e
evalStep (Z :+: n) | isNum n = pure n
evalStep (S n1 :+: n2) | isNum n1 && isNum n2 = pure $ S $ n1 :+: n2
evalStep (n :+: e) | isNum n = (n :+:) <$>  evalStep e
evalStep (e1 :+: e2) = (:+: e2) <$> evalStep e1
evalStep (Eq Z Z ) = pure T
evalStep (Eq Z n ) | isNum n = pure F
evalStep (Eq n Z ) | isNum n = pure F
evalStep (Eq T T ) = pure T
evalStep (Eq F T ) = pure F
evalStep (Eq T F ) = pure T
evalStep (Eq b e) | isBool b = Eq b <$> evalStep e
evalStep (Eq e1 e2) = flip Eq e2 <$> evalStep e1

evalStar :: Exp -> Value
evalStar e = case evalStep e of
               Nothing | isNum e  -> N $ toInt e
               Nothing | isBool e -> B $ toBool e
               Just e' -> evalStar e'
    where
      toBool T = True
      toBool F = False

      toInt Z = 0
      toInt (S n) = succ $ toInt n


evalBig :: Exp -> Value
evalBig T = B True
evalBig F = B False
evalBig Z = N 0
evalBig (S (evalBig -> N n)) =  N $ succ n
evalBig (P (evalBig -> N 0)) = N 0
evalBig (P (evalBig -> N n)) = N $ pred n
evalBig (Eq (evalBig -> N n1) (evalBig -> N n2)) = B $ n1 == n2
evalBig (Eq (evalBig -> B b1) (evalBig -> B b2)) = B $ b1 == b2
evalBig ((evalBig -> N n1) :+: (evalBig -> N n2)) = N $ n1 + n2
evalBig (IsZ (evalBig -> N n)) = B $ n==0
evalBig (If (evalBig -> B b) e1 e2) = evalBig $ if b then e1 else e2


typeOf T = Just Boolean
typeOf F = Just Boolean
typeOf Z = Just Natural
typeOf (S (typeOf -> Just Natural)) = Just Natural
typeOf ((typeOf -> Just Natural) :+: (typeOf -> Just Natural)) = Just Natural
typeOf (IsZ (typeOf -> Just Natural)) = Just Boolean
typeOf (If (typeOf -> Just Boolean) e1 e2) | typeOf e1 == typeOf e2 = typeOf e1
typeOf (Eq (typeOf -> Just t1) (typeOf -> Just t2)) | t1 == t2 = Just Boolean
typeOf _ = Nothing

checkType Boolean T  = True
checkType Boolean F  = True
checkType Natural Z  = True
checkType Natural (S (checkType Natural -> True)) = True
checkType Natural (P (checkType Natural -> True)) = True
checkType Natural ((checkType Natural -> True) :+: (checkType Natural -> True)) = True
checkType Natural (Eq (checkType Natural -> True) (checkType Natural -> True)) = True
checkType Boolean (Eq (checkType Boolean -> True) (checkType Boolean -> True)) = True
checkType Boolean (IsZ (checkType Natural -> True)) = True
checkType a (If (checkType Boolean -> True) (checkType a -> True) (checkType a -> True)) = True
checkType _ _ = False

instance Applicative (GenParser Char st ) where
    pure = return
    (<*>) = ap

lexme p = do {spaces ;  x <- p ; spaces ; return x} where
    spaces = skipMany $ satisfy isSpace
keyword  = fmap (const ())  .  lexme . string

expr' = choice [ pT, pF, pNat, pSucc, pPred, pIsZ, pIf,parens expr] where
    pT = keyword "true" >> pure T
    pF = keyword "false" >> pure F
    pNat = (toNat  . read ) <$> many1 digit
    pIsZ = IsZ  <$> (keyword "zero?"  *> expr)
    pIf = If <$> (keyword "if" *> expr) <*> (keyword "then" *> expr') <*> (keyword "else" *> expr')
    pSucc = S <$> (keyword "succ" *> expr)
    pPred = P <$> (keyword "pred" *> expr)
    toNat 0 = Z
    toNat n = S $ toNat $ pred n
    parens p = keyword "(" *> p <* keyword ")"

expr = buildExpressionParser [
        [Infix (keyword "+" *>  pure (:+:)) AssocLeft ],
        [Infix (keyword "=" *>  pure Eq) AssocNone ]
       ] expr'
parser = parse expr ""

repl = forever $
  print . (evalBig  &&& maybe (error "Cannot infer correct type") id . typeOf) . either (error.show) id . parse expr "" =<< getLine

main = putStrLn "to exit C-c" >> repl