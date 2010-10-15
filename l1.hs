{-# LANGUAGE ViewPatterns #-}

data Exp = T | F | If Exp Exp Exp | Z | S Exp | Exp :+: Exp | IsZ Exp | Eq Exp Exp | P Exp
data Value = N Int | B Bool

data T = Natural | Boolean deriving Eq
newtype Type = Maybe T

evalStep Z = N 0
evalStep T = B True
evalStep F = B False
evalStep (S)


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
evalBig (If (evalBig -> B b) e1 e2) = if b then e1 else e2


typeOf T = Just Boolean
typeOf F = Just Boolean
typeOf Z = Just Natural
typeOf (S (typeOf -> Just Natural)) = Just Natural
typeOf ((typeOf -> Just Natural) :+: (typeOf -> Just Natural)) = Just Natural
typeOf (IsZ (typeOf -> Just Natural)) = Just Boolean
typeOf (If (typeOf -> Just Boolean) e1 e2) | typeOf e1 == typeOf e2 = maybe Nothing id  $ typeOf e1
typeOf (Eq (typeOf -> Just t1) (typeOf -> Just t2)) | t1 == t2 = Boolean
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
checkType a (If (checkType Boolean -> True) (checkType a -> True) (checkType a -> True)) = a
checkType _ _ = False