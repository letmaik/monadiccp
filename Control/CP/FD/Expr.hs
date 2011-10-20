{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers & Pieter Wuille
 -}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.CP.FD.Expr (
  Expr(..),
  ToExpr(..),
  ExprKey(..),
  unExprKey
) where 

import GHC.Exts (sortWith)
import qualified Control.CP.PriorityQueue as PriorityQueue
import qualified Data.Sequence

import Control.CP.SearchTree hiding (label)
import Control.CP.Transformers
import Control.CP.ComposableTransformers
import Control.CP.Queue
import Control.CP.Solver
import Control.CP.EnumTerm
import Control.CP.Debug
import Control.CP.Mixin

-- some simple kinds of expressions
data Expr t =
    Term t
  | Const Integer
  | Plus (Expr t) (Expr t)
  | Minus (Expr t) (Expr t)
  | Mult (Expr t) (Expr t)
  | Div (Expr t) (Expr t)
  | Mod (Expr t) (Expr t)
  | Abs (Expr t)
  deriving (Show,Eq)

varrefs :: forall s. Expr s -> Int
varrefs (Term _) = 1
varrefs (Const _) = 0
varrefs (Plus a b) = varrefs a + varrefs b
varrefs (Minus a b) = varrefs a + varrefs b
varrefs (Mult a b) = varrefs a + varrefs b
varrefs (Div a b) = varrefs a + varrefs b
varrefs (Mod a b) = varrefs a + varrefs b
varrefs (Abs a) = varrefs a

simplify :: (Eq s, Show s) => Expr s -> Expr s
-- simplification rules (either decrease # of variable references, or leave that equal and decrease # of tree nodes)
--- level 0 (result in a final expression)
simplify (Mult (Const 0) _) = Const 0
simplify (Div (Const 0) _) = Const 0
simplify (Mod (Const 0) _) = Const 0
simplify (Mod _ (Const 1)) = Const 0
simplify (Mod _ (Const (-1))) = Const 0
simplify (Mod (Mult (Const a) b) (Const c)) | (a `mod` c)==0 = Const 0
simplify (Minus a b) | a==b = Const 0
simplify (Plus (Const a) (Const b)) = Const (a+b)
simplify (Minus (Const a) (Const b)) = Const (a-b)
simplify (Mult (Const a) (Const b)) = Const (a*b)
simplify (Div (Const a) (Const b)) = Const $ (a `div` b)
simplify (Abs (Const a)) = Const (abs a)
simplify (Mod (Const a) (Const b)) = Const $ (a `div` b)
simplify (Plus (Const 0) a) = a
simplify (Mult (Const 1) a) = a
simplify (Div a (Const 1)) = a
--- level 1 (result in one recursive call to simplify)
simplify (Plus a b) | a==b = 2 * a
simplify (Div a (Const (-1))) = negate a
simplify (Plus (Const c) (Plus (Const a) b)) = (Const $ c+a) + b
simplify (Plus (Const c) (Minus (Const a) b)) = (Const $ c+a) - b
simplify (Minus (Const c) (Plus (Const a) b)) = (Const $ c-a) - b
simplify (Minus (Const c) (Minus (Const a) b)) = (Const $ c-a) + b
simplify (Mult (Const c) (Mult (Const a) b)) = (Const $ a*c) * b
simplify (Div (Mult (Const a) b) (Const c)) | (a `mod` c)==0 = (Const (a `div` c)) * b
--- level 2 (result in two recursive calls to simplify)
simplify (Plus a (Mult b c)) | a==b && ((varrefs a)>0) = (c+1) * a
simplify (Plus a (Mult b c)) | a==c && ((varrefs a)>0) = (b+1) * a
simplify (Plus (Mult b c) a) | a==b && ((varrefs a)>0) = (c+1) * a
simplify (Plus (Mult b c) a) | a==c && ((varrefs a)>0) = (b+1) * a
simplify (Plus (Mult a b) (Mult c d)) | a==c = (b+d) * a
simplify (Plus (Mult a b) (Mult c d)) | a==d = (b+c) * a
simplify (Plus (Mult a b) (Mult c d)) | b==c = (a+d) * b
simplify (Plus (Mult a b) (Mult c d)) | b==d = (a+c) * b
simplify (Minus a (Mult b c)) | a==b && ((varrefs a)>0) = (1-c) * a
simplify (Minus a (Mult b c)) | a==c && ((varrefs a)>0) = (1-b) * a
simplify (Minus (Mult b c) a) | a==b && ((varrefs a)>0) = (c-1) * a
simplify (Minus (Mult b c) a) | a==c && ((varrefs a)>0) = (b-1) * a
simplify (Minus (Mult a b) (Mult c d)) | a==c = (b-d) * a
simplify (Minus (Mult a b) (Mult c d)) | a==d = (b-c) * a
simplify (Minus (Mult a b) (Mult c d)) | b==c = (a-d) * b
simplify (Minus (Mult a b) (Mult c d)) | b==d = (a-c) * b
simplify (Mult (Abs a) (Abs b)) = abs (a*b)
simplify (Div (Abs a) (Abs b)) = abs (a `div` b)
-- reordering rules (do not decrease # of variables or # of tree nodes, but normalize an expression in such a way that the same normalization cannot be applied anymore - possibly because that can only occur in a case already matched by a simplification rule above)
--- level 1
simplify (Plus a (Const c)) = (Const c) + a
simplify (Minus a (Const c)) = (Const (-c)) + a
simplify (Mult a (Const c)) = (Const c) * a
simplify (Mult (Const (-1)) a) = negate a
--- level 2
simplify (Mult (Const c) (Plus (Const a) b)) = (Const (a*c)) + ((Const c)*b)
simplify (Mult (Const c) (Minus (Const a) b)) = (Const (a*c)) - ((Const c)*b)
simplify (Plus a (Plus (Const b) c)) = (Const b) + (a+c)
simplify (Plus a (Minus (Const b) c)) = (Const b) + (a-c)
simplify (Minus a (Plus (Const b) c)) = (Const (-b)) + (a-c)
simplify (Minus a (Minus (Const b) c)) = (Const (-b)) + (a+c)
simplify (Mult a (Mult (Const b) c)) = (Const b) * (a*c)
simplify (Plus (Plus (Const a) b) c) = (Const a) + (b+c)
simplify (Plus (Minus (Const a) b) c) = (Const a) + (c-b)
simplify (Minus (Plus (Const a) b) c) = (Const a) + (b-c)
simplify (Minus (Minus (Const a) b) c) = (Const a) - (b+c)
simplify (Mult (Mult (Const a) b) c) = (Const a) * (b*c)
simplify (Mult a (Minus (Const 0) b)) = negate (a*b)
simplify (Mult (Minus (Const 0) b) a) = negate (a*b)
simplify (Div (Minus (Const 0) a) b) = negate $ a `div` b
simplify (Div a (Minus (Const 0) b)) = negate $ a `div` b
-- fallback rule
simplify a = a

instance (Eq s, Show s) => Num (Expr s) where
  a + b = simplify $ Plus a b
  a - b = simplify $ Minus a b
  a * b = simplify $ Mult a b
  abs a = simplify $ Abs a
  negate a = 0 - a
  fromInteger c = Const $ fromInteger c
  signum (Const a) = Const (signum a)
  signum a = error "signum not possible for generic Expr"

instance (Eq s, Show s) => Ord (Expr s) where
  compare (Const x) (Const y) = compare x y
  compare _ _ = error "compare not possible for generic Expr"

instance (Eq s, Show s) => Real (Expr s) where
  toRational (Const x) = toRational x
  toRational _ = error "toRational not possible for generic Expr"

instance (Eq s, Show s) => Enum (Expr s) where
  succ a = a + 1
  pred a = a - 1
  toEnum = Const . toEnum
  fromEnum (Const a) = fromEnum a
  fromEnum _ = error "fromEnum not possible for generic Expr"

instance (Eq s, Show s) => Integral (Expr s) where
  toInteger (Const a) = toInteger a
  toInteger _ = error "toInteger not possible for generic Expr"
  divMod a b = (simplify $ Div a b, simplify $ Mod a b)
  quotRem (Const a) (Const b) = case quotRem a b of (c,d) -> (Const c,Const d)
  quotRem (Const 0) b = (Const 0,Const 0)
  quotRem a (Const 1) = (a,Const 0)
  quotRem a (Const (-1)) = (negate a,Const 0)
  quotRem _ _ = error "quotRem not possible for generic Expr"

-- a class of types convertible to expressions
class ToExpr tt t where
  toExpr :: t -> Expr tt

-- integers can be used as constant expressions
instance ToExpr tt Integer where
  toExpr = Const

-- ints can be used as constant expressions
instance ToExpr tt Int where
  toExpr = Const . toInteger

-- expressions themselves are trivially convertible to expressions
instance ToExpr t (Expr t) where
  toExpr = id

-- the terms used by the solver can be used as expressions referring
-- to a variable
instance ToExpr t t where
  toExpr = Term

--------------------------------------------------------------------------------
-- ExprKey
--------------------------------------------------------------------------------

newtype ExprKey s = ExprKey (Expr s)
  deriving (Eq, Show)

unExprKey :: ExprKey s -> Expr s
unExprKey (ExprKey x) = x

instance Ord s => Ord (ExprKey s) where
  -- consts
  compare (ExprKey (Const i1)) (ExprKey (Const i2)) = compare i1 i2
  compare (ExprKey (Const _)) _ = LT
  compare _ (ExprKey (Const _)) = GT
  -- abs
  compare (ExprKey (Abs i1)) (ExprKey (Abs i2)) = compare (ExprKey i1) (ExprKey i2)
  compare (ExprKey (Abs _)) _ = LT
  compare _ (ExprKey (Abs _)) = GT
  -- plus
  compare (ExprKey (Plus a1 a2)) (ExprKey (Plus b1 b2)) = case (compare (ExprKey a1) (ExprKey b1)) of
    LT -> LT
    GT -> GT
    EQ -> compare (ExprKey a2) (ExprKey b2)
  compare (ExprKey (Plus _ _)) _ = LT
  compare _ (ExprKey (Plus _ _)) = GT
  -- minus
  compare (ExprKey (Minus a1 a2)) (ExprKey (Minus b1 b2)) = case (compare (ExprKey a1) (ExprKey b1)) of
    LT -> LT
    GT -> GT
    EQ -> compare (ExprKey a2) (ExprKey b2)
  compare (ExprKey (Minus _ _)) _ = LT
  compare _ (ExprKey (Minus _ _)) = GT
  -- mult
  compare (ExprKey (Mult a1 a2)) (ExprKey (Mult b1 b2)) = case (compare (ExprKey a1) (ExprKey b1)) of
    LT -> LT
    GT -> GT
    EQ -> compare (ExprKey a2) (ExprKey b2)
  compare (ExprKey (Mult _ _)) _ = LT
  compare _ (ExprKey (Mult _ _)) = GT
  -- div
  compare (ExprKey (Div a1 a2)) (ExprKey (Div b1 b2)) = case (compare (ExprKey a1) (ExprKey b1)) of
    LT -> LT
    GT -> GT
    EQ -> compare (ExprKey a2) (ExprKey b2)
  compare (ExprKey (Div _ _)) _ = LT
  compare _ (ExprKey (Div _ _)) = GT
  -- mod
  compare (ExprKey (Mod a1 a2)) (ExprKey (Mod b1 b2)) = case (compare (ExprKey a1) (ExprKey b1)) of
    LT -> LT
    GT -> GT
    EQ -> compare (ExprKey a2) (ExprKey b2)
  compare (ExprKey (Mod _ _)) _ = LT
  compare _ (ExprKey (Mod _ _)) = GT
  -- variables
  compare (ExprKey (Term v1)) (ExprKey (Term v2)) = compare v1 v2
