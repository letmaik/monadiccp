{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/MCP/
 - 	Pieter Wuille
 -}

{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Expr.Sugar (
  (@+), (@-), (@*), (@/), (@%), (@?), (@??), (@:),
  (!), (@!!), (@++), (@..), size, slice, xhead, xtail, xmap, xfold, list, channel, xsum,
  (@||), (@&&), inv,
  (@/=), (@>), (@<), (@>=), (@<=), (@=), 
  loopall, loopany, forall, forany,
  ExprClass,
  Expr(), ColExpr(), BoolExpr(),
  ToExpr(..), ToColExpr(..), ToBoolExpr(..),
  sorted, sSorted, allDiff, allDiffD,
  ExprClass, ExprRange,
) where 

import Data.Expr.Data
import Data.Expr.Util

----------------------------------
-- | Built-in class instances | --
----------------------------------

instance (Eq s, Eq c, Eq b, Show s, Show c, Show b) => Num (Expr s c b) where
  a + b = simplify $ a `Plus` b
  a - b = simplify $ a `Minus` b
  a * b = simplify $ a `Mult` b
  abs a = simplify $ Abs a
  negate a = simplify $ (Const 0) `Minus` a
  fromInteger c = Const $ fromInteger c
  signum (Const a) = Const $ signum a
  signum a = error "signum not possible for generic Expr"

instance (Ord s, Ord c, Ord b, Eq s, Eq c, Eq b, Show s, Show c, Show b) => Real (Expr s c b) where
  toRational (Const x) = toRational x
  toRational _ = error "toRational not possible for generic Expr"

instance (Eq s, Eq c, Eq b) => Enum (Expr s c b) where
  succ a = simplify $ a `Plus` (Const 1)
  pred a = simplify $ a `Minus` (Const 1)
  toEnum = Const . toEnum
  fromEnum (Const a) = fromEnum a
  fromEnum _ = error "fromEnum not possible for generic Expr"

instance (Ord s, Ord c, Ord b, Eq s, Eq c, Eq b, Show s, Show c, Show b) => Integral (Expr s c b) where
  toInteger (Const a) = toInteger a
  toInteger _ = error "toInteger not possible for generic Expr"
  divMod a b = (simplify $ a `Div` b, simplify $ a `Mod` b)
  quotRem (Const a) (Const b) = case quotRem a b of (c,d) -> (Const c,Const d)
  quotRem (Const 0) b = (Const 0,Const 0)
  quotRem a (Const 1) = (a,Const 0)
  quotRem a (Const (-1)) = (negate a,Const 0)
  quotRem _ _ = error "quotRem not possible for generic Expr"

---------------------------------------------
-- | convertion from/to expression types | --
---------------------------------------------

-- convertible to expressions:
class ToExpr tt cc bb t where
  toExpr :: t -> Expr tt cc bb

-- convertible to collection-expressions:
class ToColExpr tt cc bb c where
  toColExpr :: c -> ColExpr tt cc bb

-- convertible to boolean expressions:
class ToBoolExpr tt cc bb b where
  toBoolExpr :: b -> BoolExpr tt cc bb

-- infix 4 @=, @/=

class (Eq tt, Eq cc, Eq bb) => ExprClass tt cc bb a where
  (@=)  :: a -> a -> BoolExpr tt cc bb
  (@/=) :: a -> a -> BoolExpr tt cc bb
  a @/= b = boolSimplify $ BoolNot $ a @= b

class (Eq tt, Eq cc, Eq bb) => ExprRange tt cc bb r where
  (@:)  :: Expr tt cc bb -> r -> BoolExpr tt cc bb

-- integers can be used as constant expressions
instance ToExpr tt cc bb Integer where
  toExpr = Const

-- expressions themselves are trivially convertible to expressions
instance ToExpr t a b (Expr t a b) where
  toExpr = id

-- ints can be used as constant expressions
instance ToExpr tt cc bb Int where
  toExpr = Const . toInteger

-- boolean expressions can be used as integer expressions (being 0 or 1)
instance (Eq t, Eq a, Eq b) => ToExpr t a b (BoolExpr t a b) where
  toExpr = simplify . Channel

-- collection expressions themselves are trivially convertible to collection expressions
instance ToColExpr t a b (ColExpr t a b) where
  toColExpr = id

-- an expression can be used as a collection of one expressions
instance (Eq t, Eq a, Eq b) => ToColExpr t a b (Expr t a b) where
  toColExpr a = colSimplify $ ColList [a]

-- a list of expressions van be used as a collection
instance (Eq b, Eq a, Eq t) => ToColExpr t a b [Expr t a b] where
  toColExpr = colSimplify . ColList

-- a boolean constant can be used as a constant boolean expression
instance ToBoolExpr tt cc bb Bool where
  toBoolExpr = BoolConst

-- boolean expressions are trivially convertible to boolean expressions
instance ToBoolExpr t a b (BoolExpr t a b) where
  toBoolExpr = id

-- the integer terms used by an expression can be used as interger expressions
instance ToExpr t a b t where
  toExpr = Term

-- the collections terms used by an expression can be used as collection expressions
instance ToColExpr t a b a where
  toColExpr = ColTerm

-- the boolean terms used by an expression can be used as boolean expressions
instance ToBoolExpr t a b b where
  toBoolExpr = BoolTerm

-------------------------------------
-- | integer operators/functions | --
-------------------------------------

-- @+ @- @* @/ @% are identical to + - * / % for integer expressions, except
-- that they also accept types convertible to expressions, instead of only
-- expressions themselves

infixl 6 @+, @-
infixl 7 @*
infixl 7 @/
infixl 7 @%

(@+) :: (Eq t, Eq c, Eq b, ToExpr t c b p, ToExpr t c b q) => p -> q -> Expr t c b
(@-) :: (Eq t, Eq c, Eq b, ToExpr t c b p, ToExpr t c b q) => p -> q -> Expr t c b
(@*) :: (Eq t, Eq c, Eq b, ToExpr t c b p, ToExpr t c b q) => p -> q -> Expr t c b
(@/) :: (Eq t, Eq c, Eq b, ToExpr t c b p, ToExpr t c b q) => p -> q -> Expr t c b
(@%) :: (Eq t, Eq c, Eq b, ToExpr t c b p, ToExpr t c b q) => p -> q -> Expr t c b

a @+ b = simplify $ (toExpr a) `Plus` (toExpr b)
a @- b = simplify $ (toExpr a) `Minus` (toExpr b)
a @* b = simplify $ (toExpr a) `Mult` (toExpr b)
a @/ b = simplify $ (toExpr a) `Div` (toExpr b)
a @% b = simplify $ (toExpr a) `Mod` (toExpr b)

----------------------------------
-- | list operators/functions | --
----------------------------------

infix 9 !
infix 9 @!!
infix 9 @..
infixr 5 @++
infix 4 @?
infix 4 @??
infix 5 @:

(!) :: (Eq t, Eq c, Eq b) => ColExpr t c b -> Expr t c b -> Expr t c b
(@!!) :: (Eq t, Eq c, Eq b) => ColExpr t c b -> Integer -> Expr t c b
(@..) :: (Eq t, Eq c, Eq b) => Expr t c b -> Expr t c b -> ColExpr t c b
(@++) :: (Eq t, Eq c, Eq b) => ColExpr t c b -> ColExpr t c b -> ColExpr t c b

(@?) :: (Eq t, Eq c, Eq b) => BoolExpr t c b -> (Expr t c b, Expr t c b) -> Expr t c b
c @? (t,f) = simplify $ Cond c t f

(@??) :: (Eq t, Eq c, Eq b) => BoolExpr t c b -> (BoolExpr t c b, BoolExpr t c b) -> BoolExpr t c b
c @?? (t,f) = boolSimplify $ BoolCond c t f

c!p = simplify $ At c p
c @!! p = simplify $ At c (Const p)
a @.. b = colSimplify $ ColRange (toExpr a) (toExpr b)
a @++ b = colSimplify $ ColCat (toColExpr a) (toColExpr b)

size :: (Eq t, Eq c, Eq b) => ColExpr t c b -> Expr t c b
size a = simplify $ ColSize a

xfold :: (Eq t, Eq c, Eq b) => (Expr t c b -> Expr t c b -> Expr t c b) -> Expr t c b -> ColExpr t c b -> Expr t c b
xfold f i c = simplify $ Fold (\a b -> f a b) i c

xsum :: (Num (Expr t c b), Eq t, Eq c, Eq b) => ColExpr t c b -> Expr t c b
xsum c = xfold (+) (Const 0) c

list :: (Eq t, Eq c, Eq b) => [Expr t c b] -> ColExpr t c b
list x = colSimplify $ ColList x

xhead :: (Eq t, Eq c, Eq b, ToColExpr t c b p) => p -> Expr t c b
xhead c = simplify $ At (toColExpr c) (Const 0)

xtail :: (Eq t, Eq c, Eq b, ToColExpr t c b p) => p -> ColExpr t c b
xtail c = let cc = toColExpr c in colSimplify $ ColSlice (\x -> simplify (x `Plus` (Const 1))) (simplify $ (size cc) `Minus` (Const 1)) cc

slice :: (Eq t, Eq c, Eq b) => ColExpr t c b -> ColExpr t c b -> ColExpr t c b
slice c p = case (c,p) of
  (_,ColRange l h) -> colSimplify $ ColSlice (\x -> simplify (l `Plus` x)) (simplify $ Const 1 `Plus` (simplify $ h `Minus` l)) c
  (_,ColMap f (ColRange l h)) -> colSimplify $ ColSlice (\i -> simplify $ f $ simplify (l `Plus` i)) (simplify $ Const 1 `Plus` (simplify $ h `Minus` l)) c
  (_,ColSlice f n c2) -> colSimplify $ ColSlice (\i -> simplify $ c2 `At` (f i)) n c
  _ -> xmap (\i -> simplify $ c `At` i) p

xmap :: (Eq t, Eq c, Eq b) => (Expr t c b -> Expr t c b) -> ColExpr t c b -> ColExpr t c b
xmap f c = colSimplify $ ColMap f c

loopall :: (Eq t, Eq c, Eq b) => (Expr t c b,Expr t c b) -> (Expr t c b -> BoolExpr t c b) -> BoolExpr t c b
loopall (l,h) f = boolSimplify $ BoolAll f $ colSimplify $ ColRange l h

loopany :: (Eq t, Eq c, Eq b) => (Expr t c b,Expr t c b) -> (Expr t c b -> BoolExpr t c b) -> BoolExpr t c b
loopany (l,h) f = boolSimplify $ BoolAny f $ colSimplify $ ColRange l h

forall :: (Eq t, Eq c, Eq b) => (ColExpr t c b) -> (Expr t c b -> BoolExpr t c b) -> BoolExpr t c b
forall c f = boolSimplify $ BoolAll f c

forany :: (Eq t, Eq c, Eq b) => (ColExpr t c b) -> (Expr t c b -> BoolExpr t c b) -> BoolExpr t c b
forany c f = boolSimplify $ BoolAny f c

channel :: (Eq t, Eq c, Eq b) => BoolExpr t c b -> Expr t c b
channel = simplify . Channel 

-------------------------------------
-- | boolean operators/functions | --
-------------------------------------

-- infixr 1 /\
-- infixr 1 \/
infixr 2 @||
infixr 3 @&&

-- (\/) :: (Eq t, Eq c, Eq b, ToBoolExpr t c b p, ToBoolExpr t c b q) => p -> q -> BoolExpr t c b
-- (/\) :: (Eq t, Eq c, Eq b, ToBoolExpr t c b p, ToBoolExpr t c b q) => p -> q -> BoolExpr t c b
inv :: (Eq t, Eq c, Eq b, ToBoolExpr t c b p) => p -> BoolExpr t c b

a @|| b = boolSimplify $ BoolOr (toBoolExpr a) (toBoolExpr b)
a @&& b = boolSimplify $ BoolAnd (toBoolExpr a) (toBoolExpr b)
inv a = boolSimplify $ BoolNot (toBoolExpr a)
-- a \/ b = a @|| b
-- a /\ b = a @&& b

----------------------------------------
-- | relational operators/functions | --
----------------------------------------

instance (Eq t, Eq c, Eq b) => ExprClass t c b (Expr t c b) where
  a @= b = boolSimplify $ Rel a EREqual b

instance (Eq t, Eq c, Eq b) => ExprClass t c b (BoolExpr t c b) where
  a @= b = boolSimplify $ BoolEqual a b

instance (Eq t, Eq c, Eq b) => ExprClass t c b (ColExpr t c b) where
  a @= b = boolSimplify $ ColEqual a b

  
infixr 4 @<,@<=,@>,@>=
(@<) ::  (Eq t, Eq c, Eq b) => Expr t c b -> Expr t c b -> BoolExpr t c b
(@>) ::  (Eq t, Eq c, Eq b) => Expr t c b -> Expr t c b -> BoolExpr t c b
(@<=) :: (Eq t, Eq c, Eq b) => Expr t c b -> Expr t c b -> BoolExpr t c b
(@>=) :: (Eq t, Eq c, Eq b) => Expr t c b -> Expr t c b -> BoolExpr t c b

a @< b = boolSimplify $ Rel a ERLess b
a @> b = boolSimplify $ Rel b ERLess a
a @<= b = boolSimplify $ Rel a ERLess (simplify $ b `Plus` (Const 1))
a @>= b = boolSimplify $ Rel b ERLess (simplify $ a `Plus` (Const 1))

sorted c = boolSimplify $ Sorted False c
sSorted c = boolSimplify $ Sorted True c
allDiff c = boolSimplify $ AllDiff False c
allDiffD c = boolSimplify $ AllDiff True c

instance (Eq t, Eq c, Eq b) => ExprRange t c b (Expr t c b,Expr t c b) where
  a @: (l,h) = (a @>= l) @&& (a @<= h)

instance (Eq t, Eq c, Eq b) => ExprRange t c b (ColExpr t c b) where
  a @: c = boolSimplify $ Dom a c

