{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/MCP/
 - 	Pieter Wuille
 -}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}

module Data.Expr.Data (
  Expr(..),
  ColExpr(..),
  BoolExpr(..),
  ExprRel(..),
  (<<>>)
) where 

--------------------
-- | Data types | --
--------------------

-- some simple kinds of expressions
data Expr t c b =
    Term t
  | ExprHole Int
  | Const Integer
  | Plus (Expr t c b) (Expr t c b)
  | Minus (Expr t c b) (Expr t c b)
  | Mult (Expr t c b) (Expr t c b)
  | Div (Expr t c b) (Expr t c b)
  | Mod (Expr t c b) (Expr t c b)
  | Abs (Expr t c b)
  | At (ColExpr t c b) (Expr t c b)
  | Fold (Expr t c b -> Expr t c b -> Expr t c b) (Expr t c b) (ColExpr t c b)
  | Cond (BoolExpr t c b) (Expr t c b) (Expr t c b)
  | ColSize (ColExpr t c b)
  | Channel (BoolExpr t c b)

data ColExpr t c b = 
    ColTerm c
  | ColList [Expr t c b]
  | ColRange (Expr t c b) (Expr t c b)
  | ColMap (Expr t c b -> Expr t c b) (ColExpr t c b)
  | ColSlice (Expr t c b -> Expr t c b) (Expr t c b) (ColExpr t c b)   -- ColSlice f n c -> c[f(0)..f(n-1)]
  | ColCat (ColExpr t c b) (ColExpr t c b)

data ExprRel =
    EREqual
  | ERDiff
  | ERLess
  deriving (Show,Eq,Ord)

data BoolExpr t c b =
    BoolTerm b
  | BoolConst Bool
  | BoolAnd (BoolExpr t c b) (BoolExpr t c b)
  | BoolOr (BoolExpr t c b) (BoolExpr t c b)
  | BoolNot (BoolExpr t c b)
  | BoolCond (BoolExpr t c b) (BoolExpr t c b) (BoolExpr t c b)
  | Rel (Expr t c b) ExprRel (Expr t c b)
  | BoolAll (Expr t c b -> BoolExpr t c b) (ColExpr t c b)
  | BoolAny (Expr t c b -> BoolExpr t c b) (ColExpr t c b)
  | ColEqual (ColExpr t c b) (ColExpr t c b)
  | BoolEqual (BoolExpr t c b) (BoolExpr t c b)
  | AllDiff Bool (ColExpr t c b)
  | Sorted Bool (ColExpr t c b)
  | Dom (Expr t c b) (ColExpr t c b)

-----------------------
-- | Show instance | --
-----------------------

class ShowFn t where
  showFn :: Int -> t -> String
instance (Show t, Show c, Show b) => ShowFn (Expr t c b) where
  showFn _ (Term a) = "Term ("++(show a)++")"
  showFn _ (ExprHole a) = "par"++(show a)
  showFn _ (Const a) = "Const "++(show a)
  showFn l (Plus a b) = "Plus ("++(showFn l a)++") ("++(showFn l b)++")"
  showFn l (Minus a b) = "Minus ("++(showFn l a)++") ("++(showFn l b)++")"
  showFn l (Mult a b) = "Mult ("++(showFn l a)++") ("++(showFn l b)++")"
  showFn l (Div a b) = "Div ("++(showFn l a)++") ("++(showFn l b)++")"
  showFn l (Mod a b) = "Mod ("++(showFn l a)++") ("++(showFn l b)++")"
  showFn l (Abs a) = "Abs ("++(showFn l a)++")"
  showFn l (At a b) = "At ("++(showFn l a)++") ("++(showFn l b)++")"
  showFn l (Fold a b c) = "Fold ("++(showFn l a)++") ("++(showFn l b)++") ("++(showFn l c)++")"
  showFn l (ColSize a) = "ColSize ("++(showFn l a)++")"
  showFn l (Channel b) = "Channel ("++(showFn l b)++")"
  showFn l (Cond c t f) = "Cond ("++(showFn l c)++") ("++(showFn l t)++") ("++(showFn l f)++")"
instance (ShowFn l) => ShowFn [l] where
  showFn d l = "[" ++ (foldr1 (\a b -> a++","++b) $ map (showFn d) l) ++ "]"
instance (Show t, Show c, Show b) => ShowFn (ColExpr t c b) where
  showFn d (ColTerm a) = "ColTerm ("++(show a)++")"
  showFn d (ColList l) = "ColList ("++(showFn d l)++")"
  showFn d (ColMap f l) = "ColMap ("++(showFn d f)++") ("++(showFn d l)++")"
  showFn d (ColSlice f l c) = "ColSlice ("++(showFn d f)++") ("++(showFn d l)++") ("++(showFn d c)++")"
  showFn d (ColCat a b) = "ColCat ("++(showFn d a)++") ("++(showFn d b)++")"
  showFn d (ColRange a b) = "ColRange ("++(showFn d a)++") ("++(showFn d b)++")"
instance (Show t, Show c, Show b) => ShowFn (BoolExpr t c b) where
  showFn d (BoolTerm b) = "BoolTerm ("++(show b)++")"
  showFn d (BoolConst b) = "BoolConst "++(show b)
  showFn d (BoolAnd a b) = "BoolAnd ("++(showFn d a)++") ("++(showFn d b)++")"
  showFn d (BoolOr a b) = "BoolOr ("++(showFn d a)++") ("++(showFn d b)++")"
  showFn d (BoolNot a) = "BoolNot ("++(showFn d a)++")"
  showFn d (BoolEqual a b) = "BoolEqual ("++(showFn d a)++") ("++(showFn d b)++")"
  showFn d (Rel a r b) = "Rel ("++(showFn d a)++") "++(show r)++" ("++(showFn d b)++")"
  showFn d (BoolAll f c) = "BoolAll ("++(showFn d f)++") ("++(showFn d c)++")"
  showFn d (BoolAny f c) = "BoolAny ("++(showFn d f)++") ("++(showFn d c)++")"
  showFn d (ColEqual a b) = "ColEqual ("++(showFn d a)++") ("++(showFn d b)++")"
  showFn d (AllDiff _ c) = "AllDiff ("++(showFn d c)++")"
  showFn d (Sorted b c) = "Sorted "++(show b)++"("++(showFn d c)++")"
  showFn l (BoolCond c t f) = "BoolCond ("++(showFn l c)++") ("++(showFn l t)++") ("++(showFn l f)++")"
  showFn d (Dom i c) = "Dom ("++(showFn d i)++") ("++(showFn d c)++")"
instance (Show t, Show c, Show b, ShowFn e) => ShowFn (Expr t c b -> e) where
  showFn l f = "\\par"++(show l)++" -> "++(showFn (l+1) (f (ExprHole l)))
instance (Show t, Show c, Show b) => Show (Expr t c b) where
  show = showFn 0
instance (Show t, Show c, Show b) => Show (ColExpr t c b) where
  show = showFn 0
instance (Show t, Show c, Show b) => Show (BoolExpr t c b) where
  show = showFn 0

---------------------
-- | Eq instance | --
---------------------

equalExpr :: (Eq t, Eq c, Eq b) => Int -> Expr t c b -> Expr t c b -> Bool
equalExpr _ (Term a) (Term b) = a==b
equalExpr _ (ExprHole a) (ExprHole b) = a==b
equalExpr _ (Const a) (Const b) = a==b
equalExpr l (Plus a c) (Plus b d) = equalExpr l a b && equalExpr l d c
equalExpr l (Minus a c) (Minus b d) = equalExpr l a b && equalExpr l d c
equalExpr l (Mult a c) (Mult b d) = equalExpr l a b && equalExpr l d c
equalExpr l (Div a c) (Plus b d) = equalExpr l a b && equalExpr l d c
equalExpr l (Mod a c) (Plus b d) = equalExpr l a b && equalExpr l d c
equalExpr l (Abs a) (Abs b) = equalExpr l a b
equalExpr l (At a c) (At b d) = equalExpr l c d && equalColExpr l a b
equalExpr l (ColSize a) (ColSize b) = equalColExpr l a b
equalExpr l (Fold f a c) (Fold g b d) = equalExpr l a b && equalColExpr l c d && equalExpr (l+2) (f (ExprHole l) (ExprHole $ l+1)) (g (ExprHole l) (ExprHole $ l+1))
equalExpr l (Channel a) (Channel b) = equalBoolExpr l a b
equalExpr l (Cond c t f) (Cond d u g) = equalBoolExpr l c d && equalExpr l t u && equalExpr l f g
equalExpr _ _ _ = False

equalColExpr :: (Eq t, Eq c, Eq b) => Int -> ColExpr t c b -> ColExpr t c b -> Bool
equalColExpr _ (ColTerm a) (ColTerm b) = a==b
equalColExpr _ (ColList []) (ColList []) = True
equalColExpr l (ColList (a:ar)) (ColList (b:br)) = equalExpr l a b && equalColExpr l (ColList ar) (ColList br)
equalColExpr l (ColMap f a) (ColMap g b) = equalColExpr l a b && equalExpr (l+1) (f (ExprHole l)) (g (ExprHole l))
equalColExpr l (ColSlice a c e) (ColSlice b d f) = equalExpr (l+1) (a (ExprHole l)) (b  (ExprHole l)) && equalExpr l c d && equalColExpr l e f
equalColExpr l (ColCat a c) (ColCat b d) = equalColExpr l a b && equalColExpr l c d
equalColExpr l (ColRange a c) (ColRange b d) = equalExpr l a b && equalExpr l c d
equalColExpr _ _ _ = False

equalBoolExpr :: (Eq t, Eq c, Eq b) => Int -> BoolExpr t c b -> BoolExpr t c b -> Bool
equalBoolExpr _ (BoolTerm a) (BoolTerm b) = a==b
equalBoolExpr _ (BoolConst a) (BoolConst b) = a==b
equalBoolExpr l (BoolAnd a c) (BoolAnd b d) = equalBoolExpr l a b && equalBoolExpr l c d
equalBoolExpr l (BoolOr a c) (BoolOr b d) = equalBoolExpr l a b && equalBoolExpr l c d
equalBoolExpr l (BoolEqual a c) (BoolEqual b d) = equalBoolExpr l a b && equalBoolExpr l c d
equalBoolExpr l (BoolNot a) (BoolNot b) = equalBoolExpr l a b
equalBoolExpr l (Rel a r c) (Rel b s d) = r==s && equalExpr l a b && equalExpr l c d
equalBoolExpr l (BoolAll f c) (BoolAll g d) = equalColExpr l c d && equalBoolExpr (l+1) (f $ ExprHole l) (g $ ExprHole l)
equalBoolExpr l (BoolAny f c) (BoolAny g d) = equalColExpr l c d && equalBoolExpr (l+1) (f $ ExprHole l) (g $ ExprHole l)
equalBoolExpr l (ColEqual a c) (ColEqual b d) = equalColExpr l a b && equalColExpr l c d
equalBoolExpr l (AllDiff _ c) (AllDiff _ d) = equalColExpr l c d
equalBoolExpr l (Sorted a c) (Sorted b d) = a==b && equalColExpr l c d
equalBoolExpr l (BoolCond c t f) (BoolCond d u g) = equalBoolExpr l c d && equalBoolExpr l t u && equalBoolExpr l f g
equalBoolExpr l (Dom a c) (Dom b d) = equalExpr l a b && equalColExpr l c d
equalBoolExpr _ _ _ = False

instance (Eq t, Eq c, Eq b) => Eq (Expr t c b) where
  a == b = equalExpr 0 a b
instance (Eq t, Eq c, Eq b) => Eq (ColExpr t c b) where
  a == b = equalColExpr 0 a b
instance (Eq t, Eq c, Eq b) => Eq (BoolExpr t c b) where
  a == b = equalBoolExpr 0 a b

-----------------------------------------------------
-- | ExprKey: Provides ordering over expressions | --
-----------------------------------------------------

infixr 4 <<>>
a <<>> b = case a of
  EQ -> b
  _ -> a

compareColExpr :: (Ord s, Ord c, Ord b) => Int -> ColExpr s c b -> ColExpr s c b -> Ordering
compareColExpr _ (ColList []) (ColList []) = EQ
compareColExpr l (ColList (a:ar)) (ColList (b:br)) = compareExpr l a b <<>> compareColExpr l (ColList ar) (ColList br)
compareColExpr _ (ColList _) _ = LT
compareColExpr _ _ (ColList _) = GT
compareColExpr l (ColMap f1 c1) (ColMap f2 c2) = compareColExpr l c1 c2 <<>> compareExpr (l+1) (f1 $ ExprHole l) (f2 $ ExprHole l)
compareColExpr _ (ColMap _ _) _ = LT
compareColExpr _ _ (ColMap _ _) = GT
compareColExpr l (ColSlice p1 l1 c1) (ColSlice p2 l2 c2) = compareExpr (l+1) (p1 $ ExprHole l) (p2 $ ExprHole l) <<>> compareExpr l l1 l2 <<>> compareColExpr l c1 c2
compareColExpr _ (ColSlice _ _ _) _ = LT
compareColExpr _ _ (ColSlice _ _ _) = GT
compareColExpr l (ColCat a1 b1) (ColCat a2 b2) = compareColExpr l a1 a2 <<>> compareColExpr l b1 b2
compareColExpr _ (ColCat _ _) _ = LT
compareColExpr _ _ (ColCat _ _) = GT
compareColExpr l (ColRange l1 h1) (ColRange l2 h2) = compareExpr l l1 l2 <<>> compareExpr l l2 h2
compareColExpr _ (ColRange _ _) _ = LT
compareColExpr _ _ (ColRange _ _) = GT
compareColExpr _ (ColTerm t1) (ColTerm t2) = compare t1 t2

compareBoolExpr :: (Ord s, Ord c, Ord b) => Int -> BoolExpr s c b -> BoolExpr s c b -> Ordering
compareBoolExpr _ (BoolConst a) (BoolConst b) = compare a b
compareBoolExpr _ (BoolConst _) _ = LT
compareBoolExpr _ _ (BoolConst _) = GT
compareBoolExpr l (BoolAnd a1 b1) (BoolAnd a2 b2) = compareBoolExpr l a1 a2 <<>> compareBoolExpr l b1 b2
compareBoolExpr _ (BoolAnd _ _) _ = LT
compareBoolExpr _ _ (BoolAnd _ _) = GT
compareBoolExpr l (BoolOr a1 b1) (BoolOr a2 b2) = compareBoolExpr l a1 a2 <<>> compareBoolExpr l b1 b2
compareBoolExpr _ (BoolOr _ _) _ = LT
compareBoolExpr _ _ (BoolOr _ _) = GT
compareBoolExpr l (BoolEqual a1 b1) (BoolEqual a2 b2) = compareBoolExpr l a1 a2 <<>> compareBoolExpr l b1 b2
compareBoolExpr _ (BoolEqual _ _) _ = LT
compareBoolExpr _ _ (BoolEqual _ _) = GT
compareBoolExpr l (BoolNot a1) (BoolNot a2) = compareBoolExpr l a1 a2
compareBoolExpr _ (BoolNot _) _ = LT
compareBoolExpr _ _ (BoolNot _) = GT
compareBoolExpr l (Rel a1 r1 b1) (Rel a2 r2 b2) = compare r1 r2 <<>> compareExpr l a1 a2 <<>> compareExpr l b1 b2
compareBoolExpr _ (Rel _ _ _) _ = LT
compareBoolExpr _ _ (Rel _ _ _) = GT
compareBoolExpr l (BoolAll f1 c1) (BoolAll f2 c2) = compareColExpr l c1 c2 <<>> compareBoolExpr (l+1) (f1 $ ExprHole l) (f2 $ ExprHole l)
compareBoolExpr _ (BoolAll _ _) _ = LT
compareBoolExpr _ _ (BoolAll _ _) = GT
compareBoolExpr l (BoolAny f1 c1) (BoolAny f2 c2) = compareColExpr l c1 c2 <<>> compareBoolExpr (l+1) (f1 $ ExprHole l) (f2 $ ExprHole l)
compareBoolExpr _ (BoolAny _ _) _ = LT
compareBoolExpr _ _ (BoolAny _ _) = GT
compareBoolExpr l (ColEqual a1 b1) (ColEqual a2 b2) = compareColExpr l a1 a2 <<>> compareColExpr l b1 b2
compareBoolExpr _ (ColEqual _ _) _ = LT
compareBoolExpr _ _ (ColEqual _ _) = GT
compareBoolExpr l (Sorted a1 b1) (Sorted a2 b2) = compare a1 a2 <<>> compareColExpr l b1 b2
compareBoolExpr _ (Sorted _ _) _ = LT
compareBoolExpr _ _ (Sorted _ _) = GT
compareBoolExpr l (AllDiff _ b1) (AllDiff _ b2) = compareColExpr l b1 b2
compareBoolExpr _ (AllDiff _ _) _ = LT
compareBoolExpr _ _ (AllDiff _ _) = GT
compareBoolExpr l (BoolCond c1 t1 f1) (BoolCond c2 t2 f2) = compareBoolExpr l c1 c2 <<>> compareBoolExpr l t1 t2 <<>> compareBoolExpr l f1 f2
compareBoolExpr _ (BoolCond _ _ _) _ = LT
compareBoolExpr _ _ (BoolCond _ _ _) = GT
compareBoolExpr l (Dom i1 c1) (Dom i2 c2) = compareExpr l i1 i2 <<>> compareColExpr l c1 c2
compareBoolExpr _ (Dom _ _) _ = LT
compareBoolExpr _ _ (Dom _ _) = GT
compareBoolExpr _ (BoolTerm a) (BoolTerm b) = compare a b

compareExpr :: (Ord s, Ord c, Ord b) => Int -> Expr s c b -> Expr s c b -> Ordering
compareExpr _ (Const i1) (Const i2) = compare i1 i2
compareExpr _ (Const _) _ = LT
compareExpr _ _ (Const _) = GT
compareExpr _ (ExprHole i1) (ExprHole i2) = compare i1 i2
compareExpr _ (ExprHole _) _ = LT
compareExpr _ _ (ExprHole _) = GT
compareExpr l (Plus a1 b1) (Plus a2 b2) = compareExpr l a1 a2 <<>> compareExpr l b1 b2
compareExpr _ (Plus _ _) _ = LT
compareExpr _ _ (Plus _ _) = GT
compareExpr l (Minus a1 b1) (Minus a2 b2) = compareExpr l a1 a2 <<>> compareExpr l b1 b2
compareExpr _ (Minus _ _) _ = LT
compareExpr _ _ (Minus _ _) = GT
compareExpr l (Mult a1 b1) (Mult a2 b2) = compareExpr l a1 a2 <<>> compareExpr l b1 b2
compareExpr _ (Mult _ _) _ = LT
compareExpr _ _ (Mult _ _) = GT
compareExpr l (Div a1 b1) (Div a2 b2) = compareExpr l a1 a2 <<>> compareExpr l b1 b2
compareExpr _ (Div _ _) _ = LT
compareExpr _ _ (Div _ _) = GT
compareExpr l (Mod a1 b1) (Mod a2 b2) = compareExpr l a1 a2 <<>> compareExpr l b1 b2
compareExpr _ (Mod _ _) _ = LT
compareExpr _ _ (Mod _ _) = GT
compareExpr l (Abs a1) (Abs a2) = compareExpr l a1 a2
compareExpr _ (Abs _) _ = LT
compareExpr _ _ (Abs _) = GT
compareExpr l (At c1 a1) (At c2 a2) = compareExpr l a1 a2 <<>> compareColExpr l c1 c2
compareExpr _ (At _ _) _ = LT
compareExpr _ _ (At _ _) = GT
compareExpr l (ColSize c1) (ColSize c2) = compareColExpr l c1 c2
compareExpr _ (ColSize _) _ = LT
compareExpr _ _ (ColSize _) = GT
compareExpr l (Fold f1 i1 c1) (Fold f2 i2 c2) = compareExpr l i1 i2 <<>> compareColExpr l c1 c2 <<>> compareExpr (l+2) (f1 (ExprHole l) (ExprHole $ l+1)) (f2 (ExprHole l) (ExprHole $ l+1))
compareExpr _ (Fold _ _ _) _ = LT
compareExpr _ _ (Fold _ _ _) = GT
compareExpr l (Channel b1) (Channel b2) = compareBoolExpr l b1 b2
compareExpr _ (Channel _) _ = LT
compareExpr _ _ (Channel _) = GT
compareExpr l (Cond c1 t1 f1) (Cond c2 t2 f2) = compareBoolExpr l c1 c2 <<>> compareExpr l t1 t2 <<>> compareExpr l f1 f2
compareExpr _ (Cond _ _ _) _ = LT
compareExpr _ _ (Cond _ _ _) = GT
compareExpr _ (Term t1) (Term t2) = compare t1 t2

instance (Ord s, Ord c, Ord b) => Ord (Expr s c b) where
  compare = compareExpr 0

instance (Ord s, Ord c, Ord b) => Ord (ColExpr s c b) where
  compare = compareColExpr 0

instance (Ord s, Ord c, Ord b) => Ord (BoolExpr s c b) where
  compare = compareBoolExpr 0
