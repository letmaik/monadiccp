{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/MCP/
 - 	Pieter Wuille
 -}

{-# LANGUAGE StandaloneDeriving #-}

module Data.Expr.Util (
  Expr(), BoolExpr(), ColExpr(),
  transform, colTransform, boolTransform,
  transformEx, colTransformEx, boolTransformEx,
  property, colProperty, boolProperty,
  propertyEx, colPropertyEx, boolPropertyEx,
  collapse, colCollapse, boolCollapse,
  simplify, colSimplify, boolSimplify,
  WalkPhase(..), WalkResult(..), walk, colWalk, boolWalk,
) where 

import Data.Expr.Data

-------------------------
-- | Helper functions |--
-------------------------

relCheck :: Integer -> ExprRel -> Integer -> Bool
relCheck a EREqual b = a==b
relCheck a ERDiff b = a/=b
relCheck a ERLess b = a<b

-------------------------------------------------------------------------
-- | Transform expressions over one type to expressions over another | --
-------------------------------------------------------------------------

transform :: (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f) => (a->b,c->d,e->f,b->a,d->c,f->e) -> Expr a c e -> Expr b d f
transform (f,fc,fb,fi,fic,fib) = transformEx (Term . f, ColTerm . fc, BoolTerm . fb, Term . fi, ColTerm . fic, BoolTerm . fib)

transformEx :: (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f) => ((a -> Expr b d f),(c -> ColExpr b d f),(e -> BoolExpr b d f),(b -> Expr a c e),(d -> ColExpr a c e),(f -> BoolExpr a c e)) -> Expr a c e -> Expr b d f
transformEx (f,_,_,_,_,_) (Term v) = f v
transformEx f (Const i) = Const i
transformEx f (ExprHole i) = ExprHole i
transformEx f (Plus a b) = simplify $ Plus (transformEx f a) (transformEx f b)
transformEx f (Minus a b) = simplify $ Minus (transformEx f a) (transformEx f b)
transformEx f (Mult a b) = simplify $ Mult (transformEx f a) (transformEx f b)
transformEx f (Div a b) = simplify $ Div (transformEx f a) (transformEx f b)
transformEx f (Mod a b) = simplify $ Mod (transformEx f a) (transformEx f b)
transformEx f (Abs a) = simplify $ Abs (transformEx f a)
transformEx f (At c a) = simplify $ At (colTransformEx f c) (transformEx f a)
transformEx f (ColSize c) = simplify $ ColSize $ colTransformEx f c
transformEx f (Channel a) = simplify $ Channel $ boolTransformEx f a
transformEx f (Cond c t e) = simplify $ Cond (boolTransformEx f c) (transformEx f t) (transformEx f e)
transformEx t@(f,fc,fb,fi,fic,fib) (Fold m i c) = simplify $ Fold (\a b -> transformEx t (m (transformEx (fi,fic,fib,f,fc,fb) a) (transformEx (fi,fic,fib,f,fc,fb) b))) (transformEx t i) (colTransformEx t c)

colTransform :: (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f) => (a->b,c->d,e->f,b->a,d->c,f->e) -> ColExpr a c e -> ColExpr b d f
colTransform (f,fc,fb,fi,fic,fib) = colTransformEx (Term . f, ColTerm . fc, BoolTerm . fb, Term . fi, ColTerm . fic, BoolTerm . fib)

colTransformEx :: (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f) => ((a -> Expr b d f),(c -> ColExpr b d f),(e -> BoolExpr b d f),(b -> Expr a c e),(d -> ColExpr a c e),f -> BoolExpr a c e) -> ColExpr a c e -> ColExpr b d f
colTransformEx (_,f,_,_,_,_)  (ColTerm c) = f c
colTransformEx f (ColList l) = colSimplify $ ColList $ map (transformEx f) l
colTransformEx t@(f,fc,fb,fi,fic,fib) (ColMap m c) = colSimplify $ ColMap (\a -> transformEx t (m (transformEx (fi,fic,fib,f,fc,fb) a))) (colTransformEx t c)
colTransformEx t@(f,fc,fb,fi,fic,fib) (ColSlice p l c) = colSimplify $ ColSlice (\a -> transformEx t (p (transformEx (fi,fic,fib,f,fc,fb) a))) (transformEx t l) (colTransformEx t c)
colTransformEx f (ColCat a b) = colSimplify $ ColCat (colTransformEx f a) (colTransformEx f b)
colTransformEx f (ColRange a b) = colSimplify $ ColRange (transformEx f a) (transformEx f b)

boolTransform :: (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f) => (a->b,c->d,e->f,b->a,d->c,f->e) -> BoolExpr a c e -> BoolExpr b d f
boolTransform (f,fc,fb,fi,fic,fib) = boolTransformEx (Term . f, ColTerm . fc, BoolTerm . fb, Term . fi, ColTerm . fic, BoolTerm . fib)

boolTransformEx :: (Eq a, Eq b, Eq c, Eq d, Eq e, Eq f) => ((a -> Expr b d f),(c -> ColExpr b d f),(e -> BoolExpr b d f),(b -> Expr a c e),(d -> ColExpr a c e),f -> BoolExpr a c e) -> BoolExpr a c e -> BoolExpr b d f
boolTransformEx (_,_,f,_,_,_) (BoolTerm v) = f v
boolTransformEx f (BoolConst c) = BoolConst c
boolTransformEx f (BoolAnd a b) = boolSimplify $ BoolAnd (boolTransformEx f a) (boolTransformEx f b)
boolTransformEx f (BoolOr a b) = boolSimplify $ BoolOr (boolTransformEx f a) (boolTransformEx f b)
boolTransformEx f (BoolEqual a b) = boolSimplify $ BoolEqual (boolTransformEx f a) (boolTransformEx f b)
boolTransformEx f (BoolNot a) = boolSimplify $ BoolNot (boolTransformEx f a)
boolTransformEx f (Rel a r b) = boolSimplify $ Rel (transformEx f a) r (transformEx f b)
boolTransformEx t@(f,fc,fb,fi,fic,fib) (BoolAll m c) = boolSimplify $ BoolAll (\a -> boolTransformEx t (m (transformEx (fi,fic,fib,f,fc,fb) a))) (colTransformEx t c)
boolTransformEx t@(f,fc,fb,fi,fic,fib) (BoolAny m c) = boolSimplify $ BoolAny (\a -> boolTransformEx t (m (transformEx (fi,fic,fib,f,fc,fb) a))) (colTransformEx t c)
boolTransformEx f (ColEqual a b) = boolSimplify $ ColEqual (colTransformEx f a) (colTransformEx f b)
boolTransformEx f (Sorted b c) = boolSimplify $ Sorted b (colTransformEx f c)
boolTransformEx f (AllDiff b c) = boolSimplify $ AllDiff b (colTransformEx f c)
boolTransformEx f (BoolCond c t e) = boolSimplify $ BoolCond (boolTransformEx f c) (boolTransformEx f t) (boolTransformEx f e)
boolTransformEx f (Dom i c) = boolSimplify $ Dom (transformEx f i) (colTransformEx f c)

------------------------------------------------------------------------------------------
-- | Check whether an expression is possibly referring to terms with a given property | --
------------------------------------------------------------------------------------------

propertyEx :: (Expr a b c -> Maybe Bool, ColExpr a b c -> Maybe Bool, BoolExpr a b c -> Maybe Bool) -> Expr a b c -> Bool
propertyEx f@(fi,fc,fb) t = case fi t of
  Just a -> a
  Nothing -> case t of
    Plus a b -> propertyEx f a || propertyEx f b
    Minus a b -> propertyEx f a || propertyEx f b
    Mult a b -> propertyEx f a || propertyEx f b
    Div a b -> propertyEx f a || propertyEx f b
    Mod a b -> propertyEx f a || propertyEx f b
    Abs a -> propertyEx f a
    At a b -> propertyEx f b || colPropertyEx f a
    ColSize a -> colPropertyEx f a
    Fold _ _ _ -> True
    Channel b -> boolPropertyEx f b
    Cond c t e -> boolPropertyEx f c || propertyEx f t || propertyEx f e
    _ -> False

colPropertyEx :: (Expr a b c -> Maybe Bool, ColExpr a b c -> Maybe Bool, BoolExpr a b c -> Maybe Bool) -> ColExpr a b c -> Bool
colPropertyEx f@(fi,fc,fb) t = case fc t of
  Just a -> a
  Nothing -> case t of
    ColList l -> any (propertyEx f) l
    ColMap _ _ -> True
    ColSlice p l c -> propertyEx f (p (ExprHole (-1))) || propertyEx f l || colPropertyEx f c
    ColRange l h -> propertyEx f l || propertyEx f h
    ColCat a b -> colPropertyEx f a || colPropertyEx f b
    _ -> False

boolPropertyEx :: (Expr a b c -> Maybe Bool, ColExpr a b c -> Maybe Bool, BoolExpr a b c -> Maybe Bool) -> BoolExpr a b c -> Bool
boolPropertyEx f@(fi,fc,fb) t = case fb t of
  Just a -> a
  Nothing -> case t of
    BoolAnd a b -> boolPropertyEx f a || boolPropertyEx f b
    BoolOr a b -> boolPropertyEx f a || boolPropertyEx f b
    BoolNot a -> boolPropertyEx f a
    BoolEqual a b -> boolPropertyEx f a || boolPropertyEx f b
    Rel a _ b -> propertyEx f a || propertyEx f b
    BoolAll _ _ -> True
    BoolAny _ _ -> True
    ColEqual a b -> colPropertyEx f a || colPropertyEx f b
    AllDiff _ c -> colPropertyEx f c
    Sorted _ c -> colPropertyEx f c
    BoolCond c t e -> boolPropertyEx f c || boolPropertyEx f t || boolPropertyEx f e
    Dom i c -> propertyEx f i || colPropertyEx f c
    _ -> False


property :: (a -> Bool) -> (b -> Bool) -> (c -> Bool) -> Expr a b c -> Bool
property fit fct fbt = propertyEx (propInt fit, propCol fct, propBool fbt)
colProperty :: (a -> Bool) -> (b -> Bool) -> (c -> Bool) -> ColExpr a b c -> Bool
colProperty fit fct fbt = colPropertyEx (propInt fit, propCol fct, propBool fbt)
boolProperty :: (a -> Bool) -> (b -> Bool) -> (c -> Bool) -> BoolExpr a b c -> Bool
boolProperty fit fct fbt = boolPropertyEx (propInt fit, propCol fct, propBool fbt)

propInt :: (a -> Bool) -> Expr a b c -> Maybe Bool
propInt ft t = case t of
  Term x -> Just $ ft x
  _ -> Nothing

propCol :: (b -> Bool) -> ColExpr a b c -> Maybe Bool
propCol ft t = case t of
  ColTerm x -> Just $ ft x
  _ -> Nothing

propBool :: (c -> Bool) -> BoolExpr a b c -> Maybe Bool
propBool ft t = case t of
  BoolTerm x -> Just $ ft x
  _ -> Nothing


-------------------------------------------------------------------
-- | Count how many references to terms an expression contains | --
-------------------------------------------------------------------

varrefs :: Expr a b c -> Int
varrefs (Term _)     = 1
varrefs (Const _)    = 0
varrefs (ExprHole _) = 0
varrefs (Plus a b)   = varrefs a + varrefs b
varrefs (Minus a b)  = varrefs a + varrefs b
varrefs (Mult a b)   = varrefs a + varrefs b
varrefs (Div a b)    = varrefs a + varrefs b
varrefs (Mod a b)    = varrefs a + varrefs b
varrefs (Abs a)      = varrefs a
varrefs (At c i)     = varrefs i + colVarrefs c
varrefs (ColSize c)  = colVarrefs c
varrefs (Fold f i c) = varrefs i + colVarrefs c + varrefs (f (ExprHole 0) (ExprHole 1))
varrefs (Channel b)  = boolVarrefs b
varrefs (Cond c t e) = boolVarrefs c + varrefs t + varrefs e

colVarrefs :: ColExpr a b c -> Int
colVarrefs (ColTerm _) = 1
colVarrefs (ColList lst) = sum $ map varrefs lst
colVarrefs (ColMap m c) = colVarrefs c + varrefs (m (ExprHole 0))
colVarrefs (ColSlice p l c) = varrefs (p (ExprHole 0)) + varrefs l + colVarrefs c
colVarrefs (ColCat a b) = colVarrefs a + colVarrefs b
colVarrefs (ColRange a b) = varrefs a + varrefs b

boolVarrefs :: BoolExpr a b c -> Int
boolVarrefs (BoolTerm _) = 1
boolVarrefs (BoolConst _) = 0
boolVarrefs (BoolAnd a b) = boolVarrefs a + boolVarrefs b
boolVarrefs (BoolOr a b) = boolVarrefs a + boolVarrefs b
boolVarrefs (BoolEqual a b) = boolVarrefs a + boolVarrefs b
boolVarrefs (BoolNot a) = boolVarrefs a
boolVarrefs (BoolAll f c) = boolVarrefs (f $ ExprHole 0) + colVarrefs c
boolVarrefs (BoolAny f c) = boolVarrefs (f $ ExprHole 0) + colVarrefs c
boolVarrefs (Rel a _ b) = varrefs a + varrefs b
boolVarrefs (ColEqual a b) = colVarrefs a + colVarrefs b
boolVarrefs (Sorted _ c) = colVarrefs c
boolVarrefs (AllDiff _ c) = colVarrefs c
boolVarrefs (BoolCond c t e) = boolVarrefs c + boolVarrefs t + boolVarrefs e
boolVarrefs (Dom i c)    = varrefs i + colVarrefs c

------------------------------
-- | Simplify expressions | --
------------------------------

simplify :: (Eq s, Eq c, Eq b) => Expr s c b -> Expr s c b
-- dropout rules (things that won't ever be changed)
simplify a@(Const _) = a
simplify a@(Term _) = a
simplify a@(ExprHole _) = a
-- simplification rules (either decrease # of variable references, or leave that equal and decrease # of tree nodes)
--- level 0 (result in a final expression)
simplify (Mult a@(Const 0) _) = a
simplify (Div a@(Const 0) _) = a
simplify (Mod a@(Const 0) _) = a
simplify (Mod _ (Const 1)) = Const 0
simplify (Mod _ (Const (-1))) = Const 0
simplify (Mod (Mult (Const a) b) (Const c)) | (a `mod` c)==0 = Const 0
simplify (Minus a b) | a==b = Const 0
simplify (Plus (Const a) (Const b)) = Const (a+b)
simplify (Minus (Const a) (Const b)) = Const (a-b)
simplify (Mult (Const a) (Const b)) = Const (a*b)
simplify (Div (Const a) (Const b)) = Const $ (a `div` b)
simplify (Abs (Const a)) = Const (abs a)
simplify (Mod (Const a) (Const b)) = Const $ (a `mod` b)
simplify (Plus (Const 0) a) = a
simplify (Mult (Const 1) a) = a
simplify (Div a (Const 1)) = a
simplify (At (ColList l) (Const c)) = l!!(fromInteger c)
simplify (ColSize (ColList l)) = Const $ toInteger $ length l
simplify (ColSize (ColSlice _ l _)) = l
simplify (Channel (BoolConst False)) = Const 0
simplify (Channel (BoolConst True)) = Const 1
simplify (Cond (BoolConst True) t _) = t
simplify (Cond (BoolConst False) _ f) = f
--- level 1 (result in one recursive call to simplify)
simplify (Plus a b) | a==b = simplify $ Mult (Const 2) a
simplify (Div a (Const (-1))) = simplify $ Minus (Const 0) a
simplify (Plus (Const c) (Plus (Const a) b)) = simplify $ Plus (Const $ c+a) b
simplify (Plus (Const c) (Minus (Const a) b)) = simplify $ Minus (Const $ c+a) b
simplify (Minus (Const c) (Plus (Const a) b)) = simplify $ Minus (Const $ c-a) b
simplify (Minus (Const c) (Minus (Const a) b)) = simplify $ Plus (Const $ c-a) b
simplify (Mult (Const c) (Mult (Const a) b)) = simplify $ Mult (Const $ a*c) b
simplify (Div (Mult (Const a) b) (Const c)) | (a `mod` c)==0 = simplify $ Mult (Const (a `div` c)) b
simplify (ColSize (ColMap _ c)) = simplify $ ColSize c
simplify (Fold f1 i (ColMap f2 c)) = simplify $ Fold (\a b -> f1 a (f2 b)) i c
simplify (At (ColRange l h) p) = simplify $ Plus l p
simplify (Cond (BoolNot c) t f) = simplify $ Cond c f t
--- level 2 (result in two recursive calls to simplify)
simplify (Plus a (Mult b c)) | a==b && ((varrefs a)>0) = simplify $ Mult (simplify $ Plus c (Const 1)) a
simplify (Plus a (Mult b c)) | a==c && ((varrefs a)>0) = simplify $ Mult (simplify $ Plus b (Const 1)) a
simplify (Plus (Mult b c) a) | a==b && ((varrefs a)>0) = simplify $ Mult (simplify $ Plus c (Const 1)) a
simplify (Plus (Mult b c) a) | a==c && ((varrefs a)>0) = simplify $ Mult (simplify $ Plus b (Const 1)) a
simplify (Plus (Mult a b) (Mult c d)) | a==c = simplify $ Mult (simplify $ Plus b d) a
simplify (Plus (Mult a b) (Mult c d)) | a==d = simplify $ Mult (simplify $ Plus b c) a
simplify (Plus (Mult a b) (Mult c d)) | b==c = simplify $ Mult (simplify $ Plus a d) b
simplify (Plus (Mult a b) (Mult c d)) | b==d = simplify $ Mult (simplify $ Plus a c) b
simplify (Minus a (Mult b c)) | a==b && ((varrefs a)>0) = simplify $ Mult (simplify $ Minus (Const 1) c) a
simplify (Minus a (Mult b c)) | a==c && ((varrefs a)>0) = simplify $ Mult (simplify $ Minus (Const 1) b) a
simplify (Minus (Mult b c) a) | a==b && ((varrefs a)>0) = simplify $ Mult (simplify $ Minus c (Const 1)) a
simplify (Minus (Mult b c) a) | a==c && ((varrefs a)>0) = simplify $ Mult (simplify $ Minus b (Const 1)) a
simplify (Minus (Mult a b) (Mult c d)) | a==c = simplify $ Mult (simplify $ Minus b d) a
simplify (Minus (Mult a b) (Mult c d)) | a==d = simplify $ Mult (simplify $ Minus b c) a
simplify (Minus (Mult a b) (Mult c d)) | b==c = simplify $ Mult (simplify $ Minus a d) b
simplify (Minus (Mult a b) (Mult c d)) | b==d = simplify $ Mult (simplify $ Minus a c) b
simplify (Mult (Abs a) (Abs b)) = simplify $ Abs (simplify $ Mult a b)
simplify (Div (Abs a) (Abs b)) = simplify $ Abs (simplify $ Div a b)
simplify (ColSize (ColRange l h)) = simplify $ Plus (Const 1) $ simplify $ Minus h l
simplify (At (ColSlice f _ c) i) = simplify $ At c (f i)
simplify (At (ColMap m c) i) = simplify $ m $ simplify $ At c i
simplify t@(At (ColCat c1 c2) c@(Const p)) = case simplify (ColSize c1) of
  Const l | p<l -> simplify $ At c1 c
  Const l | p>=l -> simplify $ At c2 (Const $ p-l)
  _ -> t    {- no further (At _ _) rules may follow after this -}
--- level 3 (results in three recursive calls to simplify)
simplify (ColSize (ColCat a b)) = simplify $ Plus (simplify $ ColSize a) (simplify $ ColSize b)
-- reordering rules (do not decrease # of variables or # of tree nodes, but normalize an expression in such a way that the same normalization cannot be applied anymore - possibly because that can only occur in a case already matched by a simplification rule above)
--- level 1
simplify (Plus a (Const c)) = simplify $ Plus (Const c) a
simplify (Minus a (Const c)) = simplify $ Plus (Const (-c)) a
simplify (Mult a (Const c)) = simplify $ Mult (Const c) a
simplify (Mult (Const (-1)) a) = simplify $ Minus (Const 0) a
--- level 2
simplify (Mult t@(Const c) (Plus (Const a) b)) = simplify $ Plus (Const (a*c)) (simplify $ Mult t b)
simplify (Mult t@(Const c) (Minus (Const a) b)) = simplify $ Minus (Const (a*c)) (simplify $ Mult t b)
simplify (Plus a (Plus t@(Const b) c)) = simplify $ Plus t (simplify $ Plus a c)
simplify (Plus a (Minus t@(Const b) c)) = simplify $ Plus t (simplify $ Minus a c)
simplify (Minus a (Plus (Const b) c)) = simplify $ Plus (Const (-b)) (simplify $ Minus a c)
simplify (Minus a (Minus (Const b) c)) = simplify $ Plus (Const (-b)) (simplify $ Plus a c)
simplify (Mult a (Mult t@(Const b) c)) = simplify $ Mult t (simplify $ Mult a c)
simplify (Plus (Plus t@(Const a) b) c) = simplify $ Plus t (simplify $ Plus b c)
simplify (Plus (Minus t@(Const a) b) c) = simplify $ Plus t (simplify $ Minus c b)
simplify (Minus (Plus t@(Const a) b) c) = simplify $ Plus t (simplify $ Minus b c)
simplify (Minus (Minus t@(Const a) b) c) = simplify $ Minus t (simplify $ Plus b c)
simplify (Mult (Mult t@(Const a) b) c) = simplify $ Mult t (simplify $ Mult b c)
simplify (Mult a (Minus t@(Const 0) b)) = simplify $ Minus t (simplify $ Mult a b)
simplify (Mult (Minus t@(Const 0) b) a) = simplify $ Minus t (simplify $ Mult a b)
simplify (Div (Minus t@(Const 0) a) b) = simplify $ Minus t (simplify $ Div a b)
simplify (Div a (Minus t@(Const 0) b)) = simplify $ Minus t (simplify $ Div a b)
-- fallback rule
simplify a = a

colSimplify :: (Eq s, Eq c, Eq b) => ColExpr s c b -> ColExpr s c b
-- dropout rules
colSimplify t@(ColTerm _) = t
-- simplify rules
--- level 1
colSimplify (ColMap f1 (ColMap f2 c)) = colSimplify $ ColMap (f1.f2) c
colSimplify (ColMap f (ColList l)) = colSimplify $ ColList (map f l)
--- level 2
colSimplify (ColSlice p1 l1 (ColSlice p2 l2 c)) = colSimplify $ ColSlice (p1 . p2) l1 c
-- reordering rules
--- level 2
colSimplify (ColCat (ColCat c1 c2) c3) = colSimplify $ ColCat c1 (colSimplify $ ColCat c2 c3)
colSimplify (ColSlice p l (ColMap f c)) = colSimplify $ ColMap f $ colSimplify $ ColSlice p l c
-- fallback rule
colSimplify x = x

boolSimplify :: (Eq s, Eq c, Eq b) => BoolExpr s c b -> BoolExpr s c b
-- dropout rules
boolSimplify t@(BoolTerm _) = t
boolSimplify t@(BoolConst _) = t
-- simplify rules
--- level 0
boolSimplify (BoolAnd (BoolConst False) _) = BoolConst False
boolSimplify (BoolAnd (BoolConst True) a) = a
boolSimplify (BoolAnd _ (BoolConst False)) = BoolConst False
boolSimplify (BoolAnd a (BoolConst True)) = a
boolSimplify (BoolOr (BoolConst True) _) = BoolConst True
boolSimplify (BoolOr (BoolConst False) a) = a
boolSimplify (BoolOr _ (BoolConst True)) = BoolConst True
boolSimplify (BoolOr a (BoolConst False)) = a
boolSimplify (BoolNot (BoolConst a)) = BoolConst (not a)
boolSimplify (BoolEqual (BoolConst True) a) = a
boolSimplify (BoolEqual a (BoolConst True)) = a
boolSimplify (BoolNot (BoolNot a)) = a
boolSimplify (BoolOr a b) | a==b = a
boolSimplify (BoolAnd a b) | a==b = a
boolSimplify (BoolEqual a b) | a==b = BoolConst False
boolSimplify (Rel (Const a) r (Const b)) = BoolConst $ relCheck a r b
boolSimplify (BoolAll f (ColList [])) = BoolConst True
boolSimplify (BoolAny f (ColList [])) = BoolConst False
boolSimplify (BoolAll f (ColList [a])) = f a
boolSimplify (BoolAny f (ColList [a])) = f a
boolSimplify (ColEqual (ColList []) (ColList [])) = BoolConst True
boolSimplify (ColEqual (ColList []) (ColList _)) = BoolConst False
boolSimplify (ColEqual (ColList _) (ColList [])) = BoolConst False
boolSimplify (BoolCond (BoolConst True) t _) = t
boolSimplify (BoolCond (BoolConst False) _ f) = f
--- level 1
boolSimplify (BoolEqual (BoolNot a) (BoolNot b)) = boolSimplify $ BoolEqual a b
boolSimplify (BoolEqual (BoolConst False) a) = boolSimplify $ BoolNot a
boolSimplify (BoolEqual a (BoolConst False)) = boolSimplify $ BoolNot a
boolSimplify (BoolNot (Rel a EREqual b)) = boolSimplify $ Rel a ERDiff b
boolSimplify (BoolNot (Rel a ERDiff b)) = boolSimplify $ Rel a EREqual b
boolSimplify (BoolAll f (ColList [a,b])) = boolSimplify $ f a `BoolAnd` f b
boolSimplify (BoolAny f (ColList [a,b])) = boolSimplify $ f a `BoolOr` f b
boolSimplify (ColEqual (ColList [a]) (ColList [b])) = boolSimplify $ Rel a EREqual b
boolSimplify (Rel (Channel a) EREqual (Channel b)) = boolSimplify $ BoolEqual a b
boolSimplify (BoolCond (BoolNot c) t f) = boolSimplify $ BoolCond c f t
--- level 2
boolSimplify (BoolAnd (BoolNot a) (BoolNot b)) = boolSimplify $ BoolNot $ boolSimplify $ BoolOr a b
boolSimplify (BoolOr (BoolNot a) (BoolNot b)) = boolSimplify $ BoolNot $ boolSimplify $ BoolAnd a b
boolSimplify (Rel (Channel a) ERDiff (Channel b)) = boolSimplify $ BoolNot $ boolSimplify $ BoolEqual a b
boolSimplify (Rel (Channel a) ERLess (Channel b)) = boolSimplify $ BoolAnd b $ boolSimplify $ BoolNot a     -- int(b1) < int(b2)   <=>  !b1 && b2
-- fallback
boolSimplify a = a

-------------------------------------------------------------------
-- | Turn expressions over expressions into simply expressions | --
-------------------------------------------------------------------

collapse :: (Eq t, Eq c, Eq b) => Expr (Expr t c b) (ColExpr t c b) (BoolExpr t c b) -> Expr t c b
collapse (Term t) = t
collapse (Const i) = Const i
collapse (Plus a b) = simplify $ Plus (collapse a) (collapse b)
collapse (Minus a b) = simplify $ Minus (collapse a) (collapse b)
collapse (Mult a b) = simplify $ Mult (collapse a) (collapse b)
collapse (Div a b) = simplify $ Div (collapse a) (collapse b)
collapse (Mod a b) = simplify $ Mod (collapse a) (collapse b)
collapse (Abs a) = simplify $ Abs (collapse a)
collapse (At c a) = simplify $ At (colCollapse c) (collapse a)
collapse (ColSize c) = simplify $ ColSize (colCollapse c)
collapse (Fold f i c) = simplify $ Fold (\a b -> collapse $ f (Term a) (Term b)) (collapse i) (colCollapse c)
collapse (Channel b) = simplify $ Channel (boolCollapse b)
collapse (Cond c t e) = simplify $ Cond (boolCollapse c) (collapse t) (collapse e)

colCollapse :: (Eq t, Eq c, Eq b) => ColExpr (Expr t c b) (ColExpr t c b) (BoolExpr t c b) -> ColExpr t c b
colCollapse (ColTerm t) = t
colCollapse (ColList l) = colSimplify $ ColList $ map collapse l
colCollapse (ColMap f c) = colSimplify $ ColMap (\a -> collapse $ f (Term a)) (colCollapse c)
colCollapse (ColSlice p l c) = colSimplify $ ColSlice (\x -> collapse $ p (Term x)) (collapse l) (colCollapse c)
colCollapse (ColCat a b) = colSimplify $ ColCat (colCollapse a) (colCollapse b)
colCollapse (ColRange a b) = colSimplify $ ColRange (collapse a) (collapse b)

boolCollapse :: (Eq t, Eq c, Eq b) => BoolExpr (Expr t c b) (ColExpr t c b) (BoolExpr t c b) -> BoolExpr t c b
boolCollapse (BoolTerm t) = t
boolCollapse (BoolConst c) = BoolConst c
boolCollapse (BoolAnd a b) = boolSimplify $ BoolAnd (boolCollapse a) (boolCollapse b)
boolCollapse (BoolOr a b) = boolSimplify $ BoolOr (boolCollapse a) (boolCollapse b)
boolCollapse (BoolEqual a b) = boolSimplify $ BoolEqual (boolCollapse a) (boolCollapse b)
boolCollapse (BoolNot a) = boolSimplify $ BoolNot (boolCollapse a)
boolCollapse (Rel a r b) = boolSimplify $ Rel (collapse a) r (collapse b)
boolCollapse (BoolAll f c) = boolSimplify $ BoolAll (\a -> boolCollapse $ f (Term a)) (colCollapse c)
boolCollapse (BoolAny f c) = boolSimplify $ BoolAny (\a -> boolCollapse $ f (Term a)) (colCollapse c)
boolCollapse (ColEqual a b) = boolSimplify $ ColEqual (colCollapse a) (colCollapse b)
boolCollapse (Sorted b c) = boolSimplify $ Sorted b (colCollapse c)
boolCollapse (AllDiff b c) = boolSimplify $ AllDiff b (colCollapse c)
boolCollapse (BoolCond c t e) = boolSimplify $ BoolCond (boolCollapse c) (boolCollapse t) (boolCollapse e)
boolCollapse (Dom i c) = boolSimplify $ Dom (collapse i) (colCollapse c)

-----------------------------------------
-- | walk through expressions
-----------------------------------------

data WalkPhase = WalkPre | WalkSingle | WalkPost
  deriving (Ord,Eq,Enum,Show)

data WalkResult = WalkSkip | WalkDescend
  deriving (Ord,Eq,Enum,Show)

xwalker :: (Eq t, Eq c, Eq b, Monad m) => (WalkPhase -> m WalkResult) -> (Expr t c b -> WalkPhase -> m WalkResult, ColExpr t c b -> WalkPhase -> m WalkResult, BoolExpr t c b -> WalkPhase -> m WalkResult) -> ([Expr t c b],[ColExpr t c b],[BoolExpr t c b]) -> m ()
xwalker q f ([],[],[]) = do
  q WalkSingle
  return ()
xwalker q f (li,lc,lb) = do
  r <- q WalkPre
  case r of
    WalkSkip -> return ()
    WalkDescend -> do
      mapM_ (\p -> walk p f) li
      mapM_ (\p -> colWalk p f) lc
      mapM_ (\p -> boolWalk p f) lb
      q WalkPost
      return ()

walker :: (Eq t, Eq c, Eq b, Monad m) => Expr t c b -> (Expr t c b -> WalkPhase -> m WalkResult, ColExpr t c b -> WalkPhase -> m WalkResult, BoolExpr t c b -> WalkPhase -> m WalkResult) -> ([Expr t c b],[ColExpr t c b],[BoolExpr t c b]) -> m ()
walker x f@(i,c,b) l = xwalker (i x) f l
colWalker :: (Eq t, Eq c, Eq b, Monad m) => ColExpr t c b -> (Expr t c b -> WalkPhase -> m WalkResult, ColExpr t c b -> WalkPhase -> m WalkResult, BoolExpr t c b -> WalkPhase -> m WalkResult) -> ([Expr t c b],[ColExpr t c b],[BoolExpr t c b]) -> m ()
colWalker x f@(i,c,b) l = xwalker (c x) f l
boolWalker :: (Eq t, Eq c, Eq b, Monad m) => BoolExpr t c b -> (Expr t c b -> WalkPhase -> m WalkResult, ColExpr t c b -> WalkPhase -> m WalkResult, BoolExpr t c b -> WalkPhase -> m WalkResult) -> ([Expr t c b],[ColExpr t c b],[BoolExpr t c b]) -> m ()
boolWalker x f@(i,c,b) l = xwalker (b x) f l

walk :: (Eq t, Eq c, Eq b, Monad m) => Expr t c b -> (Expr t c b -> WalkPhase -> m WalkResult, ColExpr t c b -> WalkPhase -> m WalkResult, BoolExpr t c b -> WalkPhase -> m WalkResult) -> m ()
walk x@(Term _) f = walker x f ([],[],[])
walk x@(Const _) f = walker x f ([],[],[])
walk x@(Plus a b) f = walker x f ([a,b],[],[])
walk x@(Minus a b) f = walker x f ([a,b],[],[])
walk x@(Mult a b) f = walker x f ([a,b],[],[])
walk x@(Div a b) f = walker x f ([a,b],[],[])
walk x@(Mod a b) f = walker x f ([a,b],[],[])
walk x@(Abs a) f = walker x f ([a],[],[])
walk x@(At c a) f = walker x f ([a],[c],[])
walk x@(ColSize c) f = walker x f ([],[c],[])
walk x@(Fold _ i c) f = walker x f ([i],[c],[])
walk x@(Channel b) f = walker x f ([],[],[b])
walk x@(Cond c t e) f = walker x f ([t,e],[],[c])
walk x@(ExprHole _) f = return ()

colWalk x@(ColTerm _) f = colWalker x f ([],[],[])
colWalk x@(ColList l) f = colWalker x f (l,[],[])
colWalk x@(ColMap _ c) f = colWalker x f ([],[c],[])
colWalk x@(ColSlice _ l c) f = colWalker x f ([l],[c],[])
colWalk x@(ColCat a b) f = colWalker x f ([],[a,b],[])
colWalk x@(ColRange a b) f = colWalker x f ([a,b],[],[])

boolWalk x@(BoolTerm _) f = boolWalker x f ([],[],[])
boolWalk x@(BoolConst _) f = boolWalker x f ([],[],[])
boolWalk x@(BoolAnd a b) f = boolWalker x f ([],[],[a,b])
boolWalk x@(BoolOr a b) f = boolWalker x f ([],[],[a,b])
boolWalk x@(BoolEqual a b) f = boolWalker x f ([],[],[a,b])
boolWalk x@(BoolNot a) f = boolWalker x f ([],[],[a])
boolWalk x@(Rel a _ b) f = boolWalker x f ([a,b],[],[])
boolWalk x@(BoolAll _ c) f = boolWalker x f ([],[c],[])
boolWalk x@(BoolAny _ c) f = boolWalker x f ([],[c],[])
boolWalk x@(ColEqual a b) f = boolWalker x f ([],[a,b],[])
boolWalk x@(Sorted _ c) f = boolWalker x f ([],[c],[])
boolWalk x@(AllDiff _ c) f = boolWalker x f ([],[c],[])
boolWalk x@(BoolCond c t e) f = boolWalker x f ([],[],[c,t,e])
boolWalk x@(Dom i c) f = boolWalker x f ([i],[c],[])

