{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers & Pieter Wuille
 -}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.CP.FD.FD (
  FDSolver(..),
  fresh_var,
  decompose,
  compile_constraint,
  FDExpr,
  FDConstraint(..),
  FDWrapper(..),
  FDTree,
  FDLabel(..),
  wrap,
  unwrap,
  (@:), (@<), (@>), (@<=), (@>=), (@=), (@/=),
  (@+), (@-), (@*), (@/), (@%), 
  cte,
  allDiff,
  sorted,
  sSorted,
  allin
)where 

import GHC.Exts (sortWith)

import Control.CP.SearchTree hiding (label)
import Control.CP.Transformers
import Control.CP.ComposableTransformers
import Control.CP.Queue
import Control.CP.Solver
import Control.CP.EnumTerm
import Control.CP.Debug
import Control.CP.Mixin
import Control.CP.FD.Expr

--------------------------------------------------------------------------------
-- SYNTACTIC SUGAR
--------------------------------------------------------------------------------

-- define class FDSolver, instances of which must define a compile_constraint
-- function, to convert a constraint specified in syntactic sugar to a 
-- corresponding search Tree. Instances must furthermore specify a
-- FDTerm x type, referring to the type of terms used
class (Show (FDTerm s), Eq (FDTerm s), Term s (FDTerm s)) => FDSolver s where
  -- types
  type FDTerm s :: *
  -- functions
  specific_compile_constraint :: Mixin (FDConstraint s -> Tree s Bool)
  specific_decompose :: Mixin (Expr (FDTerm s) -> Tree s (FDTerm s))
  specific_fresh_var :: Mixin (Tree s (FDTerm s))
  -- default implementations
  specific_decompose = mixinId
  specific_fresh_var = mixinId

-- compile constraint + defaults
compile_constraint :: FDSolver s => FDConstraint s -> Tree s Bool
compile_constraint = mixin (specific_compile_constraint <@> default_compile_constraint)
default_compile_constraint :: FDSolver so => Mixin (FDConstraint so -> Tree so Bool)
default_compile_constraint = default_compile_alldiff 
                             <@> default_compile_sorted 
                             <@> default_compile_dom

-- decompose + default
decompose :: FDSolver s => Expr (FDTerm s) -> Tree s (FDTerm s)
decompose = mixin (front_decompose <@> specific_decompose <@> default_decompose)
default_decompose :: FDSolver s => Mixin (Expr (FDTerm s) -> Tree s (FDTerm s))
default_decompose _ _ x = debug "default_decompose" $ do
  v <- fresh_var
  compile_constraint (Same x (Term v))
  return v
front_decompose :: FDSolver s => Mixin (Expr (FDTerm s) -> Tree s (FDTerm s))
front_decompose s t (Term x) = debug "front_decompose Term" $ return x
front_decompose s t x = debug "front_decompose _" $ s x

-- fresh_var + default
fresh_var :: FDSolver s => Tree s (FDTerm s)
fresh_var = mixin (specific_fresh_var <@> default_fresh_var)
default_fresh_var :: FDSolver s => Mixin (Tree s (FDTerm s))
default_fresh_var _ _ = debug "default_fresh_var" $ NewVar $ \v -> return v

type FDExpr s = Expr (FDTerm s)

-- currently 4 simple constraints + more complex (see default compiler at the bottom)
data Show (FDTerm s) => FDConstraint s =
   Less    (Expr (FDTerm s)) (Expr (FDTerm s))
 | Diff    (Expr (FDTerm s)) (Expr (FDTerm s))
 | Same    (Expr (FDTerm s)) (Expr (FDTerm s))
 | Dom     (Expr (FDTerm s)) Integer Integer
 | AllDiff [Expr (FDTerm s)]
 | Sorted  [Expr (FDTerm s)] Bool -- True = less-or-equal, False = less

deriving instance Show (FDTerm s) => Show (FDConstraint s)


----------------------- FDWrapper

newtype FDWrapper s a = FDWrapper { subFD :: s a }

type FDTree s a = Tree (FDWrapper s) a

newtype FDLabel s = FDLabel (Label s)

instance FDSolver s => Monad (FDWrapper s) where
  FDWrapper { subFD = a } >>= f = FDWrapper { subFD = a >>= (\x -> subFD $ f x) }
  return x = FDWrapper { subFD = return x }

instance FDSolver s => Solver (FDWrapper s) where
  type Constraint (FDWrapper s) = FDConstraint s
  type Label (FDWrapper s) = FDLabel s
  add c = FDWrapper { subFD = untree False $ compile_constraint c }
  run (FDWrapper { subFD = x}) = run x
  mark = FDWrapper { subFD = mark >>= \x -> return (FDLabel x) }
  goto (FDLabel l) = FDWrapper { subFD = goto l }

data EQHelp a b where
  EQHelp :: EQHelp a a

instance (FDSolver s, t ~ Expr (FDTerm s)) => Term (FDWrapper s) t where
  type Help (FDWrapper s) t = EQHelp t (Expr (FDTerm s))
  help _ _ = EQHelp
  newvar = FDWrapper { subFD = newvar >>= (\x -> return (Term x)) }

instance (FDSolver s, FDTerm s ~ t, Eq t, EnumTerm s t, Integral (TermDomain s t)) => EnumTerm (FDWrapper s) (Expr t) where
  type TermDomain (FDWrapper s) (Expr t) = TermDomain s t
  get_domain_size (Const c) = return 1
  get_domain_size (Term v) = FDWrapper (get_domain_size v)
  get_value (Const c) = return $ Just $ fromInteger c
  get_value (Term v) = FDWrapper $ get_value v
  split_domain_partial (Const c) = return [return ()]
  split_domain_partial (Term v) = FDWrapper $ split_domain_partial v >>= return . map wrap
  split_domain (Const c) = return $ return ()
  split_domain (Term v) = FDWrapper $ split_domain v >>= return . wrap
  split_domains l = FDWrapper $ split_domains (map (\x -> case x of Term t -> t) l) >>= return . wrap

unwrap :: forall s a .FDSolver s => Tree (FDWrapper s) a -> Tree s a
unwrap Fail = Fail
unwrap (Return a) = Return a
unwrap (Try l r) = Try (unwrap l) (unwrap r)
unwrap (NewVar (f :: t -> Tree (FDWrapper s) a)) = NewVar ((\v -> 
                         case help (undefined :: FDWrapper s ()) (undefined :: t) of
                           EQHelp -> unwrap (f (Term v :: Expr (FDTerm s)))) 
			   :: FDTerm s -> Tree s a)
unwrap (Add c t) = compile_constraint c >>= (\b -> if b then (unwrap t) else Fail)
unwrap (Label (FDWrapper { subFD = m })) = Label (m >>= \x -> return (unwrap x))

wrap :: forall s a .FDSolver s => Tree s a -> Tree (FDWrapper s) a
wrap Fail = Fail
wrap (Return a) = Return a
wrap (Try l r) = Try (wrap l) (wrap r)
wrap (Label m) = Label $ FDWrapper $ m >>= return . wrap
wrap (Add c t) = Label $ FDWrapper $ add c >>= \res -> if res then return $ wrap t else return $ false
wrap (NewVar f) = Label $ FDWrapper $ newvar >>= return . wrap . f


-- TODO: wrap afmaken
-- TODO: Tree opsplitsen in Tree (Try nodes) en Conjunction (de rest)


----------------------- Operators

-- syntactic sugar for expressions
infixl 6 @+
infixl 6 @-
infixl 7 @*
infixl 7 @/
infixl 7 @%
a @+ b = (toExpr a) + (toExpr b)
a @- b = (toExpr a) - (toExpr b)
a @* b = (toExpr a) * (toExpr b)
a @/ b = (toExpr a) `div` (toExpr b)
a @% b = (toExpr a) `mod` (toExpr b)
cte x = fromInteger $ toInteger x

-- syntactic sugar for relations

infix 4 @:
a @: (b,c) = addC $ Dom a (toInteger b) (toInteger c)

infix 4 @<
a @< b = addC $ Less a b

infix 4 @<=
a @<= b = addC $ Less a (b + 1)

infix 4 @>
a @> b = addC $ Less b a

infix 4 @>=
a @>= b = addC $ Less b (a + 1)

infix 4 @=
a @= b = addC $ Same a b

infix 4 @/=
a @/= b = addC $ Diff a b

allDiff l = addC $ AllDiff l
sorted l = addC $ Sorted l True
sSorted l = addC $ Sorted l False

allin list range  = foldr1 (/\) $ map (@: range) list

---------------------------------------------------------------------------------
-- Default compilations
---------------------------------------------------------------------------------

default_compile_alldiff :: FDSolver so => Mixin (FDConstraint so -> Tree so Bool)
default_compile_alldiff s t c = case c of
  (AllDiff []) -> return True
  (AllDiff (x:xs)) -> do
    conj [ (t $ Diff x e) /\ return () | e <- xs ]
    t $ AllDiff xs
    return True
  _ -> s c

default_compile_sorted :: FDSolver so => Mixin (FDConstraint so -> Tree so Bool)
default_compile_sorted s t c = case c of
  (Sorted [] _) -> return True
  (Sorted (x:xs) eq) -> do
    conj [ (t $ Less x (if eq then e+1 else e)) /\ return () | e <- xs ]
    t $ Sorted xs eq
    return True
  _ -> s c

default_compile_dom :: FDSolver so => Mixin (FDConstraint so -> Tree so Bool)
default_compile_dom s t c = case c of
  (Dom _ l u) | l>u -> Fail
  (Dom x l u) -> do
    t $ Less x (Const $ u+1)
    t $ Less (Const $ l-1) x
    return True
  _ -> s c
