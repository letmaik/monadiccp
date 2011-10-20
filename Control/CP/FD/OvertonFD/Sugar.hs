{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers
 -}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}

module Control.CP.FD.OvertonFD.Sugar (
  newBound,
  newBoundBis,
  restart,
  restartOpt,
) where 

import Control.CP.SearchTree hiding (label)
import Control.CP.Transformers
import Control.CP.ComposableTransformers
import Control.CP.Queue
import Control.CP.Solver
import Control.CP.Debug
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.EnumTerm
import Control.CP.Mixin

import qualified Control.CP.PriorityQueue as PriorityQueue
import qualified Data.Sequence
import Control.CP.FD.OvertonFD.OvertonFD

newBound :: NewBound OvertonFD
newBound = do obj <- fd_objective
              (val:_) <- fd_domain obj 
	      l <- mark
              return ((\tree -> tree `insertTree` (obj @@< val)) :: forall b . Tree OvertonFD b -> Tree OvertonFD b)

newBoundBis :: NewBound OvertonFD 
newBoundBis = do obj <- fd_objective
                 (val:_) <- fd_domain obj 
                 let m = val `div` 2
                 return ((\tree -> (obj @@< (m + 1) \/ ( obj @@> m /\ obj @@< val)) /\ tree) :: forall b . Tree OvertonFD b -> Tree OvertonFD b)

restart :: (Queue q, Solver solver, CTransformer c, CForSolver c ~ solver,
          Elem q ~ (Label solver,Tree solver (CForResult c),CTreeState c)) 
      => q -> [c] -> Tree solver (CForResult c) -> (Int,[CForResult c])
restart q cs model = run $ eval model q (RestartST (map Seal cs) return)

restartOpt :: (Queue q, CTransformer c, CForSolver c ~ OvertonFD,
          Elem q ~ (Label OvertonFD,Tree OvertonFD (CForResult c),CTreeState c)) 
      => q -> [c] -> Tree OvertonFD (CForResult c) -> (Int,[CForResult c])
restartOpt q cs model = run $ eval model q (RestartST (map Seal cs) opt)
	where opt tree = newBound >>= \f -> return (f tree)

--------------------------------------------------------------------------------
-- SYNTACTIC SUGAR
--------------------------------------------------------------------------------

in_domain v (l,u)  = Add (Dom (Term v) l u) true

(@@<) :: FDVar -> Int -> Tree OvertonFD ()
v @@< i  = (compile_constraint $ Less (Term v) (Const $ toInteger i)) /\ return ()

(@@>) :: FDVar -> Int -> Tree OvertonFD ()
v @@> i  = (compile_constraint $ Less (Const $ toInteger i) (Term v)) /\ return ()

--------------------------------------------------------------------------------
-- FD SUGAR
--------------------------------------------------------------------------------

instance FDSolver OvertonFD where
  type FDTerm OvertonFD = FDVar
  specific_compile_constraint = convert

-- convert :: Mixin (FDConstraint OvertonFD -> Tree OvertonFD Bool)
convert s t (Same a (Const i)) = debug "convert (Same a (Const i))" $ do
  va <- decompose a
  addT $ OHasValue va $ fromInteger i
convert s t (Same (Const i) a) = debug "convert (Same (Const i) a)" $ do
  va <- decompose a
  addT $ OHasValue va $ fromInteger i
convert s t (Same (Plus a b) c) = debug "convert (Same (Plus a b) c)" $ do
  va <- decompose a
  vb <- decompose b
  vc <- decompose c
  addT $ OAdd va vb vc
convert s t (Same (Minus a b) c) = debug "convert (Same (Minus a b) c)" $ do
  va <- decompose a
  vb <- decompose b
  vc <- decompose c
  addT $ OSub va vb vc
convert s t (Same (Mult a b) c) = debug "convert (Same (Mult a b) c)" $ do
  va <- decompose a
  vb <- decompose b
  vc <- decompose c
  addT $ OMult va vb vc
convert s t (Same (Abs a) c) = debug "convert (Same (Abs a) c)" $ do
  va <- decompose a
  vc <- decompose c
  addT $ OAbs va vc
convert s t (Same a b@(Plus _ _)) = debug "convert (Same a Plus)" $ convert s t $ Same b a
convert s t (Same a b@(Minus _ _)) = debug "convert (Same a Minus)" $ convert s t $ Same b a
convert s t (Same a b@(Mult _ _)) = debug "convert (Same a Mult)" $ convert s t $ Same b a
convert s t (Same a b@(Abs _)) = debug "convert (Same a Abs)" $ convert s t $ Same b a
convert s t (Same a b) = debug "convert (Same a b)" $ do
  va <- decompose a
  vb <- decompose b
  addT $ OSame va vb
convert s t (Diff a b) = debug "convert (Diff a b)" $ do
  va <- decompose a
  vb <- decompose b
  addT $ ODiff va vb
convert s t (Less a b) = debug "convert (Less a b)" $ do
  va <- decompose a
  vb <- decompose b
  addT $ OLess va vb
convert s t x = debug "convert _" $ s x
