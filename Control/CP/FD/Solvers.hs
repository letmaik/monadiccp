{-# LANGUAGE CPP #-}

module Control.CP.FD.Solvers where

import qualified Control.CP.PriorityQueue as PriorityQueue
import qualified Data.Sequence

import Control.CP.ComposableTransformers
import Control.CP.SearchTree
import Control.CP.FD.FD
import Control.CP.FD.OvertonFD.Sugar
import Control.CP.FD.OvertonFD.OvertonFD
import Control.CP.FD.Gecode.CodegenSolver

#ifdef RGECODE
import Control.CP.FD.Gecode.RuntimeSolver
#endif

--------------------------------------------------------------------------------
-- FORCE SOLVERS
--------------------------------------------------------------------------------

as_overtonfd :: Tree (FDWrapper OvertonFD) a -> Tree (FDWrapper OvertonFD) a
as_overtonfd = id

as_gecode_codegen :: Tree (FDWrapper CodegenSolver) a -> Tree CodegenSolver a
as_gecode_codegen = unwrap

#ifdef RGECODE
as_gecode_runtime :: Tree (FDWrapper RuntimeSolver) a -> Tree (FDWrapper RuntimeSolver) a
as_gecode_runtime = id

as_gecode_search :: Tree (FDWrapper SearchSolver) a -> Tree (FDWrapper SearchSolver) a
as_gecode_search = id
#endif

------------------------------------------------------------------------------
-- SEARCH STRATEGIES
------------------------------------------------------------------------------

dfs = []
bfs = Data.Sequence.empty
pfs :: Ord a => PriorityQueue.PriorityQueue a (a,b,c)
pfs = PriorityQueue.empty

nb :: Int -> CNodeBoundedST s a
nb = CNBST
db :: Int -> CDepthBoundedST s a
db = CDBST
bb :: NewBound s -> CBranchBoundST s a
bb = CBBST
fs :: CFirstSolutionST s a
fs = CFSST
it :: CIdentityCST s a
it = CIST
ra :: Int -> CRandomST s a
ra = CRST
ld :: Int -> CLimitedDiscrepancyST s a
ld = CLDST

