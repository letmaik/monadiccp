{-# LANGUAGE Rank2Types #-}

module Control.CP.FD.Example.Example (
  example_main,
  example_main_void,
  example_main_single,
  FDModel
) where


import System (getArgs)

import Control.CP.ComposableTransformers
import Control.CP.FD.Gecode.Translate
import Control.CP.FD.Solvers
import Control.CP.FD.FD
import Control.CP.EnumTerm
import Control.CP.SearchTree hiding (label)

example_main :: (forall s. FDSolver s => [String] -> FDTree s [FDExpr s]) -> IO ()
example_main f = do
  args <- getArgs
  case args of
    ("gecode_compile":r) -> putStr $ generate_gecode $ as_gecode_codegen $ f r
    ("overton_run":r) -> print $ solve dfs fs $ as_overtonfd $ f r >>= \l -> enumerate l /\ assignments l
    [] -> putStr "Solver type required\n"
    (a:r) -> putStr ("Unsupported solver: " ++ a ++ "\n")

example_main_void :: (forall s. FDSolver s => FDTree s [FDExpr s]) -> IO ()
example_main_void f = example_main (const f)

example_main_single :: Read n => (forall s. FDSolver s => n -> FDTree s [FDExpr s]) -> IO ()
example_main_single f = example_main (f . read . head)

type FDModel = FDSolver s => Tree (FDWrapper s) [FDExpr s]
