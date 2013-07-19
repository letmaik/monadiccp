{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.CP.FD.Example (
  example_main,
  example_sat_main,
  example_sat_main_void,
  example_sat_main_single,
  example_sat_main_single_expr,
  example_sat_main_coll_expr,
  example_min_main,
  example_min_main_void,
  example_min_main_single,
  example_min_main_single_expr,
  example_min_main_coll_expr,
  runSolve,
  labeller,
  postMinimize,
  ExampleModel, ExampleMinModel, 
  module Control.CP.FD.Interface,
) where


import System.Environment (getArgs)
import Data.Maybe (fromJust,isJust)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (init,last)

import Control.CP.FD.OvertonFD.OvertonFD
import Control.CP.FD.OvertonFD.Sugar
import Control.CP.FD.FD
import Control.CP.FD.Model

import Control.CP.Debug

import Control.CP.FD.Interface
import Control.CP.SearchTree
import Control.CP.EnumTerm
import Control.CP.ComposableTransformers
import Control.CP.FD.Solvers

import Control.Monad.Cont

type ExampleModel t =    (forall s m. (Show (FDIntTerm s), FDSolver s, MonadTree m, TreeSolver m ~ (FDInstance s)) => t -> m (ModelCol))
type ExampleMinModel t = (forall s m. (Show (FDIntTerm s), FDSolver s, MonadTree m, TreeSolver m ~ (FDInstance s)) => t -> m (ModelInt,ModelCol))

postMinimize :: ExampleMinModel t -> ExampleModel t
postMinimize m = \x -> do
  (min,res) <- m x
  debug ("postMinimize: min="++(show min)) $ return ()
  label $ do
    setMinimizeVar min
    return $ return res

runSolveSAT x = solve dfs fs x
runSolveMIN x = solve dfs (bb boundMinimize) x

runSolve False x = runSolveSAT x
runSolve True  x = runSolveMIN x

labeller col = do
  label $ do
    min <- getMinimizeVar
    case min of
      Nothing -> return $ labelCol col
      Just v -> return $ do
        enumerate [v]
        labelCol col

example_main :: ExampleModel [String] -> ExampleModel ModelInt -> ExampleModel ModelCol -> Bool -> IO ()
example_main f fx fcx typ = do
  args <- getArgs
  case args of
    ("overton_run":r) -> print $ runSolve typ $ ((f r) :: Tree (FDInstance OvertonFD) ModelCol) >>= labeller
    [] -> putStr "Solver type required: must be overton_run\n"
    (a:r) -> putStr ("Unsupported solver: " ++ a ++ "\n")

example_min_main :: ExampleMinModel [String] -> ExampleMinModel ModelInt -> ExampleMinModel ModelCol -> IO ()
example_min_main f fx fcx = example_main (postMinimize f) (postMinimize fx) (postMinimize fcx) True

example_sat_main :: ExampleModel [String] -> ExampleModel ModelInt -> ExampleModel ModelCol -> IO ()
example_sat_main f fx fcx = example_main f fx fcx False

example_sat_main_void :: ExampleModel () -> IO ()
example_sat_main_void f = example_sat_main (const $ f ()) (const $ f ()) (const $ f ())

example_min_main_void :: ExampleMinModel () -> IO ()
example_min_main_void f = example_min_main (const $ f ()) (const $ f ()) (const $ f ())

example_sat_main_single :: Read n => ExampleModel n -> IO ()
example_sat_main_single f = example_sat_main (f . read . head) (error "Uncompilable model") (error "Uncompilable model")

example_min_main_single :: Read n => ExampleMinModel n -> IO ()
example_min_main_single f = example_min_main (f . read . head) (error "Uncompilable model") (error "Uncompilable model")

example_sat_main_single_expr :: ExampleModel ModelInt -> IO ()
example_sat_main_single_expr f = example_sat_main (f . fromInteger . read . head) f (\x -> f $ x!(cte 0))

example_min_main_single_expr :: ExampleMinModel ModelInt -> IO ()
example_min_main_single_expr f = example_min_main (f . fromInteger . read . head) f (\x -> f $ x!(cte 0))

example_sat_main_coll_expr :: ExampleModel ModelCol -> IO ()
example_sat_main_coll_expr f = example_sat_main (f . list . foldr (++) [] . map (map fromInteger . read . (\x -> "[" ++ x ++ "]"))) (f. list . (\x -> [x])) f

example_min_main_coll_expr :: ExampleMinModel ModelCol -> IO ()
example_min_main_coll_expr f = example_min_main (f . list . foldr (++) [] . map (map fromInteger . read . (\x -> "[" ++ x ++ "]"))) (f. list . (\x -> [x])) f
