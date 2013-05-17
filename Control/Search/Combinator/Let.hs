module Control.Search.Combinator.Let (let', set') where

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Generator
import Control.Search.Stat

stmPrefixLoop stm super = super { tryH = \i -> (stm i) @>>>@ (tryE super) i, startTryH = \i -> (stm i) @>>>@ (startTryH super) i, toString = "prefix(" ++ toString super ++ ")" }

letLoop :: Evalable m => VarId -> Stat -> Eval m -> Eval m
letLoop v@(VarId i) val super'' = 
  let super' = evalStat val super''
      super = super' { evalState_ = ("var" ++ (show i), Int, \i -> setVarInfo v i >> readStat val >>= \x -> return (x i)) : evalState_ super', 
                       toString = "let(" ++ show v ++ "," ++ show val ++ "," ++ toString super'' ++ ")" }
      in commentEval super

let'
  :: VarId
  -> Stat
  -> Search
  -> Search

let' var val s = 
  case s of
    Search { mkeval = evals, runsearch = runs } ->
      Search { mkeval = \super -> do { ss <- evals super
                                     ; return $ letLoop var val ss
                                     }
             , runsearch = runs
             }

set' :: VarId -> Stat -> Search -> Search
set' var val s = case s of
   Search { mkeval = evals, runsearch = runs } ->
     Search { mkeval = \super -> do { ss <- evals super
                                    ; let ss1 = evalStat (varStat var) ss
                                    ; let ss2 = evalStat val ss1
                                    ; return $ stmPrefixLoop (\i -> readStat (varStat var) >>= \rvar -> readStat val >>= \rval -> return $ Assign (rvar i) (rval i)) ss2
                                    }
            , runsearch = runs
            }
