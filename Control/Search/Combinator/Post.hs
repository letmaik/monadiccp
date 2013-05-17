{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.Search.Combinator.Post (post) where

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Generator
import Control.Search.Constraints

postLoop :: VarInfoM m => ConstraintGen -> MkEval m -> MkEval m
postLoop (ConstraintGen c l) par this = do
  super <- par this
  return $ commentEval $ super 
    {   tryH = try tryE super
      , startTryH = try startTryE super
      , toString = "post(<CONSTRAINT>," ++ toString super ++ ")"
      , intVarsE = l ++ intVarsE super
    }
 where try f super = \i -> -- failE super i >>= \fail -> -- XXX
                        f super i >>= \body ->
                          c i >>= \cc ->
                            return $ Post (space i) cc >>> body
--                                     (Var "status" <== VHook (rp 0 (space i) ++ "->status()")) >>>
--                                     IfThenElse (Var "status" @== VHook "SS_FAILED") (fail >>> comment "Delete-postLoop-try" >>> Delete (space i)) body


post :: ConstraintGen -> Search -> Search
post c s =
  case s of 
    Search { mkeval = m, runsearch = r } ->
      Search { mkeval = postLoop c m
             , runsearch = r
             }
