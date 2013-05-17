module Control.Search.Combinator.Failure (failure) where

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Generator

import Control.Monatron.Monatron hiding (Abort, L, state, cont)
import Control.Monatron.IdT

failLoop uid _super = 
  commentEval $   Eval { structs    = ([],[])
                       , treeState_ = []
                       , evalState_ = []
		       , pushLeftH   = \_ -> return Skip
		       , pushRightH  = \_ -> return Skip
		       , nextSameH   = \_ -> return Skip
		       , nextDiffH   = \_ -> return Skip
                       , bodyH      = \i -> cachedAbort i
                       , addH       = \_ -> return Skip
	 	       , failH      = \i -> cachedAbort i
                       , returnH    = \i -> cachedAbort i
--                       , continue   = \_ -> return true
                       , tryH       = \i -> cachedAbort i
                       , startTryH  = \i -> cachedAbort i
                       , tryLH      = \_ -> return Skip
                       , intArraysE = []
                       , intVarsE   = []
                       , boolArraysE = []
		       , deleteH     = \i -> cachedAbort i
                       , initH      = \_ -> return $ {- DebugOutput $ "fail" ++ show uid >>> -} Skip
                       , toString   = "fail" ++ show uid
                       , canBranch  = return False
                       , complete = const $ return false
                       }

failure :: Search
failure = 
  Search { mkeval     = \super -> get >>= \uid -> return (failLoop uid super)
         , runsearch  = runIdT
         }
