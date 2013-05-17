module Control.Search.Combinator.Once (once, onceOld) where

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Generator
import Control.Search.Memo
import Control.Search.Stat
import Control.Search.Combinator.Until

import Control.Monatron.IdT

onceLoop :: MkEval m
onceLoop super = return $ commentEval $ super
                 { evalState_  = ("onceMore", Bool, const $ return true) : evalState_ super
		 , bodyH     = \i -> do goOn <- bodyE super i
                                        ca <- cachedAbort i
                                        return $ IfThenElse (estate i @=> "onceMore")
                                                   goOn
                                                   ca
		 , returnH   = \i -> returnE super $ i `onCommit` assign false (estate i @=> "onceMore")
                 , toString  = "once(" ++ toString super ++ ")"
                 }

once :: Search
once = 
  Search { mkeval     = onceLoop
         , runsearch  = runIdT
         } 

onceOld = limit 1 solutionsStat
