module Control.Search.Combinator.Success (dummy) where

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Generator
import Control.Search.Memo

import Control.Monatron.IdT

successLoop :: Evalable m => Eval m -> Eval m
successLoop this = commentEval $
	    Eval { structs      = ([],[])
                 , treeState_  = []
                 , initH       = const $ return Skip
                 , evalState_  = []
		 , pushLeftH    = error "succesloop.tyE_"
		 , pushRightH   = error "succesloop.tyE_"
	         , nextSameH    = \i -> return Skip
	         , nextDiffH    = \i -> return Skip
		 , bodyH       = addE this . resetInfo -- XXX
                 , addH        = \i -> tryE this (resetInfo i)
	         , failH      = const $ return Skip
                 , returnH    = \i -> cachedCommit i
                                -- const $ return Skip
--                 , continue   = \_ -> return true
                 , tryH       = returnE this . resetInfo
                 , startTryH  = \i -> (return $ comment "<startTryE success>") @>>>@ (returnE this . resetInfo) i @>>>@ (return $ comment "</startTryE succes>")
                 , tryLH      = error "succesloop.tryE_"
                 , intArraysE  = []
                 , boolArraysE    = []
                 , intVarsE    = []
		 , deleteH     = \i -> return Skip
                 , toString = "succeed"
                 , canBranch   = return False
                 , complete = const $ return true
                 }

dummy = Search { mkeval = return . successLoop, runsearch = runIdT }
