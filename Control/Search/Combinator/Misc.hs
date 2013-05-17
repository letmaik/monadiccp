{-# LANGUAGE FlexibleContexts #-}

module Control.Search.Combinator.Misc (dbs, lds, bbmin) where

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Generator
import Control.Search.Stat

import Data.Int

import Control.Monatron.IdT

ldsLoop :: Monad m => Stat -> MkEval m
ldsLoop limit super' = return $ commentEval $ super
                     { treeState_  = entry ("lds",Int,assign 0) : treeState_ super
                     , initH  = \i -> readStat limit >>= \f -> initH super i @>>>@ return (assign (f i) (tstate i @-> "lds"))
                     , evalState_  = ("lds_complete", Bool, const $ return true) : evalState_ super
                     , pushLeftH   = \i -> pushLeft  super (i `onCommit` mkCopy i "lds")
                     , pushRightH  = \i -> pushRight super (i `onCommit` mkUpdate i "lds" (\x -> x - 1)) >>= \stmt -> 
						return $ IfThenElse 
							   (tstate (old i) @-> "lds" @>= 0) 
                                                           stmt
							   (abort i >>> (estate i @=> "lds_complete" <== false))
                     , toString = "lds(" ++ show limit ++ "," ++ toString super ++ ")"
                     , complete = \i -> return $ estate i @=> "lds_complete"
                     }
  where super = evalStat limit super'

--------------------------------------------------------------------------------
dbsLoop :: Monad m => Int32 -> MkEval m
dbsLoop limit super = return $ commentEval $ super
                     { treeState_  = entry ("depth_limit",Int,assign $ IVal limit) : treeState_ super
                     , evalState_  = ("dbs_complete", Bool, const $ return true) : evalState_ super
		     , pushLeftH   = push pushLeft
                     , pushRightH  = push pushRight
                     , toString = "dbs(" ++ show limit ++ "," ++ toString super ++ ")"
                     , complete = \i -> return $ estate i @=> "dbs_complete"
                     }
  where push dir = 
	  \i -> dir super (i `onCommit` mkUpdate i "depth_limit" (\x -> x - 1)) >>= \stmt ->
                return $ IfThenElse (tstate (old i) @-> "depth_limit" @>= 0)
                                    stmt
                                    ((estate i @=> "dbs_complete" <== false) >>> abort i)

--------------------------------------------------------------------------------
bbLoop :: Monad m => String -> MkEval m 
bbLoop var super = return $ commentEval $ super
  { treeState_  = entry ("tree_bound_version",Int,assign 0) : treeState_ super
  , evalState_   = ("bound_version",Int,const $ return 0) : ("bound",Int,const $ return $ IVal maxBound) : evalState_ super
  , returnH     = \i -> returnE super (i `onCommit`
			   let get = VHook (rp 0 (space i) ++ "->iv[VAR_" ++ var ++ "].min()")
                           in  (Assign (estate i @=> "bound") get >>> inc (estate i @=> "bound_version"))) 
  , bodyH = \i -> let set = Post (space i) (VHook (rp 0 (space i) ++ "->iv[VAR_" ++ var ++ "]") $< (estate i @=> "bound"))
                              in  do r <- bodyE super i
                                     return $ (ifthen (tstate i @-> "tree_bound_version" @< (estate i @=>"bound_version"))
                                                      (set >>> (Assign (tstate i @-> "tree_bound_version") ((tstate i @-> "tree_bound_version") + 1)))
                                                           >>> r)
  , pushLeftH  = push pushLeft
  , pushRightH = push pushRight
  , intVarsE  = var : intVarsE super
  , complete = const $ return true
  , toString = "bb(" ++ show var ++ "," ++ toString super ++ ")"
  }
  where push dir = \i -> dir super (i `onCommit` mkCopy i "tree_bound_version")

bbmin :: String -> Search
bbmin var = 
  Search { mkeval     = bbLoop var 
         , runsearch  = runIdT
         }

lds :: Stat -> Search
lds n = 
  Search { mkeval     = ldsLoop n
         , runsearch  = runIdT
         }

dbs :: Int32 -> Search
dbs n = 
  Search { mkeval     = dbsLoop n
         , runsearch  = runIdT
         } 

