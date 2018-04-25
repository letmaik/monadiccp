{-# LANGUAGE FlexibleContexts #-}

module Control.Search.Combinator.Repeat (repeat) where

import Prelude hiding (lex, until, init, repeat)

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Generator
import Control.Search.MemoReader
import Control.Search.Memo

import Control.Monatron.Monatron hiding (Abort, L, state, cont)
import Control.Monatron.Zipper hiding (i,r)

repeatLoop :: (ReaderM Bool m, Evalable m) => Int -> Eval m -> Eval m
repeatLoop uid super = commentEval $
    Eval 
       { 
         structs     = structs super @++@ mystructs 
       , toString    = "repeat" ++ show uid ++ "(" ++ toString super ++ ")"
       , treeState_  = ("dummy", Int, 
				\i -> do cc <- cachedClone i (cloneBase i)
                                         return ((parent i <== baseTstate i)
                                                 >>> cc
                                                )
                       ) : treeState_ super -- `withClone` (\k -> inc $ ref_count k)
       , initH       = \i -> initE super i
       , evalState_   = {- ("cont",Bool,const $ return true) : -} ("ref_count",Int,const $ return 1) : ("parent",THook "TreeState",const $ return Null) : evalState_ super
       , pushLeftH    = push pushLeft
       , pushRightH   = push pushRight
       , nextSameH    = nextSame super
       , nextDiffH    = nextDiff super 
       , bodyH = \i -> dec_ref i >>= \deref -> bodyE super (i `onAbort` deref)
       , addH        = addE super
       , failH       = \i -> failE super i @>>>@ dec_ref i
       , returnH     = \i -> let j deref = i `onCommit` deref
                             in dec_ref i >>= returnE super . j
       , tryH        = tryE super
       , startTryH   = startTryE super
       , tryLH       = \i -> tryE_ super i @>>>@ dec_ref i
       , boolArraysE  = boolArraysE super
       , intArraysE  = intArraysE super
       , intVarsE    = intVarsE super
       , deleteH     = error "repeatLoop.deleteE NOT YET IMPLEMENTED"
       , canBranch   = canBranch super
       , complete    = const $ return true
       }
  where mystructs = ([],[])
        fs1       = [(field,init) | (field,ty,init) <- evalState_ super]
        parent    = \i -> estate i @=> "parent"
        dec_ref    = \i -> let i'     = resetCommit $ i `withBase` ("repeat_tstate" ++ show uid)
                           in do flag <- ask 
                                 if flag 
                                   then local (const False) $ do
				 	stmt1 <- inits super i'
                                 	stmt2 <- startTryE super i'
                                        ini <- inite fs1 i'
			         	return (dec (ref_count i) 
                                               >>> ifthen (ref_count i @== 0) 
			                           (   SHook ("TreeState repeat_tstate" ++ show uid ++ ";")
			   			   >>> (baseTstate i' <== parent i)
						   >>> clone (cloneBase i) i'
			                           >>> (ref_count i' <== 1)
--			                           >>> (cont i' <== true)
  			                           >>> ini >>> stmt1 >>> stmt2))
                                   else  return $dec (ref_count i) >>> ifthen (ref_count i @== 0) (comment "Delete-repeatLoop-dec_ref" >>> Delete (space $ cloneBase i))
        push dir  = \i -> dir super (i `onCommit` inc (ref_count i))

repeat 
  :: Search
  -> Search
repeat s = 
  case s of
    Search { mkeval = evals, runsearch = runs } ->
	  Search { mkeval =
	            \super ->
	           do { uid <- get
	              ; put (uid + 1)
	              ; s' <- evals $ mapE (L . L . mmap runL . runL) super
	              ; return $ mapE (L . mmap L . runL) $ repeatLoop uid $ mapE runL s' 
	              }
	         , runsearch  =  runs . rReaderT True . runL
	         } 
