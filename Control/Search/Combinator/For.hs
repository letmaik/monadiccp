{-# LANGUAGE FlexibleContexts #-}

module Control.Search.Combinator.For (for, foreach) where

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Generator
import Control.Search.Memo
import Control.Search.MemoReader

import Data.Int

import Control.Monatron.Zipper hiding (i,r)
import Control.Monatron.Monatron hiding (Abort, L, state, cont)

forLoop :: (ReaderM Bool m, Evalable m) => Int32 -> Int -> (Eval m) -> Eval m
forLoop n uid (super) = commentEval $
    Eval 
       { 
         structs     = structs super @++@ mystructs 
       , toString    = "for" ++ show uid ++ "(" ++ show n ++ "," ++ toString super ++ ")"
       , treeState_  = treeState_ super
       , initH       = \i -> initE super i @>>>@ return (parent i <== baseTstate i) @>>>@ cachedClone i (cloneBase i)
       , evalState_  = ("counter",Int,const $ return 0) : {- ("cont",Bool,const $ return true) : -} ("ref_count",Int,const $ return 1) : ("parent",THook "TreeState",const $ return Null) : evalState_ super
       , pushLeftH    = push pushLeft
       , pushRightH   = push pushRight
       , nextSameH    = nextSame super
       , nextDiffH    = nextDiff super 
       , bodyH = \i -> dec_ref i >>= \deref -> bodyE super (i `onAbort` deref)
       , addH        = addE super
       , failH       = \i -> failE super i @>>>@ dec_ref i
       , returnH     = \i -> let j deref = i `onCommit` deref
                             in dec_ref i >>= returnE super . j
       , tryH        = \i -> do deref <- dec_ref i
                                tryE super ((i `withField` ("counter", counter)) `onAbort` deref)
       , startTryH   = \i -> do deref <- dec_ref i
                                startTryE super ((i `withField` ("counter", counter)) `onAbort` deref)
       , tryLH       = \i -> tryE_ super i @>>>@ dec_ref i
       , intArraysE  = intArraysE super
       , boolArraysE  = boolArraysE super
       , intVarsE    = intVarsE super
       , deleteH     = error "forLoop.deleteE NOT YET IMPLEMENTED"
       , canBranch   = return True
       , complete    = complete super
       }
  where mystructs = ([],[])
        fs1       = [(field,init) | (field,ty,init) <- evalState_ super]
        parent    = \i -> estate i @=> "parent"
        counter   = \i -> estate i @=> "counter"
        dec_ref    = \i -> let i'     = resetCommit $ i `withBase` ("for_tstate" ++ show uid)
                           in do flag <- ask 
                                 if flag 
                                   then local (const False) $ do
				 	stmt1 <- inits super i'
                                 	stmt2 <- startTryE super (i' `withField` ("counter", counter))
                                        ini <- inite fs1 i'
                                        cc <- cachedClone (cloneBase i) i'
                                        compl <- complete super i
			         	return (dec (ref_count i) 
                                               >>> ifthen (ref_count i @== 0) 
                                                     (   inc (counter i)
                                                     >>> comment ("forLoop: bla 1 (baseTstate i' == \"" ++ rp 0 (baseTstate i') ++ "\", ref_count i' == \"" ++ rp 0 (ref_count i') ++ "\")")
                                                     >>> ifthen (counter i @< IVal n &&& Not compl)
				                           (   SHook ("TreeState for_tstate" ++ show uid ++ ";")
                                                           >>> comment "forLoop: bla 2"
				   			   >>> (baseTstate i' <== parent i)
                                                           >>> comment "forLoop: bla 3"
							   >>> cc
                                                           >>> comment "forLoop: bla 4"
				                           >>> (ref_count i' <== 1)
                                                           >>> comment "forLoop: bla 5"
--				                           >>> (cont i' <== true)
                                                           >>> comment "forLoop: bla 6"
	                                                   >>> ini 
                                                           >>> comment "forLoop: bla 7"
                                                           >>> stmt1 
                                                           >>> comment "forLoop: bla 8"
                                                           >>> stmt2)
						     ))
                                   else return $ dec (ref_count i) >>> ifthen (ref_count i @== 0) (comment "Delete-forLoop-dec_ref" >>> Delete (space $ cloneBase i))
        push dir  = \i -> dir super (i `onCommit` inc (ref_count i))
for
  :: Int32
  -> Search
  -> Search
for n s  = 
  case s of
    Search { mkeval = evals, runsearch = runs } ->
	  Search { mkeval =
	           \super ->
	           do { uid <- get
	              ; put (uid + 1)
	              ; s' <- evals $ mapE (L . L . mmap runL . runL) super
	              ; return $ mapE (L . mmap L . runL) $ forLoop n uid (mapE runL s')
	              }
	         , runsearch   = runs . rReaderT True . runL
	         }

foreach
  :: Int32
  -> ((Info -> Value) -> Search)
  -> Search
foreach n mksearch  = 
        case mksearch (\i -> field i "counter")  of
          Search { mkeval = eval, runsearch = run } ->
           Search { mkeval = 
                    \super ->
                    do { uid <- get
                       ; put (uid + 1)
                       ; s' <- eval $ mapE (L . L . mmap runL . runL) super
                       ; return $ mapE (L . mmap L . runL) $ forLoop n uid (mapE runL s')
                       }
                  , runsearch  = run . rReaderT True . runL
                  }

