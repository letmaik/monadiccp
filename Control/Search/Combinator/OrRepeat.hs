{-# LANGUAGE FlexibleContexts #-}

module Control.Search.Combinator.OrRepeat (orRepeat) where

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Generator
import Control.Search.MemoReader
import Control.Search.Memo
import Control.Search.Stat

import Control.Monatron.Monatron hiding (Abort, L, state, cont)
import Control.Monatron.Zipper hiding (i,r)

orRepeatLoop :: (Evalable m, ReaderM Bool m) => Stat -> Int -> Eval m -> Eval m
orRepeatLoop cond uid super' = commentEval $
    Eval 
       { 
         structs     = structs super @++@ mystructs 
       , treeState_  = treeState_ super
       , toString    = "orRepeat" ++ show uid ++ "(" ++ toString super' ++ ")"
       , initH       = \i -> initE super i @>>>@ return (parent i <== baseTstate i) @>>>@ cachedClone i (cloneBase i)
       , evalState_  = {- ("cont",Bool,const $ return true) : -} ("ref_count_orr" ++ show uid,Int,const $ return 1) : ("parent",THook "TreeState",const $ return Null) : evalState_ super
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
                                tryE super (i `onAbort` deref)
       , startTryH   = \i -> do deref <- dec_ref i
                                startTryE super (i `onAbort` deref)
       , tryLH       = \i -> tryE_ super i @>>>@ dec_ref i
       , intArraysE  = intArraysE super
       , boolArraysE  = boolArraysE super
       , intVarsE    = intVarsE super
       , deleteH     = error "orRepeatLoop.deleteE NOT YET IMPLEMENTED"
       , canBranch   = return True
       , complete    = complete super
--       , complete = const $ return false
       }
  where mystructs = ([],[])
        super     = evalStat cond super'
        fs1       = [(field,init) | (field,ty,init) <- evalState_ super]
        parent    = \i -> estate i @=> "parent"
        dec_ref    = \i -> let i'     = resetAbort $ resetCommit $ i `withBase` ("orr_tstate" ++ show uid)
                               ii     = resetAbort $ resetCommit $ i
                           in do flag <- ask 
                                 if flag 
                                   then local (const False) $ do
                                        stmt1 <- inits super i'
                                        stmt2 <- startTryE super i'
                                        r     <- readStat cond
                                        ini   <- inite fs1 i'
                                        -- let cc =  clone ii i'
                                        -- cc  <- cachedClone (cloneBase ii) i'
                                        cc1 <- cachedClone (i { baseTstate = parent ii} ) i'
                                        -- cc2 <- cachedClone (i' ) i'
                                        compl <- complete super ii
                                        return (dec (ref_countx ii $ "orr" ++ show uid) 
                                               >>> ifthen (ref_countx ii ("orr" ++ show uid) @== 0) 
                                                     (ifthen (r i' &&& Not compl)
                                                           (   SHook ("TreeState orr_tstate" ++ show uid ++ ";")
                                                           >>> (baseTstate i' <== parent ii)
                                                           -- >>> ((baseTstate i' @-> "space") <== (parent ii @-> "space"))
                                                           -- >>> cc
							   >>> cc1
							   -- >>> cc2
                                                           >>> (ref_countx i' ("orr" ++ show uid) <== 1)
--                                                         >>> (cont i' <== true)
                                                           >>> ini >>> stmt1 >>> stmt2)
                                                     ))
                                   else  return $ dec (ref_countx ii ("orr" ++ show uid)) >>> ifthen (ref_countx ii ("orr" ++ show uid) @== 0) (comment "orRepeatLoop-dec_ref-Delete" >>> Delete (space $ cloneBase ii))
        push dir  = \i -> dir super (i `onCommit'` inc (ref_countx i $ "orr" ++ show uid))

orRepeat
  :: Stat
  -> Search
  -> Search
orRepeat cond s  = 
  case s of
    Search { mkeval = evals, runsearch = runs } ->
	  Search { mkeval =
	           \super ->
	           do { uid <- get
	              ; put (uid + 1)
	              ; s' <- evals $ mapE (L . L . mmap runL . runL) super
	              ; return $ mapE (L . mmap L . runL) $ orRepeatLoop cond uid (mapE runL s')
	              }
	         , runsearch   = runs . rReaderT True . runL
	         }
