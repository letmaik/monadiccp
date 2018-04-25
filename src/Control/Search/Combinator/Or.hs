{-# LANGUAGE FlexibleContexts #-}

module Control.Search.Combinator.Or ((<|>)) where

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Generator
import Control.Search.MemoReader
import Control.Search.Memo

import Control.Monatron.Monatron hiding (Abort, L, state, cont)
import Control.Monatron.Zipper hiding (i,r)

xs1 uid lsuper rsuper       = Struct ("LeftEvalState"  ++ show uid)  $ (THook "TreeState", "parent") : {- (Bool, "cont") : -} (Int, "ref_count") : [(ty, field) | (field,ty,_) <- evalState_ lsuper]
xfs1 uid lsuper rsuper       = [(field,init) | (field,ty,init) <- evalState_ lsuper ]
xs2 uid lsuper rsuper        = Struct ("RightEvalState" ++ show uid) $ xneedSide uid lsuper rsuper SecondS $ {- (Bool, "cont") : -} (Int, "ref_count") : [(ty, field) | (field,ty,_) <- evalState_ rsuper]
xfs2 uid lsuper rsuper       = [(field,init) | (field,ty,init) <- evalState_ rsuper ]
xet uid lsuper rsuper FirstS = SType $ xs1 uid lsuper rsuper
xet uid lsuper rsuper SecondS = SType $ xs2 uid lsuper rsuper
xs3 uid lsuper rsuper        = Struct ("LeftTreeState"  ++ show uid) $ (Pointer $ SType $ xs1 uid lsuper rsuper, "evalState") : [(ty, field) | (field,ty,_) <- treeState_ lsuper]
xfs3 uid lsuper rsuper       = [(field,init) | (field,ty,init) <- treeState_ lsuper]
xs4 uid lsuper rsuper        = Struct ("RightTreeState" ++ show uid) $ xneedSide uid lsuper rsuper SecondS [(Pointer $ SType $ xs2 uid lsuper rsuper, "evalState")] ++ [(ty, field) | (field,ty,_) <- treeState_ rsuper]
xst uid lsuper rsuper FirstS = SType $ xs3 uid lsuper rsuper
xst uid lsuper rsuper SecondS = SType $ xs4 uid lsuper rsuper
xneedSide :: Monoid m => Int -> Eval n -> Eval n -> SeqPos -> m -> m
xneedSide uid lsuper rsuper = \pos stm -> case pos of { FirstS -> stm;
                                                       SecondS -> if (length (evalState_ rsuper) == 0) then mempty else stm;
                                                     }

orLoop :: (ReaderM SeqPos m, Evalable m) => Int -> (Eval m) -> (Eval m) -> Eval m
orLoop uid (lsuper) (rsuper) = commentEval $
  Eval { structs     = structs lsuper @++@ structs rsuper @++@ mystructs 
       , toString    = "or" ++ show uid ++ "(" ++ toString lsuper ++ "," ++ toString rsuper ++ ")"
       , treeState_   = [entry ("is_fst",Bool,assign true)
                       , ("or_union",Union [(SType s3,"fst"),(SType s4,"snd")], 
				\i -> 
                                   let j = withPath i in1 (et FirstS) (st FirstS)
                                   in        do cc <- cachedClone i (cloneBase j)
                                                return (    (estate j <== New s1)
				                        >>> (ref_count j <== 1)
--				                        >>> (cont j <== true)
                                                        >>> (parent j <== baseTstate j)
                                                        >>> cc
                                                       )
                                       @>>>@ mseqs [init (j `withClone` (\k -> inc $ ref_count k)) | (f,init) <- fs3]
                                       @>>>@ inite fs1 j
                         )]
       , initH       = \i -> initE lsuper (withPath i in1 (et FirstS) (st FirstS))
       , evalState_  = []
       , pushLeftH    = push pushLeft
       , pushRightH   = push pushRight
       , nextSameH    = \i -> let j = i `withBase` "popped_estate"
                             in do nS1 <- local (const FirstS)  $ inSeq nextSame i
                                   nS2 <- local (const SecondS) $ inSeq nextSame i
                                   nD1 <- local (const FirstS)  $ inSeq nextDiff i
                                   nD2 <- local (const SecondS) $ inSeq nextDiff i
                                   return $ IfThenElse (is_fst i) 
                                                       (IfThenElse (is_fst j) nS1 nD1)
                                                       (IfThenElse (is_fst j) nD2 nS2) 
       , nextDiffH    = \i -> inSeq nextDiff i
       , bodyH       = \i ->
                         let f y z p = 
                               let j = withPath i y (et p) (st p)
                                 in dec_ref i >>= \deref -> bodyE z (j `onAbort` deref)
			 in IfThenElse (is_fst i) @$ local (const FirstS)  (f in1 lsuper FirstS)
                                                  @. local (const SecondS) (f in2 rsuper SecondS)
       , addH        = inSeq $ addE
       , failH       = \i -> inSeq failE i @>>>@ dec_ref i
       , returnH     = \i -> 
			     let j1 deref = (withPath i in1 (et FirstS) (st FirstS)) `onCommit` (comment "returnE-deref-j1" >>> deref >>> comment "end returnE-deref-j1")
                                 j2 deref = (withPath i in2 (et SecondS) (st SecondS)) `onCommit` (comment "returnE-deref-j2" >>> deref >>> comment "end returnE-deref-j2")
                             in seqSwitch (dec_ref1 i >>= returnE lsuper . j1)
                                          (dec_ref2 (j2 Skip) >>= returnE rsuper . j2) 
       , tryH        = \i -> 
			  do  dr <- dec_ref i
                              inSeq (\super j -> tryE super (j `onAbort` (comment "Combinator/Or tryH onAbort" >>> dr ))) i
       , startTryH   = \i -> local (const FirstS) $ inSeq startTryE i
       , tryLH       = \i -> inSeq tryE_ i @>>>@ dec_ref i
       , boolArraysE  = boolArraysE lsuper ++ boolArraysE rsuper
       , intArraysE  = intArraysE lsuper ++ intArraysE rsuper
       , intVarsE    = intVarsE lsuper ++ intVarsE rsuper
       , deleteH     = deleteMe
       , canBranch   = return True
       , complete    = \i -> do sid1 <- complete lsuper (withPath i in1 (et FirstS) (st FirstS))
                                sid2 <- complete rsuper (withPath i in2 (et SecondS) (st SecondS))
                                return $ (Cond (tstate i @-> "is_fst") sid1 sid2)

--       , complete = const $ return false
       }
  where mystructs = ([s1,s2],[s3,s4])
        s1 = xs1 uid lsuper rsuper
        s2 = xs2 uid lsuper rsuper
        s3 = xs3 uid lsuper rsuper
        s4 = xs4 uid lsuper rsuper
        fs1 = xfs1 uid lsuper rsuper
        fs2 = xfs2 uid lsuper rsuper
        fs3 = xfs3 uid lsuper rsuper
        et = xet uid lsuper rsuper
        st = xst uid lsuper rsuper
        needSide = xneedSide uid lsuper rsuper
        parent    = \i -> estate i @=> "parent"
        withSeq f = seqSwitch (f lsuper in1 FirstS) (f rsuper in2 SecondS)
        withSeq_ f = seqSwitch (f lsuper in1 FirstS) (f rsuper in2 SecondS)
        inSeq f   = \i     -> withSeq_ $ \super ins pos -> f super (withPath i ins (et pos) (st pos))
        dec_ref    = \i -> seqSwitch (dec_ref1 i) (dec_ref2 $ withPath i in2 (et SecondS) (st SecondS))
        dec_ref1   = \i ->      let j1     = withPath i in1 (et FirstS) (st FirstS)
                                    i'     = resetClone $ resetAbort $ resetCommit $ i `withBase` ("or_tstate" ++ show uid)
                                    j2     = withPath i' in2 (et SecondS) (st SecondS)
                                in (local (const SecondS) $
                                    do stmt1 <- inits rsuper j2
                                       stmt2 <- startTryE rsuper j2
                                       ini <- inite fs2 j2
                                       compl <- complete lsuper j1
				       return (    dec (ref_count j1) 
                                               >>> (ifthen (ref_count j1 @== 0) $
                                                      (
                                                      {- DebugValue ("or" ++ show uid ++ ": left finished with complete") (compl)
                                                      >>> -} (ifthen (Not compl) $
				                            (   SHook ("TreeState or_tstate" ++ show uid ++ ";")
							    >>> (baseTstate j2 <== parent j1)
                                                            >>> (is_fst i' <== false)
                                                            >>> comment "orLoop-dec_ref1-Delete" >>> Delete (estate j1)
                                                            >>> needSide SecondS (estate j2 <== New s2)  
				                            >>> needSide SecondS (ref_count j2 <== 1)
--				                            >>> (cont j2 <== true)
  				                            >>> ini
                                                            >>> stmt1 >>> stmt2
                                                            )
                                                          )
                                                      )
                                                   )
                                              )
                                   )
        dec_ref2  = \j -> {- return (DebugValue ("or" ++ show uid ++ ": right dec_ref from") (ref_count j)) @>>>@ -} (complete rsuper (withPath (resetClone $ resetAbort $ resetCommit $ j `withBase` ("or_tstate" ++ show uid)) in2 (et SecondS) (st SecondS)) >>= \compl -> (return $ needSide SecondS $ dec (ref_count j) >>> ifthen (ref_count j @== 0) ({- DebugValue ("or" ++ show uid ++ ": right finished with complete") compl >>> -} comment "orLoop-dec_ref2-Delete" >>> Delete (estate j))))
        push dir  = \i -> seqSwitch (push1 dir i) (push2 dir i)
        push1 dir = \i -> 
                           let j = withPath i in1 (et FirstS) (st FirstS)
                           in  dir lsuper (j `onCommit` (   mkCopy i "is_fst"
                                                        >>> mkCopy j "evalState"
                                                        >>> inc (ref_count j)
                                                        ))
        push2 dir = \i -> 
                           let j = withPath i in2 (et SecondS) (st SecondS)
                           in  dir rsuper (j `onCommit` (   mkCopy i "is_fst"
                                                        >>> needSide SecondS (mkCopy j "evalState")
                                                        >>> needSide SecondS (inc (ref_count j))
                                                       ))
	in1       = \state -> state @-> "or_union" @-> "fst"
	in2       = \state -> state @-> "or_union" @-> "snd"
	is_fst    = \i -> tstate i @-> "is_fst"
	deleteMe  = \i -> seqSwitch (deleteE lsuper (withPath i in1 (et FirstS) (st FirstS))) (deleteE rsuper (withPath i in2 (et SecondS) (st SecondS))) @>>>@ dec_ref i

(<|>)
  :: Search
  -> Search
  -> Search
s1 <|> s2 = 
  case s1 of
    Search { mkeval = evals1, runsearch = runs1 } ->
      case s2 of
        Search { mkeval = evals2, runsearch = runs2 } ->
	  Search {mkeval =
	          \super -> do { s2' <- evals2 $ mapE (L . L . L . mmap (mmap runL . runL) . runL)  super
	                       ; s1' <- evals1 $ mapE (L . L . mmap (mmap runL . runL) . runL) super
			       ; uid <- get
			       ; put (uid + 1)
	                       ; return $ mapE (L . mmap L . runL) $ 
			           	orLoop uid (mapE (L . mmap (mmap L) . runL . runL) s1')
	                                               (mapE (L . mmap (mmap L) . runL . runL . runL) s2')
	                       }
	         , runsearch  = runs2 . runs1 . runL . rReaderT FirstS . runL
	         }
 where 	in1       = \state -> state @-> "or_union" @-> "fst"
	in2       = \state -> state @-> "or_union" @-> "snd"
