{-# LANGUAGE FlexibleContexts #-}

module Control.Search.Combinator.If (if') where

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.MemoReader
import Control.Search.Generator
import Control.Search.Stat

import Control.Monatron.Monatron hiding (Abort, L, state, cont)
import Control.Monatron.Zipper hiding (i,r)

xs1  uid lsuper rsuper      = Struct ("LeftEvalState" ++ show uid) $ {- (Bool, "cont") : -} (Int, "ref_count") : [(ty, field) | (field,ty,_) <- evalState_ lsuper]
xfs1 uid lsuper rsuper      = [(field,init) | (field,ty,init) <- evalState_ rsuper ]
xs2  uid lsuper rsuper      = Struct ("RightEvalState" ++ show uid) $ {- (Bool, "cont") : -} (Int, "ref_count") : [(ty, field) | (field,ty,_) <- evalState_ rsuper]
xfs2 uid lsuper rsuper      = [(field,init) | (field,ty,init) <- evalState_ rsuper ]
xs3  uid lsuper rsuper      = Struct ("LeftTreeState"  ++ show uid) $ (Pointer $ SType $ xs1 uid lsuper rsuper, "evalState") : [(ty, field) | (field,ty,_) <- treeState_ lsuper]
xfs3 uid lsuper rsuper      = [(field,init) | (field,ty,init) <- treeState_ lsuper]
xs4  uid lsuper rsuper      = Struct ("RightTreeState"  ++ show uid) $ (Pointer $ SType $ xs2 uid lsuper rsuper, "evalState") : [(ty, field) | (field,ty,_) <- treeState_ rsuper]
xfs4 uid lsuper rsuper      = [(field,init) | (field,ty,init) <- treeState_ rsuper]

in1       = \state -> state @-> "if_union" @-> "if_then"
in2       = \state -> state @-> "if_union" @-> "if_else"

xpath uid lsuper rsuper i FirstS = withPath i in1 (SType $ xs1 uid lsuper rsuper) (SType $ xs3 uid lsuper rsuper)
xpath uid lsuper rsuper i SecondS = withPath i in2 (SType $ xs2 uid lsuper rsuper) (SType $ xs4 uid lsuper rsuper)

ifLoop :: (Evalable m, ReaderM SeqPos m) => Stat -> Int -> Eval m -> Eval m -> Eval m
ifLoop cond uid lsuper rsuper = commentEval $
  Eval { structs     = structs lsuper @++@ structs rsuper @++@ mystructs 
       , toString    = "if" ++ show uid ++ "(" ++ show cond ++ "," ++ toString lsuper ++ "," ++ toString rsuper ++ ")"
       , treeState_   = [("if_true", Bool,const $ return Skip),
                         ("if_union",Union [(SType s3,"if_true"),(SType s4,"if_false")],const $ return Skip)
                        ]
       , initH       = \i -> (readStat cond >>= \r -> return (assign (r i) (tstate i @-> "if_true"))) @>>>@ initstate i
       , evalState_   = []
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
                               let j = mpath i p
{-                               in   do cond  <- continue z (estate j)
                                       deref <- dec_ref i
				       stmt  <- bodyE z (j `onAbort` deref)
                                       return $ IfThenElse (cont j)
				  		    (IfThenElse cond
						                stmt
							        (   (cont j <== false)
                                                                >>> deref
                                                                >>> abort j))
						    (deref >>> abort j)
-}
                                 in dec_ref i >>= \deref -> bodyE z (j `onAbort` deref)
			 in IfThenElse (is_fst i) @$ local (const FirstS)  (f in1 lsuper FirstS) 
                                                  @. local (const SecondS) (f in2 rsuper SecondS)
       , addH        = inSeq $ addE
       , failH       = \i -> inSeq failE i @>>>@ dec_ref i
       , returnH     = \i -> 
			     let j1 deref = mpath i FirstS `onCommit` deref
                                 j2 deref = mpath i SecondS `onCommit` deref
                             in IfThenElse (is_fst i) @$ (dec_refx (j1 Skip) >>= returnE lsuper . j1) @. (dec_refx (j2 Skip) >>= returnE rsuper . j2)
--       , continue    = \_ -> return true
       , tryH        = \i -> IfThenElse (is_fst i) @$ tryE lsuper (mpath i FirstS) @. tryE rsuper (mpath i SecondS)
       , startTryH   = \i -> IfThenElse (is_fst i) @$ startTryE lsuper (mpath i FirstS) @. startTryE rsuper (mpath i SecondS)
       , tryLH       = \i -> IfThenElse (is_fst i) @$ tryE_ lsuper (mpath i FirstS) @. tryE_ rsuper (mpath i SecondS)
       , boolArraysE  = boolArraysE lsuper ++ boolArraysE rsuper
       , intArraysE  = intArraysE lsuper ++ intArraysE rsuper
       , intVarsE    = intVarsE lsuper ++ intVarsE rsuper
       , deleteH     = deleteMe
       , canBranch   = canBranch lsuper >>= \l -> canBranch rsuper >>= \r -> return (l || r)
       , complete    = \i -> do sid1 <- complete lsuper (mpath i FirstS)
                                sid2 <- complete rsuper (mpath i SecondS)
                                return $ Cond (tstate i @-> "is_fst") sid1 sid2
       }
  where mystructs = ([s1,s2],[s3,s4])
        s1 = xs1 uid lsuper rsuper
        s2 = xs2 uid lsuper rsuper
        s3 = xs3 uid lsuper rsuper
        s4 = xs4 uid lsuper rsuper
        fs1 = xfs1 uid lsuper rsuper
        fs2 = xfs2 uid lsuper rsuper
        fs3 = xfs3 uid lsuper rsuper
        fs4 = xfs4 uid lsuper rsuper
        mpath = xpath uid lsuper rsuper
        withSeq f = seqSwitch (f lsuper in1) (f rsuper in2)
        withSeq_ f = seqSwitch (f lsuper in1 FirstS) (f rsuper in2 SecondS)
        inSeq f   = \i     -> withSeq_ $ \super ins pos -> f super (mpath i pos)
        dec_ref    = \i -> seqSwitch (dec_refx $ mpath i FirstS) (dec_refx $ mpath i SecondS)
        dec_refx    = \j -> return $ dec (ref_count j) >>> ifthen (ref_count j @== 0) (comment "ifLoop-dec_refx" >>> Delete (estate j))
        push dir  = \i -> seqSwitch (push1 dir i) (push2 dir i)
        push1 dir = \i -> 
                           let j = mpath i FirstS
                           in  dir lsuper (j `onCommit` (   mkCopy i "if_true"
                                                        >>> mkCopy j "evalState"
                                                        >>> inc (ref_count j)
                                                        ))
        push2 dir = \i -> 
                           let j = mpath i SecondS
                           in  dir rsuper (j `onCommit` (   mkCopy i "if_true"
                                                        >>> mkCopy j "evalState"
                                                        >>> inc (ref_count j)
                                                       ))
        initstate = \i -> 
                               let f d = 
                                         let j = mpath i (if d then FirstS else SecondS)
                                             in       return (    (estate j <== New (if d then s1 else s2))
                                                              >>> (ref_count j <== 1)
                                                             ) 
                                                @>>>@ inite (if d then fs1 else fs2) j
                                                @>>>@ inits (if d then lsuper else rsuper) j
                                   in do thenP <- f True
                                         elseP <- f False
                                         return $ IfThenElse (tstate i @-> "if_true") thenP elseP
	in1       = \state -> state @-> "if_union" @-> "if_then"
	in2       = \state -> state @-> "if_union" @-> "if_else"
	is_fst    = \i -> tstate i @-> "if_true"
        deleteMe  = \i -> seqSwitch (deleteE lsuper (mpath i FirstS)) (deleteE rsuper (mpath i SecondS)) @>>>@ dec_ref i

if'
  :: Stat
  -> Search
  -> Search
  -> Search
if' cond s1 s2 = 
  case s1 of
    Search { mkeval = evals1, runsearch = runs1 } ->
      case s2 of
        Search { mkeval = evals2, runsearch = runs2 } ->
	  Search { mkeval =
	          \super -> do { s2' <- evals2 $ mapE (L . L . L . mmap (mmap runL . runL) . runL)  super
	                       ; s1' <- evals1 $ mapE (L . L . mmap (mmap runL . runL) . runL) super
		   	       ; uid <- get
		   	       ; put (uid + 1)
	                       ; return $ mapE (L . mmap L . runL) $ 
		   			ifLoop cond uid (mapE (L . mmap (mmap L) . runL . runL) s1')
	                                                      (mapE (L . mmap (mmap L) . runL . runL . runL) s2')
	                       }
	         , runsearch  = runs2 . runs1 . runL . rReaderT FirstS . runL
	         } 
 where 	in1       = \state -> state @-> "if_union" @-> "if_then"
	in2       = \state -> state @-> "if_union" @-> "if_else"
