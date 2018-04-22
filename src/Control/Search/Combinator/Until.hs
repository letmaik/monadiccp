{-# LANGUAGE FlexibleContexts #-}

module Control.Search.Combinator.Until (until,limit,glimit) where

import Prelude hiding (until)
import Data.Int

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.MemoReader
import Control.Search.Generator
import Control.Search.Combinator.Failure
import Control.Search.Stat

import Control.Monatron.Monatron hiding (Abort, L, state, cont)
import Control.Monatron.Zipper hiding (i,r)

untilLoop :: (Evalable m, ReaderM SeqPos m) => Stat -> Int -> (Eval m) -> (Eval m) -> Eval m
untilLoop cond uid lsuper' rsuper = commentEval c
 where c = Eval { structs     = structs lsuper @++@ structs rsuper @++@ mystructs 
                , toString    = "until" ++ show uid ++ "(" ++ show cond ++ "," ++ toString lsuper' ++ "," ++ toString rsuper ++ ")"
                , treeState_   = [entry ("is_fst",Bool,assign true)
                                ,("until_union", Union [(SType s3,"fst"),(SType s4,"snd")], 
         				 \i -> 
                                            let j = xpath i FirstS
                                            in  initSubEvalState j s1 fs1 FirstS)
                                ]
                , initH       = \i -> inits lsuper (i `xpath` FirstS)
                , evalState_  = [("until_complete",Bool,const $ return true)]
                , pushLeftH    = push pushLeft
                , pushRightH   = push pushRight
                , nextSameH    = \i -> let j = i `withBase` "popped_estate"
                                      in do let nS1 = local (const FirstS)  $ inSeq nextSame i
                                            let nS2 = local (const SecondS) $ inSeq nextSame i
                                            let nD1 = local (const FirstS)  $ inSeq nextDiff i
                                            let nD2 = local (const SecondS) $ inSeq nextDiff i
                                            swfst i (swfst j nS1 nD1) (swfst j nD2 nS2)
                , nextDiffH    = inSeq nextDiff
                , -- MAIN ENTRY POINT FOR NEW NODE
                  --   if (fst) {
                  --       if (seq_union.fst.evalState->cont) {
                  --       } else {
         	 --       }
                  --   } else {
                  --       if (seq_union.snd.evalState->cont) {
                  --       } else {
         	 --	  }
                  --   }
         	 bodyH       = \i -> 
                                 let f y z iscomplete pos = 
                                       do compl <- iscomplete (i `xpath` pos)
                                          let j = i `xpath` pos `onAbort` (comment "untilLoop.bodyE" >>> dec_ref i j compl pos)
                                          bodyE z j
         			 in do let s1 = local (const FirstS)  $ f in1 lsuper liscomplete FirstS
                                           s2 = local (const SecondS) $ f in2 rsuper riscomplete SecondS
                                       swfst i s1 s2
                , addH        = inSeq $ addE
                , failH       = \i -> inSeq' (\super j iscomplete pos -> iscomplete j >>= \compl -> (failE super j @>>>@ return (dec_ref i j compl pos))) i
                , returnH     = \i -> inSeq' (\super j iscomplete pos -> iscomplete j >>= \compl -> (returnE super (j `onCommit` dec_ref i j compl pos))) i
--                , continue    = \_ -> return true
                 -- IF THE CURRENT STATUS IS NOT FAILED
         	 -- EITHER (is_fst)
         	 --   if (<CONDITION>) {   // SWITCH TO NEW SEARCH
         	 --   } else {
         	 --       <TRY-REC>
          	 --   }
         	 -- OR      (!is_fst)
                , tryH        = tryX tryE
                , startTryH   = tryX startTryE
                , tryLH       = \i -> inSeq' (\super j iscomplete pos -> iscomplete j >>= \compl -> (tryE_ super j @>>>@ return (dec_ref i j compl pos))) i
                , boolArraysE  = boolArraysE lsuper ++ boolArraysE rsuper
                , intArraysE  = intArraysE lsuper ++ intArraysE rsuper
                , intVarsE    = intVarsE lsuper ++ intVarsE rsuper
                , deleteH     = error "untilLoop.deleteE NOT YET IMPLEMENTED"
                , canBranch   = canBranch lsuper >>= \l -> canBranch rsuper >>= \r -> return (l || r)
                , complete = \i -> return $ estate i @=> "until_complete"
--                , complete = const $ return false
                }
       needSide_ = \pos stmY stmN -> case pos of { FirstS -> if (length (evalState_ lsuper) == 0) then stmN else stmY;
                                                   SecondS -> if (length (evalState_ rsuper) == 0) then stmN else stmY;
                                                 }
       needSide :: Monoid m => SeqPos -> m -> m
       needSide = \pos stm -> needSide_ pos stm mempty
       mystructs = ([s1,s2],[s3,s4])
       s1        = Struct ("LeftEvalState"  ++ show uid)  $ needSide FirstS $ {- (Bool, "cont") : -} (Int, "ref_count_until" ++ show uid) : [(ty, field) | (field,ty,_) <- evalState_ lsuper]
       fs1       = [(field,init) | (field,ty,init) <- evalState_ lsuper ]
       s2        = Struct ("RightEvalState" ++ show uid) $ needSide SecondS $ {- (Bool, "cont") : -} (Int, "ref_count_until" ++ show uid) : [(ty, field) | (field,ty,_) <- evalState_ rsuper]
       fs2       = [(field,init) | (field,ty,init) <- evalState_ rsuper ]
       s3        = Struct ("LeftTreeState"  ++ show uid) $ needSide FirstS [(Pointer $ SType s1, "evalState")] ++ [(ty, field) | (field,ty,_) <- treeState_ lsuper]
       fs3       = [(field,init) | (field,ty,init) <- treeState_ lsuper]
       s4        = Struct ("RightTreeState" ++ show uid) $ needSide SecondS [(Pointer $ SType s2, "evalState")] ++ [(ty, field) | (field,ty,_) <- treeState_ rsuper]
       xpath i FirstS  = withPath i in1 (Pointer $ SType s1) (Pointer $ SType s3)
       xpath i SecondS  = withPath i in2 (Pointer $ SType s2) (Pointer $ SType s4)
       in1       = \state -> state @-> "until_union" @-> "fst"
       in2       = \state -> state @-> "until_union" @-> "snd"
       is_fst    = \i -> tstate i @-> "is_fst"
       withSeq f = seqSwitch (f lsuper in1) (f rsuper in2)
       withSeq_ f = seqSwitch (f lsuper in1 FirstS) (f rsuper in2 SecondS)
       inSeq  f  = \i -> withSeq_ $ \super ins pos -> f super (i `xpath` pos)
       inSeq' f  = \i -> seqSwitch (f lsuper (i `xpath` FirstS) liscomplete FirstS)  
                                   (f rsuper (i `xpath` SecondS) riscomplete SecondS)
       dec_ref   = \i j iscomplete pos -> needSide_ pos (dec (ref_countx j $ "until" ++ show uid) >>>
                                                         ifthen (ref_countx j ("until" ++ show uid) @== 0) (
                                                        {-       DebugValue ("until" ++ show uid ++ ": left branch finished with complete") iscomplete
                                                           >>> DebugValue ("until" ++ show uid ++ ": until's previous completeness was") (complet i)
                                                           >>> -} (complet i <== (complet i &&& iscomplete)) >>> Delete (estate j)
                                                         )
                                                        ) (complet i <== (complet i &&& iscomplete))
       push dir  = \i -> seqSwitch (push1 dir i) (push2 dir i)
       push1 dir = \i -> 
                          let j = i `xpath` FirstS
                          in  dir lsuper (j `onCommit` (   mkCopy i "is_fst"
                                                       >>> mkCopy j "evalState"
                                                       >>> inc (ref_countx j $ "until" ++ show uid)
                                                       ))
       push2 dir = \i -> 
                          let j = i `xpath` SecondS
                          in  dir rsuper (j `onCommit` (    mkCopy i "is_fst"
                                                       >>> mkCopy j "evalState"
                                                       >>> inc (ref_countx j $ "until" ++ show uid)
                                                      ))
       lsuper = evalStat cond lsuper'
       complet  = \i -> estate i @=> "until_complete"
       liscomplete = complete lsuper'
       riscomplete = complete rsuper
       initSubEvalState = \j s fs pos -> return (needSide pos (    (estate j <== New s)  
					                       >>> (ref_countx j ("until" ++ show uid) <== 1)
--			                                       >>> (cont j <== true)
                                                              )
                                                )
                                         @>>>@ inite fs j
       tryX        = \x i -> do lc <- liscomplete (i `xpath` FirstS)
                                rc <- riscomplete (i `xpath` SecondS)
                                let j1  = i `xpath` FirstS `onAbort` (comment "untilLoop.tryE j1" >>> dec_ref i j1 lc FirstS)
                                    j2  = i `xpath` SecondS `onAbort` (comment "untilLoop.tryE j2" >>> dec_ref i j2 rc SecondS)
                                    j2b = i `xpath` SecondS `onAbort` (comment "untilLoop.tryE j2b" >>> dec_ref i j2b rc SecondS)
                                seqSwitch (x       lsuper j1 >>= \try1 ->
                                                   deleteE lsuper j1 >>= \delete1 ->
                                                   (local (const SecondS) $
                                                     do stmt1 <- inits rsuper j2b
                                                        stmt2 <- startTryE rsuper j2b
                                                        ini <- initSubEvalState j2b s2 fs2 SecondS
                                                        return (   delete1
         						      >>> dec_ref i j1 lc FirstS
                                                     	      >>> (is_fst i <== false)
         						      >>> ini
                                                               >>> comment "initTreeState_ j2b rsuper" 
         						      >>> stmt1 
                                                               >>> comment "tryE rsuper j2b" 
         						      >>> comment ("length: " ++ show (length (abort_ j2b)))
         						      >>> stmt2)
                                                   ) >>= \start2 -> readStat cond >>= \r -> return $ IfThenElse (r j1) ({- (DebugOutput $ "until" ++ show uid ++ " switches") >>> -} start2) try1
                                                  )
                                                  (x rsuper j2) 
       swfst i t e = do  b1 <- canBranch lsuper
                         b2 <- canBranch rsuper
                         if (b1 && b2) then do { tt <- t; ee <- e; return $ IfThenElse (is_fst i) tt ee }
                                       else if b1 then t
                                                  else e


limit :: Int32 -> Stat -> Search -> Search
limit n stat s = until (stat #>= constStat (const (IVal n))) s failure

glimit :: Stat -> Search -> Search
glimit cond s = until (cond) s failure

until 
  :: Stat
  -> Search
  -> Search
  -> Search
until cond s1 s2 = 
  case s1 of
    Search { mkeval = evals1, runsearch = runs1 } ->
      case s2 of
        Search { mkeval = evals2, runsearch = runs2 } ->
	  Search { mkeval =
	          \super -> do { s2' <- evals2 $ mapE (L . L . L . mmap (mmap runL . runL) . runL)  super
	                       ; s1' <- evals1 $ mapE (L . L . mmap (mmap runL . runL) . runL) super
		   	       ; uid <- get
		   	       ; put (uid + 1)
	                       ; return $ mapE (L . mmap L . runL) $ memoLoop $
		   			untilLoop cond uid (mapE ({- L . mmap (mmap L) . runL . runL-} mmap L . runL) s1')
	                                                      (mapE ({- L . mmap (mmap L) . runL . runL . runL-} mmap L . runL . runL) s2')
	                       }
	         , runsearch  = runs2 . runs1 . runL . rReaderT FirstS . runL
	         } 
