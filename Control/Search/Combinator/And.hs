{-# LANGUAGE FlexibleContexts #-}

module Control.Search.Combinator.And (andN,(<&>)) where

import Maybe (fromMaybe, catMaybes, fromJust)

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Memo
import Control.Search.MemoReader
import Control.Search.Generator

import Control.Search.Combinator.Success

import Control.Monatron.Monatron hiding (Abort, L, state, cont)
import Control.Monatron.Zipper hiding (i,r)
import Control.Monatron.IdT

seqNLoop :: (ReaderM Int m, Evalable m) => Int -> [Eval m] -> Eval m
seqNLoop uid lst = commentEval $
  Eval { structs     = (foldr1 (@++@) $ map (structs) lst) @++@ mystructs 
       , toString = "seqN" ++ show uid ++ "(" ++ (foldr1 (\x y -> x ++ "," ++ y) $ map (toString) lst) ++ ")"
       , treeState_  = [entry ("seqn_pos",Int,assign 0)                      -- is the first or the second search active?
                       , ("seqn_union",Union [(SType (s3 i),"seq" ++ show i) | i <- [0..nbranches-1]], -- union of both tree states
				\i -> 						 -- init nested state of first search
                                   let j = xpath i 0
                                   in initSubEvalState j (s1 0) (fs1 0)
                         )]
       , initH       = \i -> (local (const 0) $ inits (xsuper 0) (xpath i 0))
       , evalState_  = [("complete",Bool,const $ return true)] -- some global data
       , pushLeftH    = push pushLeft
       , pushRightH   = push pushRight
       , nextSameH    = \i -> let j = i `withBase` "popped_estate"
                             in do nd <- inSeq nextDiff i
                                   ns <- inSeq nextSame i
                                   return $ IfThenElse ((seq_pos i) @== (seq_pos j)) ns nd
       , nextDiffH    = inSeq $ nextDiff
       , bodyH       = \i -> 
                                let seqBody super j pos = 
                                      do
                                        dr <- dec_ref "bodyE-stmt" j i pos
                                        bodyE super (j `onAbort` (comment "seqLoopN.bodyE" >>> dr))
                                    in do cb <- mapM (\x -> canBranch x >>= \b -> return (if b then 1 else 0)) {- (const $ return 1) -} lst
                                          let cu n | n==nbranches = 0
                                              cu n                = (cb!!n) + cu (n+1)
                                          ss <- mapM (\pos -> local (const $ fromIntegral pos) $ inSeq_ seqBody i) [0..nbranches-1]
                                          let cc n | n==nbranches = Skip
                                              cc n | cu n <= 1   = if ((cb !! n) == 1) then (ss !! n) else cc (n+1)
                                              cc n | otherwise      = IfThenElse (seq_pos i @== fromIntegral n) (ss !! n) (cc (n+1))
                                          return $ cc 0
       , addH        = inSeq $ addE
       , failH       = \i -> inSeq_ (\super j pos -> failE super j @>>>@ (dec_ref "failE" j i pos)) i
       , returnH     = \i -> numSwitch (\n -> if (n<nbranches-1)
                                                    then do let j1 = xpath i n
                                                                j2o = xpath i (n+1)
                                                            dr <- dec_ref "returnE-j2A" j2o i (n+1)
                                                            let j2 = j2o `onCommit` dr
                                                                j2b = resetCommit j2
				 	                    action <- local (const $ n+1) $ do stmt1 <- inits (xsuper (n+1)) j2b
                                                                                               stmt2 <- startTryE (xsuper (n+1)) j2b
                                                                                               init <- initSubEvalState j2b (s1 $ n+1) (fs1 $ n+1)
                                                                                               dr2 <- dec_ref "returnE-j1" j1 i n
					                                                       return (    comment ("Switching from branch" ++ show n ++ " to branch" ++ show (n+1))
                                                                                                           >>> dr2
                                                                                                           >>> (seq_pos i <== fromIntegral (n+1))
                                                                                                           >>> init >>> stmt1 >>> stmt2)
                                                            returnE (xsuper n) $ j1 `withCommit` const action
                                                    else do let j2o  = xpath i n
                                                            dr3 <- dec_ref "returnE-j2B" j2o i n
                                                            let j2 = j2o `onCommit` dr3
                                                            returnE (xsuper n) j2
                                          )
--       , continue    = \_ -> return true
       , tryH        = \i -> inSeq_ (\super j pos -> do { dr <- dec_ref "tryE" j i pos; return (comment "seqLoop.tryE(a)") @>>>@ tryE  super (j `onAbort` (comment "seqLoop.tryE(b)" >>> dr))}) i
       , startTryH   = \i -> local (const 0) $ inSeq_ (\super j pos -> do { dr <- dec_ref "startTryE" j i pos; return (comment "seqLoop.startTryE(a)") @>>>@ startTryE super (j `onAbort` (comment "seqLoop.startTryE(b)" >>> dr))}) i
       , tryLH       = \i -> inSeq_ (\super j pos -> tryE_ super j @>>>@ (dec_ref "tryE_" j i pos)) i
       , intArraysE  = foldr1 (++) $ map (intArraysE) lst
       , boolArraysE  = foldr1 (++) $ map (boolArraysE) lst
       , intVarsE    = foldr1 (++) $ map (intVarsE) lst
       , deleteH     = deleteMe
       , canBranch   = do res <- mapM (canBranch) lst
                          return $ or res
       , complete = \i -> return $ estate i @=> "complete"
--       , complete = const $ return false
       }
  where nbranches = length lst
        xsuper i = lst !! i
        mystructs = (catMaybes (map s1 [0..nbranches-1]),map s3 [0..nbranches-1])
	evalStruct side super = Just $ -- if (length (evalState_ super) == 0) then Nothing else Just $
			Struct (side ++ "EvalState"  ++ show uid) $ 
--				(Bool, "cont") :				-- continue or not with this search 
				(Int, "ref_count") : 				-- how many active nodes of this search
				[(ty, field) | (field,ty,_) <- evalState_ super] -- fields of this search
--        needSide = \pos stm -> if (length (evalState_ (xsuper pos)) == 0) then Skip else stm
        needSide pos stm = stm
        s1 i      = evalStruct ("Seq" ++ show i) (xsuper i)
        et i      = maybe (THook "void") (Pointer . SType) $ s1 i
        s3 i      = Struct ("Seq" ++ show i ++ "TreeState" ++ show uid) $ (case s1 i of { Nothing -> id; Just s -> ((Pointer $ SType s, "evalState"):) }) [(ty, field) | (field,ty,_) <- treeState_ (xsuper i)]
        st i      = Pointer . SType $ s3 i
        xpath i n = flip withClone (\i -> inc (ref_count i)) $ withPath i (inN n) (et n) (st n)
        fs1 n     = \i -> [(field,init) | (field,_ty,init) <- evalState_ (xsuper n) ]
        fs3 n     = \i -> [(field,init) | (field,_ty,init) <- treeState_ (xsuper n) ]
        withSeq f = numSwitch (\n -> f (xsuper n) (inN n))
        inSeq f   = \i -> numSwitch (\n -> f (xsuper n) (xpath i n))
        inSeq_ f  = \i -> numSwitch (\n -> f (xsuper n) (xpath i n) n)
        push dir  = \i -> inSeq_ ( \super j pos -> dir super (j `onCommit` (mkCopy i "seqn_pos"
                                                                            >>> needSide pos (mkCopy j "evalState")
                                                                            >>> needSide pos (inc (ref_count j))
                                                                           )
                                                             )
                                 ) i
        initSubEvalState = \j s fs -> (case s of { Nothing -> return Skip; Just ss -> return (    (estate j <== New ss)
				              >>> (ref_count j <== 1)
--			                      >>> (cont j <== true)
                                             )})
                                        @>>>@ inite (fs j) j
	deleteMe = \i -> inSeq_ (\super j pos -> do delrest <- deleteE super j
                                                    dr <- dec_ref "deleteMe" j i pos
                                                    return (delrest >>> dr)) i
--        dec_ref :: String -> Info -> Info -> Int -> Statement
        dec_ref s j i pos = complete (xsuper pos) j >>= \compl -> decrefx j pos (estate_type i,estate i) (estate_type j,estate j) (ref_count_type, ref_count j) (THook "bool", compl)
        decrefx j pos = memo "dec_ref_and" j (\(_,esti) (_,estj) (_,rcj) (_,xcl) -> return $ ((assign ((esti @=> "complete") &&& (xcl))) (esti @=> "complete") >>> 
                            needSide pos (dec (rcj) >>> ifthen (rcj @== 0) (Delete (estj)))) {- >>> DebugValue ("completeness and" ++ show uid) (esti @=> "complete") -})
	inN n     = \state -> state @-> "seqn_union" @-> ("seq" ++ show n)
	seq_pos   = \i -> tstate i @-> "seqn_pos"


andN [] = dummy
andN [s] = s
andN s =
  let sc = buildCombiner s
      in case sc of 
        SearchCombiner { runner = runner, elems = elems } ->
          Search { mkeval = \super -> do { ss <- extractCombiners elems $ mapE (L . mmap runL . runL) super
                                         ; uid <- get
                                         ; put $ uid+1
                                         ; return $ mapE (L . mmap L . runL) $ memoLoop $ seqNLoop uid ss
                                         }
                 , runsearch = runner . rReaderT 0 . runL
                 }

a <&> b = andN [a,b]

