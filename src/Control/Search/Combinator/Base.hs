module Control.Search.Combinator.Base (
    label
  , vlabel
  , glabel, gblabel
  , int_assign
  , ilabel
  , maxV, minV, lbV, ubV, domsizeV, lbRegretV, ubRegretV, degreeV, domSizeDegreeV, wDegreeV, domSizeWDegreeV, randomV, minD, maxD, meanD, medianD, randomD
  , foldVarSel, ifoldVarSel, bfoldVarSel, bifoldVarSel
  ) where

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Generator

import Control.Monatron.IdT

data Label m = Label 
	           { treeStateL   :: [(String,Type, Value -> Statement)]
                   , leftChild_L  :: [Info -> Statement]
                   , rightChild_L :: [Info -> Statement]
                   , addL         :: Info -> m Statement
                   , tryL         :: Info -> m Statement
                   , intArraysL   :: [String]
                   , boolArraysL  :: [String]
                   , intVarsL     :: [String]
                   }

v1Label var1 selVal rel e = 
            Label { treeStateL  = [("val", Int,  assign 0)
                                  ,("eq",  Bool, assign true)]
                  , leftChild_L  = 
                                  [ \i -> mkUpdate i "eq" (const true)
                                  , \i -> mkCopy i "val" ]
                  , rightChild_L =
                                  [ \i -> mkUpdate i "eq" (const false)
                                  , \i -> mkCopy i "val" ]
                  , addL        = \i -> return $
                                                 IfThenElse (eq i)
                                                   (Post (space i) (var i `rel` val i))
                                                   (Post (space i) (neg (var i `rel` val i)))
                  , tryL        = \i -> returnE e (resetInfo i) >>= \ret -> -- XXX
                                        tryE_ e (resetInfo i)   >>= \try -> -- XXX
                                        return $ (IfThenElse (Assigned (var i))
                                                          ret
                                                          (val i <== (selVal $ var i) >>> try))
                  , intArraysL  = []
                  , boolArraysL = []
                  , intVarsL    = [var1]
                  }
                  where val i = tstate i @-> "val"
                        eq  i = tstate i @-> "eq"
                        var i = IVar var1 (space i)


vLabel vars selVar selVal rel e = 
            Label { treeStateL  = [("pos", Int,  assign 0)
				  ,("val", Int,  assign 0)
                                  ,("eq",  Bool, assign true)]
                  , leftChild_L  = 
                                  [ \i -> mkUpdate i "eq" (const true)
                                  , \i -> mkCopy i "val"
                                  , \i -> mkCopy i "pos"]
                  , rightChild_L =
                                  [ \i -> mkUpdate i "eq" (const false)
                                  , \i -> mkCopy i "val"
                                  , \i -> mkCopy i "pos"]
                  , addL        = \i -> return $
                                                 IfThenElse (eq i)
                                                   (Post (space i) (var i `rel` val i))
                                                   (Post (space i) (neg (var i `rel` val i)))
                  , tryL        = \i -> returnE e (resetInfo i) >>= \ret -> -- XXX
                                        tryE_ e (resetInfo i)   >>= \try -> -- XXX
                                        return $ (selVar i vars
                                                          ret
                                                          (val i <== (selVal $ var i) >>> try))
                  , intArraysL  = [vars]
                  , boolArraysL = []
                  , intVarsL    = []
                  }
                  where val i = tstate i @-> "val"
                        pos i = tstate i @-> "pos"
                        eq  i = tstate i @-> "eq"
                        var i = AVarElem vars (space i) (pos i)

vbLabel vars selVar selVal rel e = 
            Label { treeStateL  = [("pos", Int,  assign 0)
				  ,("val", Int,  assign 0)
                                  ,("eq",  Bool, assign true)]
                  , leftChild_L  = 
                                  [ \i -> mkUpdate i "eq" (const true)
                                  , \i -> mkCopy i "val"
                                  , \i -> mkCopy i "pos"]
                  , rightChild_L =
                                  [ \i -> mkUpdate i "eq" (const false)
                                  , \i -> mkCopy i "val"
                                  , \i -> mkCopy i "pos"]
                  , addL        = \i -> return $
                                                 IfThenElse (eq i)
                                                   (Post (space i) (var i `rel` val i))
                                                   (Post (space i) (neg (var i `rel` val i)))
                  , tryL        = \i -> returnE e (resetInfo i) >>= \ret -> -- XXX
                                        tryE_ e (resetInfo i)   >>= \try -> -- XXX
                                        return $ (selVar i vars
                                                          ret
                                                          (val i <== (selVal $ var i) >>> try))
                  , intArraysL  = []
                  , boolArraysL = [vars]
                  , intVarsL    = []
                  }
                  where val i = tstate i @-> "val"
                        pos i = tstate i @-> "pos"
                        eq  i = tstate i @-> "eq"
                        var i = BAVarElem vars (space i) (pos i)

type ValSel = Value -> Value

type VarSel = Info -> String -> Statement -> Statement -> Statement

foldVarSel metric (better, zero) i vars notfound found =
  Fold vars (tstate i) (space i) zero metric better
  >>> IfThenElse (pos i @< 0) notfound found
  where pos i = tstate i @-> "pos"

ifoldVarSel metric (better, zero) i vars notfound found =
  IFold vars (tstate i) (space i) zero metric better
  >>> IfThenElse (pos i @< 0) notfound found
  where pos i = tstate i @-> "pos"

bfoldVarSel metric (better, zero) i vars notfound found =
  BFold vars (tstate i) (space i) zero metric better
  >>> IfThenElse (pos i @< 0) notfound found
  where pos i = tstate i @-> "pos"

bifoldVarSel metric (better, zero) i vars notfound found =
  BIFold vars (tstate i) (space i) zero metric better
  >>> IfThenElse (pos i @< 0) notfound found
  where pos i = tstate i @-> "pos"


--------------------------------------------------------------------------------
-- SEARCH TRANSFORMERS
--------------------------------------------------------------------------------

pushLeftTop  e = \i -> pushLeft  e (i `onCommit` mkCopy   i "space"      )
pushRightTop e = \i -> pushRight e (i `onCommit` mkUpdate i "space" Clone)


baseLoop label this = return $ commentEval $ current
  where current =
	    Eval { structs      = ([],[])
                 ,  treeState_  = map entry $ treeStateL label  
                 ,  initH       = const $ return Skip
                 ,  evalState_   = []
		 ,  pushLeftH    = \i -> cachedCommit i @>>>@ return (seqs [f i | f <- leftChild_L label])
		 ,  pushRightH   = \i -> cachedCommit i @>>>@ return (seqs [f i | f <- rightChild_L label])
	         ,  nextSameH    = \i -> return Skip
	         ,  nextDiffH    = \i -> return Skip
		 ,  bodyH       = addE this . resetInfo -- XXX
                 ,  addH        = \i -> tryE this (resetInfo i)   >>= \try -> -- XXX
			 	        addL label i              >>= \a   -> 
                                        return (a >>> try)
	         ,  failH      = const $ return Skip
                 ,  returnH    = \i -> cachedCommit i
--                 ,  continue   = \_ -> return true
                 ,  tryH       = tr label
                 ,  startTryH  = tr label
                 ,  tryLH      = \i -> pushRightTop this (newinfo i "R")            >>= \p2 -> 
                                       pushLeftTop this  (newinfo i "L")            >>= \p4 ->
                                       return $ (
                                         SHook "st->queue->push_back(TreeState());" >>>
                                         SHook "TreeState& nstateR = st->queue->back();" >>>
                                         p2 >>>
                                         SHook "st->queue->push_back(TreeState());" >>>
                                         SHook "TreeState& nstateL = st->queue->back();" >>>
                                         p4
                                       )
                 , intArraysE  = intArraysL label
                 , boolArraysE = boolArraysL label
                 , intVarsE    = intVarsL label
		 , deleteH     = \i -> return Skip
                 , toString    = "base"
                 , canBranch   = return True
                 , complete    = const $ return true
                 }
                 where new_tstate  = Var "nstate"
        tr lab i = failE this (resetInfo i) >>= \fail ->
                   tryL lab i >>= \tryl ->
                   return $ (SHook "Gecode::SpaceStatus status;" >>>
                      (Var "status" <== VHook (rp 0 (space i) ++ "->status()")) >>>
                      IfThenElse (Var "status" @== VHook "SS_FAILED") (fail >>> Delete (space i)) tryl
                   )

label :: String -> (Value -> Value) -> (Value -> Value -> Value, Value) -> (Value -> Value) -> (Value -> Value -> Constraint) -> Search
label get varMeasure varComp valSel rel = 
  Search { mkeval     = \this -> baseLoop (vLabel get (foldVarSel varMeasure varComp) valSel rel this) this 
         , runsearch  = runIdT
         }

vlabel :: String -> (Value -> Value) -> (Value -> Value -> Constraint) -> Search
vlabel get valSel rel = 
  Search { mkeval     = \this -> baseLoop (v1Label get valSel rel this) this 
         , runsearch  = runIdT
         }

ilabel :: String -> (Value -> Value) -> (Value -> Value -> Value, Value) -> (Value -> Value) -> (Value -> Value -> Constraint) -> Search
ilabel get varMeasure varComp valSel rel = 
  Search { mkeval     = \this -> baseLoop (vLabel get (ifoldVarSel varMeasure varComp) valSel rel this) this 
         , runsearch  = runIdT
         }

int_assign :: String -> VarSel -> (Value -> Value) -> (Value -> Value -> Constraint) -> Search
int_assign get varSel valSel rel = 
  Search { mkeval     = \this -> assignLoop (vLabel get varSel valSel rel this) this 
         , runsearch  = runIdT
         }

glabel :: String -> VarSel -> (Value -> Value) -> (Value -> Value -> Constraint) -> Search
glabel get varSel valSel rel = 
  Search { mkeval     = \this -> baseLoop (vLabel get varSel valSel rel this) this 
         , runsearch  = runIdT
         }

gblabel :: String -> VarSel -> (Value -> Value) -> (Value -> Value -> Constraint) -> Search
gblabel get varSel valSel rel = 
  Search { mkeval     = \this -> baseLoop (vbLabel get varSel valSel rel this) this 
         , runsearch  = runIdT
         }

maxV           = (Gt,IVal minBound)
minV           = (Lt,IVal maxBound)

lbV            = MinDom
ubV            = MaxDom 
domsizeV       = \v -> MaxDom v - MinDom v
lbRegretV      = LbRegret
ubRegretV      = UbRegret
degreeV        = Degree
domSizeDegreeV = \v -> domsizeV v `Div` degreeV v
wDegreeV       = WDegree
domSizeWDegreeV= \v -> domsizeV v `Div` wDegreeV v
randomV        = const Random

minD           = MinDom
maxD           = MaxDom
meanD          = \v -> (maxD v + minD v) `Div` 2
medianD        = \v -> Median v
randomD        = \v -> (Random `Mod` (domsizeV v)) + minD v

{-
assignLoop label this = return $ commentEval $ current
  where current =
	    Eval { structs      = ([],[])
                 ,  treeState_  = map entry $ treeStateL label  
                 ,  initH       = const $ return Skip
                 ,  evalState_   = []
		 , pushLeftH    = error "assignLoop.tyE_"
		 , pushRightH   = error "assignLoop.tyE_"
	         ,  nextSameH    = \i -> return Skip
	         ,  nextDiffH    = \i -> return Skip
		 ,  bodyH       = addE this . resetInfo -- XXX
                 ,  addH        = \i -> tryE this (resetInfo i)   >>= \try -> -- XXX
			 	        addL label i              >>= \a   -> 
                                        return (a >>> try)
	         ,  failH      = const $ return Skip
                 ,  returnH    = \i -> cachedCommit i
                 ,  tryH       = returnE this . resetInfo
                 ,  startTryH  = \i -> (return $ comment "<startTryE assign>") @>>>@ (returnE this . resetInfo) i @>>>@ (return $ comment "</startTryE succes>")
                 ,  tryLH      = error "assignLoop.tryE_"
                 , intArraysE  = intArraysL label
                 , boolArraysE = boolArraysL label
                 , intVarsE    = intVarsL label
		 , deleteH     = \i -> return Skip
                 , toString    = "assign"
                 , canBranch   = return False
                 , complete    = const $ return true
                 }
-}
assignLoop label this = return $ commentEval $ current
  where current =
	    Eval { structs      = ([],[])
                 ,  treeState_  = map entry $ treeStateL label  
                 ,  initH       = const $ return Skip
                 ,  evalState_   = []
		 ,  pushLeftH    = \i -> cachedCommit i @>>>@ return (seqs [f i | f <- leftChild_L label])
		 ,  pushRightH   = \i -> cachedCommit i @>>>@ return (seqs [f i | f <- rightChild_L label])
	         ,  nextSameH    = \i -> return Skip
	         ,  nextDiffH    = \i -> return Skip
		 ,  bodyH       = addE this . resetInfo -- XXX
                 ,  addH        = \i -> tryE this (resetInfo i)   >>= \try -> -- XXX
			 	        addL label i              >>= \a   -> 
                                        return (a >>> try)
	         ,  failH      = const $ return Skip
                 ,  returnH    = \i -> cachedCommit i
                 ,  tryH       = tr label
                 ,  startTryH  = tr label
                 ,  tryLH      = \i -> -- pushRightTop this (newinfo i "R")            >>= \p2 -> 
                                       pushLeftTop this  (newinfo i "L")            >>= \p4 ->
                                       return $ (
                                         -- SHook "queue->push_back(TreeState());" >>>
                                         -- SHook "TreeState& nstateR = queue->back();" >>>
                                         -- p2 >>>
                                         SHook "st->queue->push_back(TreeState());" >>>
                                         SHook "TreeState& nstateL = st->queue->back();" >>>
                                         p4
                                       )
                 , intArraysE  = intArraysL label
                 , boolArraysE = boolArraysL label
                 , intVarsE    = intVarsL label
		 , deleteH     = \i -> return Skip
                 , toString    = "base"
                 , canBranch   = return True
                 , complete    = const $ return true
                 }
                 where new_tstate  = Var "nstate"
        tr lab i = failE this (resetInfo i) >>= \fail ->
                   tryL lab i >>= \tryl ->
                   return $ (
                      (Var "status" <== VHook (rp 0 (space i) ++ "->status()")) >>>
                      IfThenElse (Var "status" @== VHook "SS_FAILED") (fail >>> Delete (space i)) tryl
                   )
