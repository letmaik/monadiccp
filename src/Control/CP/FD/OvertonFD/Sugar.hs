{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.CP.FD.OvertonFD.Sugar (
) where

import Data.Set(Set)
import qualified Data.Set as Set

import Control.CP.Debug
import Control.Mixin.Mixin
import Control.CP.Solver
import Control.CP.FD.FD
import Control.CP.FD.SimpleFD
import Data.Expr.Data
import Data.Expr.Sugar
-- import Control.CP.FD.Expr.Util
import Control.CP.FD.Model
import Control.CP.FD.Graph
import Control.CP.FD.OvertonFD.OvertonFD

newVars :: Term s t => Int -> s [t]
newVars 0 = return []
newVars n = do
  l <- newVars $ n-1
  n <- newvar
  return $ n:l

instance FDSolver OvertonFD where
  type FDIntTerm OvertonFD = FDVar
  type FDBoolTerm OvertonFD = FDVar

  type FDIntSpec OvertonFD = FDVar
  type FDBoolSpec OvertonFD = FDVar
  type FDColSpec OvertonFD = [FDVar]
  
  type FDIntSpecType OvertonFD = ()
  type FDBoolSpecType OvertonFD = ()
  type FDColSpecType OvertonFD = ()

  fdIntSpec_const (Const i) = ((),do
    v <- newvar
    add $ OHasValue v $ fromInteger i
    return v)
  fdIntSpec_term i = ((),return i)
  
  fdBoolSpec_const (BoolConst i) = ((),do
    v <- newvar 
    add $ OHasValue v $ if i then 1 else 0
    return v)
  fdBoolSpec_term i = ((),return i)

  fdColSpec_list l = ((),return l)
  fdColSpec_size (Const s) = ((),newVars $ fromInteger s)
  fdColSpec_const l = ((),error "constant collections not yet supported by overton interface")

  fdColInspect = return

  fdSpecify = specify <@> simple_fdSpecify
  fdProcess = process <@> simple_fdProcess

  fdEqualInt v1 v2 = addFD $ OSame v1 v2
  fdEqualBool v1 v2 = addFD $ OSame v1 v2
  fdEqualCol v1 v2 = do
    if length v1 /= length v2
      then setFailed
      else sequence_ $ zipWith (\a b -> addFD $ OSame a b) v1 v2

  fdIntVarSpec = return . Just
  fdBoolVarSpec = return . Just
  fdSplitIntDomain b = do
    d <- fd_domain b
    return $ (map (b `OHasValue`) d, True)
  fdSplitBoolDomain b = do
    d <- fd_domain b
    return $ (map (b `OHasValue`) $ filter (\x -> x==0 || x==1) d, True)

-- processBinary :: (EGVarId,EGVarId,EGVarId) -> (FDVar -> FDVar -> FDVar -> OConstraint) -> FDInstance OvertonFD ()
processBinary (v1,v2,va) f = addFD $ f (getDefIntSpec v1) (getDefIntSpec v2) (getDefIntSpec va)

-- processUnary :: (EGVarId,EGVarId) -> (FDVar -> FDVar -> OConstraint) -> FDInstance OvertonFD ()
processUnary (v1,va) f = addFD $ f (getDefIntSpec v1) (getDefIntSpec va)

specify :: Mixin (SpecFn OvertonFD)
specify s t edge = case (debug ("overton-specify("++(show edge)++")") edge) of
  EGEdge { egeCons = EGChannel, egeLinks = EGTypeData { intData=[i], boolData=[b] } } -> 
    ([(1000,b,True,do
      s <- getIntSpec i
      case s of
        Just ss -> return $ SpecResSpec ((),return (ss,Nothing))
        _ -> return SpecResNone
     )],[(1000,i,True,do
      s <- getBoolSpec b
      case s of
        Just ss -> return $ SpecResSpec ((),return (ss,Nothing))
        _ -> return SpecResNone
     )],[])
  _ -> s edge

-- process :: Mixin (EGEdge -> FDInstance OvertonFD ())
process s t con info = case (con,info) of
    (EGIntValue c, ([],[a],[])) -> case c of
      Const v -> addFD $ OHasValue (getDefIntSpec a) (fromInteger v)
      _ -> error "Overton solver does not support parametrized values"
    (EGPlus, ([],[a,b,c],[])) -> processBinary (b,c,a) OAdd
    (EGMinus, ([],[a,b,c],[])) -> processBinary (a,c,b) OAdd
    (EGMult, ([],[a,b,c],[])) -> processBinary (b,c,a) OMult
    (EGAbs, ([],[a,b],[])) -> processUnary (b,a) OAbs
    (EGDiff, ([FDSpecInfoBool {fdspBoolVal = Just (BoolConst True)}],[a,b],[])) -> addFD $ ODiff (getDefIntSpec a) (getDefIntSpec b)
    (EGLess True, ([FDSpecInfoBool {fdspBoolVal = Just (BoolConst True)}],[a,b],[])) -> addFD $ OLess (getDefIntSpec a) (getDefIntSpec b)
    (EGLess False, ([FDSpecInfoBool {fdspBoolVal = Just (BoolConst True)}],[a,b],[])) -> addFD $ OLessEq (getDefIntSpec a) (getDefIntSpec b)
    (EGEqual, ([FDSpecInfoBool {fdspBoolVal = Just (BoolConst True)}],[a,b],[])) -> addFD $ OSame (getDefIntSpec a) (getDefIntSpec b)
    _ -> s con info
