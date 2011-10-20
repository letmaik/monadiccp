{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE CPP #-}

module Control.CP.FD.Gecode.Runtime (
  RuntimeGecodeSolver
) where

import Control.Monad.State.Lazy
import System.IO.Unsafe

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Mixin.Mixin
import Data.Linear

import Control.CP.Debug
import Control.CP.Solver
import Control.CP.EnumTerm
import Control.CP.FD.FD
import Data.Expr.Sugar
import Control.CP.FD.Model
import Control.CP.FD.Gecode.Common

import qualified Control.CP.FD.Gecode.Interface as GCI

-- ################################## RuntimeGecodeSolver #########################################

newtype RuntimeGecodeState = RuntimeGecodeState {
  spaceRef :: GCI.Space
}

newtype RuntimeGecodeSolver a = RuntimeGecodeSolver { rgsStateT :: StateT RuntimeGecodeState IO a }
  deriving (Monad, MonadState RuntimeGecodeState, MonadIO)

newState :: IO RuntimeGecodeState
newState = do
  initSpace <- GCI.newSpace
  return $ RuntimeGecodeState { 
    spaceRef = initSpace
  }

liftRGS :: (GCI.Space -> IO a) -> RuntimeGecodeSolver a
liftRGS f = do
  RuntimeGecodeState { spaceRef = s } <- get
  liftIO $ f s

runRuntimeGecodeSolver :: RuntimeGecodeSolver a -> (a, RuntimeGecodeState)
runRuntimeGecodeSolver p = unsafePerformIO $ do
  initState <- newState
  runStateT (rgsStateT p) initState

continueRuntimeGecodeSolver :: RuntimeGecodeState -> RuntimeGecodeSolver a -> (a, RuntimeGecodeState)
continueRuntimeGecodeSolver st p = unsafePerformIO $ runStateT (rgsStateT p) st

propagate :: RuntimeGecodeSolver ()
propagate = liftRGS GCI.propagate

intInfo v = liftRGS $ \s -> GCI.getIntInfo s v

boolInfo v = liftRGS $ \s -> GCI.getBoolInfo s v

--------------------------------- Solver Instance ------------------------------------------

instance Solver RuntimeGecodeSolver where
  type Constraint RuntimeGecodeSolver = GecodeConstraint RuntimeGecodeSolver
  type Label RuntimeGecodeSolver = GCI.Space
  run = fst . runRuntimeGecodeSolver
  mark = do
    s <- get
    let ref = spaceRef s
    x <- liftIO $ GCI.copySpace ref
    liftIO $ GCI.modRefcount x (500000000)
    return x
  markn i = do
    s <- get
    let ref = spaceRef s
    liftIO $ GCI.modRefcount ref i
    return ref
  goto ref = do
    s <- get
    fc <- liftIO $ GCI.modRefcount ref (-1)
    if fc==0
      then put s { spaceRef = ref }
      else do
        x <- liftIO $ GCI.copySpace ref
        put s { spaceRef = x }
  add = mixin (addMeta <@> addRGS)

addRGS _ _ c = do
  debug ("addrgs: "++(show c)) $ return ()
  liftRGS $ \s -> GCI.addConstraint s c

instance Term RuntimeGecodeSolver GCI.CGIntVar where
  newvar = liftRGS GCI.newInt
  type Help RuntimeGecodeSolver GCI.CGIntVar = ()
  help _ _ = ()

instance Term RuntimeGecodeSolver GCI.CGBoolVar where
  newvar = liftRGS GCI.newBool
  type Help RuntimeGecodeSolver GCI.CGBoolVar = ()
  help _ _ = ()

------------------------------- GecodeSolver instance --------------------------------------

instance GecodeSolver RuntimeGecodeSolver where
  type GecodeIntVar RuntimeGecodeSolver = GCI.CGIntVar
  type GecodeBoolVar RuntimeGecodeSolver = GCI.CGBoolVar
  type GecodeColVar RuntimeGecodeSolver = GCI.CGColVar
  newInt_at c p = liftRGS $ \s -> GCI.newIntAt s c (fromIntegral p)
  newCol_list l = liftRGS $ \s -> GCI.newColList s l
  newCol_size l = liftRGS $ \s -> GCI.newColSize s (fromIntegral l)
  newCol_cat c1 c2 = liftRGS $ \s -> GCI.newColCat s c1 c2
  col_getSize c = liftRGS $ \s -> GCI.getColSize s c
  splitBoolDomain v = return ([GCBoolVal v $ toBoolExpr False,GCBoolVal v $ toBoolExpr True],True)
  splitIntDomain m = do
    Just info <- intInfo m
    let split = toExpr $ toInteger $ GCI.iti_med info
    let sp = termToLinear m - constToLinear split
    return ([GCLinear sp GOLessEqual, GCLinear (-sp) GOLess],GCI.iti_high info - GCI.iti_low info < 2)

--------------------------------- EnumTerm instances ---------------------------------------

instance EnumTerm RuntimeGecodeSolver GCI.CGIntVar where
  type TermBaseType RuntimeGecodeSolver GCI.CGIntVar = Integer
  getDomainSize v = do
    s <- get
    info <- intInfo v
    case info of
      Nothing -> return 0
      Just x -> return $ fromInteger $ toInteger $ GCI.iti_size x
  getValue v = do
    s <- get
    Just info <- intInfo v
    case GCI.iti_val info of
      Nothing -> return Nothing
      Just i -> return $ Just $ toInteger i
  getDomain v = error "inspection of full runtime domains is not implemented"
  setValue _ _ = error "settinf of runtime variables is not implemented"

instance EnumTerm RuntimeGecodeSolver GCI.CGBoolVar where
  type TermBaseType RuntimeGecodeSolver GCI.CGBoolVar = Bool
  getDomainSize v = do
    x <- boolInfo v
    return $ case x of
      -2 -> 0
      -1 -> 2
      _ -> 1
  getValue v = do
    x <- boolInfo v
    return $ case x of
      0 -> Just False
      1 -> Just True
      _ -> Nothing
  getDomain v = error "inspection of full runtime domains is not implemented"
  setValue _ _ = error "settinf of runtime variables is not implemented"
