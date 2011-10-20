{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Control.CP.FD.Gecode.RuntimeSearch (
  SearchGecodeSolver,
  SearchGecodeOptions(..),
  setOptions
) where

import Control.Monad.State.Lazy
import System.IO.Unsafe

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Mixin.Mixin

import Control.CP.Debug
import Control.CP.Solver
import Control.CP.EnumTerm
import Control.CP.SearchTree
import Control.CP.FD.FD
import Data.Expr.Sugar
import Control.CP.FD.Model
import Control.CP.FD.Gecode.Common

import qualified Control.CP.FD.Gecode.Interface as GCI

-- ################################## SearchGecodeSolver #########################################

data SearchGecodeState = SearchGecodeState { spaceRef :: GCI.Space, options :: SearchGecodeOptions }

data SearchGecodeOptions = SearchGecodeOptions { minimizeVar :: Maybe GCI.CGIntVar }

initOptions :: SearchGecodeOptions
initOptions = SearchGecodeOptions {
  minimizeVar = Nothing
}

setOptions :: (SearchGecodeOptions -> SearchGecodeOptions) -> SearchGecodeSolver ()
setOptions f = do
  s <- get
  put $ s { options = f $ options s }

newtype SearchGecodeSolver a = SearchGecodeSolver { sgsStateT :: StateT SearchGecodeState IO a }
  deriving (Monad, MonadState SearchGecodeState, MonadIO)

newState :: IO SearchGecodeState
newState = do
  initSpace <- GCI.newSpace
  return $ SearchGecodeState {
    spaceRef = initSpace,
    options = initOptions
  }

liftSGS :: (GCI.Space -> IO a) -> SearchGecodeSolver a
liftSGS f = do
  SearchGecodeState { spaceRef = s } <- get
  liftIO $ f s

liftSGSo :: (GCI.Space -> SearchGecodeOptions -> IO a) -> SearchGecodeSolver a
liftSGSo f = do
  s <- get
  liftIO $ f (spaceRef s) (options s)

runSearchGecodeSolver :: SearchGecodeSolver a -> (a, SearchGecodeState)
runSearchGecodeSolver p = unsafePerformIO $ do
  initState <- newState
  runStateT (sgsStateT p) initState

continueSearchGecodeSolver :: SearchGecodeState -> SearchGecodeSolver a -> (a, SearchGecodeState)
continueSearchGecodeSolver st p = unsafePerformIO $ runStateT (sgsStateT p) st

-- intTermInfo :: (GecodeIntTerm s) -> s IntTermInfo
-- intTermInfo (IntTermRef (IntVarSingle i)) = do
--   GecodeState { spaceRef = s } <- get
--   liftIO $ do 
--     doPropagation s
--     getIntTermInfo s i

propagate :: SearchGecodeSolver ()
propagate = liftSGS GCI.propagate

intInfo v = liftSGS $ \s -> GCI.getIntInfo s v

boolInfo v = liftSGS $ \s -> GCI.getBoolInfo s v

--------------------------------- Solver Instance ------------------------------------------

instance Solver SearchGecodeSolver where
  type Constraint SearchGecodeSolver = GecodeConstraint SearchGecodeSolver
  type Label SearchGecodeSolver = GCI.Space
  run = fst . runSearchGecodeSolver
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
  add c = do
    r <- mixin (addMeta <@> addSGS) c
    s <- get
    liftIO $ GCI.propagate (spaceRef s)
    return r

addSGS _ _ c = do
  debug ("addsgs: "++(show c)) $ return ()
  liftSGS $ \s -> GCI.addConstraint s c

instance Term SearchGecodeSolver GCI.CGIntVar where
  newvar = liftSGS GCI.newInt
  type Help SearchGecodeSolver GCI.CGIntVar = ()
  help _ _ = ()

instance Term SearchGecodeSolver GCI.CGBoolVar where
  newvar = liftSGS GCI.newBool
  type Help SearchGecodeSolver GCI.CGBoolVar = ()
  help _ _ = ()

------------------------------- GecodeSolver instance --------------------------------------

instance GecodeSolver SearchGecodeSolver where
  type GecodeIntVar SearchGecodeSolver = GCI.CGIntVar
  type GecodeBoolVar SearchGecodeSolver = GCI.CGBoolVar
  type GecodeColVar SearchGecodeSolver = GCI.CGColVar
  newInt_at c p = liftSGS $ \s -> GCI.newIntAt s c (fromIntegral p)
  newCol_list l = liftSGS $ \s -> GCI.newColList s l
  newCol_size l = liftSGS $ \s -> GCI.newColSize s (fromIntegral l)
  newCol_cat c1 c2 = liftSGS $ \s -> GCI.newColCat s c1 c2
--  newCol_take c p l = liftSGS $ \s -> GCI.newColTake s c (fromIntegral p) (fromIntegral l)
  col_getSize c = liftSGS $ \s -> GCI.getColSize s c
--  splitBoolDomains ((m,_):_) = return [m @= toBoolExpr False, m @= toBoolExpr True]
--  splitIntDomains ((m,f):_) = do
--    info <- intInfo f
--    return [m @< toExpr (1 + (toInteger $ GCI.iti_med info)), m @> toExpr (toInteger $ GCI.iti_med info)]
  splitBoolDomain = error "need to split bool domains?"
  splitIntDomain = error "need to split int domains?"

--------------------------------- EnumTerm instances ---------------------------------------

instance EnumTerm SearchGecodeSolver GCI.CGIntVar where
  type TermBaseType SearchGecodeSolver GCI.CGIntVar = Integer
  getDomainSize v = do
    s <- get
    Just info <- intInfo v
    return $ fromInteger $ toInteger $ GCI.iti_size info
  getValue v = do
    s <- get
    Just info <- intInfo v
    case GCI.iti_val info of
      Nothing -> return Nothing
      Just i -> do
        let ti = toInteger i
        return $ Just ti
  setValue var val = undefined
  getDomain _ = undefined
  enumerator = Just $ \l -> label $ liftSGSo $ \s o -> do
    case minimizeVar o of
      Just x -> do
        GCI.postBranchers s ([],[x],[])
        GCI.postBranchers s ([],l,[])
        GCI.setCost s x
      _ -> GCI.postBranchers s ([],l,[])
    search <- liftIO $ GCI.newSearch s (case minimizeVar o of {Nothing -> False; _ -> True})
    let
      go :: (MonadTree m, TreeSolver m ~ SearchGecodeSolver) => Int -> m ()
      go i = unsafePerformIO $ do
        res <- GCI.runSearch search
        case res of
          Nothing -> return $ false
          Just x -> return $ 
            (label $ do
              st <- get
              put $ st { spaceRef = x }
              return $ true
            ) \/ (go $ i+1)
    return $ go 0

instance EnumTerm SearchGecodeSolver GCI.CGBoolVar where
  type TermBaseType SearchGecodeSolver GCI.CGBoolVar = Bool
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
  setValue var val = undefined
  getDomain _ = undefined
  enumerator = Just $ \l -> label $ liftSGSo $ \s o -> do
    GCI.postBranchers s (l,[],[])
    case minimizeVar o of
      Just x -> GCI.setCost s x
      _ -> return ()
    search <- liftIO $ GCI.newSearch s (case minimizeVar o of {Nothing -> False; _ -> True})
    let
      go :: (MonadTree m, TreeSolver m ~ SearchGecodeSolver) => Int -> m ()
      go i = unsafePerformIO $ do
        res <- GCI.runSearch search
        case res of
          Nothing -> return $ false
          Just x -> return $ 
            (label $ do
              goto x
              return $ true
            ) \/ (go $ i+1)
    return $ go 0
