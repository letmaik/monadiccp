{-# LANGUAGE CPP #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

#ifdef RGECODE

module Control.CP.FD.Gecode.RuntimeSolver (
  SearchSolver(..),
  RuntimeSolver(..)
) where

import Maybe (fromMaybe,catMaybes,isJust,fromJust)
import List (findIndex,find)
import Data.Map hiding (map,filter)

import Control.Monad.State.Lazy
import Control.Monad.Trans
import Control.Monad.Cont

import Data.Bits
import Data.Word
import Foreign
import Foreign.Storable
import Foreign.Marshal
import Foreign.Marshal.Array
import Foreign.Ptr
import Foreign.ForeignPtr
import Foreign.C.String
import Foreign.C.Types

import Control.CP.SearchTree hiding (label)
import Control.CP.Solver
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.Debug
import Control.CP.Mixin
import Control.CP.EnumTerm

import Control.CP.FD.Gecode.Common
import Control.CP.FD.Gecode.Interface

class (Monad s, MonadState (GecodeState s) s, MonadIO s, Term s IntTerm) => RuntimeGecodeSolver s where
  stateM :: s a -> StateT (GecodeState s) IO a

instance Solver RuntimeSolver where
   type Constraint RuntimeSolver = GConstraint
   type Label RuntimeSolver = GecodeState RuntimeSolver
   add   = addRuntimeGecode
   run   = fst . runRuntimeGecode False
   mark  = do
     s <- get
     copyState s
   goto s = do
     x <- copyState s
     put x

instance Solver SearchSolver where
   type Constraint SearchSolver = GConstraint
   type Label SearchSolver = GecodeState SearchSolver
   add   = addRuntimeGecode
   run   = fst . runRuntimeGecode False
   mark  = do
     s <- get
     copyState s
   goto s = do
     x <- copyState s
     put x

--------------------------------------------------------------------------------
-- | Gecode terms
--------------------------------------------------------------------------------

instance Term SearchSolver IntTerm where
  newvar = newVarInt
  type Help SearchSolver IntTerm = ()
  help _ _ = ()
instance Term RuntimeSolver IntTerm where
  newvar = newVarInt
  type Help RuntimeSolver IntTerm = ()
  help _ _ = ()
instance Term SearchSolver BoolTerm where
  newvar = newVarBool
  type Help SearchSolver BoolTerm = ()
  help _ _ = ()
instance Term RuntimeSolver BoolTerm where
  newvar = newVarBool
  type Help RuntimeSolver BoolTerm = ()
  help _ _ = ()
  

--------------------------------------------------------------------------------
-- | Gecode monad definition 
--------------------------------------------------------------------------------

data RuntimeGecodeSolver s => GecodeState s = GecodeState { spaceRef :: Space, cexpr :: Map (ExprKey (FDTerm s)) Int }


newtype RuntimeSolver a = RuntimeSolver { rStateM :: StateT (GecodeState RuntimeSolver) IO a }
  deriving (Monad, MonadState (GecodeState RuntimeSolver), MonadIO)
newtype SearchSolver a = SearchSolver { sStateM :: StateT (GecodeState SearchSolver) IO a }
  deriving (Monad, MonadState (GecodeState SearchSolver), MonadIO)

newState :: RuntimeGecodeSolver s => Bool -> IO (GecodeState s)
newState gcs = do
  initSpace <- newSpace
  return $ GecodeState { spaceRef = initSpace, cexpr = Data.Map.empty }

copyState :: RuntimeGecodeSolver s => GecodeState s -> s (GecodeState s)
copyState state = do
  x <- liftIO $ copySpace (spaceRef state)
  return $ state { spaceRef = x }

runRuntimeGecode :: RuntimeGecodeSolver s => Bool -> s a -> (a, GecodeState s)
runRuntimeGecode gcs p = unsafePerformIO $ do
  initState <- newState gcs
  runStateT (stateM p) initState

continueRuntimeGecode :: RuntimeGecodeSolver s => GecodeState s -> s a -> (a, GecodeState s)
continueRuntimeGecode st p = unsafePerformIO $ runStateT (stateM p) st

intTermInfo :: RuntimeGecodeSolver s => IntTerm -> s IntTermInfo
intTermInfo (IntVar i) = do
  GecodeState { spaceRef = s } <- get
  liftIO $ getIntTermInfo s i

addRuntimeGecode :: RuntimeGecodeSolver s => GConstraint -> s Bool
addRuntimeGecode (CDom (IntVar i) low high) = proc $ \ptr -> c_gecode_int_dom ptr (toCGIntVar i) (toCGVal low) (toCGVal high)
addRuntimeGecode (CRel (IntVar i1) op (IntVar i2)) = proc $ \ptr -> c_gecode_int_rel ptr (toCGIntVar i1) (mapGOperator op) (toCGIntVar i2)
addRuntimeGecode (CRel (IntConst c1) op (IntVar i2)) = proc $ \ptr -> c_gecode_int_rel_cf ptr (toCGVal c1) (mapGOperator op) (toCGIntVar i2)
addRuntimeGecode (CRel (IntVar i1) op (IntConst c2)) = proc $ \ptr -> c_gecode_int_rel_cs ptr (toCGIntVar i1) (mapGOperator op) (toCGVal c2)
addRuntimeGecode (CValue (IntVar i) val) = proc $ \ptr -> c_gecode_int_value ptr (toCGIntVar i) (toCGVal val)
addRuntimeGecode (CMult (IntVar i1) (IntVar i2) (IntVar ir)) = proc $ \ptr -> c_gecode_int_mult ptr (toCGIntVar i1) (toCGIntVar i2) (toCGIntVar ir)
addRuntimeGecode (CDiv (IntVar i1) (IntVar i2) (IntVar ir)) = proc $ \ptr -> c_gecode_int_div ptr (toCGIntVar i1) (toCGIntVar i2) (toCGIntVar ir)
addRuntimeGecode (CMod (IntVar i1) (IntVar i2) (IntVar ir)) = proc $ \ptr -> c_gecode_int_mod ptr (toCGIntVar i1) (toCGIntVar i2) (toCGIntVar ir)
addRuntimeGecode (CAbs (IntVar i) (IntVar ir)) = proc $ \ptr -> c_gecode_int_abs ptr (toCGIntVar i) (toCGIntVar ir)
addRuntimeGecode (CLinear l op val) = do
  GecodeState { spaceRef = s } <- get
  let len = length l
  let vars = map (\(IntVar var,_) -> toCGIntVar var) l
  let coefs = map (\(_,coef) -> toCGVal coef) l
  liftIO $ 
    withArray vars $ \pVars ->
      withArray coefs $ \pCoefs -> do
        b <- withForeignPtr s $ \ptr -> c_gecode_int_linear ptr (fromIntegral len) pVars pCoefs (mapGOperator op) (toCGVal val)
        return $ fromCGBool b
addRuntimeGecode (CAllDiff l) = do
  GecodeState { spaceRef = s } <- get
  let len = length l
  let vars = map (\(IntVar i) -> toCGIntVar i) l
  liftIO $
    withArray vars $ \pVars -> do
      b <- withForeignPtr s $ \ptr -> c_gecode_int_alldiff ptr (fromIntegral len) pVars
      return $ fromCGBool b
addRuntimeGecode (CSorted l strict) = do
  GecodeState { spaceRef = s } <- get
  let len = length l
  let vars = map (\(IntVar i) -> toCGIntVar i) l
  liftIO $
    withArray vars $ \pVars -> do
      b <- withForeignPtr s $ \ptr -> c_gecode_int_sorted ptr (fromIntegral len) pVars (toCGBool strict)
      return $ fromCGBool b

proc f = do
  GecodeState { spaceRef = s } <- get
  liftIO $ do
    b <- withForeignPtr s f
    return $ fromCGBool b

--------------------------------------------------------------------------------
-- | RuntimeSolver solver implementation
--------------------------------------------------------------------------------

newVarInt :: RuntimeGecodeSolver s => s IntTerm
newVarInt = do
  GecodeState { spaceRef = s } <- get
  (CGIntVar r) <- liftIO $ withForeignPtr s $ c_gecode_int_newvar 
  return (IntVar $ fromIntegral r)

newVarBool :: RuntimeGecodeSolver s => s BoolTerm
newVarBool = do
  GecodeState { spaceRef = s } <- get
  (CGBoolVar r) <- liftIO $ withForeignPtr s $ c_gecode_bool_newvar
  return (BoolVar $ fromIntegral r)

--------------------------------------------------------------------------------
-- | RuntimeSolver FDSolver instance
--------------------------------------------------------------------------------

instance (RuntimeGecodeSolver s, Ord (FDTerm s)) => GecodeSolver s where
  caching_decompose super this x = Label $ do
    s <- get
    let wx = ExprKey x
    case Data.Map.lookup wx (cexpr s) of
      Nothing -> return $ do
        n@(IntVar i) <- super x
        Label $ do
          s <- get
          put $ s { cexpr = insert wx i $ cexpr s }
          return $ return n
      Just i -> return $ return $ IntVar i
  setVarImplicit (IntVar i) b = return ()

instance FDSolver RuntimeSolver where
  type FDTerm RuntimeSolver = IntTerm
  specific_compile_constraint = linearCompile <@> basicCompile
  specific_decompose = caching_decompose
  specific_fresh_var super this = do
    v@(IntVar i) <- super
    Label $ do
      setVarImplicit (IntVar i) True
      return $ Return v

instance FDSolver SearchSolver where
  type FDTerm SearchSolver = IntTerm
  specific_compile_constraint = linearCompile <@> basicCompile
  specific_decompose = caching_decompose
  specific_fresh_var super this = do
    v@(IntVar i) <- super
    Label $ do
      setVarImplicit (IntVar i) True
      return $ Return v


instance EnumTerm RuntimeSolver IntTerm where
  type TermDomain RuntimeSolver IntTerm = CInt
  get_domain_size v = do
    IntTermInfo { iti_size = size } <- intTermInfo v
    return $ fromIntegral size
  get_value v = do
    IntTermInfo { iti_val = val } <- intTermInfo v
    return val
  split_domain_partial v@(IntVar it) = do
    IntTermInfo { iti_val = val, iti_med = med, iti_size = size } <- intTermInfo v
    return $ if size == 0
      then []
      else if isJust val
        then [return ()]
        else [Add (CRel v OLess (IntConst $ (fromIntegral med)+1)) $ enumerate [v],Add (CRel (IntConst $ fromIntegral med) OLess v) $ enumerate [v]]


instance EnumTerm SearchSolver IntTerm where
  type TermDomain SearchSolver IntTerm = CInt
  get_domain_size v = do
    IntTermInfo { iti_size = size } <- intTermInfo v
    return $ fromIntegral size
  get_value v = do
    IntTermInfo { iti_val = val } <- intTermInfo v
    return val
    
  split_domains lst = do
    let 
      folder a b = case a of
        IntVar i -> (i:b)
        _ -> b
    let vars = map toCGIntVar $ foldr folder [] lst
    state <- get
    liftIO $ withArray vars $ \ptr -> withForeignPtr (spaceRef state) $ \sptr -> c_gecode_int_branch sptr (fromIntegral $ length vars) ptr
    search <- liftIO $ newSearch $ spaceRef state
    let 
      go i = unsafePerformIO $ do
        res <- runSearch search
        case res of
          Nothing -> return $ return ()
          Just x -> return $ Try (Label $ do
              put state { spaceRef = x }
              return $ return ()
            ) (go $ i+1)
    return $ go 0

  split_domain_partial v = do
    x <- split_domains [v]
    return [x]

  label _   = Label . split_domains
  enumerate = Label . split_domains

---------------------------------------------
-- | RuntimeGecodeSolver instances
---------------------------------------------

instance RuntimeGecodeSolver RuntimeSolver where
  stateM = rStateM

instance RuntimeGecodeSolver SearchSolver where
  stateM = sStateM

#endif
