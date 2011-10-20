{-# LANGUAGE CPP #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

{-# CFILES glue/interface.cpp #-}

module Control.CP.FD.Gecode.Interface (
  CGOperator(..),
  CGIntVar(..),
  CGBoolVar(..),
  CGBool(..),
  CGVal(..),
  toCGIntVar,
  toCGBoolVar,
  toCGVal,
  fromCGVal,
  toCGBool,
  fromCGBool,
  Space,
  Search,
  newSpace,
  copySpace,
  newSearch,
  runSearch,
  IntTermInfo(..),
  getIntTermInfo,
  mapGOperator,
  c_gecode_int_dom,
  c_gecode_int_rel,
  c_gecode_int_rel_cf,
  c_gecode_int_rel_cs,
  c_gecode_int_value,
  c_gecode_int_mult,
  c_gecode_int_div,
  c_gecode_int_mod,
  c_gecode_int_abs,
  c_gecode_int_linear,
  c_gecode_int_alldiff,
  c_gecode_int_sorted,
  c_gecode_int_newvar,
  c_gecode_int_branch,
  c_gecode_bool_newvar
) where

#ifdef RGECODE

import Foreign
import Foreign.C
import Foreign.C.Types
import Foreign.ForeignPtr

import Control.CP.FD.Gecode.Common

#include "gecodeglue.h"

newtype CGOperator = CGOperator CInt
  deriving Storable
newtype CGIntVar = CGIntVar CInt
  deriving Storable
newtype CGBoolVar = CGBoolVar CInt
  deriving Storable
newtype CGBool = CGBool CInt
  deriving Storable
newtype CGVal = CGVal CInt
  deriving Storable

mapGOperator :: GOperator -> CGOperator
mapGOperator OEqual = CGOperator #const GOPERATOR_OEQUAL
mapGOperator ODiff  = CGOperator #const GOPERATOR_ODIFF
mapGOperator OLess  = CGOperator #const GOPERATOR_OLESS

newtype GecodeModel = GecodeModel (Ptr GecodeModel)
newtype GecodeSearch = GecodeSearch (Ptr GecodeSearch)

foreign import ccall unsafe  "gecode_model_create"   c_gecode_model_create    :: IO (Ptr GecodeModel)
foreign import ccall unsafe  "gecode_model_destroy"  c_gecode_model_destroy   :: Ptr GecodeModel -> IO ()
foreign import ccall unsafe "&gecode_model_destroy"  c_gecode_model_finalize  :: FunPtr (Ptr GecodeModel -> IO ())
foreign import ccall unsafe  "gecode_model_copy"     c_gecode_model_copy      :: Ptr GecodeModel -> IO (Ptr GecodeModel)
foreign import ccall unsafe  "gecode_model_fail"     c_gecode_model_fail      :: Ptr GecodeModel -> IO ()
foreign import ccall unsafe  "gecode_int_newvar"     c_gecode_int_newvar      :: Ptr GecodeModel -> IO CGIntVar
foreign import ccall unsafe  "gecode_int_rel"        c_gecode_int_rel         :: Ptr GecodeModel -> CGIntVar -> CGOperator -> CGIntVar -> IO CGBool
foreign import ccall unsafe  "gecode_int_rel_cf"     c_gecode_int_rel_cf      :: Ptr GecodeModel -> CGVal -> CGOperator -> CGIntVar -> IO CGBool
foreign import ccall unsafe  "gecode_int_rel_cs"     c_gecode_int_rel_cs      :: Ptr GecodeModel -> CGIntVar -> CGOperator -> CGVal -> IO CGBool
foreign import ccall unsafe  "gecode_int_value"      c_gecode_int_value       :: Ptr GecodeModel -> CGIntVar -> CGVal -> IO CGBool
foreign import ccall unsafe  "gecode_int_mult"       c_gecode_int_mult        :: Ptr GecodeModel -> CGIntVar -> CGIntVar -> CGIntVar -> IO CGBool
foreign import ccall unsafe  "gecode_int_div"        c_gecode_int_div         :: Ptr GecodeModel -> CGIntVar -> CGIntVar -> CGIntVar -> IO CGBool
foreign import ccall unsafe  "gecode_int_mod"        c_gecode_int_mod         :: Ptr GecodeModel -> CGIntVar -> CGIntVar -> CGIntVar -> IO CGBool
foreign import ccall unsafe  "gecode_int_abs"        c_gecode_int_abs         :: Ptr GecodeModel -> CGIntVar -> CGIntVar -> IO CGBool
foreign import ccall unsafe  "gecode_int_dom"        c_gecode_int_dom         :: Ptr GecodeModel -> CGIntVar -> CGVal -> CGVal -> IO CGBool
foreign import ccall unsafe  "gecode_int_linear"     c_gecode_int_linear      :: Ptr GecodeModel -> CInt -> Ptr CGIntVar -> Ptr CGVal -> CGOperator -> CGVal -> IO CGBool
foreign import ccall unsafe  "gecode_int_alldiff"    c_gecode_int_alldiff     :: Ptr GecodeModel -> CInt -> Ptr CGIntVar -> IO CGBool
foreign import ccall unsafe  "gecode_int_sorted"     c_gecode_int_sorted      :: Ptr GecodeModel -> CInt -> Ptr CGIntVar -> CGBool -> IO CGBool
foreign import ccall unsafe  "gecode_int_info"       c_gecode_int_info        :: Ptr GecodeModel -> CGIntVar -> Ptr CGVal -> Ptr CGVal -> Ptr CGVal -> Ptr CInt -> Ptr CGVal -> IO ()
foreign import ccall unsafe  "gecode_int_branch"     c_gecode_int_branch      :: Ptr GecodeModel -> CInt -> Ptr CGIntVar -> IO ()
foreign import ccall unsafe  "gecode_bool_newvar"    c_gecode_bool_newvar     :: Ptr GecodeModel -> IO CGBoolVar
foreign import ccall unsafe  "gecode_bool_branch"    c_gecode_bool_branch     :: Ptr GecodeModel -> CInt -> Ptr CGBoolVar -> IO ()

foreign import ccall unsafe  "gecode_search_create"  c_gecode_search_create   :: Ptr GecodeModel -> IO (Ptr GecodeSearch)
foreign import ccall unsafe "&gecode_search_destroy" c_gecode_search_finalize :: FunPtr (Ptr GecodeSearch -> IO ())
foreign import ccall unsafe  "gecode_search_destroy" c_gecode_search_destroy  :: Ptr GecodeSearch -> IO ()
foreign import ccall unsafe  "gecode_search_next"    c_gecode_search_next     :: Ptr GecodeSearch -> IO (Ptr GecodeModel)

---- accessor functions

toCGIntVar :: Integral a => a -> CGIntVar
toCGIntVar n = CGIntVar $ fromIntegral n

toCGBoolVar :: Integral a => a -> CGBoolVar
toCGBoolVar n = CGBoolVar $ fromIntegral n

toCGVal :: Integral a => a -> CGVal
toCGVal n = CGVal $ fromIntegral n

fromCGVal :: Num a => CGVal -> a
fromCGVal (CGVal x) = fromIntegral x

toCGBool :: Bool -> CGBool
toCGBool n = CGBool $ if n then 1 else 0

fromCGBool :: CGBool -> Bool
fromCGBool (CGBool x) = x /= 0

type Space = ForeignPtr GecodeModel
type Search = ForeignPtr GecodeSearch

newSpace :: IO Space
newSpace = do
  x <- c_gecode_model_create
  newForeignPtr c_gecode_model_finalize x

copySpace :: Space -> IO Space
copySpace s = withForeignPtr s $ \ptr -> do
  x <- c_gecode_model_copy ptr
  newForeignPtr c_gecode_model_finalize x

newSearch :: Space -> IO Search
newSearch s = withForeignPtr s $ \ptr -> do
  x <- c_gecode_search_create ptr
  newForeignPtr c_gecode_search_finalize x

runSearch :: Search -> IO (Maybe Space)
runSearch s = withForeignPtr s $ \ptr -> do
  x <- c_gecode_search_next ptr
  if (x == nullPtr)
    then return Nothing
    else do
      res <- newForeignPtr c_gecode_model_finalize x
      return $ Just res

data IntTermInfo = IntTermInfo { iti_low :: CInt, iti_high :: CInt, iti_med :: CInt, iti_size :: CInt, iti_val :: Maybe CInt }

getIntTermInfo :: Integral a => Space -> a -> IO IntTermInfo
getIntTermInfo s i = do
  alloca $ \pLow ->
    alloca $ \pHigh ->
      alloca $ \pMed ->
        alloca $ \pSize ->
          alloca $ \pVal -> do
            withForeignPtr s $ \ptr -> c_gecode_int_info ptr (toCGIntVar i) pLow pHigh pMed pSize pVal
            vLow <- peek pLow
            vHigh <- peek pHigh
            vMed <- peek pMed
            vSize <- peek pSize
            vVal <- peek pVal
            return $ IntTermInfo {
              iti_low = fromCGVal vLow,
              iti_high = fromCGVal vHigh,
              iti_med = fromCGVal vMed,
              iti_size = fromIntegral vSize,
              iti_val = if (vSize==1) then Just (fromCGVal vVal) else Nothing 
            }

#endif
