{-# LANGUAGE CPP #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TypeFamilies #-}

{-# CFILES glue/interface.cpp #-}

module Control.CP.FD.Gecode.Interface (
  CGIntVar, CGBoolVar, CGColVar,
  Space, Search,
  newSpace, copySpace,
  newSearch, runSearch,
  newInt, newIntAt,
  newBool,
  newColList, newColSize, newColCat, newColTake,
  getColSize,
  addConstraint,
  propagate,
  postBranchers,
  IntInfo(..), getIntInfo,
  getBoolInfo,
  modRefcount,
  setCost
) where

#ifdef RGECODE

import Data.Bits

import Foreign
import Foreign.C
import Foreign.C.Types
import Foreign.ForeignPtr

import Data.Expr.Data
-- import Expr.Util
import Control.CP.FD.Gecode.Common
import Data.Linear

#include "gecodeglue.h"

newtype CGOperator = CGOperator CInt
  deriving Storable
newtype CGIntVar = CGIntVar CInt
  deriving (Storable, Eq, Ord, Show)
newtype CGColVar = CGColVar CInt
  deriving (Storable, Eq, Ord, Show)
newtype CGBoolVar = CGBoolVar CInt
  deriving (Storable, Eq, Ord, Show)
newtype CGBool = CGBool CInt
  deriving Storable
newtype CGVal = CGVal CInt
  deriving (Storable, Num, Eq, Show)

mapGOperator :: GecodeOperator -> CGOperator
mapGOperator GOEqual = CGOperator #const GOPERATOR_OEQUAL
mapGOperator GODiff  = CGOperator #const GOPERATOR_ODIFF
mapGOperator GOLess  = CGOperator #const GOPERATOR_OLESS
mapGOperator GOLessEqual = CGOperator #const GOPERATOR_OLESSEQUAL

newtype GecodeModel = GecodeModel (Ptr GecodeModel)
newtype GecodeSearch = GecodeSearch (Ptr GecodeSearch)

foreign import ccall unsafe  "gecode_model_create"   c_gecode_model_create    :: IO (Ptr GecodeModel)
foreign import ccall unsafe  "gecode_model_destroy"  c_gecode_model_destroy   :: Ptr GecodeModel -> IO ()
foreign import ccall unsafe "&gecode_model_destroy"  c_gecode_model_finalize  :: FunPtr (Ptr GecodeModel -> IO ())
foreign import ccall unsafe  "gecode_model_copy"     c_gecode_model_copy      :: Ptr GecodeModel -> IO (Ptr GecodeModel)
foreign import ccall unsafe  "gecode_model_fail"     c_gecode_model_fail      :: Ptr GecodeModel -> IO ()
foreign import ccall unsafe  "gecode_model_propagate" c_gecode_model_propagate :: Ptr GecodeModel -> IO ()
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
foreign import ccall unsafe  "gecode_int_linear_ri"  c_gecode_int_linear_ri   :: Ptr GecodeModel -> CInt -> Ptr CGIntVar -> Ptr CGVal -> CGOperator -> CGVal -> CGBoolVar -> IO CGBool
foreign import ccall unsafe  "gecode_int_alldiff"    c_gecode_int_alldiff     :: Ptr GecodeModel -> CInt -> Ptr CGIntVar -> CGBool -> IO CGBool 
foreign import ccall unsafe  "gecode_int_sorted"     c_gecode_int_sorted      :: Ptr GecodeModel -> CInt -> Ptr CGIntVar -> CGOperator -> IO CGBool
foreign import ccall unsafe  "gecode_int_info"       c_gecode_int_info        :: Ptr GecodeModel -> CGIntVar -> Ptr CGVal -> IO ()
foreign import ccall unsafe  "gecode_int_get_size"   c_gecode_int_get_size    :: Ptr GecodeModel -> CGIntVar -> IO CInt
foreign import ccall unsafe  "gecode_int_get_value"  c_gecode_int_get_value   :: Ptr GecodeModel -> CGIntVar -> IO CInt
foreign import ccall unsafe  "gecode_int_get_median" c_gecode_int_get_median  :: Ptr GecodeModel -> CGIntVar -> IO CInt
foreign import ccall unsafe  "gecode_int_branch"     c_gecode_int_branch      :: Ptr GecodeModel -> CInt -> Ptr CGIntVar -> IO ()
foreign import ccall unsafe  "gecode_bool_newvar"    c_gecode_bool_newvar     :: Ptr GecodeModel -> IO CGBoolVar
foreign import ccall unsafe  "gecode_bool_value"     c_gecode_bool_value      :: Ptr GecodeModel -> CGBoolVar -> CGBool -> IO CGBool
foreign import ccall unsafe  "gecode_bool_equal"     c_gecode_bool_equal      :: Ptr GecodeModel -> CGBoolVar -> CGBoolVar -> IO CGBool
foreign import ccall unsafe  "gecode_bool_and"       c_gecode_bool_and        :: Ptr GecodeModel -> CGBoolVar -> CGBoolVar -> CGBoolVar -> IO CGBool
foreign import ccall unsafe  "gecode_bool_or"        c_gecode_bool_or         :: Ptr GecodeModel -> CGBoolVar -> CGBoolVar -> CGBoolVar -> IO CGBool
foreign import ccall unsafe  "gecode_bool_not"       c_gecode_bool_not        :: Ptr GecodeModel -> CGBoolVar -> CGBoolVar -> IO CGBool
foreign import ccall unsafe  "gecode_bool_equiv"     c_gecode_bool_equiv      :: Ptr GecodeModel -> CGBoolVar -> CGBoolVar -> CGBoolVar -> IO CGBool
foreign import ccall unsafe  "gecode_bool_branch"    c_gecode_bool_branch     :: Ptr GecodeModel -> CInt -> Ptr CGBoolVar -> IO ()
foreign import ccall unsafe  "gecode_bool_channel"   c_gecode_bool_channel    :: Ptr GecodeModel -> CGBoolVar -> CGIntVar -> IO CGBool
foreign import ccall unsafe  "gecode_bool_info"      c_gecode_bool_info       :: Ptr GecodeModel -> CGBoolVar -> Ptr CInt -> IO ()
foreign import ccall unsafe  "gecode_bool_all"       c_gecode_bool_all        :: Ptr GecodeModel -> CInt -> Ptr CGBoolVar -> CGBoolVar -> IO CGBool
foreign import ccall unsafe  "gecode_bool_any"       c_gecode_bool_any        :: Ptr GecodeModel -> CInt -> Ptr CGBoolVar -> CGBoolVar -> IO CGBool
foreign import ccall unsafe  "gecode_col_newsize"    c_gecode_col_newsize     :: Ptr GecodeModel -> CInt -> IO CGColVar
foreign import ccall unsafe  "gecode_col_newlist"    c_gecode_col_newlist     :: Ptr GecodeModel -> CInt -> Ptr CGIntVar -> IO CGColVar
foreign import ccall unsafe  "gecode_col_newcat"     c_gecode_col_newcat      :: Ptr GecodeModel -> CGColVar -> CGColVar -> IO CGColVar
foreign import ccall unsafe  "gecode_col_newtake"    c_gecode_col_newtake     :: Ptr GecodeModel -> CGColVar -> CInt -> CInt -> IO CGColVar
foreign import ccall unsafe  "gecode_col_equal"      c_gecode_col_equal       :: Ptr GecodeModel -> CGColVar -> CGColVar -> IO CGBool
foreign import ccall unsafe  "gecode_col_at"         c_gecode_col_at          :: Ptr GecodeModel -> CGColVar -> CGIntVar -> CGIntVar -> IO CGBool
foreign import ccall unsafe  "gecode_col_at_cv"      c_gecode_col_at_cv       :: Ptr GecodeModel -> CGColVar -> CGIntVar -> CInt -> IO CGBool
foreign import ccall unsafe  "gecode_col_at_lst"     c_gecode_col_at_lst      :: Ptr GecodeModel -> CInt -> Ptr CInt -> CGIntVar -> CGIntVar -> IO CGBool
foreign import ccall unsafe  "gecode_col_at_lst_cv"  c_gecode_col_at_lst_cv   :: Ptr GecodeModel -> CInt -> Ptr CInt -> CGIntVar -> CInt -> IO CGBool
foreign import ccall unsafe  "gecode_col_dom"        c_gecode_col_dom         :: Ptr GecodeModel -> CGIntVar -> CGColVar -> IO CGBool
foreign import ccall unsafe  "gecode_int_dom_list"   c_gecode_int_dom_list    :: Ptr GecodeModel -> CGIntVar -> CInt -> Ptr CInt -> CGBoolVar -> IO CGBool
foreign import ccall unsafe  "gecode_col_cat"        c_gecode_col_cat         :: Ptr GecodeModel -> CGColVar -> CGColVar -> CGColVar -> IO CGBool
foreign import ccall unsafe  "gecode_col_take"       c_gecode_col_take        :: Ptr GecodeModel -> CGColVar -> CInt -> CInt -> CGColVar -> IO CGBool
foreign import ccall unsafe  "gecode_col_alldiff"    c_gecode_col_alldiff     :: Ptr GecodeModel -> CGColVar -> CGBool -> IO CGBool
foreign import ccall unsafe  "gecode_col_sorted"     c_gecode_col_sorted      :: Ptr GecodeModel -> CGColVar -> CGOperator -> IO CGBool
foreign import ccall unsafe  "gecode_col_sum"        c_gecode_col_sum         :: Ptr GecodeModel -> CGColVar -> CGIntVar -> IO CGBool
foreign import ccall unsafe  "gecode_col_count"      c_gecode_col_count       :: Ptr GecodeModel -> CGColVar -> CInt -> CGIntVar -> CGOperator -> CInt -> CGIntVar -> IO CGBool
foreign import ccall unsafe  "gecode_col_count"      c_gecode_col_count_c1    :: Ptr GecodeModel -> CGColVar -> CInt -> CGVal -> CGOperator -> CInt -> CGIntVar -> IO CGBool
foreign import ccall unsafe  "gecode_col_count"      c_gecode_col_count_c2    :: Ptr GecodeModel -> CGColVar -> CInt -> CGIntVar -> CGOperator -> CInt -> CGVal -> IO CGBool
foreign import ccall unsafe  "gecode_col_count"      c_gecode_col_count_c12   :: Ptr GecodeModel -> CGColVar -> CInt -> CGVal -> CGOperator -> CInt -> CGVal -> IO CGBool
foreign import ccall unsafe  "gecode_col_sumc"       c_gecode_col_sumc        :: Ptr GecodeModel -> CGColVar -> CInt -> IO CGBool
foreign import ccall unsafe  "gecode_col_getsize"    c_gecode_col_getsize     :: Ptr GecodeModel -> CGColVar -> IO CInt
foreign import ccall unsafe  "gecode_col_branch"     c_gecode_col_branch      :: Ptr GecodeModel -> CInt -> Ptr CGColVar -> IO ()

foreign import ccall unsafe  "gecode_search_create_dfs" c_gecode_search_create_dfs :: Ptr GecodeModel -> IO (Ptr GecodeSearch)
foreign import ccall unsafe  "gecode_search_create_bab" c_gecode_search_create_bab :: Ptr GecodeModel -> IO (Ptr GecodeSearch)
foreign import ccall unsafe "&gecode_search_destroy" c_gecode_search_finalize :: FunPtr (Ptr GecodeSearch -> IO ())
foreign import ccall unsafe  "gecode_search_destroy" c_gecode_search_destroy  :: Ptr GecodeSearch -> IO ()
foreign import ccall unsafe  "gecode_search_next"    c_gecode_search_next     :: Ptr GecodeSearch -> IO (Ptr GecodeModel)

foreign import ccall unsafe  "gecode_space_modrefcount" c_gecode_space_modrefcount :: Ptr GecodeModel -> CInt -> IO CInt
foreign import ccall unsafe  "gecode_space_setcost"  c_gecode_space_setcost   :: Ptr GecodeModel -> CGIntVar -> IO ()

---- accessor functions

toCGIntVar :: Integral a => a -> CGIntVar
toCGIntVar n = CGIntVar $ fromIntegral n

toCGColVar :: Integral a => a -> CGColVar
toCGColVar n = CGColVar $ fromIntegral n

toCGColIntVar :: Integral a => CGColVar -> a -> CGIntVar
toCGColIntVar (CGColVar c) a = CGIntVar $ ((c+1) `shiftL` 16) + (fromIntegral a)

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



getIntTermSize :: Num a => Space -> Int -> IO a
getIntTermSize s i = do
  ret <- withForeignPtr s $ \ptr -> c_gecode_int_get_size ptr (toCGIntVar i)
  return $ fromIntegral ret

getIntTermValue :: Num a => Space -> Int -> IO a
getIntTermValue s i = do
  ret <- withForeignPtr s $ \ptr -> c_gecode_int_get_value ptr (toCGIntVar i)
  return $ fromIntegral ret

getIntTermMedian :: Num a => Space -> Int -> IO a
getIntTermMedian s i = do
  ret <- withForeignPtr s $ \ptr -> c_gecode_int_get_median ptr (toCGIntVar i)
  return $ fromIntegral ret


fnToBool :: IO CGBool -> IO Bool
fnToBool io = do
  v <- io
  return $ fromCGBool v

---------------------------------------------------- PUBLIC INTERFACE --------------------------------------------------------

type Space = ForeignPtr GecodeModel
type Search = ForeignPtr GecodeSearch

newSpace :: IO Space
newSpace = do
  x <- c_gecode_model_create
  newForeignPtr c_gecode_model_finalize x

modRefcount :: Space -> Int -> IO Int
modRefcount s m = withForeignPtr s $ \ptr -> c_gecode_space_modrefcount ptr (fromIntegral m) >>= (return . fromIntegral)

copySpace :: Space -> IO Space
copySpace s = withForeignPtr s $ \ptr -> do
  x <- c_gecode_model_copy ptr
  if (x == nullPtr)
     then return s
     else newForeignPtr c_gecode_model_finalize x

propagate :: Space -> IO ()
propagate s = do
  withForeignPtr s $ \ptr -> c_gecode_model_propagate ptr

newSearch :: Space -> Bool -> IO Search
newSearch s optim = withForeignPtr s $ \ptr -> do
  x <- (if optim then c_gecode_search_create_bab else c_gecode_search_create_dfs) ptr
  newForeignPtr c_gecode_search_finalize x

runSearch :: Search -> IO (Maybe Space)
runSearch s = withForeignPtr s $ \ptr -> do
  x <- c_gecode_search_next ptr
  if (x == nullPtr)
    then return Nothing
    else do
      res <- newForeignPtr c_gecode_model_finalize x
      return $ Just res

addLinearConstraint :: Ptr GecodeModel -> Linear CGIntVar GecodeIntConst -> GecodeOperator -> Maybe (CGBoolVar) -> IO CGBool
addLinearConstraint ptr l o reif = do
  let (Const c,ll) = linearToListEx l
      len = length ll
      vars = map fst ll
      coefs = map (\(_,Const x) -> toCGVal x) ll
  case (c,ll,o,reif) of
    (0,[],GOEqual,_) -> return $ toCGBool True
    (_,[(v,Const f)],GOEqual,Nothing) | (c `mod` f)==0 -> c_gecode_int_value ptr v (toCGVal $ -c `div` f)
    (0,[(v1,Const a),(v2,Const b)],_,Nothing) | a==(-b) && a>0 -> c_gecode_int_rel ptr v1 (mapGOperator o) v2
    (0,[(v1,Const a),(v2,Const b)],_,Nothing) | a==(-b) && b>0 -> c_gecode_int_rel ptr v2 (mapGOperator o) v1
    (_,_,_,Nothing) -> withArray vars $ \pvars -> withArray coefs $ \pcoefs -> c_gecode_int_linear ptr (fromIntegral len) pvars pcoefs (mapGOperator o) (toCGVal $ -c)
    (_,_,_,Just rv) -> withArray vars $ \pvars -> withArray coefs $ \pcoefs -> c_gecode_int_linear_ri ptr (fromIntegral len) pvars pcoefs (mapGOperator o) (toCGVal $ -c) rv


newInt :: Space -> IO CGIntVar
newInt s = withForeignPtr s $ \ptr -> c_gecode_int_newvar ptr

newIntAt :: Space -> CGColVar -> Int -> IO CGIntVar
newIntAt _ c p = return $ toCGColIntVar c (fromIntegral p)

newBool :: Space -> IO CGBoolVar
newBool s = withForeignPtr s $ \ptr -> c_gecode_bool_newvar ptr

newColList :: Space -> [CGIntVar] -> IO CGColVar
newColList s l = withForeignPtr s $ \ptr -> withArray l $ \lptr -> c_gecode_col_newlist ptr (fromIntegral $ length l) lptr

newColSize :: Space -> Int -> IO CGColVar
newColSize s l = withForeignPtr s $ \ptr -> c_gecode_col_newsize ptr $ fromIntegral l

newColTake :: Space -> CGColVar -> Int -> Int -> IO CGColVar
newColTake s c b l = withForeignPtr s $ \ptr -> c_gecode_col_newtake ptr c (fromIntegral b) (fromIntegral l)

newColCat :: Space -> CGColVar -> CGColVar -> IO CGColVar
newColCat s a b = withForeignPtr s $ \ptr -> c_gecode_col_newcat ptr a b

setCost :: Space -> CGIntVar -> IO ()
setCost s v = withForeignPtr s $ \ptr -> c_gecode_space_setcost ptr v

postBranchers :: Space -> ([CGBoolVar],[CGIntVar],[CGColVar]) -> IO ()
postBranchers s (b,i,c) = withForeignPtr s $ \ptr -> 
  withArray b $ \bp ->
    withArray i $ \ip ->
      withArray c $ \cp -> do
        if (length c > 0) then c_gecode_col_branch ptr (fromIntegral $ length c) cp else return ()
        if (length i > 0) then c_gecode_int_branch ptr (fromIntegral $ length i) ip else return ()
        if (length b > 0) then c_gecode_bool_branch ptr (fromIntegral $ length b) bp else return ()

buildListConst (Const l,f) = [case f (Const i) of { Const r -> r } | i <- [0..l-1]]

addConstraint :: (GecodeSolver s, GecodeIntVar s ~ CGIntVar, GecodeBoolVar s ~ CGBoolVar, GecodeColVar s ~ CGColVar) => Space -> GecodeConstraint s -> IO Bool
addConstraint s c = withForeignPtr s $ \ptr -> fnToBool $ case c of
  GCBoolVal var c -> case c of
    BoolConst bool -> c_gecode_bool_value ptr var (toCGBool bool)
    _ -> (error $ "Only non-paramterized boolean constants are supported by Gecode interface: ")
  GCBoolEqual b1 b2 -> c_gecode_bool_equal ptr b1 b2
  GCIntVal var c -> case c of
    Const val -> c_gecode_int_value ptr var (toCGVal val)
    _ -> (error $ "Only non-paramterized integer constants are supported by Gecode interface: ")
  GCSize var (Right (Const s)) -> do
    os <- c_gecode_col_getsize ptr var
    if (s /= toInteger os) 
      then return $ toCGBool False
      else return $ toCGBool True
  GCLinear l o -> addLinearConstraint ptr l o Nothing
  GCLinearReif l o ri -> addLinearConstraint ptr l o $ Just ri
  GCSum (Left c) (Left l) -> c_gecode_col_sum ptr c l
  GCSum (Left c) (Right l) -> c_gecode_col_sumc ptr c $ fromIntegral l
  GCColEqual c1 c2 -> c_gecode_col_equal ptr c1 c2
  GCMult vr v1 v2 -> c_gecode_int_mult ptr v1 v2 vr
  GCDiv vr v1 v2 -> c_gecode_int_div ptr v1 v2 vr
  GCMod vr v1 v2 -> c_gecode_int_mod ptr v1 v2 vr
  GCAbs vr v1 -> c_gecode_int_abs ptr v1 vr
  GCAt (Left vr) (Left vc) (Left vp) -> c_gecode_col_at ptr vc vp vr
  GCAt (Right (Const vv)) (Left vc) (Left vp) -> c_gecode_col_at_cv ptr vc vp $ fromIntegral vv
  GCAt (Left vr) (Right (Left vl)) (Left vp) -> withArray (map fromIntegral vl) $ \ll -> c_gecode_col_at_lst ptr (fromIntegral $ length vl) ll vp vr
  GCAt (Right (Const vv)) (Right (Left vl)) (Left vp) -> withArray (map fromIntegral vl) $ \ll -> c_gecode_col_at_lst_cv ptr (fromIntegral $ length vl) ll vp $ fromIntegral vv
  GCAt (Right (Const vv)) (Right (Right (vl@(Const nl,_)))) (Left vp) -> withArray (map fromIntegral $ buildListConst vl) $ \ll -> c_gecode_col_at_lst_cv ptr (fromIntegral nl) ll vp $ fromIntegral vv
  GCAt (Left vr) (Left vc) (Right (Const vp)) -> do
    ip <- newIntAt s vc $ fromInteger vp
    c_gecode_int_rel ptr ip (mapGOperator GOEqual) vr
  GCAt (Right (Const vr)) (Left vc) (Right (Const vp)) -> do
    ip <- newIntAt s vc $ fromInteger vp
    c_gecode_int_value ptr ip $ fromInteger vr
  GCDom vi (Left vc) Nothing -> c_gecode_col_dom ptr vi vc
  GCDom vi (Right (Left vl)) Nothing -> withArray (map fromIntegral vl) $ \ll -> c_gecode_int_dom_list ptr vi (fromIntegral $ length vl) ll (toCGBoolVar $ -1)
  GCDom vi (Right (Left vl)) (Just vb) -> withArray (map fromIntegral vl) $ \ll -> c_gecode_int_dom_list ptr vi (fromIntegral $ length vl) ll vb
  GCChannel vi vb -> c_gecode_bool_channel ptr vb vi
  GCCat vr v1 v2 -> c_gecode_col_cat ptr v1 v2 vr
  GCAnd [v1,v2] vr -> c_gecode_bool_and ptr v1 v2 vr
  GCOr [v1,v2] vr -> c_gecode_bool_or ptr v1 v2 vr
  GCAnd l r -> withArray l $ \ll -> c_gecode_bool_all ptr (fromIntegral $ length l) ll r
  GCOr l r -> withArray l $ \ll -> c_gecode_bool_any ptr (fromIntegral $ length l) ll r
  GCNot vr v -> c_gecode_bool_not ptr v vr
  GCEquiv vr v1 v2 -> c_gecode_bool_equiv ptr v1 v2 vr
  GCSorted (Left vc) o -> c_gecode_col_sorted ptr vc (mapGOperator o)
  GCAllDiff b (Left vc) -> c_gecode_col_alldiff ptr vc (toCGBool b)
  GCCount col (Left val) rel (Left cnt) -> c_gecode_col_count ptr col 0 val (mapGOperator rel) 0 cnt
  GCCount col (Right (Const val)) rel (Left cnt) -> c_gecode_col_count_c1 ptr col 1 (fromIntegral val) (mapGOperator rel) 0 cnt
  GCCount col (Left val) rel (Right (Const cnt)) -> c_gecode_col_count_c2 ptr col 0 val (mapGOperator rel) 1 (fromIntegral cnt)
  GCCount col (Right (Const val)) rel (Right (Const cnt)) -> c_gecode_col_count_c12 ptr col 0 (fromIntegral val) (mapGOperator rel) 1 (fromIntegral cnt)
  _ -> error $ "Unsupported constraint: " ++ (show c)

data IntInfo = IntInfo { iti_low :: !CInt, iti_high :: !CInt, iti_med :: !CInt, iti_size :: !CInt, iti_val :: !(Maybe CInt) }

getIntInfo :: Space -> CGIntVar -> IO (Maybe IntInfo)
getIntInfo s i =
  allocaBytes (5*sizeOf (undefined::CGVal)) $ \p -> do
    withForeignPtr s $ \ptr -> c_gecode_int_info ptr i p
    vSize <- peekElemOff p 3
    if vSize==0
      then return Nothing
      else do
        vLow <- peekElemOff p 0
        vHigh <- peekElemOff p 1
        vMed <- peekElemOff p 2
        vVal <- peekElemOff p 4
        return $ Just $ IntInfo {
          iti_low = fromCGVal vLow,
          iti_high = fromCGVal vHigh,
          iti_med = fromCGVal vMed,
          iti_size = fromCGVal vSize,
          iti_val = if (vSize==1) then Just (fromCGVal vVal) else Nothing 
        }

getBoolInfo :: Space -> CGBoolVar -> IO Int
getBoolInfo s i = do
  alloca $ \inf -> do 
    withForeignPtr s $ \ptr -> c_gecode_bool_info ptr i inf
    r <- peek inf
    return $ fromIntegral r

getColSize :: Space -> CGColVar -> IO GecodeIntConst
getColSize s v = do
  val <- withForeignPtr s $ \ptr -> c_gecode_col_getsize ptr v
  return $ toConst val


#endif
