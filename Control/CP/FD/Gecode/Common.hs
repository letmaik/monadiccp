{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.CP.FD.Gecode.Common (
  GecodeSolver(..),
  GecodeConstraint(..),
  GecodeOperator(..),
  GecodeBoolSpecType(..), GecodeIntSpecType(..), GecodeColSpecType(..),
  GecodeIntSpec(..), GecodeBoolSpec(..), GecodeColSpec(..),
  GecodeIBFn(..), GecodeIIFn(..), GecodeIIIFn(..), GecodeICIFn(..), GecodeCBFn(..), GecodeCIFn(..),
  GecodeIntConst, GecodeBoolConst, GecodeColConst, GecodeListConst,
  GecodeIntParam(..), GecodeBoolParam(..), GecodeColParam(..),
  GecodeLinear,
  GecodeColVarOrSection,
  GecodeWrappedSolver, liftGC, unliftGC,
  toConst, fromConst, toBoolConst, fromBoolConst,
  addMeta, procConstraint
) where

import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe (fromJust,isJust)
import qualified Data.Set as Set
import Data.Set(Set)

import Control.Mixin.Mixin

import Control.CP.Debug
import Control.CP.FD.FD
import Data.Expr.Data
import Data.Expr.Util
import Control.CP.FD.Graph
import Control.CP.FD.Model
import Control.CP.Solver
import Control.CP.EnumTerm
import Control.CP.SearchTree
import Data.Linear

newtype GecodeIntParam = GIParam Int
  deriving (Show,Eq,Ord)

newtype GecodeBoolParam = GBParam Int
  deriving (Show,Eq,Ord)

newtype GecodeColParam = GCParam Int
  deriving (Show,Eq,Ord)

type GecodeIntConst = Expr GecodeIntParam GecodeColParam GecodeBoolParam
type GecodeBoolConst = BoolExpr GecodeIntParam GecodeColParam GecodeBoolParam
type GecodeColConst = ColExpr GecodeIntParam GecodeColParam GecodeBoolParam
type GecodeListConst  = (GecodeIntConst,GecodeIntConst -> GecodeIntConst)

-- buildList :: GecodeListConst -> Maybe [Integer]
buildList (Const n,f) = fromAll [q $ f $ Const x | x <- [0..n-1]]
  where q (Const x) = Just x
        q _ = Nothing
buildList _ = Nothing

myFromJust _ (Just x) = x
myFromJust str _ = error $ "myFromJust: "++str

type GecodeIntVarOrConst s = Either (GecodeIntVar s) GecodeIntConst
type GecodeColVarOrConst s = Either (GecodeColVar s) (Either [Integer] GecodeListConst)
type GecodeColSection s = (GecodeColVar s, GecodeListConst)

buildSection :: GecodeSolver s => GecodeColSection s -> s (GecodeColVar s)
buildSection (col,list) = case buildList list of
  Nothing -> error "Cannot instantiate section"
  Just l -> do
    ll <- mapM (\p -> newInt_at col $ Const p) l
    newCol_list ll

type GecodeColVarOrSection s = Either (GecodeColVar s) (GecodeColSection s)

-- getIntVarOrConst :: (FDSolver s, FDIntSpecType s ~ GecodeIntSpecType, FDIntSpec s ~ GecodeIntSpec s) => FDSpecInfoInt s -> GecodeIntVarOrConst s
getIntVarOrConst s = case (fdspIntSpec s) (Just GISConst) of
  Just (GITConst v) -> Right v
  _ -> case (fdspIntSpec s) (Just GISVar) of
    Just (GITVar c) -> Left c
    _ -> error "Cannot convert to Var-or-Const Int"

-- getColVarOrConst :: (FDSolver s, FDColSpecType s ~ GecodeColSpecType, FDColSpec s ~ GecodeColSpec s) => FDSpecInfoCol s -> GecodeColVarOrConst s
getColVarOrConst s = case (fdspColSpec s) (Just GCSConst) of
  Just (GCTConst t@(ColList l)) -> Right $ case fromAll [ case x of { Const y -> Just y; _ -> Nothing } | x <- l] of
    Just x -> Left x
    _ -> Right (size t, \i -> t!i)
  Just (GCTConst t) -> Right $ Right (size t, \i -> t!i)
  _ -> case (fdspColSpec s) (Just GCSVar) of
    Just (GCTVar v)    -> Left v
    _ -> error "Cannot convert to Var-or-Const Col"

getAnyColSpec s = fdspColSpec s Nothing

transIntPar (EGPTParam i) = GIParam i
transBoolPar (EGPTBoolParam i) = GBParam i
transColPar (EGPTColParam i) = GCParam i
transRevIntPar (GIParam i) = EGPTParam i
transRevBoolPar (GBParam i) = EGPTBoolParam i
transRevColPar (GCParam i) = EGPTColParam i

transFns = (transIntPar,transColPar,transBoolPar,transRevIntPar,transRevColPar,transRevBoolPar)
transIFns = (transRevIntPar,transRevColPar,transRevBoolPar,transIntPar,transColPar,transBoolPar)
transPar = transform transFns
transIPar = transform transIFns
transParBool = boolTransform transFns
transIParBool = boolTransform transIFns
transParCol = colTransform transFns
transIParCol = colTransform transIFns

type GecodeLinear s = Linear (GecodeIntVar s) GecodeIntConst

data GecodeIntSpec s =
    GITConst GecodeIntConst
  | GITLinear (GecodeLinear s)
  | GITVar (GecodeIntVar s)

deriving instance (Eq (GecodeIntVar s), Show (GecodeIntVar s), Ord (GecodeIntVar s))=> Show (GecodeIntSpec s)

data GecodeIntSpecType =
    GISConst
  | GISLinear
  | GISVar
  deriving (Enum,Bounded,Eq,Ord,Show)

data GecodeBoolSpec s =
    GBTConst GecodeBoolConst
  | GBTCondConst GecodeBoolConst GecodeBoolConst -- x := GBTCondConst a b <=> if a then x==b
  | GBTVar (GecodeBoolVar s)

deriving instance (Eq (GecodeBoolVar s), Show (GecodeBoolVar s), Ord (GecodeBoolVar s))=> Show (GecodeBoolSpec s)

data GecodeBoolSpecType =
    GBSConst
  | GBSCondConst
  | GBSVar
  deriving (Enum,Bounded,Eq,Ord,Show)

data GecodeColSpec s =
    GCTConst (GecodeColConst)
  | GCTSection (GecodeColSection s)
  | GCTVar (GecodeColVar s)

deriving instance (Eq (GecodeColVar s), Show (GecodeColVar s), Ord (GecodeColVar s)) => Show (GecodeColSpec s)

data GecodeColSpecType =
    GCSConst
  | GCSSection
  | GCSVar
  deriving (Enum,Bounded,Eq,Ord,Show)

data GecodeOperator =
    GOEqual
  | GODiff
  | GOLess
  | GOLessEqual
  deriving (Eq,Ord,Show)

invOperator :: Bool -> a -> GecodeOperator -> a -> (a,GecodeOperator,a)
invOperator False a b c = (a,b,c)
invOperator True a GOEqual b = (a,GODiff,b)
invOperator True a GODiff b = (a,GOEqual,b)
invOperator True a GOLess b = (b,GOLessEqual,a)
invOperator True a GOLessEqual b = (b,GOLess,a)

data GecodeSolver s => GecodeConstraint s =
    GCBoolVal (GecodeBoolVar s) GecodeBoolConst
  | GCBoolEqual (GecodeBoolVar s) (GecodeBoolVar s)
  | GCIntVal (GecodeIntVar s) GecodeIntConst
  | GCLinear (GecodeLinear s) GecodeOperator
  | GCLinearReif (GecodeLinear s) GecodeOperator (GecodeBoolVar s)
  | GCColEqual (GecodeColVar s) (GecodeColVar s)
  | GCMult (GecodeIntVar s) (GecodeIntVar s) (GecodeIntVar s)
  | GCDiv (GecodeIntVar s) (GecodeIntVar s) (GecodeIntVar s)
  | GCMod (GecodeIntVar s) (GecodeIntVar s) (GecodeIntVar s)
  | GCAbs (GecodeIntVar s) (GecodeIntVar s)
  | GCAt (GecodeIntVarOrConst s) (GecodeColVarOrConst s) (GecodeIntVarOrConst s)
  | GCChannel (GecodeIntVar s) (GecodeBoolVar s)
  | GCSize (GecodeColVar s) (GecodeIntVarOrConst s)
  | GCCat (GecodeColVar s) (GecodeColVar s) (GecodeColVar s)
--  | GCTake (GecodeColVar s) (GecodeColVar s) GecodeIntConst GecodeIntConst
  | GCSlice (GecodeColVar s) (GecodeColSection s)
  | GCAnd [GecodeBoolVar s] (GecodeBoolVar s)
  | GCOr  [GecodeBoolVar s] (GecodeBoolVar s)
  | GCNot (GecodeBoolVar s) (GecodeBoolVar s)
  | GCEquiv (GecodeBoolVar s) (GecodeBoolVar s) (GecodeBoolVar s)
  | GCAllDiff Bool (GecodeColVarOrSection s) -- bool is true when domain consistency is to be used
  | GCSorted (GecodeColVarOrSection s) GecodeOperator
  | GCAll (GecodeIBFn s) (GecodeColVarOrSection s) (Maybe (GecodeBoolVar s))
  | GCAny (GecodeIBFn s) (GecodeColVarOrSection s) (Maybe (GecodeBoolVar s))
  | GCAllC (GecodeCBFn s) (GecodeListConst) (Maybe (GecodeBoolVar s))
  | GCAnyC (GecodeCBFn s) (GecodeListConst) (Maybe (GecodeBoolVar s))
  | GCMap (GecodeIIFn s) (GecodeColVarOrSection s) (GecodeColVar s)
  | GCFold (GecodeIIIFn s) (GecodeColVarOrSection s) (GecodeIntVar s) (GecodeIntVar s)  -- (prev -> arg -> ret -> ()) col init ret
  | GCFoldC (GecodeICIFn s) (GecodeIntConst) (GecodeIntVar s) (GecodeIntVar s)  -- (prev -> arg -> ret -> ()) num init ret
  | GCSum (GecodeColVarOrSection s) (GecodeIntVarOrConst s)
  | GCCount (GecodeColVar s) (GecodeIntVarOrConst s) GecodeOperator (GecodeIntVarOrConst s)
  | GCDom (GecodeIntVar s) (GecodeColVarOrConst s) (Maybe (GecodeBoolVar s))
  | GCCond (GecodeConstraint s) GecodeBoolConst

procHelperInt :: GecodeSolver s => GecodeIntConst -> WalkPhase -> s WalkResult
procHelperInt _ _ = return WalkDescend
procHelperCol :: GecodeSolver s => GecodeColConst -> WalkPhase -> s WalkResult
procHelperCol c (WalkPre) = do
  return WalkDescend
procHelperCol c (WalkSingle) = do
  col_regList c
  return WalkDescend
procHelperCol c (WalkPost) = do
  col_regList c
  return WalkDescend
procHelperBool :: GecodeSolver s => GecodeBoolConst -> WalkPhase -> s WalkResult
procHelperBool _ _ = return WalkDescend
procHelper :: GecodeSolver s => (GecodeIntConst -> WalkPhase -> s WalkResult,GecodeColConst -> WalkPhase -> s WalkResult,GecodeBoolConst -> WalkPhase -> s WalkResult)
procHelper = (procHelperInt, procHelperCol, procHelperBool)

class Procable x where
  gwalk :: GecodeSolver s => x -> s ()

instance Procable GecodeIntConst where
  gwalk x = walk x procHelper

instance Procable GecodeBoolConst where
  gwalk x = boolWalk x procHelper

instance Procable GecodeColConst where
  gwalk x = colWalk x procHelper

instance Procable a => Procable (Either b a) where
  gwalk (Left _) = return ()
  gwalk (Right c) = gwalk c

instance (Ord b, Num a, Procable a) => Procable (Linear b a) where
  gwalk l = mapM_ (\(_,v) -> gwalk v) $ linearToList l

instance Procable GecodeListConst where
  gwalk (n,f) = gwalk n >> gwalk (f $ ExprHole (-1))

instance Procable (a,GecodeListConst) where
  gwalk (_,c) = gwalk c

instance Procable a => Procable [a] where
  gwalk l = mapM_ gwalk l

procConstraint (GCBoolVal _ x) = gwalk x
procConstraint (GCIntVal _ x) = gwalk x
procConstraint (GCLinear l _) = gwalk l
procConstraint (GCLinearReif l _ _) = gwalk l
procConstraint (GCAt a b c) = gwalk [a,c] >> gwalk b
procConstraint (GCSize _ a) = gwalk a
procConstraint (GCAll _ s _) = gwalk s
procConstraint (GCAny _ s _) = gwalk s
procConstraint (GCAllC _ l _) = gwalk l
procConstraint (GCAnyC _ l _) = gwalk l
procConstraint (GCFoldC _ l _ _)= gwalk l
procConstraint (GCSum s l) = gwalk l >> gwalk s
procConstraint (GCCount _ a _ b) = gwalk [a,b]
procConstraint (GCDom _ a _) = gwalk a
procConstraint (GCCond c a) = gwalk a >> procConstraint c
procConstraint _ = return ()



unwrapConstraint :: (GecodeSolver s, GecodeConstraint s ~ Constraint s) => GecodeConstraint (GecodeWrappedSolver s) -> GecodeConstraint s
unwrapConstraint (GCBoolVal a b) = GCBoolVal a b
unwrapConstraint (GCBoolEqual a b) = GCBoolEqual a b
unwrapConstraint (GCIntVal a b) = GCIntVal a b
unwrapConstraint (GCLinear a b) = GCLinear a b
unwrapConstraint (GCLinearReif a b c) = GCLinearReif a b c
unwrapConstraint (GCColEqual a b) = GCColEqual a b
unwrapConstraint (GCMult a b c) = GCMult a b c
unwrapConstraint (GCDiv a b c) = GCDiv a b c
unwrapConstraint (GCMod a b c) = GCMod a b c
unwrapConstraint (GCAbs a b) = GCAbs a b
unwrapConstraint (GCAt a b c) = GCAt a b c
unwrapConstraint (GCChannel a b) = GCChannel a b
unwrapConstraint (GCSize a b) = GCSize a b
unwrapConstraint (GCCat a b c) = GCCat a b c
unwrapConstraint (GCSlice a b) = GCSlice a b
unwrapConstraint (GCAnd a b) = GCAnd a b
unwrapConstraint (GCOr a b) = GCOr a b
unwrapConstraint (GCNot a b) = GCNot a b
unwrapConstraint (GCEquiv a b c) = GCEquiv a b c
unwrapConstraint (GCAllDiff b c) = GCAllDiff b c
unwrapConstraint (GCSorted a b) = GCSorted a b
unwrapConstraint (GCAll f a b) = GCAll (uIBFn f) a b
unwrapConstraint (GCAny f a b) = GCAny (uIBFn f) a b
unwrapConstraint (GCAllC f a b) = GCAllC (uCBFn f) a b
unwrapConstraint (GCAnyC f a b) = GCAnyC (uCBFn f) a b
unwrapConstraint (GCMap f a b) = GCMap (uIIFn f) a b
unwrapConstraint (GCFold f a b c) = GCFold (uIIIFn f) a b c
unwrapConstraint (GCFoldC f a b c) = GCFoldC (uICIFn f) a b c
unwrapConstraint (GCCount a b c d) = GCCount a b c d
unwrapConstraint (GCSum a b) = GCSum a b
unwrapConstraint (GCDom a b c) = GCDom a b c
unwrapConstraint (GCCond a b) = GCCond (unwrapConstraint a) b

wrapConstraint :: (GecodeSolver s, GecodeConstraint s ~ Constraint s) => GecodeConstraint s -> GecodeConstraint (GecodeWrappedSolver s)
wrapConstraint (GCBoolVal a b) = GCBoolVal a b
wrapConstraint (GCBoolEqual a b) = GCBoolEqual a b
wrapConstraint (GCIntVal a b) = GCIntVal a b
wrapConstraint (GCLinear a b) = GCLinear a b
wrapConstraint (GCLinearReif a b c) = GCLinearReif a b c
wrapConstraint (GCColEqual a b) = GCColEqual a b
wrapConstraint (GCMult a b c) = GCMult a b c
wrapConstraint (GCDiv a b c) = GCDiv a b c
wrapConstraint (GCMod a b c) = GCMod a b c
wrapConstraint (GCAbs a b) = GCAbs a b
wrapConstraint (GCAt a b c) = GCAt a b c
wrapConstraint (GCChannel a b) = GCChannel a b
wrapConstraint (GCSize a b) = GCSize a b
wrapConstraint (GCCat a b c) = GCCat a b c
wrapConstraint (GCSlice a b) = GCSlice a b
wrapConstraint (GCAnd a b) = GCAnd a b
wrapConstraint (GCOr a b) = GCOr a b
wrapConstraint (GCNot a b) = GCNot a b
wrapConstraint (GCEquiv a b c) = GCEquiv a b c
wrapConstraint (GCAllDiff b c) = GCAllDiff b c
wrapConstraint (GCSorted a b) = GCSorted a b
wrapConstraint (GCAll f a b) = GCAll (wIBFn f) a b
wrapConstraint (GCAny f a b) = GCAny (wIBFn f) a b
wrapConstraint (GCAllC f a b) = GCAllC (wCBFn f) a b
wrapConstraint (GCAnyC f a b) = GCAnyC (wCBFn f) a b
wrapConstraint (GCMap f a b) = GCMap (wIIFn f) a b
wrapConstraint (GCFold f a b c) = GCFold (wIIIFn f) a b c
wrapConstraint (GCFoldC f a b c) = GCFoldC (wICIFn f) a b c
wrapConstraint (GCCount a b c d) = GCCount a b c d
wrapConstraint (GCSum a b) = GCSum a b
wrapConstraint (GCDom a b c) = GCDom a b c
wrapConstraint (GCCond a b) = GCCond (wrapConstraint a) b


idx c i = 
  if i<0 
    then error "idx: i<0"
    else if i>=length c
      then error "GC idx: i>=length c"
      else c!!i

newtype GecodeFn s   =  GecodeFn    (s ())
newtype GecodeIBFn s =  GecodeIBFn  (GecodeIntVar s -> GecodeBoolVar s -> s ())
newtype GecodeCBFn s =  GecodeCBFn  (GecodeIntConst -> GecodeBoolVar s -> s ())
newtype GecodeCIFn s =  GecodeCIFn  (GecodeIntConst -> GecodeIntVar s -> s ())
newtype GecodeIIFn s =  GecodeIIFn  (GecodeIntVar s -> GecodeIntVar s -> s ())
newtype GecodeIIIFn s = GecodeIIIFn (GecodeIntVar s -> GecodeIntVar s -> GecodeIntVar s -> s ())
newtype GecodeICIFn s = GecodeICIFn (GecodeIntVar s -> GecodeIntConst -> GecodeIntVar s -> s ())

uFn (GecodeFn f) = GecodeFn (case f of (GecodeWrappedSolver m) -> m)
uIBFn (GecodeIBFn f) = GecodeIBFn (\a b -> case f a b of (GecodeWrappedSolver m) -> m)
uCBFn (GecodeCBFn f) = GecodeCBFn (\a b -> case f a b of (GecodeWrappedSolver m) -> m)
uCIFn (GecodeCIFn f) = GecodeCIFn (\a b -> case f a b of (GecodeWrappedSolver m) -> m)
uIIFn (GecodeIIFn f) = GecodeIIFn (\a b -> case f a b of (GecodeWrappedSolver m) -> m)
uIIIFn (GecodeIIIFn f) = GecodeIIIFn (\a b c -> case f a b c of (GecodeWrappedSolver m) -> m)
uICIFn (GecodeICIFn f) = GecodeICIFn (\a b c -> case f a b c of (GecodeWrappedSolver m) -> m)
wFn (GecodeFn f) = GecodeFn (GecodeWrappedSolver f)
wIBFn (GecodeIBFn f) = GecodeIBFn (\a b -> GecodeWrappedSolver $ f a b)
wCBFn (GecodeCBFn f) = GecodeCBFn (\a b -> GecodeWrappedSolver $ f a b)
wCIFn (GecodeCIFn f) = GecodeCIFn (\a b -> GecodeWrappedSolver $ f a b)
wIIFn (GecodeIIFn f) = GecodeIIFn (\a b -> GecodeWrappedSolver $ f a b)
wIIIFn (GecodeIIIFn f) = GecodeIIIFn (\a b c -> GecodeWrappedSolver $ f a b c)
wICIFn (GecodeICIFn f) = GecodeICIFn (\a b c -> GecodeWrappedSolver $ f a b c)

instance Show (GecodeIntConst -> GecodeIntConst) where
  show _ = "GecodeIntConst -> GecodeIntConst"
instance Show (GecodeIBFn s) where
  show _ = "GecodeIBFn"
instance Show (GecodeCBFn s) where
  show _ = "GecodeCBFn"
instance Show (GecodeCIFn s) where
  show _ = "GecodeCIFn"
instance Show (GecodeIIFn s) where
  show _ = "GecodeIIFn"
instance Show (GecodeIIIFn s) where
  show _ = "GecodeIIIFn"
instance Show (GecodeICIFn s) where
  show _ = "GecodeICIFn"
instance GecodeSolver s => Show (GecodeFn s) where
  show _ = "GecodeFn"

extractFull :: (a -> Maybe b) -> [a] -> Maybe [b]
extractFull _ [] = Just []
extractFull f (a:b) = case f a of
  Nothing -> Nothing
  Just r -> case extractFull f b of
    Nothing -> Nothing
    Just rr -> Just (r:rr)

-- deriving instance (Eq (GecodeIntVar s), Eq (GecodeBoolVar s), Eq (GecodeColVar s), Ord (GecodeIntVar s), Ord (GecodeBoolVar s), Ord (GecodeColVar s)) => Eq (GecodeConstraint s)
-- deriving instance (Eq (GecodeIntVar s), Eq (GecodeBoolVar s), Eq (GecodeColVar s), Ord (GecodeIntVar s), Ord (GecodeBoolVar s), Ord (GecodeColVar s)) => Ord (GecodeConstraint s)
deriving instance (GecodeSolver s, Eq (GecodeIntVar s), Eq (GecodeBoolVar s), Eq (GecodeColVar s), Ord (GecodeIntVar s), Ord (GecodeBoolVar s), Ord (GecodeColVar s), Show (GecodeIntVar s), Show (GecodeBoolVar s), Show (GecodeColVar s)) => Show (GecodeConstraint s)

intSpecToLinear (GITConst c) = constToLinear c
intSpecToLinear (GITVar v) = termToLinear v
intSpecToLinear (GITLinear l) = l

retLinear l = case linearToConst l of
  Just x -> return $ Just (900,return $ GITConst x)
  Nothing -> case linearToTerm l of
    Just x -> return $ Just (800,return $ GITVar x)
    Nothing -> return $ Just (700,return $ GITLinear l)

class (Solver s, Term s (GecodeIntVar s), Term s (GecodeBoolVar s),
       Eq (GecodeIntVar s), Eq (GecodeBoolVar s), Eq (GecodeColVar s),
       Ord (GecodeIntVar s), Ord (GecodeBoolVar s), Ord (GecodeColVar s),
       Show (GecodeIntVar s), Show (GecodeBoolVar s), Show (GecodeColVar s)
      ) => GecodeSolver s where
  type GecodeIntVar s :: *
  type GecodeBoolVar s :: *
  type GecodeColVar s :: *
  newInt_at :: GecodeColVar s -> GecodeIntConst -> s (GecodeIntVar s)
  newInt_cond :: GecodeBoolConst -> GecodeIntVar s -> GecodeIntVar s -> s (GecodeIntVar s)
  newCol_list :: [GecodeIntVar s] -> s (GecodeColVar s)
  newCol_size :: GecodeIntConst -> s (GecodeColVar s)
--  newCol_take :: GecodeColVar s -> GecodeIntConst -> GecodeIntConst -> s (GecodeColVar s)
  newCol_cat ::  GecodeColVar s -> GecodeColVar s -> s (GecodeColVar s)
  -- newCol_cmap :: GecodeListConst -> GecodeCIFn s -> s (GecodeColVar s)
  splitIntDomain :: GecodeIntVar s -> s ([GecodeConstraint s],Bool)
  splitBoolDomain :: GecodeBoolVar s -> s ([GecodeConstraint s],Bool)
  col_getSize :: GecodeColVar s -> s GecodeIntConst
  col_regList :: GecodeColConst -> s ()
  col_regList _ = return ()

instance (GecodeSolver s, Constraint s ~ GecodeConstraint s) => GecodeSolver (GecodeWrappedSolver s) where
  type GecodeIntVar (GecodeWrappedSolver s) = GecodeIntVar s
  type GecodeBoolVar (GecodeWrappedSolver s) = GecodeBoolVar s
  type GecodeColVar (GecodeWrappedSolver s) = GecodeColVar s
  newInt_at c i = liftGC $ newInt_at c i
  newInt_cond c t f = liftGC $ newInt_cond c t f
  newCol_list = liftGC . newCol_list
  newCol_size = liftGC . newCol_size
--  newCol_take c p l = liftGC $ newCol_take c p l
  newCol_cat a b = liftGC $ newCol_cat a b
  -- newCol_cmap l f = liftGC $ newCol_cmap l f
  splitIntDomain a = liftGC $ (splitIntDomain a) >>= (\(l,b) -> return (map wrapConstraint l,b))
  splitBoolDomain a = liftGC $ (splitBoolDomain a) >>= (\(l,b) -> return (map wrapConstraint l,b))
  col_getSize = liftGC . col_getSize
  col_regList = liftGC . col_regList

instance (GecodeSolver s, Constraint s ~ GecodeConstraint s, EnumTerm s t) => EnumTerm (GecodeWrappedSolver s) t where
  type TermBaseType (GecodeWrappedSolver s) t = TermBaseType s t
  getDomainSize = liftGC . getDomainSize
  splitDomain a = liftGC $ splitDomain a >>= (\(x,t) -> return (map (map wrapConstraint) x,t))
  splitDomains a = liftGC $ splitDomains a >>= (\(x,t) -> return (map (map wrapConstraint) x, t))
  getValue = liftGC . getValue
  getDomain = liftGC . getDomain
  setValue a b = liftGC $ setValue a b >>= return . map wrapConstraint
  defaultOrder = liftGC . defaultOrder
  enumerator = case enumerator of
    Just x -> Just (mapTree liftGC . x)
    Nothing -> Nothing

forceDecompInt :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => FDSpecInfoInt (GecodeWrappedSolver s) -> FDInstance (GecodeWrappedSolver s) (GecodeIntVar s)
forceDecompInt info = 
  case fdspIntSpec info $ Just GISVar of
    Just (GITVar var) -> return var
    Nothing -> case fdspIntVal info of
      Just val -> do
        x <- liftFD $ newvar
        addFD $ GCIntVal x $ transPar val
        return x
      _ -> case fdspIntSpec info Nothing of
        Just (GITVar var) -> return var
        Just (GITConst v) -> do
          x <- liftFD $ newvar
          addFD $ GCIntVal x v
          return x
        Just (GITLinear l) -> do
          x <- liftFD $ newvar
          addFD $ GCLinear (l-(termToLinear x)) GOEqual
          return x
        _ -> error "unable to decompose int?"

getReifSpec info =
  case fdspBoolVal info of
    Just val -> GBTConst $ transParBool val
    _ -> case fdspBoolSpec info (Just GBSConst) of
      Just val -> val
      _ -> case fdspBoolSpec info (Just GBSCondConst) of
        Just val -> val
        _ -> case fdspBoolSpec info (Just GBSVar) of
          Just val -> val
          _ -> error "invalid reified specification"

forceLinearInt :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => FDSpecInfoInt (GecodeWrappedSolver s) -> FDInstance (GecodeWrappedSolver s) (GecodeLinear s)
forceLinearInt info =
  case fdspIntSpec info Nothing of
    Just x -> return $ intSpecToLinear x
    Nothing -> case fdspIntVal info of
      Just val -> return $ constToLinear $ transPar val
      _ -> error "unable to decompose to linear?"

forceConstInt :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => FDSpecInfoInt (GecodeWrappedSolver s) -> FDInstance (GecodeWrappedSolver s) (Maybe GecodeIntConst)
forceConstInt info = return $
  case fdspIntVal info of
    Just par -> Just $ transPar par
    Nothing -> case fdspIntSpec info $ Just GISConst of
      Just (GITConst v) -> Just v
      Nothing -> case fdspIntSpec info Nothing of
        Just (GITConst v) -> Just v
        Nothing -> Nothing

forceDecompBool :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => FDSpecInfoBool (GecodeWrappedSolver s) -> FDInstance (GecodeWrappedSolver s) (GecodeBoolVar s)
forceDecompBool info = 
  case fdspBoolSpec info $ Just GBSVar of
    Just (GBTVar var) -> return var
    Nothing -> case fdspBoolVal info of
      Just val -> do
        x <- liftFD $ newvar
        addFD $ GCBoolVal x $ transParBool val
        return x
      _ -> case fdspBoolSpec info Nothing of
        Just (GBTVar var) -> return var
        Just (GBTConst v) -> do
          x <- liftFD $ newvar
          addFD $ GCBoolVal x v
          return x
        x -> error $ "unable to decompose bool ("++(show x)++")?"

forceDecompCol :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => String -> FDSpecInfoCol (GecodeWrappedSolver s) -> FDInstance (GecodeWrappedSolver s) (GecodeColVar s)
forceDecompCol str info = 
  case fdspColSpec info $ Just GCSVar of
    Just (GCTVar var) -> return var
    Nothing -> case fdspColSpec info Nothing of
        Just (GCTVar var) -> return var
        x -> error $ "unable to decompose col ("++(show x)++"): "++str++"?"

newtype (GecodeSolver s, Constraint s ~ GecodeConstraint s) => GecodeWrappedSolver s a = GecodeWrappedSolver (s a)
newtype (GecodeSolver s, Constraint s ~ GecodeConstraint s) => GecodeWrappedLabel s = GecodeWrappedLabel (Label s)

instance (GecodeSolver s, Constraint s ~ GecodeConstraint s) => Monad (GecodeWrappedSolver s) where
  {-# INLINE (>>=) #-}
  return = GecodeWrappedSolver . return
  (GecodeWrappedSolver m) >>= f  = GecodeWrappedSolver (m >>= (\x -> case f x of GecodeWrappedSolver r -> r))

instance (GecodeSolver s, Constraint s ~ GecodeConstraint s) => Solver (GecodeWrappedSolver s) where
  type Constraint (GecodeWrappedSolver s) = GecodeConstraint (GecodeWrappedSolver s)
  type Label (GecodeWrappedSolver s) = GecodeWrappedLabel s
  add x = do
    GecodeWrappedSolver $ procConstraint x
    GecodeWrappedSolver $ add $ unwrapConstraint x
  run (GecodeWrappedSolver w) = run w
  mark = liftGC (mark >>= \x -> return $ GecodeWrappedLabel x)
  markn n = liftGC (markn n >>= \x -> return $ GecodeWrappedLabel x)
  goto (GecodeWrappedLabel l) = liftGC (goto l)

instance (GecodeSolver s, Term s t, Constraint s ~ GecodeConstraint s) => Term (GecodeWrappedSolver s) t where
  newvar = GecodeWrappedSolver newvar
  type Help (GecodeWrappedSolver s) t = ()
  help _ _ = ()

liftGC :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => s a -> (GecodeWrappedSolver s) a
liftGC = GecodeWrappedSolver

unliftGC :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => (GecodeWrappedSolver s) a -> s a
unliftGC (GecodeWrappedSolver s) = s

instance (GecodeSolver s, GecodeConstraint s ~ Constraint s) => FDSolver (GecodeWrappedSolver s) where
  type FDIntTerm (GecodeWrappedSolver s)      = GecodeIntVar s
  type FDBoolTerm (GecodeWrappedSolver s)     = GecodeBoolVar s
  type FDIntSpec (GecodeWrappedSolver s)      = GecodeIntSpec s
  type FDBoolSpec (GecodeWrappedSolver s)     = GecodeBoolSpec s
  type FDColSpec (GecodeWrappedSolver s)      = GecodeColSpec s
  type FDIntSpecType (GecodeWrappedSolver s)  = GecodeIntSpecType
  type FDBoolSpecType (GecodeWrappedSolver s) = GecodeBoolSpecType
  type FDColSpecType (GecodeWrappedSolver s)  = GecodeColSpecType

  fdIntSpec_const  x = (GISConst, return $ GITConst $ transPar x)
  fdBoolSpec_const x = (GBSConst, return $ GBTConst $ transParBool x)
  fdColSpec_const  x = (GCSConst, return $ GCTConst $ transParCol x)
  fdIntSpec_term   x = (GISVar, return $ GITVar x)
  fdBoolSpec_term  x = (GBSVar, return $ GBTVar x)
  fdColSpec_list lst = (GCSVar, do
    let vir = map (\(GITVar v) -> v) lst
    gcv <- newCol_list vir
    return $ GCTVar gcv)
  fdColSpec_size len = (GCSVar, do
    gcv <- newCol_size $ transPar len
    return $ GCTVar gcv)
  fdIntVarSpec (GITVar v) = return $ Just v
  fdIntVarSpec _ = return Nothing
  fdBoolVarSpec (GBTVar v) = return $ Just v
  fdBoolVarSpec _ = return Nothing
  
  fdEqualBool (GBTConst a) (GBTConst b) = if a/=b then setFailed else return ()
  fdEqualBool (GBTConst a) (GBTVar b) = addFD $ GCBoolVal b a
  fdEqualBool (GBTVar b) (GBTConst a) = addFD $ GCBoolVal b a
  fdEqualBool (GBTVar a) (GBTVar b) = addFD $ GCBoolEqual a b
  -- TODO: incompatibiliteiten opmerken, en combinatie met var wordt nieuwe constraint op die var
  fdEqualBool (GBTCondConst _ _) _ = return ()
  fdEqualBool _ (GBTCondConst _ _) = return ()
  fdEqualInt (GITConst a) (GITConst b) = if a/=b then setFailed else return ()
  fdEqualInt (GITVar a) (GITConst b) = addFD $ GCIntVal a b
  fdEqualInt (GITConst b) (GITVar a) = addFD $ GCIntVal a b
  fdEqualInt a b = addFD $ GCLinear ((intSpecToLinear a)-(intSpecToLinear b)) GOEqual
  fdEqualCol (GCTVar a) (GCTVar b) = addFD $ GCColEqual a b

  fdTypeReqBool = return typeReqBool
  fdTypeReqInt = return typeReqInt
  fdTypeReqCol = return typeReqCol
  fdTypeVarInt = return $ Set.singleton GISVar
  fdTypeVarBool = return $ Set.singleton GBSVar

  fdSpecify = specify
  fdProcess = process
  fdSplitIntDomain = splitIntDomain
  fdSplitBoolDomain = splitBoolDomain
  fdConstrainIntTerm t v = return $ GCLinear ((termToLinear t)-(constToLinear $ Const v)) GOLess

  fdColInspect (GCTVar c) = do
    s <- col_getSize c
    case s of
      Const ss -> mapM (newInt_at c . toConst) [0..ss-1]
      _ -> error "Inspecting collection of indeterminate size"

-- typeReqBool :: EGEdge -> [(EGVarId,FDBoolSpecTypeSet s)]
-- typeReqBool (EGEdge { egeLinks = EGTypeData { boolData = l }}) = defBoolTypes l
-- typeReqInt _ = []
-- typeReqCol _ = []

linearTypes x = (x,Set.fromList [GISVar,GISConst,GISLinear])
onlyVarType x = (x,Set.singleton GISVar)
onlyConstType x = (x,Set.singleton GISConst)
defTypes x = (x,Set.fromList [GISVar,GISConst])
onlyBoolVarType x = (x,Set.singleton GBSVar)
defBoolTypes x = (x,Set.fromList [GBSVar,GBSConst])
reifBoolTypes x = (x,Set.fromList [GBSVar,GBSConst,GBSCondConst])
allColTypes x = (x,Set.fromList [GCSVar,GCSConst,GCSSection])
allCColTypes x = (x,Set.fromList [GCSVar,GCSConst,GCSSection])
defColTypes x = (x,Set.fromList [GCSVar])
sectionColTypes x = (x,Set.fromList [GCSSection,GCSVar])
constColTypes x = (x,Set.fromList [GCSConst,GCSVar])
constCColTypes x = (x,Set.fromList [GCSConst,GCSVar])
onlyConstColType x = (x,Set.fromList [GCSConst])

typeReqInt (EGEdge { egeCons = EGIntValue _, egeLinks = EGTypeData { intData = l }}) = map linearTypes l
typeReqInt (EGEdge { egeCons = EGPlus, egeLinks = EGTypeData { intData = l }}) = map linearTypes l
typeReqInt (EGEdge { egeCons = EGMinus, egeLinks = EGTypeData { intData = l }}) = map linearTypes l
typeReqInt (EGEdge { egeCons = EGMult, egeLinks = EGTypeData { intData = l }}) = map linearTypes l
typeReqInt (EGEdge { egeCons = EGEqual, egeLinks = EGTypeData { intData = l }}) = map linearTypes l
typeReqInt (EGEdge { egeCons = EGLess _, egeLinks = EGTypeData { intData = l }}) = map linearTypes l
typeReqInt (EGEdge { egeCons = EGDiff, egeLinks = EGTypeData { intData = l }}) = map linearTypes l
-- typeReqInt (EGEdge { egeCons = EGDiv, egeLinks = EGTypeData { intData = l }}) = map onlyVarType l
-- typeReqInt (EGEdge { egeCons = EGMod, egeLinks = EGTypeData { intData = l }}) = map onlyVarType l
-- typeReqInt (EGEdge { egeCons = EGAbs, egeLinks = EGTypeData { intData = l }}) = map onlyVarType l
-- typeReqInt (EGEdge { egeCons = EGChannel, egeLinks = EGTypeData { intData = l }}) = map onlyVarType l
-- typeReqInt (EGEdge { egeCons = EGAllC _ _ _, egeLinks = EGTypeData { intData=a:b:l }}) = (onlyConstType a):(onlyConstType b):(map defTypes l)
typeReqInt (EGEdge { egeLinks = EGTypeData { intData = l }}) = map defTypes l

typeReqBool (EGEdge { egeCons = EGEqual, egeLinks = EGTypeData { boolData = l }}) = map reifBoolTypes l
typeReqBool (EGEdge { egeCons = EGDiff, egeLinks = EGTypeData { boolData = l }}) = map reifBoolTypes l
typeReqBool (EGEdge { egeCons = EGLess _, egeLinks = EGTypeData { boolData = l }}) = map reifBoolTypes l
typeReqBool (EGEdge { egeCons = EGCondEqual, egeLinks = EGTypeData { boolData = [c,a,b] }}) = (reifBoolTypes a):(map defBoolTypes [b,c])
typeReqBool (EGEdge { egeCons = EGAll _ _ _, egeLinks = EGTypeData { boolData = (r:l) }}) = (reifBoolTypes r):(map defBoolTypes l)
typeReqBool (EGEdge { egeCons = EGAny _ _ _, egeLinks = EGTypeData { boolData = (r:l) }}) = (reifBoolTypes r):(map defBoolTypes l)
typeReqBool (EGEdge { egeLinks = EGTypeData { boolData = l }}) = map defBoolTypes l

typeReqCol (EGEdge { egeCons = EGSize, egeLinks = EGTypeData { colData=[c] }}) = [allColTypes c]
typeReqCol (EGEdge { egeCons = EGRange, egeLinks = EGTypeData { colData=[c] }}) = [constCColTypes c]
typeReqCol (EGEdge { egeCons = EGAt, egeLinks = EGTypeData { colData=[c] }}) = [allCColTypes c]
typeReqCol (EGEdge { egeCons = EGCat, egeLinks = EGTypeData { colData=[r,a,b] }}) = [allCColTypes r, allCColTypes a, allCColTypes b]
typeReqCol (EGEdge { egeCons = EGSlice _ _, egeLinks = EGTypeData { colData=[r,c] }}) = [allCColTypes r, allCColTypes c]
typeReqCol (EGEdge { egeCons = EGAllDiff _, egeLinks = EGTypeData { colData=[c] }}) = [sectionColTypes c]
typeReqCol (EGEdge { egeCons = EGSorted _, egeLinks = EGTypeData { colData=[c] }}) = [sectionColTypes c]
typeReqCol (EGEdge { egeLinks = EGTypeData { colData = l }}) = map allColTypes l

fromAll :: [Maybe a] -> Maybe [a]
fromAll [] = Just []
fromAll (Nothing:_) = Nothing
fromAll ((Just x):r) = case fromAll r of
  Nothing -> Nothing
  Just l -> Just $ x:l

fromAllConst :: (GecodeSolver s) => [GecodeIntSpec s] -> Maybe [GecodeIntConst]
fromAllConst [] = Just []
fromAllConst ((GITConst a):r) = case fromAllConst r of
  Nothing -> Nothing
  Just l -> Just $ a:l
fromAllConst _ = Nothing

-- doIntSpec :: (GecodeSolver s, Constraint s ~ GecodeConstraint s, GecodeIntSpec s ~ FDIntSpec s) => FDSpecInfoInt (GecodeWrappedSolver s) -> [FDIntSpecType (GecodeWrappedSolver s)] -> FDInstance (GecodeWrappedSolver s) (Maybe (FDIntSpec s))
doIntSpec _ [] = return Nothing
doIntSpec x (a:b) = do
  case fdspIntSpec x (Just a) of
    Nothing -> doIntSpec x b
    Just (r) -> return $ Just r

-- doBoolSpec :: (GecodeSolver s, Constraint s ~ GecodeConstraint s, GecodeBoolSpec s ~ FDBoolSpec s) => FDSpecInfoBool (GecodeWrappedSolver s) -> [FDBoolSpecType (GecodeWrappedSolver s)] -> FDInstance (GecodeWrappedSolver s) (Maybe (FDBoolSpec s))
doBoolSpec _ [] = return Nothing
doBoolSpec x (a:b) = do
  case fdspBoolSpec x (Just a) of
    Nothing -> doBoolSpec x b
    Just (r) -> return $ Just r

-- doColSpec :: (GecodeSolver s, Constraint s ~ GecodeConstraint s, GecodeColSpec s ~ FDColSpec s) => FDSpecInfoCol (GecodeWrappedSolver s) -> [FDColSpecType (GecodeWrappedSolver s)] -> FDInstance (GecodeWrappedSolver s) (Maybe (FDColSpec s))
doColSpec _ [] = return Nothing
doColSpec x (a:b) = do
  case (fdspColSpec x) (Just a) of
    Nothing -> doColSpec x b
    Just (r) -> return $ Just r

getVarOrSection c = do
  r <- doColSpec c [GCSVar,GCSSection]
  case r of
    Nothing -> return Nothing
    Just (GCTVar v) -> return $ Just $ Left v
    Just (GCTSection x) -> return $ Just $ Right x
    _ -> return Nothing

linearSpec :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => ([GecodeLinear (GecodeWrappedSolver s)] -> Maybe (GecodeLinear (GecodeWrappedSolver s))) -> [EGVarId] -> FDInstance (GecodeWrappedSolver s) (Maybe (GecodeLinear (GecodeWrappedSolver s)))
linearSpec f l = do
  lst <- mapM getIntSpec l
  debug ("linearSpec: lst="++(show lst)) $ return ()
  case fromAll lst of
    Nothing -> return Nothing
    Just rl -> return $ f $ map intSpecToLinear rl

constSpec :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => ([GecodeIntConst] -> Maybe GecodeIntConst) -> [EGVarId] -> FDInstance (GecodeWrappedSolver s) (Maybe GecodeIntConst)
constSpec f l = do
  lst <- mapM specConst l
  case fromAll lst of
    Nothing -> return Nothing
    Just spec -> return $ f spec

constMaybeSpec :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => ([GecodeIntConst] -> Maybe GecodeIntConst) -> [EGVarId] -> EGVarId -> SpecFnRes (GecodeWrappedSolver s)
constMaybeSpec f l r =
  let m = constSpec f l
      in ([],[(900,r,True,do 
        x <- m
        return $ case x of
          Nothing -> SpecResNone
          Just k -> SpecResSpec (GISConst,return $ (GITConst k,Just $ transIPar k))
      )],[])

constFullSpec :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => ([GecodeIntConst] -> GecodeIntConst) -> [EGVarId] -> EGVarId -> SpecFnRes (GecodeWrappedSolver s)
constFullSpec f l r = constMaybeSpec (\i -> Just $ f i) l r

linearMaybeSpec :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => ([GecodeLinear (GecodeWrappedSolver s)] -> Maybe (GecodeLinear (GecodeWrappedSolver s))) -> [EGVarId] -> EGVarId -> SpecFnRes (GecodeWrappedSolver s)
linearMaybeSpec f l r = 
  let m = linearSpec f l
      in ([],
           [
             (1000,r,True,do 
               x <- m
               return $ case x of
                 Nothing -> SpecResNone
                 Just k -> case linearToConst k of
                   Nothing -> SpecResNone
                   Just c -> SpecResSpec (GISConst,return $ (GITConst c,Just $ transIPar c))
             ),
             (800,r,True,do 
               x <- m
               return $ case x of
                 Nothing -> SpecResNone
                 Just k -> case linearToTerm k of
                   Nothing -> SpecResNone
                   Just c -> SpecResSpec (GISVar,return $ (GITVar c, Nothing))
             ),
             (700,r,True,do 
               x <- m
               return $ case x of
                 Nothing -> SpecResNone
                 Just k -> SpecResSpec (GISLinear, return $ (GITLinear k, Nothing))
             )
           ],
         [])

linearFullSpec :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => ([GecodeLinear (GecodeWrappedSolver s)] -> (GecodeLinear (GecodeWrappedSolver s))) -> [EGVarId] -> EGVarId -> SpecFnRes (GecodeWrappedSolver s)
linearFullSpec f l r = linearMaybeSpec (\i -> Just $ f i) l r

specConst l = do
  r <- getIntSpec_ l $ Set.singleton GISConst
  case r of
    Just (_,GITConst x) -> return $ Just x
    _ -> do
      rr <- getIntVal l
      return $ case rr of
        Nothing -> Nothing
        Just x -> Just $ transPar x

specBoolConst l = do
  r <- getBoolVal l
  case r of
    Just x -> return $ Just $ transParBool x
    _ -> do
      rr <- getBoolSpec_ l $ Set.singleton GBSConst
      return $ case rr of
        Just (_,GBTConst x) -> Just x
        Nothing -> Nothing
        _ -> error $ "Weird result in specBoolConst: " ++ (show rr)

specColConst l = do
  r <- getColVal l
  case r of
    Just x -> return $ Just $ transParCol x
    _ -> do
      rr <- getColSpec_ l $ Set.singleton GCSConst
      return $ case rr of
        Just (_,GCTConst x) -> Just x
        Nothing -> Nothing
        _ -> error $ "Weird result in specColConst: " ++ (show rr)

specMap :: (GecodeSolver s, GecodeConstraint s ~ Constraint s) => EGModel -> ([FDSpecInfoBool (GecodeWrappedSolver s)],[FDSpecInfoInt (GecodeWrappedSolver s)],[FDSpecInfoCol (GecodeWrappedSolver s)]) -> FDInstance (GecodeWrappedSolver s) (Maybe (GecodeIntConst -> GecodeIntConst))
specMap model (lb,li,lc) = do
  let mf cv = 
        do
          let cc = transIPar cv
              ev2 = myFromJust "specMap1" $ Map.lookup (-2) $ intData $ externMap model
              ev1 = myFromJust "specMap2" $ Map.lookup (-1) $ intData $ externMap model
              sm2 = addEdge (EGIntValue cc) (EGTypeData { boolData=[], intData=[ev2], colData=[] }) model
              fb n = Just $ idx lb n
              fi (-1) = Nothing
              fi (-2) = Nothing
              fi n = Just $ idx li n
              fc n = Just $ idx lc n
          (rb,ri,rc) <- specSubModelEx sm2 (fb,fi,fc)
          return $ case Map.lookup ev1 ri of
            Nothing -> Nothing
            Just x -> case fdspIntVal x of
              Nothing -> Nothing
              Just v -> Just v
  level <- getLevel
  let gt = GIParam (-(1000+level))
  rm <- mf (Term gt)
  case rm of
    Nothing -> return Nothing
    Just rr -> do
      let tf :: GecodeIntConst -> GecodeIntConst
          tf rs =
             let mmi g | g==gt = rs
                 mmi x = Term x
                 in transformEx (mmi,ColTerm,BoolTerm,Term,ColTerm,BoolTerm) $ transPar rr
      return $ Just tf

specify :: (GecodeSolver s, GecodeConstraint s ~ Constraint s) => Mixin (SpecFn (GecodeWrappedSolver s))
specify sup t edge = case edge of
  EGEdge { egeCons = EGPlus, egeLinks = EGTypeData { intData=[r,a,b] } } -> linearFullSpec (\[x,y] -> x+y) [a,b] r
  EGEdge { egeCons = EGMinus, egeLinks = EGTypeData { intData=[r,a,b] } } -> linearFullSpec (\[x,y] -> x-y) [a,b] r
  EGEdge { egeCons = EGDiv, egeLinks = EGTypeData { intData=[r,a,b] } } -> constFullSpec (\[x,y] -> x `div` y) [a,b] r
  EGEdge { egeCons = EGMod, egeLinks = EGTypeData { intData=[r,a,b] } } -> constFullSpec (\[x,y] -> x `mod` y) [a,b] r
  EGEdge { egeCons = EGMult, egeLinks = EGTypeData { intData=[r,a,b] } } -> linearMaybeSpec (\[x,y] -> linearMultiply x y) [a,b] r
  EGEdge { egeCons = EGSize, egeLinks = EGTypeData { intData=[s], colData=[c] } } ->
    ([],[(900,s,True,do
      cc <- getColSpec c
      case cc of
        (Just (GCTConst c)) -> return $ SpecResSpec (GISConst, return $ (GITConst $ size c, Just $ transIPar $ size c))
        (Just (GCTSection (_,(lll,_)))) -> return $ SpecResSpec (GISConst, return $ (GITConst lll, Just $ transIPar lll))
        (Just (GCTVar v)) -> return $ SpecResSpec (GISConst, col_getSize v >>= (\x -> return $ (GITConst x, Just $ transIPar x)))
        _ -> return SpecResNone
    )],(\(_,_,x) -> x) (sup edge))
  EGEdge { egeCons = EGMap sm (nb,ni,nc), egeLinks = EGTypeData {  intData=il, boolData=bl, colData=(r:c:cl)  } } -> 
    ([],[],[(250,r,False,do
      cc <- getColSpec c
      case cc of
        (Just (GCTSection (_,(lll,_)))) -> return $ SpecResSpec (GCSVar, newCol_size lll >>= (\x -> return (GCTVar x, Nothing)))
        (Just (GCTVar v)) -> return $ SpecResSpec (GCSVar, col_getSize v >>= newCol_size >>= (\x -> return (GCTVar x, Nothing)))
        _ -> return SpecResNone
    ),(925,c,True,do
      cc <- getColSpec c
      blm <- mapM (\x -> (getBoolSpec_ x (Set.singleton GBSConst) >> getFullBoolSpec x)) bl
      ilm <- mapM (\x -> (getIntSpec_ x (Set.singleton GISConst) >> getFullIntSpec x)) il
      clm <- mapM (\x -> (getColSpec_ x (Set.singleton GCSConst) >> getFullColSpec x)) cl
      ff <- specMap sm (blm,ilm,clm)
      case (cc,ff) of
        (Just (GCTConst c), Just fff) -> return $ SpecResSpec (GCSConst, return (GCTConst $ xmap fff c, Just $ transIParCol $ xmap fff c))
        _ -> return SpecResNone
    ),(225,c,False,do
      cc <- getColSpec r
      case cc of
        (Just (GCTConst c)) -> return $ SpecResSpec (GCSVar, newCol_size (size c) >>= (\x -> return (GCTVar x, Nothing)))
        (Just (GCTSection (_,(lll,_)))) -> return $ SpecResSpec (GCSVar, newCol_size lll >>= (\x -> return (GCTVar x, Nothing)))
        (Just (GCTVar v)) -> return $ SpecResSpec (GCSVar, col_getSize v >>= newCol_size >>= (\x -> return (GCTVar x, Nothing)))
        _ -> return SpecResNone
    )])
  EGEdge { egeCons = EGRange, egeLinks = EGTypeData { intData=[l,h], colData=[r] } } -> 
    ([],[],[(560,r,True,do
      -- ll <- getIntVal l
      -- hh <- getIntVal h
      ll <- specConst l
      hh <- specConst h
      case (ll,hh) of
        (Just (Const lll), Just (Const hhh)) -> return $ SpecResSpec (GCSConst, return $ (GCTConst (ColList [Const x | x <- [lll..hhh]]), Just $ ColList [Const x | x <- [lll..hhh]]))
        _ -> return SpecResNone
    ),(550,r,True,do
      -- ll <- getIntVal l
      -- hh <- getIntVal h
      ll <- specConst l
      hh <- specConst h
      case (ll,hh) of
        (Just lll, Just hhh) -> return $ SpecResSpec (GCSConst, return $ (GCTConst (lll @.. hhh), Just $ transIParCol (lll @.. hhh)))
        _ -> return SpecResNone
    )])
  EGEdge { egeCons = EGCondInt, egeLinks = EGTypeData { boolData=[c], intData=[r,t,f] } } ->
    ([],[(999,r,True,do
      cc <- specBoolConst c
      tt <- specConst t
      ff <- specConst f
      case (cc,tt,ff) of
        (Just ccc,Just ttt,Just fff) -> return $ SpecResSpec (GISConst, return $ (GITConst $ simplify $ Cond ccc ttt fff, Just $ transIPar $ simplify $ Cond ccc ttt fff))
        _ -> return SpecResNone
    ),(990,r,True,do
      cc <- specBoolConst c
      tt <- getIntSpec_ t (Set.singleton GISVar)
      ff <- getIntSpec_ f (Set.singleton GISVar)
      case (cc,tt,ff) of
        (Just ccc,Just (_,GITVar ttt),Just (_,GITVar fff)) -> return $ SpecResSpec (GISVar, newInt_cond ccc ttt fff >>= (\x -> return (GITVar x, Nothing)))
--        (ccc,ttt,fff) -> error $ "Unable to use newInt_cond: ccc="++(show ccc)++" ttt="++(show ttt)++" fff="++(show fff)++""
        _ -> return SpecResNone
    )],[])
  EGEdge { egeCons = EGAt, egeLinks = EGTypeData { intData=[r,p], colData=[c] }} ->
    ([],[(600,r,True,do
      pp <- specConst p
      cc <- getColSpec c
      case (pp,cc) of
        (Just ppp, Just (GCTVar ccc)) -> debug ("EGAt spec: newInt_at gctvar c="++(show ccc)++" p="++(show ppp)++" r="++(show r)) $ return $ SpecResSpec (GISVar, newInt_at ccc ppp >>= (\x -> return (GITVar x,Nothing)))
        _ -> return SpecResNone
    ),(850,r,True,do
      pp <- specConst p
      cc <- getColSpec c
      case (pp,cc) of
        (Just ppp, Just (GCTSection (ccc,(lll,fff)))) -> debug ("EGAt spec: newInt_at gctsection c="++(show ccc)++" p="++(show ppp)) $ return $ SpecResSpec (GISVar, newInt_at ccc (fff $ ppp) >>= (\x -> return (GITVar x, Nothing)))
        _ -> return SpecResNone
    ),(900,r,True,do
      cc <- specColConst c
      pp <- specConst p
      case (pp,cc) of
        (Just ppp, Just c) -> return $ SpecResSpec (GISConst, return $ (GITConst $ (c!ppp),Just $ transIPar (c!ppp)))
        _ -> return SpecResNone
    )],[])
  EGEdge { egeCons = EGSlice sm (nb,ni,nc), egeLinks = EGTypeData { intData=(n:il), boolData=bl, colData=(r:c:cl) } } -> ([],[],
    [(500,r,True,do
      blm <- mapM (\x -> (getBoolSpec_ x (Set.singleton GBSConst) >> getFullBoolSpec x)) bl
      ilm <- mapM (\x -> (getIntSpec_ x (Set.singleton GISConst) >> getFullIntSpec x)) il
      clm <- mapM (\x -> (getColSpec_ x (Set.singleton GCSConst) >> getFullColSpec x)) cl
      fff <- specMap sm (blm,ilm,clm)
      cc <- getColSpec c
      nn <- specConst n
      case (cc,nn,fff) of
        (Just (GCTVar ccc),Just nnn,Just ff) -> return $ SpecResSpec (GCSSection, return (GCTSection (ccc,(nnn,ff)),Nothing))
        _ -> debug ("not absorbing egslice/gctvar: cc="++(show cc)++" nn="++(show nn)++" fff="++(show $ isJust $ fff)) $ return SpecResNone
    ),(550,r,True,do
      blm <- mapM (\x -> (getBoolSpec_ x (Set.singleton GBSConst) >> getFullBoolSpec x)) bl
      ilm <- mapM (\x -> (getIntSpec_ x (Set.singleton GISConst) >> getFullIntSpec x)) il
      clm <- mapM (\x -> (getColSpec_ x (Set.singleton GCSConst) >> getFullColSpec x)) cl
      ff <- specMap sm (blm,ilm,clm)
      cc <- getColSpec c
      nn <- specConst n
      case (cc,nn,ff) of
        (Just (GCTSection (ccc,(_,fff))),Just nnn,Just rf) -> return $ SpecResSpec (GCSSection, return (GCTSection (ccc,(nnn,fff . rf)),Nothing))
        _ -> debug ("not absorbing egslice/gctsection: cc="++(show cc)++" nn="++(show nn)++" ff="++(show $ isJust $ ff)) $ return SpecResNone
    ),(575,r,True,do
      blm <- mapM (\x -> (getBoolSpec_ x (Set.singleton GBSConst) >> getFullBoolSpec x)) bl
      ilm <- mapM (\x -> (getIntSpec_ x (Set.singleton GISConst) >> getFullIntSpec x)) il
      clm <- mapM (\x -> (getColSpec_ x (Set.singleton GCSConst) >> getFullColSpec x)) cl
      ff <- specMap sm (blm,ilm,clm)
      cc <- specColConst c
      nn <- specConst n
      case (cc,nn,ff) of
        (Just ll,Just nnn,Just rf) -> return $ SpecResSpec (GCSConst, return (GCTConst $ slice ll (xmap rf ((Const 0) @.. (nnn-1))), Just $ transIParCol $ slice ll (xmap rf ((Const 0) @.. (nnn-1)))))
        _ -> debug ("not absorbing egslice/const: cc="++(show cc)++" nn="++(show nn)++" ff="++(show $ isJust $ ff)) $ return SpecResNone
    ),(580,r,True,do
      blm <- mapM (\x -> (getBoolSpec_ x (Set.singleton GBSConst) >> getFullBoolSpec x)) bl
      ilm <- mapM (\x -> (getIntSpec_ x (Set.singleton GISConst) >> getFullIntSpec x)) il
      clm <- mapM (\x -> (getColSpec_ x (Set.singleton GCSConst) >> getFullColSpec x)) cl
      fff <- specMap sm (blm,ilm,clm)
      cc <- specColConst c
      nn <- specConst n
      case (cc,nn,fff) of
        (Just l,Just (Const p),Just ff) -> do
          let nl = map (ff . Const) [0..p-1]
          case (extractFull (\x -> case x of { Const i -> Just $ fromInteger i; _ -> Nothing }) nl) of
            Just ll -> return $ SpecResSpec (GCSConst, return (GCTConst $ ColList [l ! Const i | i <- ll], Just $ transIParCol $ ColList [l ! Const i | i <- ll]))
            _ -> return SpecResNone
        _ -> debug ("not absorbing egslice/list: cc="++(show cc)++" nn="++(show nn)++" fff="++(show $ isJust $ fff)) $ return SpecResNone
    )])
  EGEdge { egeCons = EGCat, egeLinks = EGTypeData { colData=[r,a,b] }} -> ([],[],
    [(500,r,True,do
      aa <- getColSpec a
      bb <- getColSpec b
      case (aa,bb) of
        (Just (GCTVar aaa),Just (GCTVar bbb)) -> return $ SpecResSpec (GCSVar, newCol_cat aaa bbb >>= (\x -> return (GCTVar x, Nothing)))
        _ -> return SpecResNone
    ),(550,r,True,do
      aa <- getColSpec a
      bb <- getColSpec b
      case (aa,bb) of
        (Just (GCTConst a),Just (GCTConst b)) -> return $ SpecResSpec (GCSConst, return (GCTConst (a @++ b),Just $ transIParCol $ a @++ b))
        _ -> return SpecResNone
    )])
  EGEdge { egeCons = EGCondEqual, egeLinks = EGTypeData { boolData=[c,r,v] }} -> (
    [(999,r,True,do
      dc <- specBoolConst c
      dv <- specBoolConst v
      case (dc,dv) of
        (Just cc,Just vv) -> return $ SpecResSpec (GBSCondConst, return (GBTCondConst cc vv, Nothing))
--        _ -> do
--          cc <- getBoolSpec c
--          vv <- getBoolSpec v
--          error $ "Unable to use conditional equality (c="++(show cc)++", v="++(show vv)++")"
        _ -> return SpecResNone
    )],[],[])
  EGEdge { egeCons = EGChannel, egeLinks = EGTypeData { intData=[i], boolData=[b] }} -> (
    [],[(1000,i,True,do
      db <- specBoolConst b
      case (db) of
        (Just bb) -> return $ SpecResSpec (GISConst, return (GITConst $ channel bb, Just $ transIPar $ channel bb))
        _ -> return SpecResNone
    )],[])
  EGEdge { egeCons = EGEquiv, egeLinks = EGTypeData { boolData=[r,a,b] }} -> (
    [(1000,r,True,do
      da <- specBoolConst a
      db <- specBoolConst b
      case (da,db) of
        (Just aa,Just bb) -> return $ SpecResSpec (GBSConst, return (GBTConst $ boolSimplify $ BoolEqual aa bb, Just $ transIParBool $ boolSimplify $ BoolEqual aa bb))
        _ -> return SpecResNone
    ),(2000,a,True,do
      dr <- specBoolConst r
      case dr of
        (Just (BoolConst True)) -> return $ debug ("bool unification: "++(show a)++","++(show b)) $ SpecResUnify b
        _ -> return $ debug ("no bool unification: "++(show a)++","++(show b)) $ SpecResNone
    ),(2000,b,True,do
      dr <- specBoolConst r
      case dr of
        (Just (BoolConst True)) -> return $ debug ("bool unification: "++(show a)++","++(show b)) $ SpecResUnify a
        _ -> return $ debug ("no bool unification: "++(show a)++","++(show b)) $ SpecResNone
    )],[],[])
  EGEdge { egeCons = EGEqual, egeLinks = EGTypeData { boolData=[r], intData=[a,b] }} -> (
    [(1000,r,True,do
      da <- specConst a
      db <- specConst b
      case (da,db) of
        (Just aa,Just bb) -> return $ SpecResSpec (GBSConst, return (GBTConst $ boolSimplify $ Rel aa EREqual bb, Just $ transIParBool $ boolSimplify $ Rel aa EREqual bb))
        _ -> return SpecResNone
    )],[(2000,a,True,do
      dr <- specBoolConst r
      case dr of
        (Just (BoolConst True)) -> return $ debug ("int unification: "++(show a)++","++(show b)) $ SpecResUnify b
        _ -> return $ debug ("no int unification: "++(show a)++","++(show b)++" r="++(show dr)) $ SpecResNone
    ),(2000,b,True,do
      dr <- specBoolConst r
      case dr of
        (Just (BoolConst True)) -> return $ debug ("int unification: "++(show a)++","++(show b)) $ SpecResUnify a
        _ -> return $ debug ("no int unification: "++(show a)++","++(show b)++" r="++(show dr)) $ SpecResNone
    )],[])
  EGEdge { egeCons = EGDiff, egeLinks = EGTypeData { boolData=[r], intData=[a,b] }} -> (
    [(1000,r,True,do
      da <- specConst a
      db <- specConst b
      case (da,db) of
        (Just aa,Just bb) -> return $ SpecResSpec (GBSConst, return (GBTConst $ boolSimplify $ Rel aa ERDiff bb, Just $ transIParBool $ boolSimplify $ Rel aa ERDiff bb))
        _ -> return SpecResNone
    )],[],[])
  EGEdge { egeCons = EGAnd, egeLinks = EGTypeData { boolData=[r,a,b] }} -> (
    [(1000,r,True,do
      da <- specBoolConst a
      db <- specBoolConst b
      case (da,db) of
        (Just aa,Just bb) -> return $ SpecResSpec (GBSConst, return (GBTConst $ boolSimplify $ BoolAnd aa bb, Just $ transIParBool $ boolSimplify $ BoolAnd aa bb))
        _ -> return SpecResNone
    )],[],[])
  EGEdge { egeCons = EGOr, egeLinks = EGTypeData { boolData=[r,a,b] }} -> (
    [(1000,r,True,do
      da <- specBoolConst a
      db <- specBoolConst b
      case (da,db) of
        (Just aa,Just bb) -> return $ SpecResSpec (GBSConst, return (GBTConst $ boolSimplify $ BoolOr aa bb, Just $ transIParBool $ boolSimplify $ BoolOr aa bb))
        _ -> return SpecResNone
    )],[],[])
  EGEdge { egeCons = EGLess strict, egeLinks = EGTypeData { boolData=[r], intData=[a,b] }} -> (
    [(1000,r,True,do
      da <- specConst a
      db <- specConst b
      case (da,db) of
        (Just aa,Just bb) -> return $ SpecResSpec (GBSConst, return (GBTConst $ (if strict then (@<) else (@<=)) aa bb, Just $ transIParBool $ (if strict then (@<) else (@<=)) aa bb))
        _ -> return SpecResNone
    )],[],[])
  EGEdge { egeCons = EGNot, egeLinks = EGTypeData { boolData=[r,a] }} -> (
    [(1000,r,True,do
      da <- specBoolConst a
      case (da) of
        (Just aa) -> return $ SpecResSpec (GBSConst, return (GBTConst $ boolSimplify $ BoolNot aa, Just $ transIParBool $ boolSimplify $ BoolNot aa))
        _ -> return SpecResNone
    )],[],[])
  _ -> sup edge

removeFrom [] fn = Nothing
removeFrom (a:b) fn = case fn a of
  True -> Just b
  False -> case removeFrom b fn of
    Nothing -> Nothing
    Just r -> Just (a:r)

reduceCountFold :: (GecodeSolver s, GecodeConstraint s ~ Constraint s) => (EGConstraintSpec -> FDSpecInfo (GecodeWrappedSolver s) -> FDInstance (GecodeWrappedSolver s) ()) -> (EGConstraintSpec,FDSpecInfo (GecodeWrappedSolver s)) -> FDInstance (GecodeWrappedSolver s) Bool
reduceCountFold t (EGFold model (nb,ni,nc),(vb,res:init:vi,col:vc)) = do
  let mp = externMap model
      vold = myFromJust "reduceCountFold1" $ Map.lookup (-2) $ intData mp
      vnew = myFromJust "reduceCountFold2"  $ Map.lookup (-1) $ intData mp
      varg = myFromJust "reduceCountFold3"  $ Map.lookup (-3) $ intData mp
  case 
    (do
      (plusid,plusedge) <- findEdge model EGIntType vnew (==0) (==EGPlus)
      let plusargs = map ((intData $ egeLinks plusedge)!!) [1,2]
      [channelres] <- debug ("reduceCountFold: plusid="++(show plusid)) $ removeFrom plusargs (==vold)
      (channelid,channeledge) <- debug ("reduceCountFold: channelres="++(show channelres)++" externMap="++(show $ mp)) $ findEdge model EGIntType channelres (==0) (==EGChannel)
      (equalid,equaledge) <- debug ("reduceCountFold: channelid="++(show channelid)) $ findEdge model EGBoolType (head $ boolData $ egeLinks channeledge) (==0) (==EGEqual)
      let equalargs = map ((intData $ egeLinks equaledge)!!) [0,1]
      [valnode] <- debug ("reduceCountFold: equalargs="++(show equalargs)) $ removeFrom equalargs (==varg)
      case findEdge model EGIntType valnode (==0) (\x -> case x of { EGIntValue _ -> True; _ -> False }) of
        Just (valid,valedge) -> return ([plusid,channelid,equalid,valid],case (egeCons valedge) of { EGIntValue val -> Right val })
        _ -> case findEdge model EGIntType valnode (==0) (\x -> case x of { EGIntExtern _ -> True; _ -> False}) of
          Just (extid,extedge) -> do
            return ([plusid,channelid,equalid,extid],case (egeCons extedge) of { EGIntExtern ext -> Left $ ext })
          _ -> fail ""
    ) of
      Nothing -> return False
      Just (edges,val) -> do
        dcs <- doColSpec col [GCSVar]
        case dcs of
          Just (GCTVar dcol) -> do
            dval <- case val of
              Right x -> return $ Right $ transPar x
              Left x -> return $ getIntVarOrConst (vi!!x)
            case (fdspIntVal res,fdspIntVal init) of
              (Just rrr, Just iii) -> do
                addFD $ GCCount dcol dval GOEqual (Right $ transPar $ rrr-iii)
                return True
              _ -> do
                dsum <- liftFD $ newvar
                sum <- liftFD $ specInfoIntTerm dsum
                t EGPlus ([],[res,init,sum],[])
                addFD $ GCCount dcol dval GOEqual (Left dsum)
                return True
          _ -> return False
reduceCountFold _ _ = return False

reduceMultCountFold :: (GecodeSolver s, GecodeConstraint s ~ Constraint s) => (EGConstraintSpec -> FDSpecInfo (GecodeWrappedSolver s) -> FDInstance (GecodeWrappedSolver s) ()) -> (EGConstraintSpec,FDSpecInfo (GecodeWrappedSolver s)) -> FDInstance (GecodeWrappedSolver s) Bool
reduceMultCountFold t (EGFold model (nb,ni,nc),(vb,res:init:vi,col:vc)) = do
  let mp = externMap model
      vold = myFromJust "reduceMultCountFold1" $ Map.lookup (-2) $ intData mp
      vnew = myFromJust "reduceMultCountFold2"  $ Map.lookup (-1) $ intData mp
      varg = myFromJust "reduceMultCountFold3"  $ Map.lookup (-3) $ intData mp
  case 
    (do
      (plusid,plusedge) <- findEdge model EGIntType vnew (==0) (==EGPlus)
      let plusargs = map ((intData $ egeLinks plusedge)!!) [1,2]
      [channelres] <- debug ("reduceMultCountFold: plusid="++(show plusid)) $ removeFrom plusargs (==vold)
      (channelid,channeledge) <- debug ("reduceMultCountFold: channelres="++(show channelres)++" externMap="++(show $ mp)) $ findEdge model EGIntType channelres (==0) (==EGChannel)
      (equalid,equaledge) <- debug ("reduceMultCountFold: channelid="++(show channelid)) $ findEdge model EGBoolType (head $ boolData $ egeLinks channeledge) (==0) (==EGEqual)
      let equalargs = map ((intData $ egeLinks equaledge)!!) [0,1]
      [valnode] <- debug ("reduceMultCountFold: equalargs="++(show equalargs)) $ removeFrom equalargs (==varg)
      case findEdge model EGIntType valnode (==0) (\x -> case x of { EGIntValue _ -> True; _ -> False }) of
        Just (valid,valedge) -> return ([plusid,channelid,equalid,valid],case (egeCons valedge) of { EGIntValue val -> Right val })
        _ -> case findEdge model EGIntType valnode (==0) (\x -> case x of { EGIntExtern _ -> True; _ -> False}) of
          Just (extid,extedge) -> do
            return ([plusid,channelid,equalid,extid],case (egeCons extedge) of { EGIntExtern ext -> Left $ ext })
          _ -> fail ""
    ) of
      Nothing -> return False
      Just (edges,val) -> do
        dcs <- doColSpec col [GCSVar]
        case dcs of
          Just (GCTVar dcol) -> do
            dval <- case val of
              Right x -> return $ Right $ transPar x
              Left x -> return $ getIntVarOrConst (vi!!x)
            case (fdspIntVal res,fdspIntVal init) of
              (Just rrr, Just iii) -> do
                addFD $ GCCount dcol dval GOEqual (Right $ transPar $ rrr-iii)
                return True
              _ -> do
                dsum <- liftFD $ newvar
                sum <- liftFD $ specInfoIntTerm dsum
                t EGPlus ([],[res,init,sum],[])
                addFD $ GCCount dcol dval GOEqual (Left dsum)
                return True
          _ -> return False
reduceMultCountFold _ _ = return False

reduceSumFoldToMap :: (GecodeSolver s, GecodeConstraint s ~ Constraint s) => (EGConstraintSpec -> FDSpecInfo (GecodeWrappedSolver s) -> FDInstance (GecodeWrappedSolver s) ()) -> (EGConstraintSpec,FDSpecInfo (GecodeWrappedSolver s)) -> FDInstance (GecodeWrappedSolver s) Bool
reduceSumFoldToMap t (EGFold model (nb,ni,nc),(vb,res:init:vi,col:vc)) = do
  let mp = externMap model
      vold = myFromJust "reduceSumFoldToMap1" $ Map.lookup (-2) $ intData mp
      vnew = myFromJust "reduceSumFoldToMap2" $ Map.lookup (-1) $ intData mp
      varg = myFromJust "reduceSumFoldToMap3" $ Map.lookup (-3) $ intData mp
      ncold = length $ myFromJust "reduceSumFoldToMap4" $ Map.lookup vold $ intData $ egmLinks model
      ncnew = length $ myFromJust "reduceSumFoldToMap5" $ Map.lookup vnew $ intData $ egmLinks model
      ncarg = length $ myFromJust "reduceSumFoldToMap6" $ Map.lookup varg $ intData $ egmLinks model
      filt (EGEdge { egeCons = EGPlus, egeLinks = EGTypeData { intData = [o,i1,i2] } }) | (vnew==o && vold==i1) = Just i2
      filt (EGEdge { egeCons = EGPlus, egeLinks = EGTypeData { intData = [o,i1,i2] } }) | (vnew==o && vold==i2) = Just i1
      filt _ = Nothing
      in if (ncnew==2 && ncold==2)
           then do
             let (nm1,nn) = filterModel model filt
             case nn of
               [ii] -> do
                 let filt2 (EGEdge { egeCons = EGIntExtern _ }) = Just ()
                     filt2 _ = Nothing
                     (nm2,_) = filterModel nm1 filt2
                     nm3 = addEdge (EGIntExtern (-1)) (EGTypeData { intData=[ii],colData=[],boolData=[] }) nm2
                     nm4 = addEdge (EGIntExtern (-2)) (EGTypeData { intData=[varg],colData=[],boolData=[] }) nm3
                     nm5 = delNode EGIntType vold nm4
                     nm6 = delNode EGIntType vnew nm5
                     nm = nm5
                 dcs <- doColSpec col [GCSVar]
                 case dcs of
                   Just (GCTVar dcol) -> do
                     size <- liftFD $ col_getSize dcol
                     dmap <- liftFD $ newCol_size size
                     let cmap = FDSpecInfoCol { fdspColSpec = const $ Just (GCTVar dmap), fdspColVal = Nothing, fdspColVar = Nothing, fdspColTypes = Set.singleton GCSVar }
                     t (EGMap nm (nb,ni,nc)) (vb,vi,cmap:col:vc)
                     dsum <- liftFD $ newvar
                     sum <- liftFD $ specInfoIntTerm dsum
                     addFD $ GCSum (Left dmap) (Left dsum)
                     t EGPlus ([],[res,init,sum],[])
                     return True
                   _ -> return False
               _ -> return False
           else return False
reduceSumFoldToMap _ _ = return False

extractSumFold :: (GecodeSolver s, GecodeConstraint s ~ Constraint s) => EGModel -> FDSpecInfoCol (GecodeWrappedSolver s) -> FDSpecInfoInt (GecodeWrappedSolver s) -> FDSpecInfoInt (GecodeWrappedSolver s) -> (EGConstraintSpec -> FDSpecInfo (GecodeWrappedSolver s) -> FDInstance (GecodeWrappedSolver s) ()) -> FDInstance (GecodeWrappedSolver s) EGModel
extractSumFold model col init res t = do
  let mp = externMap model
      vold = myFromJust "extractSumFold1" $ Map.lookup (-2) $ intData mp
      vnew = myFromJust "extractSumFold2" $ Map.lookup (-1) $ intData mp
      varg = myFromJust "extractSumFold3" $ Map.lookup (-3) $ intData mp
      ncold = length $ myFromJust "extractSumFold4" $ Map.lookup vold $ intData $ egmLinks model
      ncnew = length $ myFromJust "extractSumFold5" $ Map.lookup vnew $ intData $ egmLinks model
      ncarg = length $ myFromJust "extractSumFold6" $ Map.lookup varg $ intData $ egmLinks model
      filt (EGEdge { egeCons = EGPlus, egeLinks = EGTypeData { intData = [o,i1,i2] } }) | (vnew==o && ((vold==i1 && varg==i2) || (vold==i2 && varg==i1))) = Just ()
      filt _ = Nothing
      in if (ncnew==2 && ncold==2 && ncarg==2)
           then do
             let (nm,nn) = filterModel model filt
             if nn==[()]
               then do
                 dcs <- doColSpec col [GCSVar,GCSSection]
                 case dcs of
                   Just (GCTVar dcol) -> do
                     case (fdspIntVal res, fdspIntVal init) of
                       (Just rrr, Just iii) -> addFD $ GCSum (Left dcol) (Right $ transPar $ rrr-iii)
                       _ -> do
                         dsum <- liftFD $ newvar
                         sum <- liftFD $ specInfoIntTerm dsum
                         addFD $ GCSum (Left dcol) (Left dsum)
                         t EGPlus ([],[res,init,sum],[])
                     return nm
                   Just (GCTSection (dcol,(nnn,fff))) -> do
                     case (fdspIntVal res, fdspIntVal init) of
                       (Just rrr, Just iii) -> addFD $ GCSum (Right (dcol,(nnn,fff))) (Right $ transPar $ rrr-iii)
                       _ -> do
                         dsum <- liftFD $ newvar
                         sum <- liftFD $ specInfoIntTerm dsum
                         addFD $ GCSum (Right (dcol,(nnn,fff))) (Left dsum)
                         t EGPlus ([],[res,init,sum],[])
                     return nm
                   _ -> return model
               else return model
           else return model

tryColSpecs s [] = fdspColSpec s Nothing
tryColSpecs s (a:b) = case fdspColSpec s (Just a) of
  Nothing -> tryColSpecs s b
  Just x -> Just x
tryIntSpecs s [] = fdspIntSpec s Nothing
tryIntSpecs s (a:b) = case fdspIntSpec s (Just a) of
  Nothing -> tryIntSpecs s b
  Just x -> Just x
tryBoolSpecs s [] = fdspBoolSpec s Nothing
tryBoolSpecs s (a:b) = case fdspBoolSpec s (Just a) of
  Nothing -> tryBoolSpecs s b
  Just x -> Just x


process :: (GecodeSolver s, GecodeConstraint s ~ Constraint s) => Mixin (EGConstraintSpec -> FDSpecInfo (GecodeWrappedSolver s) -> FDInstance (GecodeWrappedSolver s) ())
process s t cons info = debug ("gecode_process "++(show cons)++" "++(show info)) $ case (cons,info) of
  (EGPlus, ([],[r,a,b],[])) -> addFD $ GCLinear ((intSpecToLinear $ getDefIntSpec a)+(intSpecToLinear $ getDefIntSpec b)-(intSpecToLinear $ getDefIntSpec r)) GOEqual
  (EGMinus, ([],[r,a,b],[])) -> addFD $ GCLinear ((intSpecToLinear $ getDefIntSpec r)+(intSpecToLinear $ getDefIntSpec b)-(intSpecToLinear $ getDefIntSpec a)) GOEqual
  (EGIntValue c, ([],[r],[])) -> addFD $ GCLinear ((intSpecToLinear $ getDefIntSpec r)-(constToLinear $ transPar c)) GOEqual
  (EGBoolValue c, ([r],[],[])) -> do
    dr <- forceDecompBool r
    addFD $ GCBoolVal dr $ transParBool c
  (EGMult, ([],[r,a,b],[])) -> 
    case (fdspIntVal a,fdspIntVal b) of
      (Just val,_) -> do
        dr <- forceDecompInt r
        addFD $ GCLinear ((intSpecToLinear $ getDefIntSpec b)*(constToLinear $ transPar val)-(termToLinear dr)) GOEqual
      (_,Just val) -> do
        dr <- forceDecompInt r
        addFD $ GCLinear ((intSpecToLinear $ getDefIntSpec a)*(constToLinear $ transPar val)-(termToLinear dr)) GOEqual
      _ -> do
        da <- forceDecompInt a
        db <- forceDecompInt b
        dr <- forceDecompInt r
        addFD $ GCMult dr da db
  (EGCondEqual, ([c,a,v],[],[])) -> do
    case (getReifSpec c, getReifSpec v) of
      (GBTConst (BoolConst False),_) -> return ()
      (GBTConst (BoolConst True),GBTConst vv) -> do
        da <- forceDecompBool a
        addFD $ GCBoolVal da vv
      (GBTConst cc, GBTConst vv) -> do
        da <- forceDecompBool a
        addFD $ GCCond (GCBoolVal da vv) cc
      (cc,vv) -> error $ "Unsupported conditional equality required: ("++(show cc)++","++(show vv)++")"
  (EGDiv, ([],[r,a,b],[])) -> do
    dr <- forceDecompInt r
    da <- forceDecompInt a
    db <- forceDecompInt b
    addFD $ GCDiv dr da db
  (EGMod, ([],[r,a,b],[])) -> do
    dr <- forceDecompInt r
    da <- forceDecompInt a
    db <- forceDecompInt b
    addFD $ GCMod dr da db
  (EGAbs, ([],[r,a],[])) -> do
    dr <- forceDecompInt r
    da <- forceDecompInt a
    addFD $ GCAbs dr da
  (EGAt, ([],[r,p],[c])) -> do
    let dr = getIntVarOrConst r
    let dp = getIntVarOrConst p
    let dc = getColVarOrConst c
    addFD $ GCAt dr dc dp
  (EGChannel, ([b],[i],[])) -> do
    db <- forceDecompBool b
    di <- forceDecompInt i
    addFD $ GCChannel di db
  (EGCat, ([],[],[r,a,b])) -> do
    da <- forceDecompCol "egCat-A" a
    db <- forceDecompCol "egCat-B" b
    dr <- forceDecompCol "egCat-R" r
    addFD $ GCCat dr da db
{-  (EGSlice f n, ([],[],[r,c])) -> do
    dr <- forceDecompCol "egSlice-R" r
    dc <- forceDecompCol "egSlice-C" c
    addFD $ GCSlice dr (dc,(transPar n,transPar . f . transIPar))
    return () -}
  (EGAnd, ([r,a,b],[],[])) -> do
    dr <- forceDecompBool r
    da <- forceDecompBool a
    db <- forceDecompBool b
    addFD $ GCAnd [da,db] dr
  (EGOr, ([r,a,b],[],[])) -> do
    dr <- forceDecompBool r
    da <- forceDecompBool a
    db <- forceDecompBool b
    addFD $ GCOr [da,db] dr
  (EGNot, ([r,a],[],[])) -> do
    dr <- forceDecompBool r
    da <- forceDecompBool a
    addFD $ GCNot dr da
  (EGEquiv, ([a,b,c],[],[])) -> do
    case (fdspBoolVal a, fdspBoolVal b, fdspBoolVal c) of
      (Just (BoolConst True),_,_) -> do 
        db <- forceDecompBool b
        dc <- forceDecompBool c
        addFD $ GCBoolEqual db dc
      (_,Just (BoolConst True),_) -> do 
        dc <- forceDecompBool c
        da <- forceDecompBool a
        addFD $ GCBoolEqual dc da
      (_,_,Just (BoolConst True)) -> do 
        da <- forceDecompBool a   
        db <- forceDecompBool a
        addFD $ GCBoolEqual da db
      (Just (BoolConst False),_,_) -> do 
        db <- forceDecompBool b
        dc <- forceDecompBool c
        addFD $ GCNot db dc
      (_,Just (BoolConst False),_) -> do 
        dc <- forceDecompBool c
        da <- forceDecompBool a
        addFD $ GCNot dc da
      (_,_,Just (BoolConst False)) -> do 
        da <- forceDecompBool a
        db <- forceDecompBool a
        addFD $ GCNot da db
      _ -> do
        da <- forceDecompBool a
        db <- forceDecompBool b
        dc <- forceDecompBool c
        addFD $ GCEquiv da db dc
  (EGEqual, ([i],[a,b],[])) -> do
    da <- forceLinearInt a
    db <- forceLinearInt b
    case (getReifSpec i) of
      GBTConst (BoolConst True) ->                       addFD $ GCLinear (da-db) GOEqual
      GBTConst (BoolConst False) ->                      addFD $ GCLinear (da-db) GODiff
      GBTCondConst (BoolConst True) (BoolConst True) ->  addFD $ GCLinear (da-db) GOEqual
      GBTCondConst (BoolConst True) (BoolConst False) -> addFD $ GCLinear (da-db) GODiff
      GBTCondConst (BoolConst False) _ ->                return ()
      GBTCondConst cond (BoolConst True) ->              addFD $ GCCond (GCLinear (da-db) GOEqual) cond
      GBTCondConst cond (BoolConst False) ->             addFD $ GCCond (GCLinear (da-db) GODiff) cond
      _ -> do
        di <- forceDecompBool i
        addFD $ GCLinearReif (da-db) GOEqual di
  (EGDiff, ([i],[a,b],[])) -> do
    da <- forceLinearInt a
    db <- forceLinearInt b
    case getReifSpec i of
      GBTConst (BoolConst True) -> addFD $ GCLinear (da-db) GODiff
      GBTConst (BoolConst False) -> addFD $ GCLinear (da-db) GOEqual
      GBTCondConst (BoolConst True) (BoolConst True) -> addFD $ GCLinear (da-db) GODiff
      GBTCondConst (BoolConst True) (BoolConst False) -> addFD $ GCLinear (da-db) GOEqual
      GBTCondConst (BoolConst False) _ -> return ()
      GBTCondConst cond (BoolConst True) -> addFD $ GCCond (GCLinear (da-db) GODiff) cond
      GBTCondConst cond (BoolConst False) -> addFD $ GCCond (GCLinear (da-db) GOEqual) cond
      _ -> do
        di <- forceDecompBool i
        addFD $ GCLinearReif (da-db) GODiff di
  (EGLess q, ([i],[a,b],[])) -> do
    da <- forceLinearInt a
    db <- forceLinearInt b
    case getReifSpec i of
      GBTConst (BoolConst True) -> addFD $ GCLinear (da-db) (if q then GOLess else GOLessEqual)
      GBTConst (BoolConst False) -> addFD $ GCLinear (db-da) (if q then GOLessEqual else GOLess)
      GBTCondConst (BoolConst True) (BoolConst True) -> addFD $ GCLinear (da-db) (if q then GOLess else GOLessEqual)
      GBTCondConst (BoolConst True) (BoolConst False) -> addFD $ GCLinear (db-da) (if q then GOLessEqual else GOLess)
      GBTCondConst (BoolConst False) _ -> return ()
      GBTCondConst cond (BoolConst True) -> addFD $ GCCond (GCLinear (da-db) (if q then GOLess else GOLessEqual)) cond
      GBTCondConst cond (BoolConst False) -> addFD $ GCCond (GCLinear (db-da) (if q then GOLessEqual else GOLess)) cond
      GBTCondConst c b -> error $ "EGLess: weird conditional: c="++(show c)++" b="++(show b)
      _ -> do
        di <- forceDecompBool i
        addFD $ GCLinearReif (da-db) (if q then GOLess else GOLessEqual) di
  (EGAllDiff b, ([],[],[c])) -> do
    cc <- doColSpec c [GCSVar,GCSSection]
    case cc of
      Just (GCTSection (v,(n,f))) -> addFD $ GCAllDiff b (Right (v,(n,f)))
      Just (GCTVar v) -> addFD $ GCAllDiff b (Left v)
  (EGSorted q, ([],[],[c])) -> do
    cc <- doColSpec c [GCSVar,GCSSection]
    case cc of
      Just (GCTSection (v,(n,f))) -> addFD $ GCSorted (Right (v,(n,f))) (if q then GOLess else GOLessEqual)
      Just (GCTVar v) -> addFD $ GCSorted (Left v) (if q then GOLess else GOLessEqual)
      _ -> error $ "Wth? Sorted this: "++(show cc)++" ??"
  (EGSize, ([],[s],[c])) -> do
    dc <- forceDecompCol "egSize-C" c
    ds <- forceDecompInt s
    addFD $ GCSize dc (Left ds)
  (EGDom, ([],[i],[c])) -> do
    let dc = getColVarOrConst c
    di <- forceDecompInt i
    addFD $ GCDom di dc Nothing
  (EGAll sm (nb,ni,nc) force,(r:vb,vi,c:vc)) -> case tryColSpecs c [GCSConst,GCSVar,GCSSection] of
    Just (GCTVar dc) -> do
      let mf iv bv = 
            do
              div <- specInfoIntTerm iv
              dbv <- if force then return (error "GCAll undefined 2") else specInfoBoolTerm bv
              let fb (-1) = dbv
                  fb n = idx vb n
                  fi (-1) = div
                  fi n = idx vi n
              runFD $ procSubModel sm (fb,fi,(idx vc))
      case (force,getReifSpec r) of
        (False,GBTCondConst (BoolConst True) (BoolConst True)) -> addFD $ GCAll (GecodeIBFn mf) (Left dc) Nothing
        (_,GBTCondConst (BoolConst False) _) -> return ()
        (False,GBTCondConst cond (BoolConst True)) -> addFD $ GCCond (GCAll (GecodeIBFn mf) (Left dc) Nothing) cond
        (False,_) -> do
          dr <- forceDecompBool r
          addFD $ GCAll (GecodeIBFn mf) (Left dc) (Just dr)
        (True,_) -> addFD $ GCAll (GecodeIBFn mf) (Left dc) Nothing
    Just (GCTSection dc) -> do
      let mf iv bv = 
            do
              div <- specInfoIntTerm iv
              dbv <- if force then return (error "GCAll undefined 2") else specInfoBoolTerm bv
              let fb (-1) = dbv
                  fb n = idx vb n
                  fi (-1) = div
                  fi n = idx vi n
              runFD $ procSubModel sm (fb,fi,(idx vc))
      case (force,getReifSpec r) of
        (False,GBTCondConst cond (BoolConst True)) -> addFD $ GCCond (GCAll (GecodeIBFn mf) (Right dc) Nothing) cond
        (False,_) -> do
          dr <- forceDecompBool r
          addFD $ GCAll (GecodeIBFn mf) (Right dc) (Just dr)
        (True,_) -> addFD $ GCAll (GecodeIBFn mf) (Right dc) Nothing
    Just (GCTConst dc) -> do
      let mf cv bv =
            do
              let cc = transIPar cv
              dbv <- if force then return (error "GCAllC undefined 2") else specInfoBoolTerm bv
              let ev1 = myFromJust "process:EGAll" $ Map.lookup (-1) $ intData $ externMap sm
              let sm2 = addEdge (EGIntValue cc) (EGTypeData { boolData=[], intData=[ev1], colData=[] }) sm
              let fb (-1) = Just $ dbv
                  fb n = Just $ idx vb n
                  fi (-1) = Nothing
                  fi n = Just $ idx vi n
                  fc n = Just $ idx vc n
              runFD $ procSubModelEx sm2 (fb,fi,fc)
      case (force,getReifSpec r) of
        (False,GBTCondConst cond (BoolConst True)) -> addFD $ GCCond (GCAllC (GecodeCBFn mf) (size dc,(dc!)) Nothing) cond
        (False,_) -> do
          dr <- forceDecompBool r
          addFD $ GCAllC (GecodeCBFn mf) (size dc, (dc!)) (Just dr)
        (True,_) -> addFD $ GCAllC (GecodeCBFn mf) (size dc, (dc!)) Nothing
  (EGMap sm (nb,ni,nc),(vb,vi,cr:c:vc)) -> do
    dc <- forceDecompCol "egMap-C" c
    dcr <- forceDecompCol "egMap-CR" cr
    let mf iv rv =
          do
            div <- specInfoIntTerm iv
            drv <- specInfoIntTerm rv
            let fi (-1) = drv
                fi (-2) = div
                fi n = idx vi n
            runFD $ procSubModel sm ((idx vb),fi,(idx vc))
    addFD $ GCMap (GecodeIIFn mf) (Left dc) dcr
  xx@(EGFold om (nb,ni,nc),(vb,res:init:vi,col:vc)) -> do
    sm <- extractSumFold om col init res t
    if emptyModel sm
      then return ()
      else do
        xxx <- reduceCountFold t xx
        case xxx of
          True -> return ()
          False -> do
            zzz <- reduceMultCountFold t xx
            case zzz of
              True -> return ()
              False -> do
                yyy <- reduceSumFoldToMap t xx
                case yyy of
                  True -> return ()
                  False -> do
                    dcs <- getVarOrSection col
                    case dcs of
                      Nothing -> do
                        case fdspColSpec col Nothing of
                          Just (GCTConst sss) -> do
                            dinit <- forceDecompInt init
                            dres <- forceDecompInt res
                            let mf iv xv rv = 
                                  do
                                    let xx = transIPar xv
                                    let ev3 = myFromJust "process:EGMap" $ Map.lookup (-3) $ intData $ externMap sm
                                    let sm2 = addEdge (EGIntValue xx) (EGTypeData { boolData = [], intData=[ev3], colData=[] }) sm
                                    drv <- specInfoIntTerm rv
                                    div <- specInfoIntTerm iv
                                    let fb n = Just $ idx vb n
                                    let fi (-1) = Just drv
                                        fi (-2) = Just div
                                        fi (-3) = Nothing
                                        fi n = Just $ idx vi n
                                        fc n = Just $ idx vc n
                                    runFD $ procSubModelEx sm2 (fb,fi,fc)
                            addFD $ GCFoldC (GecodeICIFn (\prev arg next -> mf prev ((sss!) arg) next)) (size sss) dinit dres
                      Just dcol -> do
                        dinit <- forceDecompInt init
                        dres <- forceDecompInt res
                        let mf iv xv rv =
                              do
                                div <- specInfoIntTerm iv
                                drv <- specInfoIntTerm rv
                                dxv <- specInfoIntTerm xv
                                let fi (-1) = drv
                                    fi (-2) = div
                                    fi (-3) = dxv
                                    fi n = idx vi n
                                runFD $ procSubModel sm ((idx vb),fi,(idx vc))
                        addFD $ GCFold (GecodeIIIFn mf) dcol dinit dres
  _ -> s cons info

addMeta :: (GecodeSolver s, Constraint s ~ GecodeConstraint s) => Mixin (GecodeConstraint s -> s Bool)
addMeta _ t (GCAllC (GecodeCBFn mf) (Const l,f) Nothing) = do
  let m i = do
        mf (f i) (error "addMeta GCAllC undefined")
  mapM_ m [0..fromIntegral (l-1)]
  return True
addMeta _ t (GCAllC (GecodeCBFn mf) (Const l,f) (Just dr)) = do
  let m i = do
        b <- newvar
        mf (f i) b
        return b
  lst <- mapM m [0..fromIntegral (l-1)]
  t $ GCAnd lst dr
  return True
addMeta s t (GCAll (GecodeIBFn mf) (Left dc) Nothing) = do
  dcs <- col_getSize dc
  let m i = do
        v <- newInt_at dc i
        mf v (error "addMeta GCAll undefined")
  mapM_ m [0..fromIntegral $ dcs-1]
  return True
addMeta s t (GCAll (GecodeIBFn mf) (Left dc) (Just dr)) = do
  dcs <- col_getSize dc
  let m i = do
        v <- newInt_at dc i
        b <- newvar
        mf v b
        return b
  lst <- mapM m [0..fromIntegral $ dcs-1]
  t $ GCAnd lst dr
addMeta s t (GCAny (GecodeIBFn mf) (Left dc) (Just dr)) = do
  dcs <- col_getSize dc
  let m i = do
        v <- newInt_at dc i
        b <- newvar
        mf v b
        return b
  lst <- mapM m [0..fromIntegral $ dcs-1]
  t $ GCOr lst dr
addMeta s t (GCMap (GecodeIIFn mf) (Left dc) dcr) = do
  dcs <- col_getSize dc
  t $ GCSize dcr (Right dcs)
  let m i = do
        v <- newInt_at dc i
        r <- newInt_at dcr i
        mf v r
  mapM_ m [0..fromIntegral $ dcs-1]
  return True
addMeta s t (GCFold (GecodeIIIFn mf) (Left dc) dinit dres) = do
  dcs <- col_getSize dc
  vars <- mapM (\_ -> newvar) [1..fromIntegral $ dcs-1]
  let av = (dinit : vars) ++ [dres]
  let m i = do
        let prev = idx av i
        let next = idx av (i+1)
        elem <- newInt_at dc $ toConst i
        mf prev elem next
  mapM_ m [0..fromIntegral $ dcs-1]
  return True
addMeta s t (GCFoldC (GecodeICIFn mf) (nnn) dinit dres) = do
  let (Const n) = nnn
  vars <- mapM (\_ -> newvar) [1..fromIntegral $ n-1]
  let av = (dinit : vars) ++ [dres]
  let m i = do
        let prev = idx av i
        let next = idx av (i+1)
        let elem = Const $ fromIntegral i
        mf prev elem next
  mapM_ m [0..fromIntegral $ n-1]
  return True
addMeta s t (GCFold a (Right dc) b c) = do
  nc <- buildSection dc
  t $ GCFold a (Left nc) b c
addMeta s t (GCMap a (Right dc) b) = do
  nc <- buildSection dc
  t $ GCMap a (Left nc) b
addMeta s t (GCAll a (Right dc) b) = do
  nc <- buildSection dc
  t $ GCAll a (Left nc) b
addMeta s t (GCAny a (Right dc) b) = do
  nc <- buildSection dc
  t $ GCAny a (Left nc) b
addMeta s t (c@(GCSorted (Right ss) op)) = do
  nc <- buildSection ss
  t $ GCSorted (Left nc) op
addMeta s t (c@(GCAllDiff b (Right ss))) = do
  nc <- buildSection ss
  t $ GCAllDiff b (Left nc)
addMeta s t ((GCSlice c ss)) = do
  nc <- buildSection ss
  t $ GCColEqual nc c
addMeta s t (GCSum (Right ss) f) = do
  nc <- buildSection ss
  t $ GCSum (Left nc) f
addMeta s _ c = s c

toConst :: Integral a => a -> GecodeIntConst
toConst = Const . toInteger

fromConst :: Num a => GecodeIntConst -> a
fromConst (Const x) = fromInteger x

toBoolConst :: Bool -> GecodeBoolConst
toBoolConst = BoolConst

fromBoolConst :: GecodeBoolConst -> Bool
fromBoolConst (BoolConst x) = x
