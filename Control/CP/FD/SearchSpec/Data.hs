{-# LANGUAGE StandaloneDeriving #-}

module Control.CP.FD.SearchSpec.Data (
  OptimDirection(..),
  VarExpr(..),
  VarStat(..),
  Labelling(..),
  SearchSpec(..),
  ConstraintExpr,
  ConstraintRefs(..),
  mmapSearch
) where

import Control.CP.Solver
import Control.CP.FD.FD
import Data.Expr.Data
import Control.Search.Generator
import Control.Search.Language

-- Wouter Swierstra - Data Types a la Carte
-- Jacques Carette, Oleg - Finally Tagless

data VarStat =
    DLowerBound
  | DUpperBound
  | DDomSize
  | DLowerRegret
  | DUpperRegret
  | DDegree
  | DWDregree
  | DRandom
  | DMedian
  | DDummy Int
  deriving (Eq,Ord,Show)

data OptimDirection = 
    Maximize
  | Minimize
  deriving (Eq,Ord,Show)

type VarExpr = Expr VarStat () ()

data ConstraintRefs =
    VarRef
  | ValRef
  deriving (Eq,Ord,Show)

type ConstraintExpr = Expr ConstraintRefs () ()
type ConstraintBoolExpr = BoolExpr ConstraintRefs () ()

data Labelling v a b =
    LabelInt v VarExpr (ConstraintExpr -> ConstraintExpr-> ConstraintBoolExpr)
  | LabelCol a VarExpr OptimDirection VarExpr (ConstraintExpr -> ConstraintExpr -> ConstraintBoolExpr)
  | LabelBool b VarExpr

data SearchSpec v a b =
    Labelling (Labelling v a b)
  | CombineSeq (SearchSpec v a b) (SearchSpec v a b)
  | CombinePar (SearchSpec v a b) (SearchSpec v a b)
  | TryOnce (SearchSpec v a b)
  | LimitSolCount Integer (SearchSpec v a b)
  | LimitDepth Integer (SearchSpec v a b)
  | LimitNodeCount Integer (SearchSpec v a b)
  | LimitDiscrepancy Integer (SearchSpec v a b)
  | BranchBound v OptimDirection (SearchSpec v a b)
  | PrintSol [v] [a] [b] (SearchSpec v a b)

deriving instance (Show v, Show a, Show b) => Show (SearchSpec v a b)

instance (Show v, Show a, Show b) => Show (Labelling v a b) where
  show (LabelInt v x f) = "LabelInt " ++ (show v) ++ " " ++ (show x) ++ " " ++ (show $ f (Term VarRef) (Term ValRef))
  show (LabelCol v x d s f) = "LabelCol " ++ (show v) ++ " " ++ (show x) ++ " " ++ show d ++ " " ++ show s ++ " " ++ (show $ f (Term VarRef) (Term ValRef))
  show (LabelBool v x) = "LabelBool " ++ (show v) ++ " " ++ (show x)

mmapSearch :: (Monad m) => SearchSpec v1 a1 b1 -> (v1 -> m v2) -> (a1 -> m a2) -> (b1 -> m b2) -> m (SearchSpec v2 a2 b2)
mmapSearch (Labelling (LabelInt v x f)) vf af bf = vf v >>= \y -> return $ Labelling $ LabelInt y x f
mmapSearch (Labelling (LabelCol a x d s f)) vf af bf = af a >>= \y -> return $ Labelling $ LabelCol y x d s f
mmapSearch (Labelling (LabelBool v x)) vf af bf = bf v >>= \y -> return $ Labelling $ LabelBool y x
mmapSearch (CombineSeq a b) vf af bf = do
  ad <- mmapSearch a vf af bf
  bd <- mmapSearch b vf af bf
  return (CombineSeq ad bd)
mmapSearch (CombinePar a b) vf af bf = do
  ad <- mmapSearch a vf af bf
  bd <- mmapSearch b vf af bf
  return (CombinePar ad bd)
mmapSearch (TryOnce a) vf af bf = do
  ad <- mmapSearch a vf af bf
  return (TryOnce ad)
mmapSearch (LimitSolCount n a) vf af bf = do
  ad <- mmapSearch a vf af bf
  return (LimitSolCount n ad)
mmapSearch (LimitDepth n a) vf af bf = do
  ad <- mmapSearch a vf af bf
  return $ (LimitDepth n ad)
mmapSearch (LimitNodeCount n a) vf af bf = do
  ad <- mmapSearch a vf af bf
  return $ (LimitNodeCount n ad)
mmapSearch (LimitDiscrepancy n a) vf af bf = do
  ad <- mmapSearch a vf af bf
  return $ (LimitDiscrepancy n ad)
mmapSearch (BranchBound v d a) vf af bf = do
  vd <- vf v
  ad <- mmapSearch a vf af bf
  return (BranchBound vd d ad)
mmapSearch (PrintSol i c b a) iF cF bF = do
  vi <- mapM iF i
  vc <- mapM cF c
  vb <- mapM bF b
  ad <- mmapSearch a iF cF bF
  return (PrintSol vi vc vb ad)
