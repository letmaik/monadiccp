{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers & Pieter Wuille
 -}

{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.CP.FD.Model (
  Model,
  ModelIntTerm(..),
  ModelBoolTerm(..),
  ModelColTerm(..),
  ModelFunctions(..),
  ModelInt,  ToModelInt(..), ModelIntArg,
  ModelCol,  ToModelCol(..), ModelColArg,
  ModelBool, ToModelBool(..), ModelBoolArg,
  modelVariantInt, modelVariantBool, modelVariantCol,
  ModelTermType(..),
  showModel,
  cte,
) where

import Data.Expr.Data
import Data.Expr.Util
import Data.Expr.Sugar

data ModelIntTerm t = 
    ModelIntVar Int
  | ModelIntPar Int
  deriving (Show)

data ModelColTerm t = 
    ModelColVar Int
  | ModelColPar Int
  deriving (Show)

data ModelBoolTerm t = 
    ModelBoolVar Int
  | ModelBoolPar Int
  | ModelExtra t
  deriving (Show)

data ModelFunctions =
    ForNewBool (ModelBoolExpr ModelFunctions -> Model)
  | ForNewInt (ModelIntExpr ModelFunctions -> Model)
  | ForNewCol (ModelColExpr ModelFunctions -> Model)

data ModelIntros =
     NewBool Int FlatModel
   | NewInt Int FlatModel
   | NewCol Int FlatModel
   deriving (Show,Eq)

instance Ord ModelIntros where
  compare (NewBool n1 m1) (NewBool n2 m2) = compare n1 n2 <<>> compare m1 m2
  compare (NewBool _ _) _ = LT
  compare _ (NewBool _ _) = GT
  compare (NewInt n1 m1) (NewInt n2 m2) = compare n1 n2 <<>> compare m1 m2
  compare (NewInt _ _) _ = LT
  compare _ (NewInt _ _) = GT
  compare (NewCol n1 m1) (NewCol n2 m2) = compare n1 n2 <<>> compare m1 m2

instance Show ModelFunctions where
  show (ForNewBool f) = show $ explicate (-999999) $ f $ BoolTerm $ ModelBoolVar (-1000000)
  show (ForNewInt f) = show $ explicate (-1999999) $ f $ Term $ ModelIntVar (-2000000)
  show (ForNewCol f) = show $ explicate (-2999999) $ f $ ColTerm $ ModelColVar (-3000000)
  
instance Eq ModelFunctions where
  a==b = False

instance Ord ModelFunctions where
  compare _ _ = error "Unable to compare model functions"

-- instance Show Model where 
--   show x = show $ explicate 0 x

deriving instance Eq t => Eq (ModelBoolTerm t)
deriving instance Ord t => Ord (ModelBoolTerm t)
deriving instance Eq t => Eq (ModelIntTerm t)
deriving instance Ord t => Ord (ModelIntTerm t)
deriving instance Eq t => Eq (ModelColTerm t)
deriving instance Ord t => Ord (ModelColTerm t)

type ModelIntExpr t       = Expr        (ModelIntTerm  t) (ModelColTerm  t) (ModelBoolTerm  t)
type ModelBoolExpr t      = BoolExpr    (ModelIntTerm  t) (ModelColTerm  t) (ModelBoolTerm  t)
type ModelColExpr t       = ColExpr     (ModelIntTerm  t) (ModelColTerm  t) (ModelBoolTerm  t)

type ModelInt = ModelIntExpr ModelFunctions
type ModelBool = ModelBoolExpr ModelFunctions
type ModelCol = ModelColExpr ModelFunctions

type ModelIntArg = ModelIntTerm ModelFunctions
type ModelBoolArg = ModelBoolTerm ModelFunctions
type ModelColArg = ModelColTerm ModelFunctions

type FlatModelInt = ModelIntExpr ModelIntros
type FlatModelBool = ModelBoolExpr ModelIntros
type FlatModelCol = ModelColExpr ModelIntros

type Model = ModelBool
type FlatModel = FlatModelBool

explicate :: Int -> Model -> FlatModel
explicate num mod = boolTransformEx (it,ct,bt,iit,ict,ibt) mod
  where it (ModelIntVar i) = Term $ ModelIntVar i
        it (ModelIntPar i) = Term $ ModelIntPar i
        ct (ModelColVar i) = ColTerm $ ModelColVar i
        ct (ModelColPar i) = ColTerm $ ModelColPar i
        iit (ModelIntVar i) = Term $ ModelIntVar i
        iit (ModelIntPar i) = Term $ ModelIntPar i
        ict (ModelColVar i) = ColTerm $ ModelColVar i
        ict (ModelColPar i) = ColTerm $ ModelColPar i
        ibt (ModelBoolVar i) = BoolTerm $ ModelBoolVar i
        ibt (ModelBoolPar i) = BoolTerm $ ModelBoolPar i
        bt (ModelBoolVar i) = BoolTerm $ ModelBoolVar i
        bt (ModelBoolPar i) = BoolTerm $ ModelBoolPar i
        bt (ModelExtra (ForNewBool f)) = BoolTerm $ ModelExtra $ NewBool num $ explicate (num+1) $ f $ BoolTerm $ ModelBoolVar num
        bt (ModelExtra (ForNewInt f)) = BoolTerm $ ModelExtra $ NewInt num $ explicate (num+1) $ f $ Term $ ModelIntVar num
        bt (ModelExtra (ForNewCol f)) = BoolTerm $ ModelExtra $ NewCol num $ explicate (num+1) $ f $ ColTerm $ ModelColVar num

flatten :: Model -> FlatModel
flatten = explicate 0

showModel :: Model -> String
showModel = show . flatten

variantIntTerm :: ModelIntTerm a -> Bool
variantIntTerm (ModelIntVar _) = True
variantIntTerm (ModelIntPar _) = False

variantBoolTerm :: ModelBoolTerm a -> Bool
variantBoolTerm (ModelBoolVar _) = True
variantBoolTerm (ModelBoolPar _) = False
variantBoolTerm (ModelExtra _) = True

variantColTerm :: ModelColTerm a -> Bool
variantColTerm (ModelColVar _) = True
variantColTerm (ModelColPar _) = False

modelVariantInt  :: ModelIntExpr x -> Bool
modelVariantInt  =     property variantIntTerm variantColTerm variantBoolTerm
modelVariantCol  :: ModelColExpr x -> Bool
modelVariantCol  =  colProperty variantIntTerm variantColTerm variantBoolTerm
modelVariantBool :: ModelBoolExpr x -> Bool
modelVariantBool = boolProperty variantIntTerm variantColTerm variantBoolTerm

newBool :: (ModelBool -> Model) -> Model
newBool = boolSimplify . BoolTerm . ModelExtra . ForNewBool

newInt :: (ModelInt -> Model) -> Model
newInt = boolSimplify . BoolTerm . ModelExtra . ForNewInt

newCol :: (ModelCol -> Model) -> Model
newCol = boolSimplify . BoolTerm . ModelExtra . ForNewCol

class ModelTermType s where
  newModelTerm :: (s -> Model) -> Model

instance ModelTermType ModelBool where
  newModelTerm = newBool

instance ModelTermType ModelInt where
  newModelTerm = newInt

instance ModelTermType ModelCol where
  newModelTerm = newCol

cte :: Integral a => a -> ModelInt
cte = Const . toInteger

class ToModelBool t where
  asBool :: t -> ModelBool

class ToModelInt t where
  asExpr :: t -> ModelInt

class ToModelCol t where
  asCol :: t -> ModelCol

instance ToExpr (ModelIntTerm ModelFunctions) (ModelColTerm ModelFunctions) (ModelBoolTerm ModelFunctions) t => ToModelInt t where
  asExpr = toExpr

instance ToBoolExpr (ModelIntTerm ModelFunctions) (ModelColTerm ModelFunctions) (ModelBoolTerm ModelFunctions) t => ToModelBool t where
  asBool = toBoolExpr

instance ToColExpr (ModelIntTerm ModelFunctions) (ModelColTerm ModelFunctions) (ModelBoolTerm ModelFunctions) t => ToModelCol t where
  asCol = toColExpr
