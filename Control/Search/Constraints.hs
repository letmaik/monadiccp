{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverlappingInstances #-}

module Control.Search.Constraints
  ( clvar, cvar, cvars, cbvars, cval, cop, ctrue, cfalse, cexprStatVal, cexprStatMed, cexprStatMin, cexprStatMax
  , ConstraintExpr(..), ConstraintGen(..)
  ) where

import Text.PrettyPrint hiding (space)
import List (sort, nub, sortBy)
import Unsafe.Coerce

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Memo
import Control.Search.Stat
import Control.Search.Generator

import Control.Monatron.Monatron hiding (Abort, L, state, cont)
import Control.Monatron.Zipper hiding (i,r)
import Control.Monatron.IdT

import Data.Maybe (fromJust)
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Search.SStateT

data ConstraintExpr = ConstraintExpr (forall m. VarInfoM m => m IValue) Bool [String]

data ConstraintGen = ConstraintGen (forall m. VarInfoM m => Info -> m Constraint) [String]

cvars :: String -> Integer -> ConstraintExpr
cvars v n = ConstraintExpr (return $ \i -> (AVarElem v (space i) (fromInteger n))) True [v]

cbvars :: String -> Integer -> ConstraintExpr
cbvars v n = ConstraintExpr (return $ \i -> (BAVarElem v (space i) (fromInteger n))) True [v]

cvar :: String -> ConstraintExpr
cvar v = ConstraintExpr (return $ \i -> (IVar v (space i))) True [v]

cval :: Integer -> ConstraintExpr
cval i = ConstraintExpr (return $ const $ fromInteger i) False []

clvar :: VarId -> ConstraintExpr
clvar v@(VarId n) = ConstraintExpr (do inf <- lookupVarInfo v
                                       return $ const $ estate inf @=> ("var" ++ show n)
                                   ) False []

cop :: ConstraintExpr -> (Value -> Value -> Constraint) -> ConstraintExpr -> ConstraintGen
cop (ConstraintExpr v1 _ l1) op (ConstraintExpr v2 _ l2) = ConstraintGen (\info -> (v1 >>= \x -> v2 >>= \y -> return (x info `op` y info))) (l1 ++ l2)

ctrue :: ConstraintGen
ctrue = ConstraintGen (const $ return TrueC) []

cfalse :: ConstraintGen
cfalse = ConstraintGen (const $ return FalseC) []

cexprStat f (ConstraintExpr m c l) = Stat (\e -> e { intVarsE = l ++ intVarsE e }) (m >>= \iv -> return (\info -> (if c then iv info @-> (f ++ "()") else iv info)))
cexprStatVal = cexprStat "val"
cexprStatMin = cexprStat "min"
cexprStatMax = cexprStat "max"
cexprStatMed = cexprStat "med"


