{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

module Control.CP.FD.Gecode.Common (
  GTerm(..),
  GType(..),
  IntTerm(..),
  BoolTerm(..),
  GConstraint(..),
  GOperator(..),
  GecodeSolver(..),
  orElse,
  linearCompile,
  basicCompile
) where

import Maybe (fromMaybe,catMaybes,isJust,fromJust)
import List (findIndex,find)
import Data.Map hiding (map,filter)

import Control.Monad.State.Lazy
import Control.Monad.Trans
import Control.Monad.Cont


import Control.CP.SearchTree hiding (label)
import Control.CP.Solver
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.Debug
import Control.CP.Mixin
-- import Control.CP.Gecode.Gecode

--------------------------------------------------------------------------------
-- | Gecode terms
--------------------------------------------------------------------------------

class GTerm t where
  getVarId :: t -> Maybe Int
  getIntValue :: t -> Maybe Integer
  getDefBounds :: t -> (Integer,Integer)

data GType = TypeInt | TypeBool
  deriving (Show, Eq)

-- | integer terms
data IntTerm
  = IntVar Int
  | IntConst Integer
  deriving Eq

instance Ord IntTerm where
  compare (IntVar i1) (IntVar i2) = compare i1 i2
  compare (IntVar _) _ = LT
  compare _ (IntVar _) = GT
  compare (IntConst c1) (IntConst c2) = compare c1 c2

instance Show IntTerm where
  show (IntVar i) = "i" ++ (show i)
  show (IntConst i) = (show i)

instance GTerm IntTerm where
  getVarId (IntVar i) = Just i
  getVarId (IntConst _) = Nothing
  getIntValue (IntVar _) = Nothing
  getIntValue (IntConst c) = Just c
  getDefBounds _ = (-1000000000,1000000000)

-- | boolean terms
data BoolTerm where
  BoolVar :: Int -> BoolTerm
  BoolConst :: Bool -> BoolTerm
  deriving Eq

instance Show BoolTerm where
  show (BoolVar i) = "b" ++ (show i)
  show (BoolConst b) = show b

instance GTerm BoolTerm where
  getVarId (BoolVar i) = Just i
  getVarId (BoolConst _) = Nothing
  getIntValue (BoolVar _) = Nothing
  getIntValue (BoolConst c) = Just $ if c then 1 else 0
  getDefBounds _ = (0,1)

-- instance Term Gecode BoolTerm where
--   type TermInfo Gecode BoolTerm = Bool
--   newvar = newVar False TypeBool >>= return . BoolVar
-- 
-- instance Term Gecode IntTerm where
--   type TermInfo Gecode IntTerm = Bool
--   newvar = newVar False TypeInt >>= return . IntVar


--------------------------------------------------------------------------------
-- | Gecode constraints 
--------------------------------------------------------------------------------

data GConstraint  
  = forall t . GTerm t => CDiff t t
  | forall t . GTerm t => CSame t t
  | CRel IntTerm GOperator IntTerm
  | CMult IntTerm IntTerm IntTerm
  | CAbs IntTerm IntTerm
  | CDiv IntTerm IntTerm IntTerm
  | CMod IntTerm IntTerm IntTerm
  | CValue IntTerm Integer
  | CDom IntTerm Integer Integer
  | CLinear [(IntTerm,Integer)] GOperator Integer
  | CAllDiff [IntTerm]
  | CSorted [IntTerm] Bool

instance Show GConstraint where
  show (CRel x o y) = "(Rel: " ++ (show x) ++ (show o) ++ (show y) ++ ")"
  show (CMult x y z) = "(Mult: " ++ (show x) ++ " * " ++ (show y) ++ " = " ++ (show z) ++ ")"
  show (CDiv x y z) = "(Div: " ++ (show x) ++ " / " ++ (show y) ++ " = " ++ (show z) ++ ")"
  show (CMod x y z) = "(Mod: " ++ (show x) ++ " % " ++ (show y) ++ " = " ++ (show z) ++ ")"
  show (CAbs x y) = "(Abs: abs " ++ (show x) ++ " = " ++ (show y) ++ ")"
  show (CDom x y z) = "(Dom: " ++ (show x) ++ " in [" ++ (show y) ++ "," ++ (show z) ++ "])"
  show (CValue x y) = "(Value: " ++ (show x) ++ " is " ++ (show y) ++ ")"
  show (CLinear l o c) = "(Linear: " ++ (show l) ++ (show o) ++ (show c) ++ ")"
  show (CAllDiff l) = "(AllDiff: " ++ (show l) ++ ")"

data GOperator
  = OEqual
  | ODiff
  | OLess

instance Show GOperator where
  show OEqual = "=="
  show ODiff  = "/="
  show OLess  = "<"

--------------------------------------------------------------------------------
-- | Gecode FDSolver instance
--------------------------------------------------------------------------------

class (Solver s, Term s IntTerm) => GecodeSolver s where
  setVarImplicit :: IntTerm -> Bool -> s ()
  setVarImplicit _ _ = return ()
  caching_decompose :: GecodeSolver s => Mixin (Expr (FDTerm s) -> Tree s IntTerm)
  caching_decompose s _ x = s x

-- | basic compilation

basicCompile :: (FDSolver s, Constraint s ~ GConstraint, FDTerm s ~ IntTerm) => Mixin (FDConstraint s -> Tree s Bool)
basicCompile s t (Same a (Plus b c)) = do
  va <- getAsVar a
  vb <- getAsVar b
  vc <- getAsVar c
  addT (CLinear [(va,1),(vb,-1),(vc,-1)] OEqual 0)
basicCompile s t (Same a (Minus b c)) = do
  va <- getAsVar a
  vb <- getAsVar b
  vc <- getAsVar c
  addT (CLinear [(va,1),(vb,1),(vc,1)] OEqual 0)
basicCompile s t (Same a (Mult b c)) = do
  va <- getAsVar a
  vb <- getAsVar b
  vc <- getAsVar c
  addT (CMult vb vc va)
basicCompile s t (Same a (Div b c)) = do
  va <- getAsVar a
  vb <- getAsVar b
  vc <- getAsVar c
  addT (CDiv vb vc va)
basicCompile s t (Same a (Mod b c)) = do
  va <- getAsVar a
  vb <- getAsVar b
  vc <- getAsVar c
  addT (CMod vb vc va)
basicCompile s t (Same a (Abs b)) = do
  va <- getAsVar a
  vb <- getAsVar b
  addT (CAbs vb va)
basicCompile s t (Same a@(Plus _ _) b) = basicCompile s t $ Same b a
basicCompile s t (Same a@(Minus _ _) b) = basicCompile s t $ Same b a
basicCompile s t (Same a@(Mult _ _) b) = basicCompile s t $ Same b a
basicCompile s t (Same a@(Div _ _) b) = basicCompile s t $ Same b a
basicCompile s t (Same a@(Mod _ _) b) = basicCompile s t $ Same b a
basicCompile s t (Same a@(Abs _) b) = basicCompile s t $ Same b a
basicCompile s t (Same a@(Const _) b) = basicCompile s t $ Same b a
basicCompile s t (Same a (Const i)) = do
  va <- getAsVar a
  addT (CValue va i)
basicCompile s t (x@(Same a b))  = do
  va <- getAsVar a
  vb <- getAsTerm b
  addT (CRel va OEqual vb)
basicCompile s t (Diff a b) = do
  va <- getAsVar a
  vb <- getAsTerm b
  addT (CRel va ODiff vb)
basicCompile s t (Less a b) = do
  va <- getAsVar a
  vb <- getAsTerm b
  addT (CRel va OLess vb)
basicCompile s t (Dom a l h) = do
  va <- getAsVar a
  addT (CDom va l h)
basicCompile s t (AllDiff l) = do
  vl <- mapM getAsVar l
  addT (CAllDiff vl)
basicCompile s t (Sorted l e) = do
  vl <- mapM getAsVar l
  addT (CSorted vl e)
-- basicCompile s _ x = s x

getAsVar :: (FDSolver s, Constraint s ~ GConstraint, FDTerm s ~ IntTerm) => Expr IntTerm -> Tree s IntTerm
getAsVar = decompose
getAsTerm :: (FDSolver s, Constraint s ~ GConstraint, FDTerm s ~ IntTerm) => Expr IntTerm -> Tree s IntTerm
getAsTerm (Const c) = return $ IntConst c
getAsTerm x = decompose x

-- | linear constraint compilation

linearCompile :: (FDSolver s, Constraint s ~ GConstraint, FDTerm s ~ IntTerm) => Mixin (FDConstraint s -> Tree s Bool)
linearCompile s t (Same a@(Plus _ _) b) = linearCompileX a b OEqual
linearCompile s t (Same a@(Minus _ _) b) = linearCompileX a b OEqual
linearCompile s t (Same b a@(Plus _ _)) = linearCompileX a b OEqual
linearCompile s t (Same b a@(Minus _ _)) = linearCompileX a b OEqual
linearCompile s t (Diff a@(Plus _ _) b) = linearCompileX a b ODiff
linearCompile s t (Diff a@(Minus _ _) b) = linearCompileX a b ODiff
linearCompile s t (Diff a b@(Plus _ _)) = linearCompileX a b ODiff
linearCompile s t (Diff a b@(Minus _ _)) = linearCompileX a b ODiff
linearCompile s t (Less a@(Plus _ _) b) = linearCompileX a b OLess
linearCompile s t (Less a@(Minus _ _) b) = linearCompileX a b OLess
linearCompile s t (Less a b@(Plus _ _)) = linearCompileX a b OLess
linearCompile s t (Less a b@(Minus _ _)) = linearCompileX a b OLess
linearCompile s t x          = s x

linearCompileX a b o =  
  do t1 <- linearExprCompile a
     t2 <- linearExprCompile b
     let (x,a,c) = linearAdd t1 t2 1 (-1)
     addT (CLinear (filter (\(_,a) -> a /= 0) $ map (\(xe,ae) -> (IntVar xe,ae)) $ zip x a) o c)

linearExprCompile :: (FDSolver s, Constraint s ~ GConstraint, FDTerm s ~ IntTerm) => Expr (FDTerm s) -> Tree s ([Int],[Integer],Integer)
linearExprCompile (Term (IntVar i)) = 
  return ([i],[1],0)
linearExprCompile (Term (IntConst c)) = 
  return ([],[],-c)
linearExprCompile (Const c) = 
  return ([],[],-c)
linearExprCompile (Plus a b) = 
  do t1 <- linearExprCompile a
     t2 <- linearExprCompile b
     return $ linearAdd t1 t2 1 1
linearExprCompile (Minus a b) = 
  do t1 <- linearExprCompile a
     t2 <- linearExprCompile b
     return $ linearAdd t1 t2 1 (-1)
linearExprCompile (Mult (Const c) a) = 
  do t <- linearExprCompile a
     return $ linearAdd t ([],[],0) c 1
linearExprCompile (Mult a (Const c)) = 
  linearExprCompile (Mult (Const c) a)
linearExprCompile x =
  do (IntVar i) <- getAsVar x
     return ([i],[1],0)

linearAdd (x1,a1,c1) (x2,a2,c2) m1 m2 = case (x1,a1) of
  ([],[]) -> (x2,map (*m2) a2,m1*c1+m2*c2)
  (x1e:x1s,a1e:a1s) -> linearAdd (x1s,a1s,c1) (linearAddTerm (x2,a2,c2) x1e a1e m2 m1 [] []) m1 1

linearAddTerm (x1,a1,c1) x2e a2e m1 m2 xc ac = case (x1,a1) of
  ([],[]) -> (x2e:xc,(a2e*m2):ac,c1*m1)
  (x1e:x1s,a1e:a1s) -> if x1e == x2e
      then ((x2e:x1s) ++ xc,((a1e*m1+a2e*m2):(map (*m1) a1s)) ++ ac,c1*m1)
      else linearAddTerm (x1s,a1s,c1) x2e a2e m1 m2 (x1e:xc) ((a1e*m1):ac)

-- | utility

orElse :: Maybe a -> Maybe a -> Maybe a
orElse = mplus
