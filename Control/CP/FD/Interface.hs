{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Control.CP.FD.Interface (
  FDSolver,
  FDInstance,
  (@+),(@-),(@*),(@/),(@%),(!),(@!!),(@..),(@++),size,xfold,xsum,xhead,xtail,list,slice,xmap,cte,
  (Control.CP.FD.Interface.@||),
  (Control.CP.FD.Interface.@&&),
  Control.CP.FD.Interface.inv,
  (Control.CP.FD.Interface.@=),
  (Control.CP.FD.Interface.@/=),
  (Control.CP.FD.Interface.@<),
  (Control.CP.FD.Interface.@>),
  (Control.CP.FD.Interface.@<=),
  (Control.CP.FD.Interface.@>=),
  (Control.CP.FD.Interface.@:),
  (Control.CP.FD.Interface.@?),
  (Control.CP.FD.Interface.@??),
  Control.CP.FD.Interface.channel,
  val,
--  Control.CP.FD.Interface.newInt, Control.CP.FD.Interface.newBool, Control.CP.FD.Interface.newCol,
  Control.CP.FD.Interface.sorted, 
  Control.CP.FD.Interface.sSorted,
  Control.CP.FD.Interface.forall,
  Control.CP.FD.Interface.forany,
  Control.CP.FD.Interface.loopall,
  Control.CP.FD.Interface.allDiff,
  Control.CP.FD.Interface.allDiffD,
  Control.CP.FD.Interface.loopany,
  allin,
  asExpr, asCol, Control.CP.FD.Interface.asBool,
  colList, labelCol, 
  ModelInt, ModelCol, ModelBool,
  exists, true, false,
--  Modelable,
) where

import Control.CP.FD.FD (FDSolver, FDInstance, FDIntTerm, getColItems)
import qualified Control.CP.FD.Model as Model
import Control.CP.FD.Model (Model, ModelBool, ModelCol, ModelInt, ToModelBool, asBool, asExpr, asCol, cte, newModelTerm, ModelIntArg, ModelBoolArg, ModelColArg)
import qualified Data.Expr.Sugar as Sugar
import Data.Expr.Util
import Data.Expr.Data
import Data.Expr.Sugar ((@+),(@-),(@*),(@/),(@%),(!),(@!!),(@..),(@++),size,xfold,xhead,xtail,slice,xmap,xsum,list)
import Control.CP.Solver
import Control.CP.SearchTree
import Control.CP.EnumTerm

newtype DummySolver a = DummySolver ()

instance Monad DummySolver where
  return _ = DummySolver ()
  _ >>= _ = DummySolver ()

data EQHelp b where
  EQHelp :: Model.ModelTermType b => ((b -> Model) -> Model) -> EQHelp b

instance Model.ModelTermType t => Term DummySolver t where
  type Help DummySolver t = EQHelp t
  help _ _ = EQHelp newModelTerm
  newvar = DummySolver ()

instance Solver DummySolver where
  type Constraint DummySolver = Either Model ()
  type Label DummySolver = ()
  add _ = DummySolver ()
  run _ = error "Attempt to run dummy solver"
  mark = DummySolver ()
  goto _ = DummySolver ()

newtype Model.ModelTermType t => DummyTerm t = DummyTerm t

-- class (Solver s, Term s ModelBool, Term s ModelInt, Term s ModelCol) => Modelable s where

-- instance Modelable DummySolver where

-- instance FDSolver s => Modelable (FDInstance s) where


treeToModel :: Tree DummySolver () -> Model
treeToModel (Return _) = BoolConst True
treeToModel (Try a b) = (Sugar.@||) (treeToModel a) (treeToModel b)
treeToModel (Add (Left c) m) = (Sugar.@&&) c (treeToModel m)
treeToModel Fail = BoolConst False
treeToModel (Label _) = error "Cannot turn labelled trees into expressions"
treeToModel (NewVar (f :: t -> Tree DummySolver ())) = case (help ((error "treeToModel undefined 1") :: DummySolver ()) ((error "treeToModel undefined 2") :: t)) of EQHelp ff -> ff (\x -> treeToModel $ f (x :: t))

addM :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => Model -> m ()
addM m = addC $ Left m

infixr 2 @||
(@||) :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => Tree DummySolver () -> Tree DummySolver () -> m ()
(@||) a b = addM $ treeToModel $ a \/ b

infixr 3 @&&
(@&&) :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => Tree DummySolver () -> Tree DummySolver () -> m ()
(@&&) a b = addM $ treeToModel $ a /\ b

channel :: Tree DummySolver () -> ModelInt
channel a = Sugar.channel $ treeToModel a

inv :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => Tree DummySolver () -> m ()
inv a = addM $ Sugar.inv $ treeToModel a

infix 4 @=, @/=, @<, @>, @<=, @>=

class ModelExprClass a where
  (@=) :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => a -> a -> m ()
  (@/=) :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => a -> a -> m ()

instance ModelExprClass ModelInt where
  a @= b  = addM $ (Sugar.@=)  a b
  a @/= b = addM $ (Sugar.@/=) a b

instance ModelExprClass ModelCol where
  a @= b  = addM $ (Sugar.@=)  a b
  a @/= b = addM $ (Sugar.@/=) a b

instance ModelExprClass ModelBool where
  a @= b  = addM $ (Sugar.@=)  a b
  a @/= b = addM $ (Sugar.@/=) a b

instance ModelExprClass (Tree DummySolver ()) where
  a @= b  = addM $ (Sugar.@=)  (treeToModel a) (treeToModel b)
  a @/= b = addM $ (Sugar.@/=) (treeToModel a) (treeToModel b)

(@<) :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => ModelInt -> ModelInt -> m ()
(@<) a b = addM $ (Sugar.@<) a b

(@>) :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => ModelInt -> ModelInt -> m ()
(@>) a b = addM $ (Sugar.@>) a b

(@>=) :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => ModelInt -> ModelInt -> m ()
(@>=) a b = addM $ (Sugar.@>=) a b

(@<=) :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => ModelInt -> ModelInt -> m ()
(@<=) a b = addM $ (Sugar.@<=) a b

val :: Tree DummySolver () -> ModelInt
val = Sugar.toExpr . treeToModel

{- newBool :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => (ModelBool -> Tree DummySolver a) -> m a
newBool = exists

newInt :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => (ModelInt -> m a) -> m a
newInt = exists

newCol :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => (ModelCol -> m a) -> m a
newCol = exists
-}

asBool :: (FDSolver s, MonadTree m, TreeSolver m ~ FDInstance s, ToModelBool t) => t -> m ()
asBool = addM . Control.CP.FD.Model.asBool

sorted :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => ModelCol -> m ()
sorted = addM . Sugar.sorted

sSorted :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => ModelCol -> m ()
sSorted = addM . Sugar.sSorted

allDiff :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => ModelCol -> m ()
allDiff = addM . Sugar.allDiff

allDiffD :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => ModelCol -> m ()
allDiffD = addM . Sugar.allDiffD

mm (nv@(Term tv)) m x = 
     let tf t = if (t==tv) then x else Term t
         tb t = if (Term t==x) then nv else Term t
         in boolTransformEx (tf,ColTerm,BoolTerm,tb,ColTerm,BoolTerm) m

forall :: (Term s ModelInt, Term s ModelBool, Term s ModelCol, Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => ModelCol -> (ModelInt -> Tree DummySolver ()) -> m ()
-- forall col f = exists $ \nv -> addM $ Sugar.forall col $ mm nv $ treeToModel $ f nv
forall col f = addM $ Sugar.forall col (treeToModel . f)

forany :: (Term s ModelInt, Term s ModelBool, Term s ModelCol, Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => ModelCol -> (ModelInt -> Tree DummySolver ()) -> m ()
-- forany col f = exists $ \nv -> addM $ Sugar.forany col $ mm nv $ treeToModel $ f nv
forany col f = addM $ Sugar.forany col (treeToModel . f)

loopall :: (Term s ModelInt, Term s ModelBool, Term s ModelCol, Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => (ModelInt,ModelInt) -> (ModelInt -> Tree DummySolver ()) -> m ()
-- loopall r f = exists $ \nv -> addM $ Sugar.loopall r $ mm nv $ treeToModel $ f nv
loopall r f = addM $ Sugar.loopall r (treeToModel . f)

loopany :: (Term s ModelInt, Term s ModelBool, Term s ModelCol, Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => (ModelInt,ModelInt) -> (ModelInt -> Tree DummySolver ()) -> m ()
-- loopany r f = exists $ \nv -> addM $ Sugar.loopany r $ mm nv $ treeToModel $ f nv
loopany r f = addM $ Sugar.loopany r (treeToModel . f)

colList :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s) => ModelCol -> Int -> m [ModelInt]
colList col len = do
  addM $ (Sugar.@=) (size col) (asExpr len)
  return $ map (\i -> col!cte i) [0..len-1]

labelCol :: (FDSolver s, MonadTree m, TreeSolver m ~ FDInstance s, EnumTerm s (FDIntTerm s)) => ModelCol -> m [TermBaseType s (FDIntTerm s)]
labelCol col = label $ do
  lst <- getColItems col maxBound
  return $ do
    lsti <- colList col $ length lst
    enumerate lsti
    assignments lsti

infix 5 @:

(@:) :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s, Sugar.ExprRange ModelIntArg ModelColArg ModelBoolArg r, Term s ModelInt, Term s ModelBool, Term s ModelCol) => ModelInt -> r -> m ()
a @: b = addM $ (Sugar.@:) a b

infix 4 @?
infix 4 @??

a @? (t,f) = (Sugar.@?) (treeToModel a) (t,f)
a @?? (t,f) = addM $ (Sugar.@??) (treeToModel a) (treeToModel t, treeToModel f)

allin :: (Constraint s ~ Either Model q, MonadTree m, TreeSolver m ~ s, Sugar.ExprRange ModelIntArg ModelColArg ModelBoolArg r, Term s ModelInt, Term s ModelBool, Term s ModelCol) => ModelCol -> r -> m ()
allin c b = Control.CP.FD.Interface.forall c $ \x -> addM $ (Sugar.@:) x b
