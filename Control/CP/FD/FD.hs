{- 
 - Origin:
 - 	Constraint Programming in Haskell 
 - 	http://overtond.blogspot.com/2008/07/pre.html
 - 	author: David Overton, Melbourne Australia
 -
 - Modifications:
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers
 -} 

{-# OPTIONS_GHC -fglasgow-exts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverlappingInstances #-}

module Control.CP.FD.FD where 

import Prelude hiding (lookup)
import Maybe (fromJust,isJust)
import Control.Monad.State.Lazy
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.Map ((!), Map)
import Control.Monad (liftM,(<=<))

import Control.CP.FD.Domain as Domain

import Control.CP.Solver

-- import Debug.Trace
trace = flip const
--------------------------------------------------------------------------------
-- Solver instance -------------------------------------------------------------
--------------------------------------------------------------------------------

instance Solver FD where
  type Constraint FD  = FD_Constraint
  type Term       FD  = FD_Term
  type Label      FD  = FDState

  newvar 	= newVar () >>= return . FD_Var 
  add    	= addFD
  run p   	= runFD p

  mark	= get
  goto	= put 

data FD_Term where
  FD_Var :: FDVar -> FD_Term
  deriving Show

un_fd (FD_Var v) = v

data FD_Constraint where
  FD_Diff :: FD_Term -> FD_Term -> FD_Constraint
  FD_Same :: FD_Term -> FD_Term -> FD_Constraint
  FD_Less :: FD_Term  -> FD_Term -> FD_Constraint
  FD_LT   :: FD_Term -> Int -> FD_Constraint
  FD_GT   :: FD_Term -> Int -> FD_Constraint
  FD_HasValue :: FD_Term -> Int -> FD_Constraint
  FD_Eq   :: (ToExpr a, ToExpr b) => a -> b -> FD_Constraint
  FD_NEq   :: (ToExpr a, ToExpr b) => a -> b -> FD_Constraint
  FD_AllDiff :: [FD_Term] -> FD_Constraint
  FD_Dom     :: FD_Term -> (Int,Int) -> FD_Constraint

addFD (FD_Diff (FD_Var v1) (FD_Var v2)) = different v1 v2
addFD (FD_Same (FD_Var v1) (FD_Var v2)) = same      v1 v2
addFD (FD_Less (FD_Var v1) (FD_Var v2)) = v1 .<. v2     
addFD (FD_HasValue (FD_Var v1) i)       = hasValue v1  i
addFD (FD_Eq e1 e2)                     = e1 .==. e2
addFD (FD_NEq e1 e2)                    = e1 ./=. e2 
-- addFD (FD_AllDiff vs)                   = allDifferent (map un_fd vs)
addFD (FD_Dom v (l,u))                  = v `in_range` (l-1,u+1)
addFD (FD_LT (FD_Var v) i)              = do iv <- exprVar $ toExpr i
                                             v .<. iv
addFD (FD_GT (FD_Var v) i)              = do iv <- exprVar $ toExpr i
                                             iv .<. v


(#<) :: (To_FD_Term a, To_FD_Term b) => a -> b -> FD Bool
x #< y =
  do xt <- to_fd_term x
     yt <- to_fd_term y
     addFD (FD_Less xt yt)

in_range :: FD_Term -> (Int,Int) -> FD Bool
in_range x (l,u) =
  do l #< x
     x #< u

all_different = addFD . FD_AllDiff

instance ToExpr FD_Term where
  toExpr (FD_Var v) = toExpr v

fd_domain :: FD_Term -> FD [Int]
fd_domain (FD_Var v)  = do d <- lookup v
                           return $ elems d

fd_objective :: FD FD_Term
fd_objective =
  do s <- get
     return $ FD_Var $ objective s

class To_FD_Term a where
  to_fd_term :: a -> FD FD_Term

instance To_FD_Term FD_Term where
  to_fd_term = return . id

instance To_FD_Term Int where
  to_fd_term i =  newVar i >>= return . FD_Var

instance To_FD_Term Expr  where
  to_fd_term e = unExpr e >>= return . FD_Var

--------------------------------------------------------------------------------

-- The FD monad
newtype FD a = FD { unFD :: StateT FDState Maybe a }
    deriving (Monad, MonadState FDState, MonadPlus)

-- FD variables
newtype FDVar = FDVar { unFDVar :: Int } deriving (Ord, Eq, Show)

type VarSupply = FDVar

data VarInfo = VarInfo
     { delayedConstraints :: FD Bool, domain :: Domain }

instance Show VarInfo where
  show x = show $ domain x

type VarMap = Map FDVar VarInfo

data FDState = FDState
     { varSupply :: VarSupply, varMap :: VarMap, objective :: FDVar }
     deriving Show

instance Eq FDState where
  s1 == s2 = f s1 == f s2
           where f s = head $ elems $ domain $ varMap s ! (objective s) 

instance Ord FDState where
  compare s1 s2  = compare (f s1) (f s2)
           where f s = head $ elems $  domain $ varMap s ! (objective s) 

  -- TOM: inconsistency is not observable within the FD monad
consistentFD :: FD Bool
consistentFD = return True

-- Run the FD monad and produce a lazy list of possible solutions.
runFD :: FD a -> a
runFD fd = fromJust $ evalStateT (unFD fd') initState
           where fd' = fd -- fd' = newVar () >> fd

initState :: FDState
initState = FDState { varSupply = FDVar 0, varMap = Map.empty, objective = FDVar 0 }

-- Get a new FDVar
newVar :: ToDomain a => a -> FD FDVar
newVar d = do
    s <- get
    let v = varSupply s
    put $ s { varSupply = FDVar (unFDVar v + 1) }
    modify $ \s ->
        let vm = varMap s
            vi = VarInfo {
                delayedConstraints = return True,
                domain = toDomain d}
        in
        s { varMap = Map.insert v vi vm }
    return v

newVars :: ToDomain a => Int -> a -> FD [FDVar]
newVars n d = replicateM n (newVar d)

-- Lookup the current domain of a variable.
lookup :: FDVar -> FD Domain
lookup x = do
    s <- get
    return . domain $ varMap s ! x

-- Update the domain of a variable and fire all delayed constraints
-- associated with that variable.
update :: FDVar -> Domain -> FD Bool
update x i = do
    trace (show x ++ " <- " ++ show i)  (return ())
    s <- get
    let vm = varMap s
    let vi = vm ! x
    trace ("where old domain = " ++ show (domain vi)) (return ())
    put $ s { varMap = Map.insert x (vi { domain = i}) vm }
    delayedConstraints vi

-- Add a new constraint for a variable to the constraint store.
addConstraint :: FDVar -> FD Bool -> FD ()
addConstraint x constraint = do
    s <- get
    let vm = varMap s
    let vi = vm ! x
    let cs = delayedConstraints vi
    put $ s { varMap =
        Map.insert x (vi { delayedConstraints = do b <- cs 
                                                   if b then constraint
                                                        else return False}) vm }
 
-- Useful helper function for adding binary constraints between FDVars.
type BinaryConstraint = FDVar -> FDVar -> FD Bool
addBinaryConstraint :: BinaryConstraint -> BinaryConstraint 
addBinaryConstraint f x y = do
    let constraint  = f x y
    b <- constraint 
    when b $ (do addConstraint x constraint
                 addConstraint y constraint)
    return b

-- Constrain a variable to a particular value.
hasValue :: FDVar -> Int -> FD Bool
var `hasValue` val = do
    vals <- lookup var
    if val `member` vals
       then do let i = singleton val
               if (i /= vals) 
                  then update var i
                  else return True
       else return False

-- Constrain two variables to have the same value.
same :: FDVar -> FDVar -> FD Bool
same = addBinaryConstraint $ \x y -> do
    xv <- lookup x
    yv <- lookup y
    let i = xv `intersection` yv
    if not $ Domain.null i
       then whenwhen (i /= xv)  (i /= yv) (update x i) (update y i)
       else return False

whenwhen c1 c2 a1 a2  =
  if c1
     then do b1 <- a1
             if b1 
                then if c2
                        then a2
                        else return True
                else return False 
     else if c2
             then a2
             else return True

-- Constrain two variables to have different values.
different :: FDVar  -> FDVar  -> FD Bool
different = addBinaryConstraint $ \x y -> do
    xv <- lookup x
    yv <- lookup y
    if not (isSingleton xv) || not (isSingleton yv) || xv /= yv
       then whenwhen (isSingleton xv && xv `isSubsetOf` yv)
                     (isSingleton yv && yv `isSubsetOf` xv)
                     (update y (yv `difference` xv))
                     (update x (xv `difference` yv))
       else return False

-- Constrain a list of variables to all have different values.
allDifferent :: [FDVar ] -> FD  ()
allDifferent (x:xs) = do
    mapM_ (different x) xs
    allDifferent xs
allDifferent _ = return ()

-- Constrain one variable to have a value less than the value of another
-- variable.
infix 4 .<.
(.<.) :: FDVar -> FDVar -> FD Bool
(.<.) = addBinaryConstraint $ \x y -> do
    xv <- lookup x
    yv <- lookup y
    let xv' = filterLessThan (findMax yv) xv
    let yv' = filterGreaterThan (findMin xv) yv
    if  not $ Domain.null xv'
        then if not $ Domain.null yv'
                then whenwhen (xv /= xv') (yv /= yv') (update x xv') (update y yv')
	        else return False
        else return False

{-
-- Get all solutions for a constraint without actually updating the
-- constraint store.
solutions :: FD s a -> FD s [a]
solutions constraint = do
    s <- get
    return $ evalStateT (unFD constraint) s

-- Label variables using a depth-first left-to-right search.
labelling :: [FDVar s] -> FD s [Int]
labelling = mapM label where
    label var = do
        vals <- lookup var
        val <- FD . lift $ elems vals
        var `hasValue` val
        return val
-}

dump :: [FDVar] -> FD [Domain]
dump = mapM lookup

newtype Expr = Expr { unExpr :: FD (FDVar) }

class ToExpr a where
    toExpr :: a -> Expr

instance ToExpr FDVar where
    toExpr = Expr . return

instance ToExpr Expr where
    toExpr = id

instance Integral i => ToExpr i where
    toExpr n = Expr $ newVar n

exprVar :: ToExpr a => a -> FD FDVar
exprVar = unExpr . toExpr

-- Add constraint (z = x `op` y) for new var z
addArithmeticConstraint :: (ToExpr a, ToExpr b) =>
    (Domain -> Domain -> Domain) ->
    (Domain -> Domain -> Domain) ->
    (Domain -> Domain -> Domain) ->
    a -> b -> Expr
addArithmeticConstraint getZDomain getXDomain getYDomain xexpr yexpr = Expr $ do
    x <- exprVar xexpr
    y <- exprVar yexpr
    xv <- lookup x
    yv <- lookup y
    z <- newVar (getZDomain xv yv)
    let constraint z x y getDomain = do
        xv <- lookup x
        yv <- lookup y
        zv <- lookup z
        let znew = zv `intersection` (getDomain xv yv)
	trace (show z ++ " before: "  ++ show zv ++ show "; after: " ++ show znew) (return ())
        if not $ Domain.null znew
           then if (znew /= zv) 
                   then update z znew
                   else return True
           else return False
    let zConstraint = constraint z x y getZDomain
        xConstraint = constraint x z y getXDomain
        yConstraint = constraint y z x getYDomain
    addConstraint z xConstraint
    addConstraint z yConstraint
    addConstraint x zConstraint
    addConstraint x yConstraint
    addConstraint y zConstraint
    addConstraint y xConstraint
    return z

infixl 6 .+.
(.+.) :: (ToExpr a, ToExpr b) => a -> b -> Expr
(.+.) = addArithmeticConstraint getDomainPlus getDomainMinus getDomainMinus

infixl 6 .-.
(.-.) :: (ToExpr a, ToExpr b) => a -> b -> Expr
(.-.) = addArithmeticConstraint getDomainMinus getDomainPlus
    (flip getDomainMinus)

infixl 7 .*.
(.*.) :: (ToExpr a, ToExpr b) => a -> b -> Expr
(.*.) = addArithmeticConstraint getDomainMult getDomainDiv getDomainDiv

getDomainPlus :: Domain -> Domain -> Domain
getDomainPlus xs ys = toDomain (zl, zh) where
    zl = findMin xs + findMin ys
    zh = findMax xs + findMax ys

getDomainMinus :: Domain -> Domain -> Domain
getDomainMinus xs ys = toDomain (zl, zh) where
    zl = findMin xs - findMax ys
    zh = findMax xs - findMin ys

getDomainMult :: Domain -> Domain -> Domain
getDomainMult xs ys = toDomain (zl, zh) where
    zl = minimum products
    zh = maximum products
    products = [x * y |
        x <- [findMin xs, findMax xs],
        y <- [findMin ys, findMax ys]]

getDomainDiv :: Domain -> Domain -> Domain
getDomainDiv xs ys = toDomain (zl, zh) where
    zl = minimum quotientsl
    zh = maximum quotientsh
    quotientsl = [if y /= 0 then x `div` y else minBound |
        x <- [findMin xs, findMax xs],
        y <- [findMin ys, findMax ys]]
    quotientsh = [if y /= 0 then x `div` y else maxBound |
        x <- [findMin xs, findMax xs],
        y <- [findMin ys, findMax ys]]

infix 4 .==.
(.==.) :: (ToExpr a, ToExpr b) => a -> b -> FD Bool
xexpr .==. yexpr = do
    x <- exprVar xexpr
    y <- exprVar yexpr
    x `same` y

infix 4 ./=.
(./=.) :: (ToExpr a, ToExpr b) => a -> b -> FD Bool
xexpr ./=. yexpr = do
    x <- exprVar xexpr
    y <- exprVar yexpr
    x `different` y
