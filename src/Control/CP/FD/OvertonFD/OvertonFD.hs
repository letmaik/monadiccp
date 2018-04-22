{- 
 - Origin:
 -      Constraint Programming in Haskell 
 -      http://overtond.blogspot.com/2008/07/pre.html
 -      author: David Overton, Melbourne Australia
 -
 - Modifications:
 -      Monadic Constraint Programming
 -      http://www.cs.kuleuven.be/~toms/Haskell/
 -      Tom Schrijvers
 -} 

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.CP.FD.OvertonFD.OvertonFD (
  OvertonFD,
  fd_objective,
  fd_domain,
  FDVar,
  OConstraint(..),
  lookup,
) where

import Prelude hiding (lookup)
import Data.Maybe (fromJust,isJust)
import Control.Monad.State.Lazy
import Control.Monad.Trans
import qualified Data.Map as Map
import Data.Map ((!), Map)
import Control.Monad (liftM,(<=<))

import Control.CP.FD.OvertonFD.Domain as Domain
import Control.CP.FD.FD hiding ((!))
import Control.CP.Solver
import Control.CP.SearchTree
import Control.CP.EnumTerm

import Control.CP.Debug

--------------------------------------------------------------------------------
-- Solver instance -------------------------------------------------------------
--------------------------------------------------------------------------------

data OConstraint =
    OHasValue FDVar Int
  | OSame FDVar FDVar
  | ODiff FDVar FDVar
  | OLess FDVar FDVar
  | OLessEq FDVar FDVar
  | OAdd FDVar FDVar FDVar
  | OSub FDVar FDVar FDVar
  | OMult FDVar FDVar FDVar
  | OAbs FDVar FDVar
  deriving (Show,Eq)

instance Solver OvertonFD where
  type Constraint OvertonFD  = OConstraint
  type Label      OvertonFD  = FDState
  add c         = debug ("addOverton("++(show c)++")") $ addOverton c
  run p         = debug ("runOverton") $ runOverton p
  mark  = get
  goto  = put 

instance Term OvertonFD FDVar where
  newvar        = newVar ()
  type Help OvertonFD FDVar = ()
  help _ _ = ()

instance EnumTerm OvertonFD FDVar where
  type TermBaseType OvertonFD FDVar = Int
  getDomain = fd_domain
  setValue var val = return [var `OHasValue` val]

--------------------------------------------------------------------------------
-- Constraints -----------------------------------------------------------------
--------------------------------------------------------------------------------

addOverton (OHasValue v i) = v `hasValue` i
addOverton (OSame a b) = a `same` b
addOverton (ODiff a b) = a `different` b
addOverton (OLess a b) = a .<. b
addOverton (OLessEq a b) = a .<=. b
addOverton (OAdd a b c) = addSum a b c
addOverton (OSub a b c) = addSub a b c
addOverton (OMult a b c) = addMult a b c
addOverton (OAbs a b) = addAbs a b

fd_domain :: FDVar -> OvertonFD [Int]
fd_domain v = do d <- lookup v
                 return $ elems d

fd_objective :: OvertonFD FDVar
fd_objective =
  do s <- get
     return $ objective s

--------------------------------------------------------------------------------

-- The FD monad
newtype OvertonFD a = OvertonFD { unFD :: State FDState a }
    deriving (Monad, Applicative, Functor, MonadState FDState)

-- FD variables
newtype FDVar = FDVar { unFDVar :: Int } deriving (Ord, Eq, Show)

type VarSupply = FDVar

data VarInfo = VarInfo
     { delayedConstraints :: OvertonFD Bool, domain :: Domain }

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

  -- TOM: inconsistency is not observable within the OvertonFD monad
consistentFD :: OvertonFD Bool
consistentFD = return True

-- Run the FD monad and produce a lazy list of possible solutions.
runOverton :: OvertonFD a -> a
runOverton fd = 
  let j = evalState (unFD fd) initState
      in j

initState :: FDState
initState = FDState { varSupply = FDVar 0, varMap = Map.empty, objective = FDVar 0 }

-- Get a new FDVar
newVar :: ToDomain a => a -> OvertonFD FDVar
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

newVars :: ToDomain a => Int -> a -> OvertonFD [FDVar]
newVars n d = replicateM n (newVar d)

-- Lookup the current domain of a variable.
lookup :: FDVar -> OvertonFD Domain
lookup x = do
    s <- get
    return . domain $ varMap s ! x

-- Update the domain of a variable and fire all delayed constraints
-- associated with that variable.
update :: FDVar -> Domain -> OvertonFD Bool
update x i = do
    debug (show x ++ " <- " ++ show i)  (return ())
    s <- get
    let vm = varMap s
    let vi = vm ! x
    debug ("where old domain = " ++ show (domain vi)) (return ())
    put $ s { varMap = Map.insert x (vi { domain = i}) vm }
    delayedConstraints vi

-- Add a new constraint for a variable to the constraint store.
addConstraint :: FDVar -> OvertonFD Bool -> OvertonFD ()
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
type BinaryConstraint = FDVar -> FDVar -> OvertonFD Bool
addBinaryConstraint :: BinaryConstraint -> BinaryConstraint 
addBinaryConstraint f x y = do
    let constraint  = f x y
    b <- constraint 
    when b $ (do addConstraint x constraint
                 addConstraint y constraint)
    return b

-- Constrain a variable to a particular value.
hasValue :: FDVar -> Int -> OvertonFD Bool
var `hasValue` val = do
    vals <- lookup var
    if val `member` vals
       then do let i = singleton val
               if (i /= vals) 
                  then update var i
                  else return True
       else return False

-- Constrain two variables to have the same value.
same :: FDVar -> FDVar -> OvertonFD Bool
same = addBinaryConstraint $ \x y -> do 
    debug "inside same" $ return ()
    xv <- lookup x
    yv <- lookup y
    debug (show xv ++ " same " ++ show yv) $ return ()
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
different :: FDVar  -> FDVar  -> OvertonFD Bool
different = addBinaryConstraint $ \x y -> do
    xv <- lookup x
    yv <- lookup y
    if not (isSingleton xv) || not (isSingleton yv) || xv /= yv
       then whenwhen (isSingleton xv && xv `isSubsetOf` yv)
                     (isSingleton yv && yv `isSubsetOf` xv)
                     (update y (yv `difference` xv))
                     (update x (xv `difference` yv))
       else return False

-- Constrain one variable to have a value less than the value of another
-- variable.
infix 4 .<.
(.<.) :: FDVar -> FDVar -> OvertonFD Bool
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

-- Constrain one variable to have a value less than or equal to the value of another 
-- variable.
infix 4 .<=.
(.<=.) :: FDVar -> FDVar -> OvertonFD Bool
(.<=.) = addBinaryConstraint $ \x y -> do
    xv <- lookup x
    yv <- lookup y
    let xv' = filterLessThan (1 + findMax yv) xv
    let yv' = filterGreaterThan ((findMin xv) - 1) yv
    if  not $ Domain.null xv'
        then if not $ Domain.null yv'
                then whenwhen (xv /= xv') (yv /= yv') (update x xv') (update y yv')
                else return False
        else return False

{-
-- Get all solutions for a constraint without actually updating the
-- constraint store.
solutions :: OvertonFD s a -> OvertonFD s [a]
solutions constraint = do
    s <- get
    return $ evalStateT (unFD constraint) s

-- Label variables using a depth-first left-to-right search.
labelling :: [FDVar s] -> OvertonFD s [Int]
labelling = mapM label where
    label var = do
        vals <- lookup var
        val <- OvertonFD . lift $ elems vals
        var `hasValue` val
        return val
-}

dump :: [FDVar] -> OvertonFD [Domain]
dump = mapM lookup

-- Add constraint (z = x `op` y) for var z
addArithmeticConstraint :: 
    (Domain -> Domain -> Domain) ->
    (Domain -> Domain -> Domain) ->
    (Domain -> Domain -> Domain) ->
    FDVar -> FDVar -> FDVar -> OvertonFD Bool
addArithmeticConstraint getZDomain getXDomain getYDomain x y z = do
    xv <- lookup x
    yv <- lookup y
    let constraint z x y getDomain = do
        xv <- lookup x
        yv <- lookup y
        zv <- lookup z
        let znew = debug "binaryArith:intersection" $ (debug "binaryArith:zv" $ zv) `intersection` (debug "binaryArith:getDomain" $ getDomain xv yv)
        debug ("binaryArith:" ++ show z ++ " before: "  ++ show zv ++ show "; after: " ++ show znew) (return ())
        if debug "binaryArith:null?" $ not $ Domain.null (debug "binaryArith:null?:znew" $ znew)
           then if (znew /= zv) 
                   then debug ("binaryArith:update") $ update z znew
                   else return True
           else return False
    let zConstraint = debug "binaryArith: zConstraint" $ constraint z x y getZDomain
        xConstraint = debug "binaryArith: xConstraint" $ constraint x z y getXDomain
        yConstraint = debug "binaryArith: yConstraint" $ constraint y z x getYDomain
    debug ("addBinaryArith: z x") (return ())
    addConstraint z xConstraint
    debug ("addBinaryArith: z y") (return ())
    addConstraint z yConstraint
    debug ("addBinaryArith: x z") (return ())
    addConstraint x zConstraint
    debug ("addBinaryArith: x y") (return ())
    addConstraint x yConstraint
    debug ("addBinaryArith: y z") (return ())
    addConstraint y zConstraint
    debug ("addBinaryArith: y x") (return ())
    addConstraint y xConstraint
    debug ("addBinaryArith: done") (return ())
    return True

-- Add constraint (z = op x) for var z
addUnaryArithmeticConstraint :: (Domain -> Domain) -> (Domain -> Domain) -> FDVar -> FDVar -> OvertonFD Bool
addUnaryArithmeticConstraint getZDomain getXDomain x z = do
    xv <- lookup x
    let constraint z x getDomain = do
        xv <- lookup x
        zv <- lookup z
        let znew = zv `intersection` (getDomain xv)
        debug ("unaryArith:" ++ show z ++ " before: "  ++ show zv ++ show "; after: " ++ show znew) (return ())
        if not $ Domain.null znew
           then if (znew /= zv) 
                   then update z znew
                   else return True
           else return False
    let zConstraint = constraint z x getZDomain
        xConstraint = constraint x z getXDomain
    addConstraint z xConstraint
    addConstraint x zConstraint
    return True

addSum = addArithmeticConstraint getDomainPlus getDomainMinus getDomainMinus

addSub = addArithmeticConstraint getDomainMinus getDomainPlus (flip getDomainMinus)

addMult = addArithmeticConstraint getDomainMult getDomainDiv getDomainDiv

addAbs = addUnaryArithmeticConstraint absDomain (\z -> mapDomain z (\i -> [i,-i]))

getDomainPlus :: Domain -> Domain -> Domain
getDomainPlus xs ys = toDomain (zl, zh) where
    zl = findMin xs + findMin ys
    zh = findMax xs + findMax ys

getDomainMinus :: Domain -> Domain -> Domain
getDomainMinus xs ys = toDomain (zl, zh) where
    zl = findMin xs - findMax ys
    zh = findMax xs - findMin ys

getDomainMult :: Domain -> Domain -> Domain
getDomainMult xs ys = (\d -> debug ("multDomain" ++ show d ++ "=" ++ show xs ++ "*" ++ show ys ) d) $ toDomain (zl, zh) where
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
