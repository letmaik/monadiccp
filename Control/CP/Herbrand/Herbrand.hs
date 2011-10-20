{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternGuards #-}
-- |This module provides a Herbrand solver.
--
--  The type of terms is parameterized by the "HTerm" type class.
module Control.CP.Herbrand.Herbrand (
  HTerm(..),
  Herbrand(..),
  failure,
  success,
  unify,
  shallow_normalize,
  registerAction,
  HState,
  Unify,
  initState,
  addH,
  newvarH
) where 

import Control.Monad.State.Lazy
import Control.Applicative

import Data.Map

import Control.CP.Solver

-- |Herbrand terms

-- type VarId = Int

class Ord (VarId t) => HTerm t where
  type VarId t :: *
  data VarSupply t :: *
  varSupply :: VarSupply t
  supplyVar :: VarSupply t -> (t, VarSupply t)
  mkVar    :: VarId t -> t
  isVar    :: t   -> Maybe (VarId t)
  children :: t -> ([t], [t] -> t)
  nonvar_unify
        :: (MonadState (HState t m) m) => t -> t -> m Bool

-- |Herbrand monad

data Herbrand t a = Herbrand { unH :: State (HState t (Herbrand t)) a }

instance Monad (Herbrand t) where
  return x  = Herbrand $ return x
  m >>=  f  = Herbrand $ unH m >>= unH . f

instance MonadState (HState t (Herbrand t)) (Herbrand t) where
  get  = Herbrand $ get
  put  = Herbrand . put

instance Functor (Herbrand t) where
  fmap f fa  = fa >>= return . f 

instance Applicative (Herbrand t) where
  pure         = return
  (<*>) ff fa  = do f <- ff 
                    a <- fa
	            return $ f a

-- |State

type Heap t m   = Map (VarId t) (Binding t m)

data Binding t m 
  = VAR (VarId t)	-- ^ indirection to other variable
  | NONVAR t 		-- ^ bound to term
  | ACTION (m Bool)	-- ^ attributed variable, with given action

data HState t m = HState { var_supply :: VarSupply t
                         , heap       :: Heap t m
                         }

updateState :: (HTerm t, MonadState (HState t m) m) => (HState t m -> HState t m) -> m ()
updateState f = get >>= put . f

-- |Solver instance 

instance HTerm t => Solver (Herbrand t) where
  type Constraint (Herbrand t)  = Unify t 
  type Label      (Herbrand t)  = HState t (Herbrand t)
  add     = addH
  mark    = get
  goto    = put
  run     = flip evalState initState . unH

instance HTerm t => Term (Herbrand t) t where
  newvar  = newvarH
  type Help (Herbrand t) t = ()
  help _ _ = ()

initState :: HTerm t => HState t m
initState = HState varSupply Data.Map.empty

-- New variable

newvarH :: (HTerm t,MonadState (HState t m) m) => m t
newvarH = do state <- get
             let vs = var_supply state
             let (var,vs') = supplyVar vs
             put state{var_supply = vs'}
             return  var

{- Representatin of variables
   --------------------------

   Each variable is represented by
   * a VarId
   * a possible Binding on the Heap
       - if there is a binding, then the variable's meaning 
         is that of the binding
       - if there is no binding, then variable's meaning is 
         that of an unbound variable

-}

-- Unification

data Unify t = t `Unify` t

addH :: (HTerm t, MonadState (HState t m) m) => Unify t -> m Bool
addH (Unify t1 t2) = unify t1 t2

-- | unify two arbitrary terms
unify :: (HTerm t, MonadState (HState t m) m) => t -> t -> m Bool
unify t1 t2 = 
  do nt1 <- shallow_normalize t1
     nt2 <- shallow_normalize t2
     case (isVar nt1, isVar nt2) of
       (Just v1, Just v2) 
          | v1 == v2      -> success
	  | otherwise     -> bindv v1 v2
       (Just v1, Nothing) -> bindt v1 nt2
       (Nothing, Just v2) -> bindt v2 nt1
       (Nothing, Nothing) -> nonvar_unify nt1 nt2

success, failure :: Monad m => m Bool
success  = return True
failure  = return False
m1 `andM` m2  = m1 >>= \b -> if b then m2 else return b 

-- | bind a variable to a term
bindt :: (HTerm t, MonadState (HState t m) m) => VarId t -> t -> m Bool
bindt v t  = do r <- lookupVar v
                updater v (NONVAR t)
                case r of
		  Just (ACTION action) -> action
                  Nothing              -> success

-- | alias one variable to another
bindv :: (HTerm t, MonadState (HState t m) m) => VarId t -> VarId t -> m Bool
bindv v1 v2  = do r1 <- lookupVar v1
                  r2 <- lookupVar v2
                  case (r1,r2) of
                    (Just (ACTION a1), Just (ACTION a2)) 
				      -> let r3 = noACTION
                                         in do updater v1 r3
                                               updater v2 r3
				               a1 `andM` a2
                    (Just _, Nothing) -> updater v1 (VAR v2) >> success
                    (Nothing, Just _) -> updater v2 (VAR v1) >> success
                    (Nothing,Nothing) -> updater v1 (VAR v2) >> success

             where noACTION = ACTION success

updater v  r  = updateState $ \state -> state{heap = insert v r (heap state)}

lookupVar v  = do state <- get
                  return $ Data.Map.lookup v (heap state)

-- Actions

registerAction :: (HTerm t, MonadState (HState t m) m) => t -> m Bool -> m ()
registerAction t action  =
  do nt <- shallow_normalize t
     case isVar nt of
       Just v  ->
         do r <- lookupVar v
            case r of
              Nothing          -> updater v (ACTION action)
              Just (ACTION a1) -> updater v (ACTION (a1 `andM` action))
       Nothing -> return ()

-- TODO: unregister action?

-- Normalization

shallow_normalize :: (HTerm t, MonadState (HState t m) m) => t -> m t
shallow_normalize t  = gnormalize return t

normalize :: (HTerm t, MonadState (HState t m) m) => t -> m t
normalize t          = gnormalize nvnormalize t
  where nvnormalize t  =  let (ts,mkt)  = children t
                          in mapM normalize ts >>= return . mkt

gnormalize nvnormalize t
  | Just v <- isVar t  = vnormalize v
  | otherwise          = nvnormalize t
  where vnormalize v   = do state <- get
                            case Data.Map.lookup v (heap state) of
                              Just (VAR v')   -> vnormalize v'
                              Just (NONVAR t) -> nvnormalize t
                              _               -> return $ mkVar v
