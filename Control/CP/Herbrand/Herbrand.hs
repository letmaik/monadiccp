{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
module Control.CP.Herbrand.Herbrand where 

import Control.Monad.State.Lazy
import Control.Applicative

import Data.Map

import Control.CP.Solver

-- Herbrand terms

type VarId = Int

class HTerm t where
  mkVar    :: VarId -> t
  isVar    :: t   -> Maybe VarId
  children :: t -> ([t], [t] -> t)
  nonvar_unify
        :: t -> t -> Herbrand t Bool

-- Herbrand monad

newtype Herbrand t a = Herbrand { unH :: State (HState t) a }
  deriving (Monad, MonadState (HState t))

instance Functor (Herbrand t) where
  fmap f fa  = fa >>= return . f 


instance Applicative (Herbrand t) where
  pure         = return
  (<*>) ff fa  = do f <- ff 
                    a <- fa
	            return $ f a

type Subst t = Map VarId t

data HState t = HState {var_supply :: VarId
                       ,subst      :: Subst t
                       }

updateState :: HTerm t => (HState t -> HState t) -> Herbrand t ()
updateState f = get >>= put . f

-- Solver instance 

instance HTerm t => Solver (Herbrand t) where
  type Term       (Herbrand t)  = t
  type Constraint (Herbrand t)  = Unify t 
  type Label      (Herbrand t)  = HState t
  newvarSM  = newvarH
  addSM     = addH
  markSM    = get
  gotoSM    = put
  runSM     = flip evalState initState . unH

initState = HState 0 Data.Map.empty

-- New variable

newvarH :: HTerm t => Herbrand t t
newvarH = do state <- get
             let varid = var_supply state
             put state{var_supply = varid + 1}
             return $ mkVar varid

-- Unification

data Unify t = t `Unify` t

addH (Unify t1 t2) = unify t1 t2

unify :: HTerm t => t -> t -> Herbrand t Bool
unify t1 t2 = 
  do nt1 <- shallow_normalize t1
     nt2 <- shallow_normalize t2
     case (isVar nt1, isVar nt2) of
       (Just v1, Just v2) 
          | v1 == v2      -> success
       (Just v1, _      ) -> bind v1 nt2 >> success
       (_      , Just v2) -> bind v2 nt1 >> success
       (_      , _      ) -> nonvar_unify nt1 nt2

success, failure :: HTerm t => Herbrand t Bool
success  = return True
failure  = return False

bind :: HTerm t => VarId -> t -> Herbrand t ()
bind v t  = updateState $ \state -> state{subst = insert v t (subst state)}

-- Normalization

shallow_normalize :: HTerm t => t -> Herbrand t t
shallow_normalize t
  | Just v <- isVar t    
     = do state <- get
          case Data.Map.lookup v (subst state) of
            Just t' -> shallow_normalize t'
            Nothing -> return t 
  | otherwise  
     = return t

normalize :: HTerm t => t -> Herbrand t t
normalize t
  | Just v <- isVar t  = do state <- get
                            case Data.Map.lookup v (subst state) of
                              Just t' -> normalize t'
                              Nothing -> return t
  | otherwise          = let (ts,mkt)  = children t
                         in pure mkt <*> mapM normalize ts
