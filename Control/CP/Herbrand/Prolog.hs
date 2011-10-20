{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.CP.Herbrand.Prolog 
 ( Prolog
 , module Control.CP.Herbrand.PrologTerm
 , PConstraint (..) 
 ) where 

import Control.Monad (zipWithM)

import Control.CP.Solver
import Control.CP.Herbrand.Herbrand
import Control.CP.Herbrand.PrologTerm

-- Prolog Solver

newtype Prolog a  = Prolog { runProlog :: Herbrand PrologTerm a }
  deriving Monad

instance Solver Prolog where
  type Constraint Prolog  = PConstraint 
  type Label      Prolog  = Label (Herbrand PrologTerm)
  add     = addProlog
  mark    = Prolog $ mark
  goto    = Prolog . goto
  run     = run . runProlog

instance Term Prolog PrologTerm where
  newvar  = Prolog $ newvar
  type Help Prolog PrologTerm = ()
  help _ _ = ()

data PConstraint = PrologTerm := PrologTerm
                 | NotFunctor PrologTerm String 
                 | PrologTerm :/= PrologTerm

addProlog :: PConstraint -> Prolog Bool
addProlog (x := y)          = Prolog (unify x y)
addProlog (x :/= y)          = Prolog (diff x y)
addProlog (NotFunctor x f)  = Prolog (notFunctor x f)

notFunctor :: PrologTerm -> String -> Herbrand PrologTerm Bool
notFunctor x f  = do t <- shallow_normalize x
                     case t of
                       PVar _    ->
                         registerAction t (notFunctor t f) >> success
                       PTerm g _ ->
                         if g == f then failure
                                   else success

diff :: PrologTerm -> PrologTerm -> Herbrand PrologTerm Bool
diff x y  =
  do x' <- shallow_normalize x
     y' <- shallow_normalize y
     b <- diff' x' y'
     case b of
       DYes        -> success
       DNo         -> failure
       DMaybe vars -> mapM (\v -> registerAction v (diff x y)) vars >> success
 

  where diff' x@(PVar v1) (PVar v2)  =
          if v1 == v2 then return $ DNo
                      else return $ DMaybe [x]
        diff' x@(PVar _) (PTerm _ _) =
          return $ DMaybe [x]
        diff' (PTerm _ _) y@(PVar _) =
          return $ DMaybe [y]
        diff' (PTerm f xs) (PTerm g ys) 
          | x /= y                  = return $ DYes
          | length xs /= length ys  = return $ DYes        
          | otherwise               =
              do xs' <- mapM shallow_normalize xs
                 ys' <- mapM shallow_normalize ys
                 bs  <- zipWithM diff' xs' ys'
                 return $ foldr dand DYes bs
                            
data DiffBool  = DYes | DNo | DMaybe [PrologTerm]

dand DNo         _          = DNo
dand _          DNo         = DNo
dand (DMaybe x) (DMaybe y)  = DMaybe (x ++ y)
dand DYes       x           = x
dand x          DYes        = x

