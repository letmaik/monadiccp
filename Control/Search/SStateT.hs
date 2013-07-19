{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Control.Search.SStateT (
  SStateT, sstateT, runSStateT,
  Tup2(..), snd2, fst2
) where

import Control.Monad.Fix
import Control.Monatron.MonadT
import Control.Monatron.AutoInstances ()
import Control.Monatron.Operations
import Control.Monatron.AutoLift

data Tup2 a b = Tup2 a !b

fst2 (Tup2 a _) = a
snd2 (Tup2 _ b) = b

newtype SStateT s m a = SS { unSS :: s -> m (Tup2 a s) }

sstateT ::  (s -> m (Tup2 a s)) -> SStateT s m a
sstateT = SS

runSStateT :: s -> SStateT s m a -> m (Tup2 a s) 
runSStateT s m = unSS m s

instance MonadT (SStateT s) where
    lift  m           = SS $ \s -> m >>= \a -> return (Tup2 a s)
    m `tbind` k       = SS $ \s -> unSS m s >>= \ ~(Tup2 a s') -> unSS (k a) s'

instance (MonadFix m) => MonadFix (SStateT s m) where
  mfix f  = SS $ \s -> mfix (runSStateT s . f . fst2)

instance FMonadT (SStateT s) where
    tmap' d1 _d2 g f (SS m) = SS (f . fmapD d1 (\(Tup2 x s) -> (Tup2 (g x) s)) . m)

instance MMonadT (SStateT s) where
    flift t           = SS (\s -> fmap (\a -> (Tup2 a s)) t)
    monoidalT (SS t)  = SS (\s -> Comp $ fmap (\(Tup2 (SS t') s') -> t' s') (t s))

instance Monad m => StateM z (SStateT z m) where
    stateModel = modelSStateT

modelSStateT            :: Monad m => AlgModel (StateOp s) (SStateT s m)
modelSStateT (Get g)    = sstateT (\s -> return (Tup2 (g s) s))
modelSStateT (Put s a)  = sstateT (\_ -> return (Tup2 a s))
