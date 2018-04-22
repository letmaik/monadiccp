{-# Language FlexibleInstances #-}
{-# language OverlappingInstances #-}
{-# language IncoherentInstances #-}

module Control.Monatron.AutoInstances where

import Control.Monatron.MonadT

------------------------------------------------------------------
instance (Monad m, MonadT t) => Monad (t m) where
    return = pure
    fail   = lift . fail
    (>>=)  = tbind

instance (Monad m, MonadT t) => Functor (t m) where fmap = liftM

instance (Monad m, MonadT t) => Applicative (t m) where
  pure = treturn
  (<*>) = ap
