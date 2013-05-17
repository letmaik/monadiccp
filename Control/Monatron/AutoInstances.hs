{-# OPTIONS
  -XFlexibleInstances
  -XOverlappingInstances
#-}

module Control.Monatron.AutoInstances where

import Control.Monatron.MonadT

------------------------------------------------------------------
instance (Monad m, MonadT t) => Monad (t m) where
    return = treturn
    fail   = lift . fail
    (>>=)  = tbind

instance (Monad m, MonadT t) => Functor (t m) where fmap = liftM
