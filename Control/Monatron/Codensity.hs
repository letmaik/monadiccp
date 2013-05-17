{-# OPTIONS -XRank2Types #-}

module Control.Monatron.Codensity (
 Codensity,
 codensity,
 runCodensity
) where

import Control.Monatron.MonadT
import Control.Monad.Fix
import Control.Monatron.AutoInstances()

----------------------------------------------------------
-- Codensity Monad
----------------------------------------------------------

newtype Codensity f a = Codensity { 
      unCodensity :: forall b. (a -> f b) -> f b 
}

codensity :: (forall b. (a -> f b) -> f b) -> Codensity f a
codensity = Codensity

runCodensity :: Monad m => Codensity m a -> m a
runCodensity c = unCodensity c return 

instance MonadT Codensity where
    lift m        = Codensity (m >>=)
    c `tbind` f   = Codensity (\k -> unCodensity c (\a -> unCodensity (f a) k))

-- still need to prove that MonadFix laws hold
instance MonadFix m => MonadFix (Codensity m) where
    mfix f = Codensity $ \k -> mfix (runCodensity. f) >>= k

------------------------

