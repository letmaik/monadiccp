{-# LANGUAGE FlexibleInstances #-}
-- {-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TypeOperators #-}

module Control.Monatron.MonadInfo (
  MInfo(..), MonadInfo(minfo), MonadInfoT(tminfo),
  miInc
) where

import Control.Monatron.Monad
import Control.Monatron.MonadT
import Control.Monatron.IdT
import Control.Monatron.Transformer
import Control.Monatron.Zipper
import Control.Monatron.Codensity

import Data.Map (Map)
import qualified Data.Map as Map

newtype MInfo = MInfo (Map String Int)
  deriving (Show, Eq, Ord)

miBase = MInfo Map.empty

miInc s (MInfo m) = MInfo $ Map.alter (\x -> case x of { Nothing -> Just 1; Just n -> Just (n+1) }) s m

undef :: a
undef = error "MonadInfo: undefined"

class Monad m => MonadInfo m where
  minfo :: m a -> MInfo

class MonadT t => MonadInfoT t where
  tminfo :: MonadInfo m => t m a -> MInfo

instance MonadInfoT (StateT s) where
  tminfo x = miInc "StateT" (minfo $ runStateT (undef :: s) x)

instance Monoid w => MonadInfoT (WriterT w) where
  tminfo x = miInc "WriterT" (minfo $ runWriterT x)

instance MonadInfoT (ReaderT s) where
  tminfo x = miInc "ReaderT" (minfo $ runReaderT (undef :: s) x)

instance MonadInfoT (ExcT x) where
  tminfo x = miInc "ExcT" (minfo $ runExcT x)

instance MonadInfoT (ContT x) where
  tminfo x = miInc "ContT" (minfo $ runContT (undef) x)

instance MonadInfoT ListT where
  tminfo x = miInc "ListT" (minfo $ runListT x)

instance Functor f => MonadInfoT (StepT f) where
  tminfo x = miInc "StepT" (minfo $ runStepT x)

instance (MonadInfoT t1, MonadInfoT t2) => MonadInfoT (t1 :> t2) where
  tminfo x = miInc ":>" (minfo $ runZipper x)

instance MonadInfoT Codensity where
  tminfo x = miInc "Codensity" (minfo $ runCodensity x)

instance MonadInfo Id where
  minfo _ = miInc "Id"  miBase

instance MonadInfo Lift where
  minfo _ = miInc "Lift"  miBase

instance MonadInfoT IdT where
  tminfo x = miInc "IdT" (minfo $ runIdT x)

instance (MonadInfo m, MonadInfoT t) => MonadInfo (t m) where
  minfo x = tminfo x

