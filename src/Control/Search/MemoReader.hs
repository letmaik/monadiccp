{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.Search.MemoReader where

import Control.Search.Memo

import Data.Map (Map)
import qualified Data.Map as Map

import Control.Monatron.Monatron hiding (Abort, L, state, cont)
import Control.Monatron.Zipper hiding (i,r)
import Control.Monatron.MonadInfo
import Control.Monatron.IdT

newtype MemoReaderT r m a = MemoReaderT { unMemoReaderT :: Int -> ReaderT r m a }

instance MonadT (MemoReaderT r) where
  lift m = MemoReaderT $ const $ lift m
  tbind (MemoReaderT i) f = MemoReaderT (\n -> i n `tbind` (\r -> unMemoReaderT (f r) n))

instance MonadInfoT (MemoReaderT r) where
  tminfo x = miInc "MemoReaderT" (minfo $ runReaderT undefined (unMemoReaderT x 0))

instance FMonadT (MemoReaderT s) where
  tmap' d1 d2 g f (MemoReaderT m) = MemoReaderT (tmap' d1 d2 g f . m)

memoReaderT :: MemoM m => (e -> Int -> m a) -> MemoReaderT e m a
memoReaderT f = MemoReaderT (\n -> readerT (\e -> f e n))

deMemoReaderT :: MemoM m => e -> Int -> MemoReaderT e m a -> m a
deMemoReaderT e i (MemoReaderT f) = runReaderT e (f i)

runMemoReaderT :: (MemoM m, Show s) => s -> MemoReaderT s m a -> m a
runMemoReaderT s r = 
  do x1 <- getMemo
     let l = Map.size (memoRead x1)
     setMemo x1 { memoRead = Map.insert l (show s) $ memoRead x1 }
     r <- deMemoReaderT s l r
     x2 <- getMemo
     setMemo x2 { memoRead = Map.delete l $ memoRead x2 }
     return r

modelMemoReaderT :: (Show s, MemoM m) => Model (ReaderOp s) (MemoReaderT s m)
modelMemoReaderT (Ask g)     = memoReaderT (\s n -> deMemoReaderT s n (g s))
modelMemoReaderT (InEnv s a) = memoReaderT (\_ n -> deMemoReaderT s n (do { m1 <- getMemo
                                                                          ; let oldVal = memoRead m1 Map.! n
                                                                          ; setMemo m1 { memoRead = Map.insert n (show s) (memoRead m1) }
                                                                          ; x <- a
                                                                          ; m2 <- getMemo
                                                                          ; setMemo m2 { memoRead = Map.insert n oldVal (memoRead m2) }
                                                                          ; return x
                                                                          }
                                                                      )
                                           )

instance (MemoM m, Show s) => ReaderM s (MemoReaderT s m) where
  readerModel = modelMemoReaderT

