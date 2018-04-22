{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE OverlappingInstances #-}


module Control.Search.Memo where

import Control.Monatron.Monatron hiding (Abort, L, state, cont)
import Control.Monatron.Zipper hiding (i,r)
import Control.Monatron.IdT
import Control.Monatron.MonadInfo

import Data.List (sort, nub, sortBy)
import Data.Maybe (fromJust)
import Data.Map (Map)
import qualified Data.Map as Map

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.SStateT

data MemoKey  = MemoKey { memoFn :: String, memoInfo :: Maybe Info, memoStack :: Maybe String, memoExtra :: Maybe (Map Int String), memoStatement :: Maybe Statement, memoParams :: [String] }
  deriving (Eq, Ord)

data MemoValue = MemoValue { memoId :: Int, memoCode :: Statement, memoUsed :: Int, memoFields :: [(String,String)] }

data MemoInfo = MemoInfo { memoMap :: Map MemoKey MemoValue 
                         , memoCount :: Int
                         , memoRead :: Map Int String
                         }

initMemoInfo = MemoInfo { memoMap = Map.empty
                        , memoCount = 0
                        , memoRead = Map.empty
                        }

newtype MemoT m a = MemoT { unMemoT :: SStateT MemoInfo m a }
  deriving (MonadT,StateM MemoInfo,FMonadT)

instance MonadInfoT MemoT where
  tminfo x = miInc "MemoT" (minfo $ runMemoT x)

-- runMemoT :: Monad m => MemoT m a -> m (a,[(String,Statement,[(String,String)])])
runMemoT m = do (Tup2 a s) <- runSStateT initMemoInfo (unMemoT m)
                return (a, {- map (\(key,val) -> ( memoFn key ++ show (memoId val)
                                              , comment (" fn=" ++ memoFn key ++ " stack='" ++ show (memoStack key) ++ "' extra='" ++ show (memoExtra key) ++ "' used: " ++ show (memoUsed val)) >>> memoCode val
                                              , memoFields key
                                              )
                                 ) $ -} sortBy (\(ka,va) (kb,vb) -> compare (memoId va) (memoId vb)) $ Map.toList (memoMap s)
                       )

-- runReaderMemoT :: (ReaderM r m, ReaderMemoM r (MemoT m)) => MemoT m a -> m (a,[(String,Statement,Info)])
-- runReaderMemoT m = do val <- ask
--                      runMemoT (memoLocal (const val) m)

class Monad m => MemoM m where
  getMemo :: m MemoInfo 
  setMemo :: MemoInfo -> m ()

instance Monad m => MemoM (MemoT m) where
  getMemo  = MemoT $ get 
  setMemo  = MemoT . put

instance (MemoM m, FMonadT t) => MemoM (t m) where
  getMemo = lift $ getMemo
  setMemo = lift . setMemo

