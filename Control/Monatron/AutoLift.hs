{-# OPTIONS
  -XFlexibleInstances
  -XMultiParamTypeClasses
  -XFunctionalDependencies
  -XUndecidableInstances
  -XOverlappingInstances
#-}

--  -XOverlappingInstances

module Control.Monatron.AutoLift (
 StateM(..), get,put,
 WriterM (..), tell,
 ReaderM(..), ask,local,
 ExcM(..), throw,handle,
 ContM(..), callCC,
 ListM(..), mZero,mPlus,
 module Control.Monatron.Operations
) where

import Control.Monatron.Operations
import Control.Exception (SomeException)


------------------------------------------------------------------
-- State
class Monad m => StateM z m | m -> z where
    stateModel :: AlgModel (StateOp z) m

instance Monad m => StateM z (StateT z m) where
    stateModel = modelStateT

instance (StateM z m, MonadT t) => StateM z (t m) where
    stateModel = liftAlgModel stateModel

get :: StateM z m => m z
get = getX stateModel

put :: StateM z m => z -> m ()
put = putX stateModel

------------------------------------------------------------------
-- Traces
class (Monoid z, Monad m) => WriterM z m | m -> z where
    writerModel :: AlgModel (WriterOp z) m

instance (Monoid z, Monad m) => WriterM z (WriterT z m) where
    writerModel = modelWriterT

instance (Monoid z, WriterM z m, MonadT t) => WriterM z (t m) where
    writerModel = liftAlgModel writerModel

tell :: (Monoid z, WriterM z m) => z -> m ()
tell z = traceX writerModel z

------------------------------------------------------------------
-- Environments
class Monad m => ReaderM z m | m -> z where
    readerModel :: Model (ReaderOp z) m

instance Monad m => ReaderM z (ReaderT z m) where
    readerModel = modelReaderT

instance (ReaderM z m, Functor m, FMonadT t) => ReaderM z (t m) where
    readerModel = liftModel readerModel

ask :: ReaderM z m => m z
ask = askX readerModel

local :: ReaderM z m => (z -> z) -> m a -> m a
local = localX readerModel

------------------------------------------------------------------
-- Throw and Handle
class Monad m => ExcM z m | m -> z where
    throwModel :: AlgModel (ThrowOp z) m
    handleModel :: Model (HandleOp z) m

instance Monad m => ExcM z (ExcT z m) where
    throwModel = modelThrowExcT
    handleModel = modelHandleExcT

instance ExcM SomeException IO where
    throwModel  = modelThrowIO
    handleModel = modelHandleIO

instance (ExcM z m, Functor m, FMonadT t) => ExcM z (t m) where
    throwModel = liftAlgModel throwModel
    handleModel = liftModel handleModel

throw :: ExcM z m => z -> m a
throw = throwX throwModel

handle :: ExcM z m => m a -> (z -> m a) -> m a
handle = handleX handleModel

------------------------------------------------------------------
-- callCC operation

class Monad m => ContM r m | m -> r where
    contModel :: AlgModel (ContOp r) m

instance Monad m => ContM (m r) (ContT r m) where
    contModel = modelContT

instance (ContM r m, MonadT t) => ContM r (t m) where
    contModel = liftAlgModel contModel

callCC :: ContM r m => ((a -> r) -> a) -> m a
callCC = callCCX contModel

------------------------------------------------------------------
-- MPlus operations

class Monad m => ListM m where
    listModel :: AlgModel ListOp m

instance Monad m => ListM (ListT m) where
    listModel = modelListT

instance (ListM m, MonadT t) => ListM (t m) where
    listModel = liftAlgModel listModel

mZero :: (ListM m) => m a
mZero = zeroListX listModel

mPlus :: ListM m => m a -> m a -> m a
mPlus = plusListX listModel
