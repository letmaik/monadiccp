{-# OPTIONS -XRank2Types #-}

module Control.Monatron.Operations (
    ExtModel, Model, AlgModel, toAlg, liftModel, liftAlgModel, liftExtModel,                         
    StateOp(..), modelStateT, getX, putX,
    ReaderOp(..), modelReaderT, askX, inEnvX,  localX,     
    WriterOp(..), modelWriterT, traceX,
    ThrowOp(..),HandleOp(..), modelThrowExcT, modelHandleExcT,
    modelThrowIO, modelHandleIO, throwX, handleX,
    ContOp(..), modelContT, callccX, callCCX, abortX,
    StepOp(..), stepX, modelStepT,
    ListOp(..), modelListT, zeroListX, plusListX,
    module Control.Monatron.Transformer
) where

import Control.Monatron.Codensity
import Control.Monatron.Transformer
import qualified Control.Exception as IO (throwIO,catch,SomeException)

-------------------------------------------------
-- Models and Standard Liftings
-------------------------------------------------
      
type ExtModel f g m  = forall a. f (m (g a)) -> m a
type Model f m       = forall a. f (m a) -> m a
type AlgModel f m    = forall a. f a -> m a

toAlg       :: (Functor f, Monad m) => Model f m -> AlgModel f (Codensity m)
toAlg op t  = codensity $ \k ->  op (fmap k t)

liftModel     :: (Functor f, Monad m, Functor m, FMonadT t, Monad (t (Codensity m))) => 
                 Model f m -> Model f (t m)
liftModel op  = tmap runCodensity . join . lift . toAlg op . fmap (tmap lift)

liftAlgModel     :: (MonadT t, Monad m, Functor f) => AlgModel f m -> AlgModel f (t m)
liftAlgModel op  = lift . op

liftExtModel     ::  (  Functor f, Functor g, Monad m, Functor m, 
                        MMonadT t, Functor (t f), Functor (t m)) => 
                     ExtModel f g m -> ExtModel f g (t m)
liftExtModel op  =    tmap (op . fmap deComp . deComp) . 
                      monoidalT . flift . fmap  (monoidalT . fmap flift) 
      
----------------------
-- State Operations
----------------------
      
data StateOp s a = Get (s -> a) | Put s a

instance Functor (StateOp s) where
    fmap f (Get g)    = Get (f . g)
    fmap f (Put s a)  = Put s (f a)

modelStateT            :: Monad m => AlgModel (StateOp s) (StateT s m)
modelStateT (Get g)    = stateT (\s -> return (g s, s))
modelStateT (Put s a)  = stateT (\_ -> return (a, s))

getX     :: Monad m => AlgModel (StateOp s) m -> m s
getX op  = op $ Get id

putX       :: Monad m => AlgModel (StateOp s) m -> s -> m ()
putX op s  = op $ Put s ()
      
----------------------
-- Reader Operations
----------------------
      
data ReaderOp s a = Ask (s -> a) | InEnv s a

instance Functor (ReaderOp s) where
    fmap f (Ask g)      = Ask (f . g)
    fmap f (InEnv s a)  = InEnv s (f a)

modelReaderT              :: Monad m => Model (ReaderOp s) (ReaderT s m)
modelReaderT (Ask g)      = readerT (\s -> runReaderT s (g s))
modelReaderT (InEnv s a)  = readerT (\_ -> runReaderT s a)

askX     :: Monad m => Model (ReaderOp s) m -> m s
askX op  = op $ Ask return

inEnvX         :: Monad m => Model (ReaderOp s) m -> s -> m a -> m a
inEnvX op s m  = op $ InEnv s m 
      
--derived

localX :: Monad m => Model (ReaderOp z) m -> (z -> z) -> m a -> m a
localX m f t = do z <- askX m
                  inEnvX m (f z) t

------------------------
-- Exception Operations
------------------------
      
data ThrowOp x a   = Throw x
data HandleOp x a  = Handle a (x -> a)

instance Functor (ThrowOp x) where
    fmap _ (Throw x) = Throw x

instance Functor (HandleOp x) where
    fmap f (Handle a h) = Handle (f a) (f . h)

modelThrowExcT            :: Monad m => AlgModel (ThrowOp x) (ExcT x m)
modelThrowExcT (Throw x)  = excT (return (Left x))

modelHandleExcT               :: Monad m => Model (HandleOp x) (ExcT x m)
modelHandleExcT (Handle m h)  = excT (runExcT m >>= \exa -> case  exa of
                                                Left x  -> runExcT (h x)
                                                Right a -> return (Right a))

modelThrowIO              :: AlgModel (ThrowOp IO.SomeException) IO
modelThrowIO (Throw x)    = IO.throwIO x

modelHandleIO               :: Model (HandleOp IO.SomeException) IO
modelHandleIO (Handle m h)  = IO.catch m h

throwX       :: Monad m => AlgModel (ThrowOp x) m -> x -> m a
throwX op x  = op $ Throw x

handleX         :: Monad m => Model(HandleOp x) m -> m a -> (x -> m a) -> m a
handleX op m h  = op $ Handle m h
      
------------------------
-- Writer Operations
------------------------
      
data WriterOp w a = Trace w a

instance Functor (WriterOp w) where
    fmap f (Trace w a) = Trace w (f a)

modelWriterT :: (Monad m, Monoid w) => AlgModel (WriterOp w) (WriterT w m)
modelWriterT (Trace w a)  = writerT (return (a,w))

traceX       :: (Monad m) => AlgModel (WriterOp w) m -> w -> m ()
traceX op w  = op $ Trace w ()
      
--------------------------
-- Continuation Operations
--------------------------
      
data ContOp r a = Abort r | CallCC ((a -> r) -> a)

instance Functor (ContOp r) where
    fmap _ (Abort r)      = Abort r
    fmap f (CallCC k)     = CallCC (\c -> f (k (c . f)))

modelContT             :: Monad m => AlgModel (ContOp (m r)) (ContT r m)
modelContT (Abort mr)  = contT $ \_ -> mr
modelContT (CallCC k)  = contT $ \c -> c (k c)

abortX       :: Monad m => AlgModel (ContOp r) m -> r -> m a
abortX op r  = op (Abort r)

callCCX       :: Monad m => AlgModel (ContOp r) m -> ((a -> r) -> a) -> m a
callCCX op f  = op (CallCC f)

callccX       :: Monad m => AlgModel (ContOp r) m -> ((a -> m b) -> m a) -> m a
callccX op f  =  join $ callCCX op (\k -> f (\x -> abortX op (k (return x))))  
      
--------------------------
-- Step Operations
--------------------------
      
newtype StepOp f x = StepOp (f x)

instance (Functor f) => Functor (StepOp f) where 
    fmap h (StepOp fa) = StepOp (fmap h fa)

modelStepT              :: (Functor f, Monad m) => Model (StepOp f) (StepT f m)
modelStepT (StepOp fa)  = stepT (return (Right fa))

stepX     :: (Monad m) => Model (StepOp f) m -> f (m x) -> m x
stepX op  = op . StepOp 
  
--------------------------
-- List Operations
--------------------------
      
data ListOp a = ZeroList | PlusList a a

instance Functor ListOp where
    fmap _ ZeroList        = ZeroList
    fmap f (PlusList a b)  = PlusList (f a) (f b)

modelListT               :: Monad m => AlgModel ListOp (ListT m)
modelListT ZeroList        = emptyL
modelListT (PlusList t u)  = appendL (return t) (return u)

zeroListX         :: Monad m => AlgModel ListOp m -> m a
zeroListX op      = op ZeroList

plusListX         :: Monad m => AlgModel ListOp m -> m a -> m a -> m a
plusListX op t u  = join $ op (PlusList t u)

