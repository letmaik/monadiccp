
module Control.Monatron.Monad (
  State, Writer, Reader, Exception, Cont,
  state,writer,reader,exception,cont,
  runState, runWriter, runReader, runException, runCont,
  Id(..), Lift(..)
) where
  

import Control.Monatron.Transformer
import Control.Monad
import Control.Monad.Fix

newtype Id a   = Id {runId :: a}
data    Lift a = L  {runLift :: a}

type State s      = StateT s Id
type Writer w     = WriterT w Id
type Reader r     = ReaderT r Id
type Exception x  = ExcT x Id
type Cont r       = ContT r Id

state :: (s -> (a, s)) -> State s a
state st = stateT $ \s -> Id $ st s

runState :: s -> State s a -> (a,s)
runState s = runId. runStateT s

writer :: Monoid w => (a,w) -> Writer w a
writer = writerT . Id

runWriter :: Monoid w => Writer w a -> (a,w)
runWriter = runId. runWriterT

reader :: (r -> a) -> Reader r a
reader e = readerT $ \r -> Id (e r)

runReader :: r -> Reader r a -> a
runReader r = runId . runReaderT r

exception :: Either x a -> Exception x a
exception = excT . Id

runException :: Exception x a -> Either x a
runException = runId. runExcT

cont :: ((a -> r) -> r) -> Cont r a
cont c = contT $ \k -> Id $ c (runId . k)

runCont :: (a -> r) -> Cont r a  -> r
runCont k = runId. runContT (Id. k)

instance Monad Id where
    return  = Id
    fail    = error
    m >>= f = f (runId m)

instance Monad Lift where
  return x  = L x
  fail x    = error x
  L x >>= k = k x

instance Functor Id   where fmap = liftM
instance Functor Lift where fmap = liftM

instance MonadFix Id   where mfix f = let m = f (runId m)   in m
instance MonadFix Lift where mfix f = let m = f (runLift m) in m
