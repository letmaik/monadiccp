{-# LANGUAGE ScopedTypeVariables #-}

module Control.Monatron.Transformer (
  StateT, stateT, runStateT,
  WriterT, writerT, runWriterT,
  ReaderT, readerT, runReaderT,
  ExcT, excT, runExcT,
  ContT, contT, runContT,
  StepT, stepT, runStepT, caseStepT, unfoldStepT,
  ListT, listT, runListT, foldListT, collectListT, emptyL, appendL,
--  module Monatron.Operations,
  module Control.Monatron.MonadT,
  module Data.Monoid
) where

--import Monatron.Operations
import Control.Monad.Fix
import Control.Monatron.MonadT
-- for Writer
import Data.Monoid hiding ((<>))
-- for Error (and Reader?)
--import Monatron.Codensity
import Control.Monatron.AutoInstances()

--State Monad Transformer
newtype StateT s m a = S { unS :: s -> m (a,s) }

stateT ::  (s -> m (a, s)) -> StateT s m a
stateT = S

runStateT :: s -> StateT s m a -> m (a,s) 
runStateT s m = unS m s

instance MonadT (StateT s) where
    lift  m           = S $ \s -> m >>= \a -> return (a,s)
    m `tbind` k       = S $ \s -> unS m s >>= \ ~(a, s') -> unS (k a) s'

instance (MonadFix m) => MonadFix (StateT s m) where
  mfix f  = S $ \s -> mfix (runStateT s . f . fst)

instance FMonadT (StateT s) where
    tmap' d1 _d2 g f (S m) = S (f . fmapD d1 (\(x,s) -> (g x,s)) . m)

instance MMonadT (StateT s) where
    flift t          = S (\s -> fmap (\a -> (a,s)) t)
    monoidalT (S t)  = S (\s -> Comp $ fmap (\(S t',s') -> t' s') (t s))

{-
-- StateT implementation of operations
withStateT :: Monad m => Fop (With s) (StateT s m)
withStateT (With f)  = S $ \s  -> runStateT s (f s)

makeStateT :: Monad m => Fop (Make s) (StateT s m)
makeStateT (Make (m,s)) = S $ \_ -> runStateT s m
-}

--------------------------------------------------------------
-- Writer Monad Transformer

newtype WriterT w m a = W {unW :: m (a,w) } 

writerT :: (Monoid w, Monad m) => m (a,w) -> WriterT w m a
writerT = W

runWriterT :: (Monoid w) => WriterT w m a -> m (a,w)
runWriterT = unW
                 
instance Monoid w => MonadT (WriterT w) where  
    tbind (W m) f  = W (do  (a,w) <- m
                            (a',w') <- unW (f a)
                            return (a',w `mappend` w'))
    lift m         = W (liftM (\a -> (a,mempty)) m)

{-
instance (MonadFix m, Monoid w) => MonadFix (WriterT w m) where
    mfix f = W $ mfix (unW. f) 
-}

instance Monoid w => FMonadT (WriterT w) where
    tmap' d1 _d2 g f  = W . f . fmapD d1 (\(x,s) -> (g x,s)) . unW

instance Monoid w => MMonadT (WriterT w) where
    flift t          = W (fmap (\a -> (a,mempty)) t)
    monoidalT (W t)  = W $ Comp $  fmap (\(W t',w) -> 
                                   fmap (\(a,w') -> (a,w `mappend` w')) t') $ t

{-
-- WriterT implementation of operations
withWriterT :: (Monoid w, Monad m) => Fop (With w) (WriterT w m)
withWriterT (With c)   = W $ S $ \w -> runWriterT (c w)


makeWriterT :: (Monoid w, Monad m) => Fop (Make w) (WriterT w m)
makeWriterT (Make (m, w)) = writerT $ runWriterT m >>= \(a,w') -> 
                            return (a,w' `mappend` w)
-}
--------------------------------------------------------------
-- Reader Monad Transformer
newtype ReaderT s m a = R { unR :: s -> m a }

runReaderT      :: s -> ReaderT s m a -> m a
runReaderT s m  = unR m s

instance MonadT (ReaderT s) where
    tbind m k  = R (\s -> unR m s >>= \a -> unR (k a) s)
    lift  m    = R (\_ -> m)

readerT :: Monad m => (e -> m a) -> ReaderT e m a
readerT = R

{-
instance (MonadFix m) => MonadFix (ReaderT w m) where
    mfix f = R $ mfix (unR. f) 
-}

instance FMonadT (ReaderT s) where
    tmap' d1 _d2 g f (R m) = R (f . fmapD d1 g . m)

instance MMonadT (ReaderT s) where
    flift t          = R (\_ -> t)
    monoidalT (R t)  = R (\s -> Comp $ fmap (($ s) . unR) (t s))

{-
-- ReaderT implementation of operations
makeReaderT :: Monad m => Fop (Make e) (ReaderT e m)
makeReaderT = R . makeStateT . fmap unR

withReaderT :: Monad m => Fop (With e) (ReaderT e m)
withReaderT = R . withStateT . fmap unR
-}
--------------------------------------------------------------
-- Exceptions Monad Transformer
newtype ExcT x m a = X {unX :: m (Either x a)}

excT :: Monad m => m (Either x a) -> ExcT x m a
excT = X

runExcT :: Monad m => ExcT x m a -> m (Either x a)
runExcT = unX
--
instance (MonadFix m) => MonadFix (ExcT x m) where
  mfix f  = X $ mfix (unX . f . fromRight)
    where fromRight (Right a) = a
          fromRight _         = error "ExceptionT: mfix looped."


--
instance MonadT (ExcT x) where
    lift m           = X (liftM Right m)
    (X m) `tbind` f  = X (do a <- m
                             case a of
                                Left x  -> return (Left x)
                                Right b -> unX (f b))


instance FMonadT (ExcT x) where
    tmap' d1 _d2 g f  = X . f . fmapD d1 func . unX where
      func (Left x)   = Left x
      func (Right y)  = Right (g y)

{-
-- internal operations
throwExcT :: Monad m => Fop (Throw x) (ExcT x m)
throwExcT (Throw x) = X $ return (Left x)
--
handleExcT :: Monad m => Fop (Handle x) (ExcT x m)
handleExcT (Handle (m, h)) = X (unX m >>= \exa ->
                                    case exa of
                                      Left x  -> unX (h x)
                                      Right a -> return (Right a))

-- Instances of the operations for IO exceptions
throwIO :: Fop (Throw IO.SomeException) IO
throwIO (Throw x) = IO.throwIO x
--
handleIO :: Fop (Handle IO.SomeException) IO
handleIO (Handle (m, h)) = IO.catch m h
-}

--------------------------------------------------------------
-- Continuations Monad Transformer

newtype ContT r m a = C {unC :: (a -> m r) -> m r}

runContT :: (a -> m r) -> ContT r m a -> m r
runContT = flip unC

contT ::  ((a -> m r) -> m r) -> ContT r m a
contT = C

instance MonadT (ContT r) where
    lift m = C (m >>=)
    m `tbind` k   = C $ \c -> unC m (\a -> unC (k a) c)

{-
callCCContT :: Monad m => Fop (CallCC (m r)) (ContT r m)
callCCContT (CallCC f) = C $ \k -> unC (f (\a -> unC a k)) k

abortContT :: Monad m => Fop (Abort (m r)) (ContT r m)
abortContT (Abort mr) = C $ \_ -> mr
-}
--------------------------------------------------------------
-- List monad transformer

data LSig f a b = NilT b
                | ConsT a (f a)

newtype ListT m a = L {unL :: m (LSig (ListT m) a ())}

runListT :: ListT m a -> m (LSig (ListT m) a ())
runListT = unL

listT :: m (LSig (ListT m) a ()) -> ListT m a
listT = L

emptyL :: Monad m => ListT m a
emptyL = L $ return $ NilT ()

appendL :: Monad m=> ListT m a -> ListT m a -> ListT m a
appendL (L m1) (L m2) = L $ do
            l <- m1
            case l of
              NilT ()    -> m2
              ConsT a l1 -> return (ConsT a (appendL l1 (L m2)))

foldListT :: Monad m => (a -> m b -> m b) -> m b -> ListT m a -> m b
foldListT c n (L m) = do l <- m 
                         case l of 
                            NilT ()    -> n 
                            ConsT a l1 -> c a (foldListT c n l1)

collectListT :: Monad m => ListT m a -> m [a]
collectListT lt = foldListT (\a m -> m >>= return. (a:)) (return []) lt

instance MonadT ListT where
    lift m       = L $ liftM (`ConsT` emptyL) m
    m `tbind` f  = L $ foldListT (\a l -> unL $ f a `appendL` L l)
                                 (return $ NilT ())
                                 m

instance FMonadT ListT where
    tmap' d1 d2 g t (L m) = L $ t $ fmapD d1 (\lsig  -> case lsig of
                                            NilT ()    -> NilT ()
                                            ConsT a l  -> ConsT (g a) (tmap' d1 d2 g t l)) m

{-
mZeroListT :: Monad m => Fop MZero (ListT m)
mZeroListT (MZero _) = emptyL 

mPlusListT :: (Monad m) => Fop MPlus (ListT m)
mPlusListT (MPlus (a, b)) = appendL a b
-}
------------------------------------------------
-- Step Monad Transformer
------------------------------------------------
      
newtype StepT f m x = T {runT :: m (Either x (f (StepT f m x)))}

stepT :: m (Either x (f (StepT f m x))) -> StepT f m x
stepT = T

runStepT :: StepT f m x ->  m (Either x (f (StepT f m x)))
runStepT = runT

{-
instance (Functor f, Monad m) => Monad (StepT f m) where
    return  = treturn
    (>>=)   = tbind
-}

--instance (Functor f, Monad m) => Functor (StepT f m) where fmap = liftM

caseStepT            ::  (Functor f, Monad m) =>  
                         (a -> StepT f m x) -> (f (StepT f m a) -> StepT f m x)
                         -> StepT f m a -> StepT f m x
caseStepT v c (T m)  = T (m >>= either (runT . v) (runT . c))

unfoldStepT      :: (Functor f, Monad m) => (y -> m (Either x (f y))) -> y -> StepT f m x
unfoldStepT k y  = T (liftM (fmap (fmap (unfoldStepT k))) (k y))

instance (Functor f) => MonadT (StepT f) where
    tbind t f  = caseStepT f (T . return . Right . fmap (`tbind` f)) t
    lift       = T . liftM Left

instance (Functor f) => FMonadT (StepT f) where
    tmap' d1 d2 g t (T m) = T (t (fmapD d1 (either (Left . g) (Right . fmap (tmap' d1 d2 g t))) m))
