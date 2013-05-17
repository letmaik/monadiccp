{-# OPTIONS -fglasgow-exts -XNoMonomorphismRestriction #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}

module Control.Monatron.Zipper where

import Control.Monatron.MonadT ()
import Control.Monatron.IdT ()
import Control.Monatron.AutoLift 
import Control.Monatron.Operations
import Control.Monatron.Monad ()
-- import Monatron.AutoInstances()

newtype (t1 :> (t2 :: (* -> *) -> * -> *)) m a = L { runL :: t1 (t2 m) a }

runZipper :: (t1 :> t2) m a -> t1 (t2 m) a
runZipper = runL

zipper :: t1 (t2 m) a -> (t1 :> t2) m a 
zipper = L

-- * Relative Navigation

-- | shift focus to left
leftL  :: (t1 :> t2) m a -> t1 (t2 m) a
leftL   = runL

-- | shift focus to right
rightL :: t1 (t2 m) a -> (t1 :> t2) m  a
rightL  =  L 

-- The zipper is an FMonadT and a MonadT

instance (FMonadT t1, FMonadT t2) => FMonadT (t1 :> t2) where
     tmap' d1 d2 g f       = 
       L . tmap' (FunctorD (mtmap d1)) (FunctorD (mtmap d2)) g (tmap' d1 d2 id f) . runL

instance (MonadT t1, MonadT t2) => MonadT (t1 :> t2) where
     lift         = L . lift . lift
     tbind m f    = L $ runL m >>= runL . f
     
-- Instances of the zipper for the various effects
     
instance (Monad m, MonadT t1, MonadT t2, StateM z (t2 m)) => StateM z ((t1 :> t2) m) where
     stateModel = L . liftAlgModel stateModel
     
instance (WriterM z (t2 m), MonadT t1, Monad m, MonadT t2) => WriterM z ((t1 :> t2) m) where
     writerModel  = L . liftAlgModel writerModel

instance (ReaderM z (t2 m), FMonadT t1, FMonadT t2, Functor (t2 m), Monad m) => 
         ReaderM z ((t1 :> t2) m) where     
      readerModel  = L . liftModel readerModel . fmap runL 
      
instance (ExcM z (t2 m), FMonadT t1, FMonadT t2, Functor (t2 m), Monad m) => 
         ExcM z ((t1 :> t2) m) where
    throwModel  = L . liftAlgModel throwModel
    handleModel = L . liftModel handleModel . fmap runL 
    
instance (ContM r (t2 m), FMonadT t1, FMonadT t2, Functor (t2 m), Monad m) => 
         ContM r ((t1 :> t2) m) where
    contModel = L . liftAlgModel contModel
    
instance (ListM (t2 m), FMonadT t1, FMonadT t2, Functor (t2 m), Monad m) => 
         ListM ((t1 :> t2) m) where
    listModel = L . liftAlgModel listModel
    
-- runtest :: (((),Int),Int)
-- runtest = runState 0 $ runStateT 0 $ runZipper (put 3)

-- Views and masks; could be in a different file
    
data (:><:) m n = View {
  to    :: forall a . m a -> n a,
  from  :: forall a . n a -> m a
}

i :: m :><: m
i = View id id

o :: (Monad m, MonadT t1, MonadT t2) => t1 (t2 m) :><: (t1 :> t2) m
o = View rightL leftL

vlift  :: (FMonadT t, Functor m, Functor n) 
       => (m :><: n) -> (t m :><: t n)
vlift v  = View (tmap (to v)) (tmap (from v))


hcomp :: (n :><: o) -> (m :><: n) -> (m :><: o)
v2 `hcomp` v1  =  View  (to v2 . to v1) (from v1 . from v2)

vcomp  :: (Functor m1, Functor m2, FMonadT t) 
       => (t m2 :><: m3) -> (m1 :><: m2) -> (t m1 :><: m3)
v2 `vcomp` v1  = v2 `hcomp` (vlift v1)

-- program :: StateM Int m => m Int
-- program = put 3 >> return 4

-- t = runState 1 $ runStateT 0 $ runIdT $ runIdT $ view i program

r :: Monad m => StateT s m :><: ReaderT s m
r  = View  {
  to    = \s -> readerT (\e -> liftM fst $ runStateT e s),
  from  = \e -> stateT (\s ->  liftM (\x -> (x,s)) $ runReaderT s e)
}

stateIso  :: Monad m => (s1 -> s2) -> (s2 -> s1) -> StateT s1 m :><: StateT s2 m
stateIso f fm1 = View  {to = iso f fm1, from = iso fm1 f } where 
  iso g h m = stateT $ \s2 -> do  (a, s1) <- runStateT (h s2) m
                                  return (a, g s1)
                                  
getv :: StateM s n => (m :><: n) -> m s
getv var  = from var get 

putv :: StateM s n => (m :><: n) -> s -> m ()
putv var  = from var . put
