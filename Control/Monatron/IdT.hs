module Control.Monatron.IdT  where 

import Control.Monatron.Monatron

newtype IdT m a = IdT { runIdT :: m a }

instance MonadT IdT where
    lift         = IdT
    tbind m f    = IdT $ runIdT m >>= runIdT . f 
    
instance FMonadT IdT where
    tmap' d1 _d2 g f       = IdT . f . fmapD d1 g . runIdT

