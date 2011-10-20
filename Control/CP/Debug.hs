{-# LANGUAGE CPP #-}

module Control.CP.Debug (
  debug,
  imdebug
) where

import Debug.Trace

debug :: String -> a -> a
imdebug :: Show a => String -> a -> a

{-# INLINE debug #-}
{-# INLINE imdebug #-}

#ifdef DEBUG
debug = trace
imdebug s a = trace ("imdebug " ++ s ++ ": " ++ (show a)) a
#else
debug = flip const
imdebug = flip const
#endif
