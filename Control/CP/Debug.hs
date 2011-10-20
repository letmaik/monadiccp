{-# LANGUAGE CPP #-}

module Control.CP.Debug (
  debug
) where

import Debug.Trace

#ifdef DEBUG
debug = trace
#else
debug = flip const
#endif
