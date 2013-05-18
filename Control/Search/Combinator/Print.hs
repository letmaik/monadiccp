{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

module Control.Search.Combinator.Print (prt,dbg) where

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Generator

import Control.Monatron.IdT

printLoop :: [String] -> MkEval m
printLoop lst super = return $ commentEval $ super
                       { returnH = \i -> returnE super $ i `onCommit` Print (space i) lst
                       , toString = "print(" ++ toString super ++ ")"
                       }

debugLoop :: Evalable m => String -> MkEval m
debugLoop str super = return $ commentEval $ super
                 { initH = \i -> return (DebugOutput str) @>>>@ initH super i
                 , toString = "debug(" ++ show str ++ "," ++ toString super ++ ")"
                 }

prt :: [String] -> Search
prt l = 
  Search { mkeval     = printLoop l
         , runsearch  = runIdT
         }

dbg :: String -> Search
dbg str = 
  Search { mkeval     = debugLoop str
         , runsearch  = runIdT
         }
