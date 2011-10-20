{-# LANGUAGE OverlappingInstances #-}

import Control.CP.FD.Example.Example
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.SearchTree

main = example_main_single model

model n = exist n $ \list -> do
  allin list (0,n-1)
  let dlist = zipWith (\a b -> abs $ a-b) (take (n-1) list) (tail list)
  allin dlist (1,n-1)
  allDiff list
  allDiff dlist
  (list!!0) @< (list!!1)
  (dlist!!0) @> (dlist!!(n-2))
  return list
