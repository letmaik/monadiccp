{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example
import Control.CP.SearchTree
import Control.CP.Solver
import Control.CP.FD.Interface

model :: ExampleModel ModelInt
model n =
  exists $ \x -> do
  exists $ \y -> do
    let xy = x @++ y
    size x @= n
    size y @= n
    x `allin` (cte 1,2*n)
    y `allin` (cte 1,2*n)
    sSorted x
    sSorted y
    (x!cte 0) @< (y!cte 0)
    allDiff xy
    let sx = xmap (\v -> v*v) x
    let sy = xmap (\v -> v*v) y
    xsum x @=  xsum y
    xsum sx @= xsum sy
    let t1 = 2*n*(2*n+1) `div` 4
    let t2 = 2*n*(2*n+1)*(4*n+1) `div` 12
    xsum x @= t1
    xsum y @= t1
    xsum sx @= t2
    xsum sy @= t2
    return xy

main = example_sat_main_single_expr model

