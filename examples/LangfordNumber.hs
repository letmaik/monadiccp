{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

model :: ExampleModel ModelCol
model c = do
  let n = c!0
      k = c!1
  exists $ \y -> do
    size y @= k*n
    y `allin` (cte 1,n)
    exists $ \p -> do
      size p @= k*n
      p `allin` (cte 0,k*n-1)
      loopall (cte 0,n-1) $ \i ->
        loopall (cte 0,k-2) $ \j ->
          p!(i*k+j) + i+2 @= p!(i*k+j+1)
      allDiffD p
      loopall (cte 0,n-1) $ \i ->
        loopall (cte 0,k-1) $ \j ->
          y!(p!(i*k+j)) @= i+1
    y!0 @< y!(n*k-1)
    return y

main = example_sat_main_coll_expr model

