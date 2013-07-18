{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

main = example_sat_main_single_expr model

model :: ExampleModel ModelInt
model n = exists $ \col -> do
  size col @= n
  loopall (0,(n-1)) $ \i -> do
    let v0 = col ! i
        v1 = col ! ((i+1) `mod` n)
        v2 = col ! ((i+2) `mod` n)
    2 * v1 @= 2 * v2 - v0
    v0 @: (cte (-10), cte 10)
  return col


