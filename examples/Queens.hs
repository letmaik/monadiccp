{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

model :: ExampleModel ModelInt
model n = exists $ \p -> do
  size p @= n
  p `allin` (cte 0,n-1)
  allDiff p
  loopall (cte 0,n-2) $ \i -> do
    loopall (i+1,n-1) $ \j -> do
      (p!i) + i @/= (p!j) + j
      (p!i) - i @/= (p!j) - j
  return p

main = example_sat_main_single_expr model

