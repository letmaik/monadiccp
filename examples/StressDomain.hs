{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

main = example_sat_main_single_expr model

model :: ExampleModel ModelInt
model n = exists $ \col -> do
  l <- colList col 5
  col `allin` (cte 0, cte 5*n)
  let revCol = list (reverse l)
      colP   = list [0,2,4]
  forall revCol $ \v ->
    forall colP $ \p -> 
      loopall (0,5*n) $ \j ->
        v @/= 5*j+p
  loopall (0,5*(n `div` 2)) $ \j ->
    forall revCol $ \v -> do
       v @>= 5*j
       v @<= 5*(j+5*(n `div` 2))
  return col
