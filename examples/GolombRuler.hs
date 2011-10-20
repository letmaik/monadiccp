{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

model :: ExampleMinModel ModelInt
model n =
  exists $ \m -> do
    size m @= n
    m `allin` (cte 0,n*n)
    let dn = (n*n-n) `div` 2
    exists $ \d -> do
      size d @= dn
      d `allin` (cte 0,n*n)
      let diag i j = d ! (((i*(2*n-i-1)) `div` 2) + j - i - 1)
      m!(cte 0) @= cte 0
      loopall (cte 1,n-1) $ \j -> do
        diag 0 j @= m!j
      loopall (cte 1,n-2) $ \i ->
        loopall (i+1,n-1) $ \j -> do
          diag i j @= (m!j) - (m!i)
      loopall (cte 0,n-1) $ \i ->
        loopall (i+1,n-1) $ \j -> do
          diag i j @>= (j-i)*(j-i+1) `div` 2
      diag 0 1 @<= diag (n-2) (n-1)
      allDiff d
    sSorted m
    return (m!(n-1),m)

main = example_min_main_single_expr model
