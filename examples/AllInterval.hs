{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

-- diffList: the differences between successive elements of a list
diffList l = exists $ \d -> do     -- request a (collection) variable d
  let n = size l                   -- introduce n as alias for size l
  size d @= n-1                    -- size of d must be one less than l
  loopall (0,n-2) $ \i -> do       -- for each i in [0..n-2]
    d!i @= abs (l!i - l!(i+1))     -- d[i] = abs(l[i]-l[i+1])
  return d                         -- and return d to the caller

model :: ExampleModel ModelInt     -- type signature
model n =                          -- function 'model' takes argument n
  exists $ \x -> do                -- request a (collection) variable x
    size x @= n                    -- whose size must be n
    d <- diffList x                -- d becomes the diffList of x
    x `allin` (cte 0,n-1)          -- all x elements are in [0..n-1]
    d `allin` (cte 1,n-1)          -- all d elements are in [1..n-1]
    allDiff x                      -- all x elements are different
    allDiff d                      -- all d elements are different
    x @!! 0 @< x @!! 1             -- some symmetry breaking
    d @!! 0 @> d ! (n-2)           -- some symmetry breaking
    return x                       -- return the list itself

main = example_sat_main_single_expr model

