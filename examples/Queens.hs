{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

noattack i j qi qj = do
  qi        @/=  qj
  qi  +  i  @/=  qj  +  j
  qi  -  i  @/=  qj  -  j

model :: ExampleModel ModelInt
model n = exists $ \p -> do
  size p @= n
  p `allin` (cte 0,n-1)
  allDiff p
  loopall (cte 0,n-2) $ \i -> 
    loopall (i+1,n-1) $ \j ->
      noattack i j (p!i) (p!j)
  return p

main = example_sat_main_single_expr model

