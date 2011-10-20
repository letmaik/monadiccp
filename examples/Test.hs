{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

model :: ExampleModel ()
model _ = exists $ \arr -> do
  arr `allin` (cte 0,cte 10)
  size arr @= 4
  xsum arr @= 10
  xsum (xmap (\x -> x*x) arr) @= 30
  sorted arr
  return arr

main = example_sat_main_void model
