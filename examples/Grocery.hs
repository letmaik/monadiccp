{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

-- A kid goes into a grocery store and buys four items. The cashier charges $7.11. 
-- The kid pays and is about to leave when the cashier calls the kid back, and says 
-- "Hold on, I multiplied the four items instead of adding them; I'll try again... 
-- Gosh, with adding them the price still comes to $7.11"! What were the prices of 
-- the four items?

import Control.CP.FD.Example

model :: ExampleModel ()
model _ = exists $ \col -> do
  [a,b,c,d] <- colList col 4
  sorted col
  allin col (cte 0,cte 711)
  a+b+c+d @= 711
  (a*b)*(c*d) @= 711000000
  return col

main = example_sat_main_void model
