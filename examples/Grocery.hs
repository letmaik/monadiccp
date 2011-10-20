-- A kid goes into a grocery store and buys four items. The cashier charges $7.11. 
-- The kid pays and is about to leave when the cashier calls the kid back, and says 
-- "Hold on, I multiplied the four items instead of adding them; I'll try again... 
-- Gosh, with adding them the price still comes to $7.11"! What were the prices of 
-- the four items?

import Control.CP.FD.Example.Example
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.SearchTree

main = example_main_void model

model :: FDModel
model =
  exist 4 $ \list@[a,b,c,d] -> 
      list `allin` (0,711) /\
      a + b + c + d @= 711 /\
      (a * b) * (c * d) @= 711*100*100*100 /\
      sorted list /\
      return list
