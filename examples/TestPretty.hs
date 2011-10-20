{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.CP.FD.Example

model :: ExampleModel ModelInt
model i = exists $ \col -> do
  [a,b,c,d] <- colList col 4
  forall col (@>0)
  forall col (@<=10)
--  loopall (1,4) $ \(x :: ModelInt) -> (xfold (+) (cte 0) (xlist [col!x,col!(4-x)]) @== 5)
  loopall (1,4) $ \i -> i*(col!(i-1)) @<= 100
  allDiff col
  sorted col
  xfold (+) (cte 0) col @= i
  return col

main = example_sat_main_single_expr model

