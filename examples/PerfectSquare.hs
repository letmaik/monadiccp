{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

model :: ExampleModel ModelCol
model c = do
  let numSquares = c!0
      totalSize = c!1
      s = slice c ((cte 2) @.. (1+numSquares))
  exists $ \pos -> do
    size pos @= 2*numSquares
    let x i = pos!i
        y i = pos!(i+numSquares)
    pos `allin` (cte 0,totalSize-1)
    loopall (0,numSquares-1) $ \i -> do
      x i @<= totalSize - (s!i)
      y i @<= totalSize - (s!i)
    loopall (0,numSquares-1) $ \i ->
      loopall (i+1,numSquares-1) $ \j -> ((x i)+(s!i) @<= (x j)) @|| ((x j)+(s!j) @<= (x i)) @|| ((y i)+(s!i) @<= (y j)) @|| ((y j)+(s!j) @<= (y i))
--  loopall (0,totalSize-1) $ \c -> do
--    totalSize @= xsum (xmap (\i -> (s!i)*channel((x i) @: (c-(s!i)+1,c))) ((cte 0) @.. (numSquares-1)))
--    totalSize @= xsum (xmap (\i -> (s!i)*channel((y i) @: (c-(s!i)+1,c))) ((cte 0) @.. (numSquares-1)))
    return pos

main = example_sat_main_coll_expr model
