{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}

import Control.CP.FD.Example

model :: ExampleModel ModelInt
model num = do
  let spc = spec num
      width = (spc!  cte 0)
      height = (spc! cte 1) 
      board0 = (slice spc (cte 2 @.. (width*height+1))) @++ (list [cte $ -1])
      brd = slice board0 $ xmap (\i -> ((i @% (width+1)) @= width) @? (width*height,width*(i @/ (width+1))+(i @% (width+1)))) (cte 0 @.. ((width+1)*height-1))
  exists $ \board -> do
    board @= brd
    exists $ \ps -> do
      size ps @= 56
      let p1 i = ps!(2*i)
          p2 i = ps!(2*i+1)
          posdiffs = list [1,width+1]
      exists $ \x -> do
        size x @= (width+1)*height
        loopall (0,height-1) $ \i -> x!(i*(width+1)+width) @= cte 28
        loopall (0,6) $ \i ->
          loopall (i,6) $ \j -> do
            let dc = j-i+((1+17*i-(i+1)*(i+1)) `div` 2)
                diff = abs $ (p1 dc) - (p2 dc)
            diff @: posdiffs
            (j @= i) @?? (p1 dc @< p2 dc,true)
            board!(p1 dc) @= i
            board!(p2 dc) @= j
            x!(p1 dc) @= dc
            x!(p2 dc) @= dc
      return ps

main = example_sat_main_single_expr model

specs :: ModelCol
specs = list 
  [
      8,7,
      2,1,0,3,0,4,5,5,
      6,2,0,6,3,1,4,0,
      3,2,3,6,2,5,4,3,
      5,4,5,1,1,2,1,2,
      0,0,1,5,0,5,4,4,
      4,6,2,1,3,6,6,1,
      4,2,0,6,5,3,3,6,

      8,7,
      5,1,2,4,6,2,0,5,
      6,6,4,3,5,0,1,5,
      2,0,4,0,4,0,5,0,
      6,1,3,6,3,5,4,3,
      3,1,0,1,2,2,1,4,
      3,6,6,2,4,0,5,4,
      1,3,6,1,2,3,5,2,

      8,7,
      4,4,5,4,0,3,6,5,
      1,6,0,1,5,3,4,1,
      2,6,2,2,5,3,6,0,
      1,3,0,6,4,4,2,3,
      3,5,5,2,4,2,2,1,
      2,1,3,3,5,6,6,1,
      5,1,6,0,0,0,4,0,

      8,7,
      3,0,2,3,3,4,4,3,
      6,5,3,4,2,0,2,1,
      6,5,1,2,3,0,2,0,
      4,5,4,1,6,6,2,5,
      4,3,6,1,0,4,5,5,
      1,3,2,5,6,0,0,1,
      0,5,4,6,2,1,6,1,

      8,7,
      4,1,5,2,4,4,6,2,
      2,5,6,1,4,6,0,2,
      6,5,1,1,0,1,4,3,
      6,2,1,1,3,2,0,6,
      3,6,3,3,5,5,0,5,
      3,0,1,0,0,5,4,3,
      3,2,4,5,4,2,6,0,

      8,7,
      4,1,2,1,0,2,4,4,
      5,5,6,6,0,4,6,3,
      6,0,5,1,1,0,5,3,
      3,4,2,2,0,3,1,2,
      3,6,5,6,1,2,3,2,
      2,5,0,6,6,3,3,5,
      4,1,0,0,4,1,4,5
  ]

spec n = slice specs ((58*n) @.. (58*(n+1)))
