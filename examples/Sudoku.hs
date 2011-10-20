{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

model :: ExampleModel ()
model () = exists $ \mat -> do
  size mat @= 81
  allin mat (cte 1,cte 9)
  let row i = slice mat $ xmap (\p -> i*9+p) (cte 0 @.. cte 8)
  let col i = slice mat $ xmap (\p -> i+9*p) (cte 0 @.. cte 8)
  let block r c = slice mat $ xmap (\p -> 3*c+27*r+p) $ list [0,1,2,9,10,11,18,19,20]
  let pos r c = mat!(r*9+c)
  loopall (cte 0,cte 2) $ \i ->
    loopall (cte 0,cte 2) $ \j -> do
      allDiffD $ row $ i*3+j
      allDiffD $ col $ i*3+j
      allDiffD $ block i j
  pos 0 8 @= cte 2
  pos 1 0 @= cte 4
  pos 1 4 @= cte 3
  pos 1 8 @= cte 1
  pos 2 4 @= cte 1
  pos 2 6 @= cte 9
  pos 2 7 @= cte 5
  pos 3 0 @= cte 5
  pos 3 2 @= cte 2
  pos 3 3 @= cte 8
  pos 3 6 @= cte 1
  pos 4 3 @= cte 7
  pos 4 5 @= cte 2
  pos 5 2 @= cte 7
  pos 5 5 @= cte 9
  pos 5 6 @= cte 2
  pos 5 8 @= cte 4
  pos 6 1 @= cte 4
  pos 6 4 @= cte 2
  pos 7 0 @= cte 1
  pos 7 2 @= cte 9
  pos 7 4 @= cte 7
  pos 7 8 @= cte 6
  pos 8 0 @= cte 3
  pos 8 3 @= cte 5
  return mat

main = example_sat_main_void model
