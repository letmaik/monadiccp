{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

main = example_sat_main_void model

model :: ExampleModel ()
model _ = exists $ \vars -> do
  [n1,n2,n3,n4,n5,
   c1,c2,c3,c4,c5,
   p1,p2,p3,p4,p5,
   a1,a2,a3,a4,a5,
   d1,d2,d3,d4,d5] <- colList vars 25
  let ns = slice vars (cte 0 @.. cte 4)
      cs = slice vars (cte 5 @.. cte 9)
      ps = slice vars (cte 10 @.. cte 14)
      as = slice vars (cte 15 @.. cte 19)
      ds = slice vars (cte 20 @.. cte 24)
  vars `allin` (cte 1, cte 5)
  allDiff ns
  allDiff cs
  allDiff ps
  allDiff as
  allDiff ds
  n1 @= c2
  n2 @= a1
  n3 @= p1
  n4 @= d3
  n5 @= 1
  d5 @= 3
  p3 @= d1
  c1 @= d4
  p5 @= a4
  p2 @= c3
  c1 @= c5+1
  plusorminus a3 p4 1
  plusorminus a5 p2 1
  plusorminus n5 c4 1
  return vars

plusorminus x y c =
  x @= y+c @|| x @= y-c
