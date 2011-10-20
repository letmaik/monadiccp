{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

aroundY = list [-1,-1,0,1,1,1,0,-1]
aroundX = list [0,1,1,1,0,-1,-1,-1]

model :: ExampleModel ()
model () = do 
  let c = board
  let s = c!0
      spec x y = c!(1+y*s+x)
  exists $ \m -> do
    m `allin` (cte 0,cte 1)
    size m @= s*s+1
    m!(s*s) @= cte 0
    let v x y = (x@>=s @|| x@<0 @|| y@>=s @|| y@<0) @? (s*s,y*s+x)
    let around x y = slice m $ xmap (\p -> v (x+(aroundX!p)) (y+(aroundY!p))) (cte 0 @.. cte 7)
    loopall (cte 0,s-1) $ \x -> 
      loopall (cte 0,s-1) $ \y -> do
        ((spec x y) @< (cte 0)) @?? (true,do
            m!(y*s+x) @= 0
            xsum (around x y) @= (spec x y)
          )
    return m

main = example_sat_main_void model

u = (-1)

board = list $
  [
    10,

    1,u,u,2,u,2,u,2,u,u,
    u,3,2,u,u,u,4,u,u,1,
    u,u,u,1,3,u,u,u,4,u,
    3,u,1,u,u,u,3,u,u,u,
    u,2,1,u,1,u,u,3,u,2,
    u,3,u,2,u,u,2,u,1,u,
    2,u,u,3,2,u,u,2,u,u,
    u,3,u,u,u,3,2,u,u,3,
    u,u,3,u,3,3,u,u,u,u,
    u,2,u,2,u,u,u,2,2,u
  ]
