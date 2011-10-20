{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

model :: ExampleModel (ModelInt,ModelInt,ModelInt,ModelInt)
model (v,q,l,d) = do
  let n = q*l
  let nseqpair = (v*(v-1)) `div` 2
  exists $ \c -> do
    size c @= n*v
    c `allin` (cte 1,q)
    let el ro co = c ! (ro*n+co)
    loopall (cte 0,v-1) $ \row -> do
      loopall (1,q) $ \val -> do
        xsum (xmap (\col -> channel (el row col @= val)) (0 @.. (n-1))) @= l
    loopall (cte 0,v-1) $ \a -> do
      loopall (a+1,v-1) $ \b -> do
        xsum (xmap (\col -> channel (el a col @/= el b col)) (0 @.. (n-1))) @= d
    return c

main = example_sat_main_void (\_ -> model (5,3,2,4))
