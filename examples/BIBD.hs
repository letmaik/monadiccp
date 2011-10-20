{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

-- path :: ModelInt -> ModelCol -> (ModelInt -> ModelInt) -> (ModelInt -> ModelInt) -> ModelCol
-- row :: ModelInt -> ModelCol -> ModelInt -> ModelCol
-- col :: ModelInt -> ModelCol -> ModelInt -> ModelCol
path nc ne l r c = slice l $ xmap (\k -> nc*(r k)+(c k)) (0 @.. (ne-1))
row nc ne l i = path nc ne l (const i) id
col nc ne l i = path nc ne l id (const i)

model :: ExampleModel (ModelInt,ModelInt,ModelInt)
model (v,k,lambda) = exists $ \mm -> do
  let b = (v*(v-1)*lambda) `div` (k*(k-1))
  let r = (lambda*(v-1)) `div` (k-1)
  size mm @= b*v
  let p r c = mm!(r*b+c)
  mm `allin` (cte 0,cte 1)
  loopall (0,v-1) $ \rr -> xsum (row b b mm rr) @= r
  loopall (0,b-1) $ \cc -> xsum (col b v mm cc) @= k
  loopall (0,v-1) $ \r1 -> do
    loopall (r1+1,v-1) $ \r2 -> do
      xsum (xmap (\i -> (p r1 i) * (p r2 i)) (0 @.. (b-1))) @= lambda
  return mm

main = example_sat_main_void (\_ -> model (6,3,2))


