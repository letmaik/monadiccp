{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

path :: ModelInt -> ModelCol -> (ModelInt -> ModelInt) -> (ModelInt -> ModelInt) -> ModelCol
path n l r c = slice l $ xmap (\k -> n*(r k)+(c k)) (0 @.. (n-1))

row :: ModelInt -> ModelCol -> ModelInt -> ModelCol
row n l i = path n l (const i) id

col :: ModelInt -> ModelCol -> ModelInt -> ModelCol
col n l i = path n l id (const i)

diag1 n l = path n l id id
diag2 n l = path n l id (\x -> n-x-1)

model :: ExampleModel ModelInt
model n = exists $ \mat -> do
  let nn = n*n
  let s = n*(nn+1) `div` 2
  size mat @= n*n
  loopall (0,n-1) $ \i -> do
    xfold (+) (cte 0) (col n mat i) @= s
    xfold (+) (cte 0) (row n mat i) @= s
  xfold (+) (cte 0) (diag1 n mat) @= s
  xfold (+) (cte 0) (diag2 n mat) @= s
  mat `allin` (cte 1,nn)
  allDiff mat
  (mat @!! 0) @> (mat!(n-1))
  (mat @!! 0) @> (mat!(n*n-n))
  return mat

main = example_sat_main_single_expr model
