{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

import Control.CP.FD.Example

count col val =                -- count c v = #{foreach i: c[i]==v}
  xsum $ xmap (\v -> channel (v @= val)) col

model :: ExampleModel ModelInt
model n = exists $ \col -> do  -- request a (collection) variable col
  size col @= n                -- col has length n
  col `allin` (cte 0,n-1)      -- all col elements are in [0..n-1]
  loopall (0,n-1) $ \i -> do   -- foreach i in [0..n-1]:
    count col i @= (col!i)        -- col[i] == count col i
  xsum col @= n                -- sum(col) = n
                               -- sum(i*col[i]) = n
  (xsum (xmap (\i -> (i-1)*(col!i)) ((cte 0) @.. (n-1)))) @= cte 0
  return col                   -- return col

main = example_sat_main_single_expr model
