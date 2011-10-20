-- --------------------------------------------------------------------------
-- Benchmark (Finite Domain)                                               --
--                                                                         --
-- Name           : partit.pl                                              --
-- Title          : integer partitionning                                  --
-- Original Source: Daniel Diaz - INRIA France                             --
-- Adapted by     : Daniel Diaz for GNU Prolog                             --
-- Date           : September 1993 (modified March 1997)                   --
--                                                                         --
-- Partition numbers 1,2,...,N into two groups A and B such that:          --
--   a) A and B have the same length,                                      --
--   b) sum of numbers in A = sum of numbers in B,                         --
--   c) sum of squares of numbers in A = sum of squares of numbers in B.   --
--                                                                         --
-- This problem admits a solution if N is a multiple of 8.                 --
--                                                                         --
-- Note: finding a partition of 1,2...,N into 2 groups A and B such that:  --
--                                                                         --
--     Sum (k^p) = Sum l^p                                                 --
--   k in A      l in B                                                    --
--                                                                         --
-- admits a solution if N mod 2^(p+1) = 0 (N is a multiple of 2^(p+1)).    --
-- Condition a) is a special case where p=0, b) where p=1 and c) where p=2.--
--                                                                         --
-- Two redundant constraints are used:                                     --
--                                                                         --
--   - in order to avoid duplicate solutions (permutations) we impose      --
--     A1<A2<....<AN/2, B1<B2<...<BN/2 and A1<B1. This achieves much more  --
--     pruning than only fd_all_differents(A) and fd_all_differents(B).    --
--                                                                         --
--   - the half sums are known                                             --
--                              N                                          --
--        Sum k^1 = Sum l^1 = (Sum i) / 2 = N*(N+1) / 4                    --
--       k in A    l in B      i=1                                         --
--                              N                                          --
--        Sum k^2 = Sum l^2 = (Sum i^2)/2 = N*(N+1)*(2*N+1) / 12           --
--       k in A    l in B      i=1                                         --

import Control.CP.FD.Example.Example
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.SearchTree

main = example_main_single model

model n =
  exist n $ \list1 ->
  exist n $ \list2 ->
      allin list1 (1,2*n)  /\
      allin list2 (1,2*n)  /\
 (let list = list1 ++ list2 
  in  ascending list1    /\
      ascending list2    /\
      head list1 @< head list2 /\
      allDiff list  /\
      csum list1 @= csum list2 /\
      csum (square list1) @= csum (square list2) /\
      csum list1 @= (cte $ hs (2*n)) /\
      csum list2 @= (cte $ hs (2*n)) /\
      csum (square list1) @= (cte $ hss (2*n)) /\
      csum (square list2) @= (cte $ hss (2*n)) /\
      return list
 ) 

ascending list = sSorted list

hs, hss :: Int -> Int
hs  n  = (n * (n + 1)) `div` 4
hss n  = (n * (n + 1) * (2 * n +1)) `div` 12

csum l = foldl1 (+) l

square l = map (\x -> x * x) l
