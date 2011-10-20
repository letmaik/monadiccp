import Control.CP.FD.Example.Example
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.SearchTree

import List (tails)
import Data.Map (toList)

main = example_main_single model

-- generate a disjunction producing a list of variables, consisting of alr
-- prefixed by up to maxlen new variables
varexist :: FDSolver solver => Int -> [FDExpr solver] -> Tree (FDWrapper solver) [FDExpr solver]
varexist maxlen alr = 
  if maxlen==0
  then return alr
  else return alr \/ (exists $ \x -> varexist (maxlen-1) (x:alr))

-- constr list i = (if (i < (length list)-2) then v2 @= v0 * v1 - i else true) /\ v0 @: (-10,10)
constr list i = 2*v1 @= 2*v2 - v0 /\ 
                v0 @: (-10,10)
   where v0 = list !! i
         v1 = list !! ((i+1) `mod` (length list))
         v2 = list !! ((i+2) `mod` (length list))

model :: FDSolver solver => Int -> Tree (FDWrapper solver) [FDExpr solver]
model n = exists $ \x -> 
          do list <- varexist n [x]
             conj $ [ constr list i | i <- [0..(length list)-1] ]
             return list
