import List (transpose)

import Control.CP.FD.Example.Example
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.SearchTree

main = example_main_single model

cutAt p l = case (splitAt p l) of
  (l,[]) -> [l]
  (b,r) -> b:(cutAt p r)
mexist r c = exist (r*c) $ \list -> return $ cutAt c list
lsum v l = (foldl1 (+) l) @= v
diag bc ic m = map (\x -> (m!!x)!!(bc+ic*x)) [0..(length m)-1]

model :: FDSolver solver => Int -> Tree (FDWrapper solver) [FDExpr solver]
model n = exist 5 $ \l -> do
  allin l (0,5*n)
  let forvar v = conj $ map (\p -> conj $ map (\j -> v @/= 5*j+p) [0..(cte (5*n))]) [0,2,4]
  conj $ map forvar $ reverse l
  conj $ map (\j -> conj $ map (\v -> v @>= cte (5*j) /\ v @<= cte (5*(j+5*(n `div` 2)))) $ reverse l) [0..5*(n `div` 2)]
  return l
