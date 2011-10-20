import Control.CP.FD.Example.Example
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.SearchTree
import Data.List (transpose)

main = example_main_single model

cutAt p l = case (splitAt p l) of
  (l,[]) -> [l]
  (b,r) -> b:(cutAt p r)
mexist r c = exist (r*c) $ \list -> return $ cutAt c list
lsum v l = (foldl1 (+) l) @= v
diag bc ic m = map (\x -> (m!!x)!!(bc+ic*x)) [0..(length m)-1]

interleave [] ys = ys
interleave (x:xs) ys = x : (interleave ys xs)

model n = do
  let nn = n*n
  let s = nn*(nn+1) `div` (2*n)
  let sums = lsum $ cte s
  m <- mexist n n
  allin (concat m) (1,nn)
  conj $ interleave (map sums m) (map sums $ transpose m)
  sums $ diag 0 1 m
  sums $ diag (n-1) (-1) m
  allDiff $ concat m
  (m!!0)!!0 @> (m!!0)!!(n-1)
  (m!!0)!!0 @> (m!!(n-1))!!0
  return $ concat m
