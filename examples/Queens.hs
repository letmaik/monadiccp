{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers & Pieter Wuille
 -}

import Control.CP.FD.Example.Example
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.SearchTree

main = example_main_single nqueens

nqueens n = 
  exist n $ \q -> q `allin` (1,n) /\ conj [  
     q!!i       @/=  q!!j       /\  
    (q!!i) @+ i @/= (q!!j) @+ j /\  
    (q!!i) @- i @/= (q!!j) @- j  
    | i <- [0..n-1], j <- [0..n-1], i > j  
  ] /\ return q
