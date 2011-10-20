{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers & Pieter Wuille
 -}

import Control.CP.FD.Example.Example
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.SearchTree

main = example_main_void model

model :: FDSolver solver => Tree (FDWrapper solver) [FDExpr solver]
model = exist 2 $ \[a,b] -> a @: (1,5) /\
			   b @: (0,4) /\
			   a - b @= 1 /\
			   (a @= 2 \/ a @= 3 \/ a @= 4) /\
			   return [a,b]
