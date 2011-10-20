{-
%   File   : olympic.pl
%   Author : Neng-Fa ZHOU
%   Date   : 1993
%   Purpose: solve a puzzle taken from Olympic Arithmetic Contest
/***********************************************************************
   Given ten variables with the following configuration:

               X7   X8   X9   X10

                  X4   X5   X6

                     X2   X1             

                        X1

  We already know that X1 is equal to 3 and want to assign each variable
  with a different integer from {1,2,...,10} such that for any three
  variables 
                      Xi   Xj

                         Xk
  the following constraint is satisfied:

                    |Xi-Xj| = Xk
***********************************************************************/
-}


import Control.CP.FD.Example.Example
import Control.CP.FD.FD
import Control.CP.FD.Expr
import Control.CP.SearchTree

main = example_main_void model

model :: FDSolver solver => Tree (FDWrapper solver) [Expr (FDTerm solver)]
model = 
  exist 10 $ \list@[x1,x2,x3,x4,x5,x6,x7,x8,x9,x10] 
		    -> list `allin` (1,10) /\ 
                       allDiff list        /\ 
		       x1 @= 3             /\ 
    		       minus x2 x3 x1 	   /\
                       minus x4 x5 x2 	   /\
                       minus x5 x6 x3 	   /\
                       minus x7 x8 x4 	   /\
    		       minus x8 x9 x5 	   /\
    		       minus x9 x10 x6     /\
		       return list

minus x1 x2 x3 = (abs (x1-x2)) @= x3
