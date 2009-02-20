{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers
 -}
module Control.CP.Main where

import Control.CP.ComposableTransformers
import Control.CP.FD
import Control.CP.FDSugar
import List (tails)
import Control.CP.SearchTree hiding (label)
import System (getArgs)

--------------------------------------------------------------------------------
-- MAIN FUNCTIONS
--------------------------------------------------------------------------------

main = main1


main1 = getArgs >>= print . solve dfs it . nqueens . read . head
main2 = getArgs >>= print . solve dfs (nb 100 :- db  25 :- bb newBound)  . nqueens . read . head

main3 = getArgs >>= print . solve dfs (db 9) . nqueens . read . head

main4 = do (n1:_) <- getArgs 
           let n = read n1
           loop 1 n
  where loop i n
          | i > n     = return ()
          | otherwise =
              do -- print . (\(i,l) -> (i,not $ Prelude.null l)) . solve dfs (it :- fs :- ra 13 :- ld l) . nqueens $ i
                 print . (\(i,l) -> (i, {- not $ Prelude.null-}  l)) . restart dfs (map db [3..10]) . nqueens $ i
                 -- print . (\(i,l) -> (i, {- not $ Prelude.null-}  l)) . restartOpt dfs (replicate 10 fs) . nqueens $ i
                 loop (i+1) n

main5 = getArgs >>= loop 1 . read . head
  where loop i n
          | i > n     = return ()
          | otherwise =
              do print . (\(i,l) -> (i,minimum l)) . solve dfs (ld 5 :- bb newBoundBis) . gmodel $ i
                 loop (i+1) n

--------------------------------------------------------------------------------
-- PATH MODEL
--------------------------------------------------------------------------------

gmodel n = NewVar $ \_ -> path 1 n 0

path :: Int -> Int -> Int -> Tree FD Int
path x y d = if x == y 
               then Return d
               else disj [ Label (fd_objective >>= \o -> return (o @> (d+d' - 1) /\ (path z y (d+d')))) 
                         | (z,d') <- edge x
                         ]

edge i | i < 20     = [ (i+1,4), (i+2,1) ]
       | otherwise  = []

--------------------------------------------------------------------------------
-- N QUEENS MODEL
--------------------------------------------------------------------------------

nqueens n = 
  exist n $ \queens -> queens `allin` (1,n) /\ 
                       alldifferent queens  /\ 
                       diagonals queens     /\
                       -- enumerate ({- middleout -} endsout queens) /\
                       -- enumerate (middleout queens) /\
                       enumerate (queens) /\
		       assignments queens

allin queens range  =  
  conj [q `in_domain` range 
       | q <- queens 
       ] 

alldifferent :: [ FD_Term ] -> Tree FD ()
alldifferent queens =
  conj [ qi @\= qj 
       | qi:qjs <- tails queens 
       , qj <- qjs 
       ]
 
diagonals queens = 
  conj [ qi @\== (qj @+ d) /\ qj @\== (qi @+ d) 
       | qi:qjs <- tails queens 
       , (qj,d) <- zip qjs [1..] 
       ]
