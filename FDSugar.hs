{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers
 -}
{-# LANGUAGE TransformListComp #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE TypeFamilies #-}

module FDSugar where 

import SearchTree hiding (label)
import Transformers
import ComposableTransformers
import Queue
import Solver

import GHC.Exts (sortWith)
import qualified PriorityQueue
import qualified Data.Sequence
import FD

dfs = []
bfs = Data.Sequence.empty
pfs :: Ord a => PriorityQueue.PriorityQueue a (a,b,c)
pfs = PriorityQueue.empty

nb :: Int -> CNodeBoundedST FD a
nb = CNBST
db :: Int -> CDepthBoundedST FD a
db = CDBST
bb :: NewBound FD -> CBranchBoundST FD a
bb = CBBST
fs :: CFirstSolutionST FD a
fs = CFSST
it :: CIdentityCST FD a
it = CIST
ra :: Int -> CRandomST FD a
ra = CRST
ld :: Int -> CLimitedDiscrepancyST FD a
ld = CLDST

newBound :: NewBound FD
newBound = do obj <- fd_objective
              (val:_) <- fd_domain obj 
	      l <- markSM
              return ((\tree -> tree `insertTree` (obj @< val)) :: forall b . Tree FD b -> Tree FD b)

newBoundBis :: NewBound FD 
newBoundBis = do obj <- fd_objective
                 (val:_) <- fd_domain obj 
                 let m = val `div` 2
                 return ((\tree -> (obj @< (m + 1) \/ ( obj @> m /\ obj @< val)) /\ tree) :: forall b . Tree FD b -> Tree FD b)

restart :: (Queue q, Solver solver, CTransformer c, CForSolver c ~ solver,
          Elem q ~ (Label solver,Tree solver (CForResult c),CTreeState c)) 
      => q -> [c] -> Tree solver (CForResult c) -> (Int,[CForResult c])
restart q cs model = runSM $ eval model q (RestartST (map Seal cs) return)

restartOpt :: (Queue q, CTransformer c, CForSolver c ~ FD,
          Elem q ~ (Label FD,Tree FD (CForResult c),CTreeState c)) 
      => q -> [c] -> Tree FD (CForResult c) -> (Int,[CForResult c])
restartOpt q cs model = runSM $ eval model q (RestartST (map Seal cs) opt)
	where opt tree = newBound >>= \f -> return (f tree)

--------------------------------------------------------------------------------
-- ENUMERATION
--------------------------------------------------------------------------------

enumerate = Label . (label in_order) 
-- enumerate = Label . (label firstfail) 

label sel qs  = do qs' <- sel qs 
                   label' qs' 
  where label' []      = return true
        label' (q:qs)  = do d <- fd_domain q 
--                            return $ enum q (middleout d) /\ enumerate qs
                            return $ enum q d /\ enumerate qs

in_order :: Monad m => a -> m a
in_order = return 

firstfail qs = do ds <- mapM fd_domain qs 
                  return [ q | (d,q) <- zip ds qs 
                             , then sortWith by (length d) ] 
enum queen values = 
  disj [ queen @= value 
       | value <- values 
       ] 

value var = do [val] <- fd_domain var
               return val

middleout l = let n = (length l) `div` 2 in
              interleave (drop n l) (reverse $ take n l)

endsout  l = let n = (length l) `div` 2 in
              interleave (reverse $ drop n l) (take n l)

interleave []     ys = ys
interleave (x:xs) ys = x:interleave ys xs
--------------------------------------------------------------------------------
-- RESULT
--------------------------------------------------------------------------------

assignments = mapM assignment 
assignment q = Label $ value q >>= (return . Return)
--------------------------------------------------------------------------------
-- SYNTACTIC SUGAR
--------------------------------------------------------------------------------

in_domain v (l,u)  = Add (FD_Dom v (l,u)) true
(@\=) :: FD_Term -> FD_Term -> Tree FD ()
v1 @\= v2  = Add (FD_NEq v1 v2) true

(@=) :: FD_Term -> Int -> Tree FD ()
v1 @= v2  = Add (FD_Eq v1 v2) true

data Plus  = FD_Term :+ Int 
(@+) = (:+)

(@\==) :: FD_Term -> Plus -> Tree FD ()
v1 @\== (v2 :+ i)  = Add (FD_NEq v1 (v2 .+. i))  true

(@<) :: FD_Term -> Int -> Tree FD ()
v @< i  = Add (FD_LT v i) true

(@>) :: FD_Term -> Int -> Tree FD ()
v @> i  = Add (FD_GT v i) true
