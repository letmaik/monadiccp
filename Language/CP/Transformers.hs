{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers
 -}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types #-}
module Language.CP.Transformers where 

import Language.CP.Solver
import Language.CP.SearchTree
import Language.CP.Queue

--------------------------------------------------------------------------------
-- EVALUATION
--------------------------------------------------------------------------------

eval :: (Solver solver, Queue q, Elem q ~ (Label solver,Tree solver (ForResult t),TreeState t), Transformer t,
         ForSolver t ~ solver) 
     => Tree solver (ForResult t) -> q -> t -> solver (Int,[ForResult t])
eval tree q t  = do (es,ts) <- initT t tree
                    eval' 0 tree q t es ts

eval' :: SearchSig solver q t (ForResult t) 
eval' i (Return x) wl t es ts  = do (j,xs) <- returnT (i+1) wl t es
                                    return (j,(x:xs)) 
eval' i (Add c k)  wl t es ts = do b <- addSM c 
                                   if b then eval' (i+1) k wl t es ts
                                        else continue (i+1) wl t es
eval' i (NewVar f) wl t es ts = do v <- newvarSM 
                                   eval' (i+1) (f v) wl t es ts
eval' i (Try l r)  wl t es ts  = 
  do now <- markSM 
     let wl' = pushQ (now,l,leftT t es ts) $ pushQ (now,r,rightT t es ts) wl
     continue (i+1) wl' t es
eval' i Fail       wl t es ts  = continue (i+1) wl t es
eval' i (Label m)  wl t es ts  = do tree <- m
                                    eval' (i+1) tree wl t es ts
 
continue :: ContinueSig solver q t (ForResult t) 
continue i wl t es  
	| isEmptyQ wl  = endT i wl t es -- return (i,[])
        | otherwise    = let ((past,tree,ts),wl') = popQ wl
                         in  do gotoSM past
                                nextT i tree wl' t es ts 

--------------------------------------------------------------------------------
-- TRANSFORMER
--------------------------------------------------------------------------------

type SearchSig solver q t a =
     (Solver solver, Queue q, Transformer t,   
          Elem q ~ (Label solver,Tree solver a,TreeState t),
	  ForSolver t ~ solver) 
     => Int -> Tree solver a -> q -> t -> EvalState t -> TreeState t -> solver (Int,[a])

type ContinueSig solver q t a =
     (Solver solver, Queue q, Transformer t,   
          Elem q ~ (Label solver,Tree solver a,TreeState t),
	  ForSolver t ~ solver) 
     => Int -> q -> t -> EvalState t -> solver (Int,[a])

class Transformer t where
  type EvalState t :: *
  type TreeState t :: *
  type ForSolver t :: (* -> *)
  type ForResult t :: *
  leftT, rightT :: t -> EvalState t -> TreeState t -> TreeState t
  leftT  _ _ = id
  rightT    = leftT
  nextT :: SearchSig (ForSolver t) q t (ForResult t)
  nextT  = eval'
  initT :: t -> Tree (ForSolver t) (ForResult t) -> (ForSolver t) (EvalState t,TreeState t)
  returnT :: ContinueSig solver q t (ForResult t) 
  returnT i wl t es  = continue i wl t es
  endT  :: ContinueSig solver q t (ForResult t)
  endT i wl t es     = return (i,[])

newtype DepthBoundedST (solver :: * -> *) a = DBST Int

instance Solver solver => Transformer (DepthBoundedST solver a) where
  type EvalState (DepthBoundedST solver a)  = ()
  type TreeState (DepthBoundedST solver a)  = Int
  type ForSolver (DepthBoundedST solver a)  = solver
  type ForResult (DepthBoundedST solver a)  = a
  initT (DBST n) _  = return ((),n)
  leftT _ _ ts      = ts - 1
  nextT i tree q t es ts
    | ts == 0    = continue i q t es
    | otherwise  = eval' i tree q t es ts

newtype NodeBoundedST (solver :: * -> *) a = NBST Int

instance Solver solver => Transformer (NodeBoundedST solver a)  where
  type EvalState (NodeBoundedST solver a) = Int
  type TreeState (NodeBoundedST solver a) = ()
  type ForSolver (NodeBoundedST solver a) = solver
  type ForResult (NodeBoundedST solver a) = a
  initT (NBST n) _  = return (n,())
  nextT i tree q t es ts
    | es == 0    = return (i,[])
    | otherwise  = eval' i tree q t (es - 1) ts

