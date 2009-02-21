{- 
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers
 -}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.CP.ComposableTransformers where 

import Control.CP.Transformers
import Control.CP.SearchTree
import Control.CP.Solver
import Control.CP.Queue

import System.Random (mkStdGen, randoms)

--------------------------------------------------------------------------------
-- EVALUATION
--------------------------------------------------------------------------------

solve :: (Queue q, Solver solver, CTransformer c, CForSolver c ~ solver,
          Elem q ~ (Label solver,Tree solver (CForResult c),CTreeState c)) 
      => q -> c -> Tree solver (CForResult c) -> (Int,[CForResult c])
solve q c model = run $ eval model q (TStack c)

--------------------------------------------------------------------------------
-- COMPOSABLE TRANSFORMERS
--------------------------------------------------------------------------------

data TStack es ts (solver :: * -> *) a where
   TStack :: (CTransformer c, CForSolver c ~ solver, CForResult c ~ a) 
          => c -> TStack (CEvalState c) (CTreeState c) solver a

instance Solver solver => Transformer (TStack es ts solver a) where
  type EvalState (TStack es ts solver a) = es
  type TreeState (TStack es ts solver a) = ts
  type ForSolver (TStack es ts solver a) = solver
  type ForResult (TStack es ts solver a) = a
  initT  (TStack c) _  = return $ initCT c
  leftT  (TStack c) _  = leftCT c
  rightT (TStack c) _  = rightCT c
  nextT = nextTStack 
  returnT i wl t@(TStack c) es = returnCT c es (\es' -> continue i wl t es') (\es' -> endT i wl t es')

nextTStack :: 
     (Solver solver, Queue q, Elem q ~ (Label solver,Tree solver a,ts))
     => Int -> Tree solver a -> q -> (TStack es ts solver a) -> es -> ts -> solver (Int,[a])
nextTStack i tree q t es ts =
    case t of
      TStack c ->
        nextCT tree c es ts (\tree' es' ts' -> eval' i tree' q t es' ts') 
                            (\es'       -> continue i q t es')
			    (\es' -> endT i q t es')

--------------------------------------------------------------------------------
type CSearchSig c a =
     (Solver (CForSolver c), CTransformer c) 
     => Tree (CForSolver c) a -> c -> CEvalState c -> CTreeState c -> (EVAL c a) -> (CONTINUE c a) -> (EXIT c a) -> (CForSolver c) (Int,[a])

type CContinueSig c a =
     (Solver (CForSolver c), CTransformer c) 
     => c -> CEvalState c -> (CONTINUE c a) -> (EXIT c a) -> (CForSolver c) (Int,[a])

type EVAL     c a = (Tree (CForSolver c) a -> CEvalState c -> CTreeState c-> (CForSolver c) (Int,[a]))
type CONTINUE c a = (CEvalState c -> (CForSolver c) (Int,[a]))
type EXIT     c a = (CEvalState c) -> (CForSolver c) (Int,[a]) 

class Solver (CForSolver c) => CTransformer c where
  type CEvalState c :: *
  type CTreeState c :: *
  type CForSolver c :: (* -> *)
  type CForResult c :: *
  initCT :: c -> (CEvalState c, CTreeState c)
  leftCT, rightCT :: c -> CTreeState c -> CTreeState c
  leftCT  _  = id
  rightCT    = leftCT
  nextCT :: CSearchSig c (CForResult c)
  nextCT   = evalCT
  returnCT :: CContinueSig c (CForResult c) 
  returnCT = continueCT
  completeCT :: c -> CEvalState c -> Bool
  completeCT _ _ = True

evalCT :: CSearchSig c a
evalCT tree c es ts eval continue exit =
  eval tree es ts

continueCT :: CContinueSig c a
continueCT c es continue exit =
  continue es

exitCT :: CContinueSig c a
exitCT c es continue exit =
  exit es

newtype CNodeBoundedST (solver :: * -> *) a = CNBST Int

instance Solver solver => CTransformer (CNodeBoundedST solver a) where
  type CEvalState (CNodeBoundedST solver a) = Int
  type CTreeState (CNodeBoundedST solver a) = ()
  type CForSolver (CNodeBoundedST solver a) = solver
  type CForResult (CNodeBoundedST solver a) = a
  initCT (CNBST n)  = (n,())  
  nextCT tree c es ts eval' continue exit
    | es == 0    = exit es
    | otherwise  = eval' tree (es - 1) ts

newtype CDepthBoundedST (solver :: * -> *) a = CDBST Int

instance Solver solver => CTransformer (CDepthBoundedST solver a) where
  type CEvalState (CDepthBoundedST solver a)  = Bool
  type CTreeState (CDepthBoundedST solver a)  = Int
  type CForSolver (CDepthBoundedST solver a)  = solver
  type CForResult (CDepthBoundedST solver a)  = a
  initCT (CDBST n)  = (True,n)
  leftCT _ ts      = ts - 1
  nextCT tree c es ts eval' continue exit
    | ts == 0    = continue False
    | otherwise  = eval' tree es ts
  completeCT _ es  = es

newtype CLimitedDiscrepancyST (solver :: * -> *) a = CLDST Int

instance Solver solver => CTransformer (CLimitedDiscrepancyST solver a) where
  type CEvalState (CLimitedDiscrepancyST solver a) = ()
  type CTreeState (CLimitedDiscrepancyST solver a) = Int
  type CForSolver (CLimitedDiscrepancyST solver a) = solver
  type CForResult (CLimitedDiscrepancyST solver a) = a
  initCT (CLDST n)  = ((),n)
  rightCT _ n  = n - 1
  nextCT tree c es ts eval' continue exit
    | ts == 0    = continue es
    | otherwise  = eval' tree es ts

newtype CRandomST (solver :: * -> *) a  = CRST Int

instance Solver solver => CTransformer (CRandomST solver a) where
  type CEvalState (CRandomST solver a) = [Bool]
  type CTreeState (CRandomST solver a) = ()
  type CForSolver (CRandomST solver a) = solver
  type CForResult (CRandomST solver a) = a
  initCT (CRST n)  = (randoms $ mkStdGen n,())
  nextCT tree@(Try l r) c (switch:es)
    | switch        = evalCT (Try r l) c es
    | otherwise     = evalCT tree      c es
  nextCT tree@(Add d (Try l r)) c (switch:es)
    | switch        = evalCT (Add d (Try r l)) c es
    | otherwise     = evalCT tree      c es
  nextCT tree c es  = evalCT tree      c es

data CIdentityCST (solver :: * -> *) a  = CIST

instance Solver solver => CTransformer (CIdentityCST solver a) where
  type CEvalState (CIdentityCST solver a)  = ()
  type CTreeState (CIdentityCST solver a)  = ()
  type CForSolver (CIdentityCST solver a)  = solver
  type CForResult (CIdentityCST solver a)  = a
  initCT _  = ((),())

data CFirstSolutionST (solver :: * -> *) a  = CFSST

instance Solver solver => CTransformer (CFirstSolutionST solver a) where
  type CEvalState (CFirstSolutionST solver a)  = Bool
  type CTreeState (CFirstSolutionST solver a)  = ()
  type CForSolver (CFirstSolutionST solver a)  = solver
  type CForResult (CFirstSolutionST solver a)  = a
  initCT _  = (True,())
  returnCT _ es continue exit =
    exit False
  completeCT _ es = es 


--------------------------------------------------------------------------------
data Composition es ts solver a where
  (:-) :: (CTransformer c1, CTransformer c2,
           CForSolver c1 ~ solver, CForSolver c2 ~ solver,
           CForResult c1 ~ a,      CForResult c2 ~ a
          ) 
       => c1 -> c2 -> Composition (CEvalState c1,CEvalState c2) (CTreeState c1,CTreeState c2) solver a

instance Solver solver => CTransformer (Composition es ts solver a) where
  type CEvalState (Composition es ts solver a) = es
  type CTreeState (Composition es ts solver a) = ts
  type CForSolver (Composition es ts solver a) = solver
  type CForResult (Composition es ts solver a) = a
  initCT (c1 :- c2)       = let (es1,ts1) = initCT c1 
                                (es2,ts2) = initCT c2 
                            in ((es1,es2),(ts1,ts2))
  leftCT (c1 :- c2) (ts1,ts2)   = (leftCT c1 ts1,leftCT c2 ts2)
  rightCT (c1 :- c2) (ts1,ts2)  = (rightCT c1 ts1,rightCT c2 ts2)
  nextCT tree (c1 :- c2) (es1,es2) (ts1,ts2) eval' continue exit  =
    nextCT tree c1 es1 ts1 
           (\tree' es1' ts1' -> nextCT tree' c2 es2 ts2 
                                   (\tree'' es2' ts2' -> eval' tree'' (es1',es2') (ts1',ts2'))
                                   (\es2' -> continue (es1',es2'))
				   (\es2' -> exit (es1',es2')) ) 
           (\es1' -> continue (es1',es2))
           (\es1' -> exit (es1',es2))
  returnCT (c1 :- c2) (es1,es2) continue exit =
    returnCT c1 es1 (\es1' -> returnCT c2 es2 (\es2' -> continue (es1',es2')) (\es2' -> exit (es1',es2'))) 
		    (\es1' -> exit (es1',es2))
  completeCT (c1 :- c2) (es1,es2)  = completeCT c1 es1 && completeCT c2 es2

--------------------------------------------------------------------------------
-- BRANCH & BOUND
--------------------------------------------------------------------------------

newtype CBranchBoundST (solver :: * -> *) a = CBBST (NewBound solver) 
data    BBEvalState solver  = BBP Int (Bound solver)

type Bound    solver  = forall a. Tree solver a -> Tree solver a
type NewBound solver  = solver (Bound solver)

instance Solver solver => CTransformer (CBranchBoundST solver a) where
  type CEvalState (CBranchBoundST solver a) = BBEvalState solver
  type CTreeState (CBranchBoundST solver a) = Int
  type CForSolver (CBranchBoundST solver a) = solver
  type CForResult (CBranchBoundST solver a) = a
  initCT _  = (BBP 0 id,0)
  nextCT tree c es@(BBP nv bound) v eval continue exit
    | nv > v        = eval (bound tree) es nv
    | otherwise     = eval tree         es v
  returnCT (CBBST newBound) (BBP v bound) continue exit =
    do bound' <- newBound
       continue $ BBP (v + 1) bound' 

--------------------------------------------------------------------------------
-- RESTARTING
--------------------------------------------------------------------------------

data SealedCST es ts solver a where
  Seal :: CTransformer c => c -> SealedCST (CEvalState c) (CTreeState c) (CForSolver c) (CForResult c)

instance Solver solver => CTransformer (SealedCST es ts solver a) where
  type CEvalState (SealedCST es ts solver a) = es
  type CTreeState (SealedCST es ts solver a) = ts
  type CForSolver (SealedCST es ts solver a) = solver
  type CForResult (SealedCST es ts solver a) = a
  leftCT (Seal c) 	= leftCT c
  rightCT (Seal c)	= rightCT c
  initCT (Seal c)       = initCT c
  nextCT tree (Seal c)  = nextCT tree c
  returnCT (Seal c)     = returnCT c
  completeCT (Seal c)   = completeCT c

data RestartST es ts (solver :: * -> *) a = RestartST [SealedCST es ts solver a] (Tree solver a -> solver (Tree solver a))

instance Solver solver => Transformer (RestartST es ts solver a) where
  type EvalState (RestartST es ts solver a) = (SealedCST es ts solver a,[SealedCST es ts solver a],es,Label solver,Tree solver a)
  type TreeState (RestartST es ts solver a) = ts
  type ForSolver (RestartST es ts solver a) = solver
  type ForResult (RestartST es ts solver a) = a
  initT  (RestartST (c:cs) _) tree  = 
 	let (es,ts) = initCT c
        in do l <-  mark
	      return ((c,cs,es,l,tree),ts)
  leftT  _ (c,_,_,_,_)      = leftCT c
  rightT _ (c,_,_,_,_)      = rightCT c
  nextT i tree q t es@(c,cs,es_c,l,tree0) ts = 
        nextCT tree c es_c ts (\tree' es_c' ts' -> eval' i tree' q t (c,cs,es_c',l,tree0) ts') 
                              (\es_c'       -> continue i q t (c,cs,es_c',l,tree0))
			      (\es_c' -> endT i q t (c,cs,es_c',l,tree0))
  returnT i wl t es@(c,cs,es_c,l,tree0)  = returnCT c es_c (\es_c' -> continue i wl t (c,cs,es_c',l,tree0)) (\es_c' -> endT i wl t (c,cs,es_c',l,tree0))
  endT i wl t es@(_,[],_,_,_)      = return (i,[])
  endT i wl t@(RestartST _ f) es@(c0,(c:cs),es_c0,l,tree0)   
    | completeCT c0 es_c0  = return (i,[])
    | otherwise            = let (es,ts) = initCT c
                             in  do tree' <- f tree0
                                    continue i (pushQ (l,tree',ts) $ emptyQ wl) t (c,cs,es,l,tree0)
 
