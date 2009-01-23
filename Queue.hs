{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-
 - The Queue data type, a worklist data type for search.
 -
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers
 -}

module Queue where

import qualified Data.Sequence
import qualified PriorityQueue

class Queue q where   
  type Elem q :: *
  emptyQ   :: q -> q
  isEmptyQ :: q -> Bool
  popQ     :: q -> (Elem q,q)
  pushQ    :: Elem q -> q -> q

instance Queue [a] where
  type Elem [a] = a
  emptyQ _     = []
  isEmptyQ     = Prelude.null
  popQ (x:xs)  = (x,xs)
  pushQ        = (:)

instance Queue (Data.Sequence.Seq a) where
  type Elem (Data.Sequence.Seq a)  = a
  emptyQ _                   = Data.Sequence.empty
  isEmptyQ                   = Data.Sequence.null 
  popQ (Data.Sequence.viewl -> x Data.Sequence.:< xs)  = (x,xs)
  pushQ                      = flip (Data.Sequence.|>)

instance Ord a => Queue (PriorityQueue.PriorityQueue a (a,b,c)) where
  type Elem (PriorityQueue.PriorityQueue a (a,b,c)) = (a,b,c)
  emptyQ _ = PriorityQueue.empty
  isEmptyQ = PriorityQueue.is_empty 
  pushQ x@(k,_,_)  = PriorityQueue.insert k x
  popQ q   = let ((_,x),q') = PriorityQueue.deleteMin q
             in (x,q')
