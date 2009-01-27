{- Copyright (c) 2008 the authors listed at the following URL, and/or
the authors of referenced articles or incorporated external code:
http://en.literateprograms.org/Priority_Queue_(Haskell)?action=history&offset=20080608152146

Permission is hereby granted, free of charge, to any person obtaining
a copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be
included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.
IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY
CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT,
TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE
SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

Retrieved from: http://en.literateprograms.org/Priority_Queue_(Haskell)?oldid=13634
-}

module Language.CP.PriorityQueue (
    PriorityQueue,
    empty,
    is_empty,
    minKey,
    minKeyValue,
    insert,
    deleteMin,
    deleteMinAndInsert
) where

 
import Prelude


-- Declare the data type constructors.

data Ord k => PriorityQueue k a = Nil | Branch k a (PriorityQueue k a) (PriorityQueue k a)
 

-- Declare the exported interface functions.

-- Return an empty priority queue.

is_empty Nil = True
is_empty _   = False

empty :: Ord k => PriorityQueue k a
empty = Nil


-- Return the highest-priority key.

minKey :: Ord k => PriorityQueue k a -> k
minKey = fst . minKeyValue


-- Return the highest-priority key plus its associated value.

minKeyValue :: Ord k => PriorityQueue k a -> (k, a)
minKeyValue Nil              = error "empty queue"
minKeyValue (Branch k a _ _) = (k, a)


-- Insert a key/value pair into a queue.

insert :: Ord k => k -> a -> PriorityQueue k a -> PriorityQueue k a
insert k a q = union (singleton k a) q

deleteMin :: Ord k => PriorityQueue k a -> ((k,a), PriorityQueue k a)
deleteMin(Branch k a l r) = ((k,a),union l r)

-- Delete the highest-priority key/value pair and insert a new key/value pair into the queue.

deleteMinAndInsert :: Ord k => k -> a -> PriorityQueue k a -> PriorityQueue k a
deleteMinAndInsert k a Nil              = singleton k a
deleteMinAndInsert k a (Branch _ _ l r) = union (insert k a l) r



-- Declare the private helper functions.

-- Join two queues in sorted order.

union :: Ord k => PriorityQueue k a -> PriorityQueue k a -> PriorityQueue k a
union l Nil = l
union Nil r = r
union l@(Branch kl _ _ _) r@(Branch kr _ _ _)
    | kl <= kr  = link l r
    | otherwise = link r l


-- Join two queues without regard to order.

-- (This is a helper to the union helper.)

link (Branch k a Nil m) r = Branch k a r m
link (Branch k a ll lr) r = Branch k a lr (union ll r)


-- Return a queue with a single item from a key/value pair.

singleton :: Ord k => k -> a -> PriorityQueue k a
singleton k a = Branch k a Nil Nil
