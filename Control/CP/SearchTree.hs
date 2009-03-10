{-# OPTIONS_GHC -fglasgow-exts #-}
{-
 - The Tree data type, a generic modelling language for constraint solvers.
 -
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers
 -}

module Control.CP.SearchTree  where

import Monad
import Control.CP.Solver

-------------------------------------------------------------------------------
----------------------------------- Tree --------------------------------------
-------------------------------------------------------------------------------

data Tree s a where
  Fail    :: Tree s a                                  -- failure
  Return  :: a -> Tree s a                             -- finished
  Try     :: Tree s a -> Tree s a -> Tree s a          -- disjunction
  Add     :: Constraint s -> Tree s a -> Tree s a      -- sequentially adding a constraint to a tree
  NewVar  :: Term s t => (t -> Tree s a) -> Tree s a   -- add a new variable to a tree
  Label   :: s (Tree s a) -> Tree s a      	       -- label with a strategy

instance Show (Tree s a)  where
  show Fail 		= "Fail"
  show (Return _) 	= "Return"
  show (Try l r)        = "Try (" ++ show l ++ ") (" ++ show r ++ ")"
  show (Add _ t)        = "Add (" ++ show t ++ ")"
  show (NewVar _)       = "NewVar"
  show (Label _)        = "Label"

instance Solver s => Functor (Tree s) where
	fmap  = liftM 
 
instance Solver s => Monad (Tree s) where
  return = Return
  (>>=)  = bindTree
  

bindTree     :: Solver s => Tree s a -> (a -> Tree s b) -> Tree s b
Fail           `bindTree` k  = Fail
(Return x)     `bindTree` k  = k x
(Try m n)      `bindTree` k  = Try (m `bindTree` k) (n `bindTree` k)
(Add c m)      `bindTree` k  = Add c (m `bindTree` k)
(NewVar f)     `bindTree` k  = NewVar (\x -> f x `bindTree` k)    
(Label m)      `bindTree` k  = Label (m >>= \t -> return (t `bindTree` k))

insertTree     :: Solver s => Tree s a -> Tree s () -> Tree s a
(NewVar f)     `insertTree` t  = NewVar (\x -> f x `insertTree` t)    
(Add c  o)     `insertTree` t  = Add c (o `insertTree` t)
other 	       `insertTree` t  = t /\ other


{- Monad laws:
 -
 - 1. return x >>= f  ==  f x
 -
 -    return a >>= f  
 -    == Return a >>= f		(return def)
 -    == f x			(bind def) 
 -
 - 2. m >>= return  =  m
 -
 -   By induction
 -     case m of
 -     1) Return x -> 
 -          Return x >>= return
 -          == return x			(bind def)
 -          == Return x        		(return def)
 -     2) Fail ->
 -          Fail >>= return
 -          == Fail			(bind def)
 -     3)  Try l r >>= return
 -         == Try (l >>= return) (r >>= return) (bind def)
 -         == Try l r				(induction)
 -      4) Add c m >>= return
 -         == Add c (m >>= return) 	(bind def)
 -         == Add c m 			(induction) 
 - 	5) NewVar f >>= return
 - 	   == NewVar (\v -> f v >>= return) 	(bind def) 
 - 	   == NewVar (\v -> f v)		((co)-induction?)
 - 	   == NewVar f				(eta reduction)
 - 	6) Label sm >>= return
 - 	   == Label (sm >>= \m -> return (m >>= return))	(bind def)
 - 	   == Label (sm >>= \m -> return m)			(co-induction)
 - 	   == Label (sm >>= return)				(eta reduction)
 - 	   == Label sm						(2nd monad law for Monad s)
 -
 - 3. (m >>= f) >>= g = m >>= (\x -> f x >>= g)
 - 
 -   By induction
 -     case m of
 -     1) (Return y >>= f) >>= g 
 -	  == f y >>= g					(bind def)
 -	  == (\x -> f x >>= g) y			(beta expansion)
 -	  == Return y >>= (\x -> f x >>= g)		(bind def)
 -     2) (Fail >>= f) >>= g
 -        == Fail >>= g					(bind def)
 -        == Fail					(bind def)
 -        == Fail >>= (\x -> f x >>= g)			(bind def) 
 -     3) (Try l r >>= f) >>= g
 -        == Try (l >>= f) (r >>= f)) >>= g 				(bind def)
 -        == Try ((l >>= f) >>= g) ((r >>= f) >>= g)			(bind def)
 -        == Try (l >>= (\x -> f x >>= g)) (r >>= (\x -> f x >>= g)) 	(induction)
 -        == Try l r >>= (\x -> f x >>= g)				(bind def)
 -     4) (NewVar m >>= f) >>= g
 -        == NewVar (\v -> m v >>= f) >>= g			(bind def)
 -        == NewVar (\w -> (\v -> m v >>= f) w >>= g)		(bind def)
 -        == NewVar (\w -> (m w >>= f) >>= g)			(beta reduction)  
 -        == NewVar (\w -> m w >>= (\x -> f x >>= g))		(co-induction)
 -        == NewVar m >>= (\x -> f x >>= g)			(bind def)
 -     5) (Label sm >>= f) >>= g
 -         == Label (sm >>= \m -> return (m >>= f)) >>= g 	(bind def) 
 -         == Label ((sm >>= \m -> return (m >>= f)) >>= \m' -> return (m' >>= g))
 -         == Label (sm >>= (\m -> return (m >>= f) >>= \m' -> return (m' >>= g)))
 -         == Label (sm >>= \m -> return ((m >>= f) >>= g))
 -         == Label (sm >>= \m -> return (m >>= (\x -> f x >>= g)))
 -         == Label sm >>= (\x -> f x >>= g)
 -
 -}

-------------------------------------------------------------------------------
----------------------------------- Sugar -------------------------------------
-------------------------------------------------------------------------------
 
infixr 3 /\
(/\) :: Solver s => Tree s a -> Tree s b -> Tree s b
(/\) = (>>)
 
infixl 2 \/
(\/) :: Solver s => Tree s a -> Tree s a -> Tree s a
(\/) = Try

false :: Tree s a
false = Fail
 
true :: Tree s ()
true = Return ()

disj :: Solver s => [Tree s a] -> Tree s a
disj = foldr (\/) false

conj :: Solver s => [Tree s ()] -> Tree s ()
conj = foldr (/\) true

disj2 :: Solver s => [Tree s a] -> Tree s a
disj2 (x:  [])  = x
disj2 l        = let (xs,ys)      = split l
                     split []     = ([],[])
                     split (a:as) = let (bs,cs) = split as
                                    in  (a:cs,bs)
                 in  Try (disj2 xs) (disj2 ys)
 
exists :: Term s t => (t -> Tree s a) -> Tree s a
exists f = NewVar f

exist :: (Solver s, Term s t) => Int -> ([t] -> Tree s a) -> Tree s a
exist n ftree = f n []
         where f 0 acc  = ftree acc
               f n acc  = exists $ \v -> f (n-1) (v:acc)

forall :: (Solver s, Term s t)  => [t] -> (t -> Tree s ()) -> Tree s ()
forall list ftree = conj $ map ftree list
 
label :: Solver s => s (Tree s a) -> Tree s a
label = Label

prim :: Solver s => (s a) -> Tree s a
prim action = Label (action >>= return . return)

add :: Solver s => Constraint s -> Tree s ()
add c = Add c true
