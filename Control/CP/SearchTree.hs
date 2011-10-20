{-
 - The Tree data type, a generic modelling language for constraint solvers.
 -
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers
 -}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.CP.SearchTree (
  Tree(..),
  transformTree,
  bindTree,
  insertTree,
  (/\),
  true,
  disj,
  conj,
  disj2,
  prim,
  addC,
  addT,
  exist,
  forall,
  indent,
  showTree,
  mapTree,
  MonadTree(..),
  untree
) where

import Control.CP.Solver
import Control.Mixin.Mixin

import Control.Monad
import Control.Monad.Cont
import Control.Monad.Reader
import Control.Monad.Writer
import Control.Monad.State

import Data.Monoid


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

flattenTree :: Solver s => Tree s a -> Maybe ([Constraint s],a)
flattenTree Fail = Nothing
flattenTree (Return a) = Just ([],a)
flattenTree (Try _ _) = Nothing
flattenTree (Add c t) = case flattenTree t of
  Nothing -> Nothing
  Just (l,a) -> Just (c:l,a)
flattenTree (NewVar _) = Nothing
flattenTree (Label _) = Nothing

transformTree :: Solver s => Mixin (Tree s a -> Tree s a)
transformTree _ _ Fail = Fail
transformTree _ _ (Return x) = Return x
transformTree _ t (Try x y) = Try (t x) (t y)
transformTree _ t (Add c x) = Add c (t x)
transformTree _ t (NewVar f) = NewVar (\x -> t $ f x)
transformTree _ t (Label m) = Label $ m >>= return . t
-- transformTree s _ x = s x

mapTree :: (Solver s1, Solver s2, MonadTree m, TreeSolver m ~ s2) => (forall t. s1 t -> s2 t) -> Tree s1 a -> m a
mapTree _ Fail = false
mapTree _ (Return a) = return a
mapTree f (Try a b) = mapTree f a \/ mapTree f b
-- mapTree f (Add c n) = label $ f $ (add c >>= \t -> if t then return (mapTree f n) else return false)
-- mapTree (NewVar _) = undefined
mapTree f (Label l) = label $ (f l) >>= (\t -> return (mapTree f t))

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
(NewVar f)   `bindTree` k  = NewVar (\x -> f x `bindTree` k)    
(Label m)      `bindTree` k  = Label (m >>= \t -> return (t `bindTree` k))

insertTree     :: Solver s => Tree s a -> Tree s () -> Tree s a
(NewVar f)   `insertTree` t  = NewVar (\x -> f x `insertTree` t)    
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
 - 	5) NewVar i f >>= return
 - 	   == NewVar i (\v -> f v >>= return) 	(bind def) 
 - 	   == NewVar i (\v -> f v)		((co)-induction?)
 - 	   == NewVar i f				(eta reduction)
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
 -     4) (NewVar i m >>= f) >>= g
 -        == NewVar i (\v -> m v >>= f) >>= g			(bind def)
 -        == NewVar i (\w -> (\v -> m v >>= f) w >>= g)		(bind def)
 -        == NewVar i (\w -> (m w >>= f) >>= g)			(beta reduction)  
 -        == NewVar i (\w -> m w >>= (\x -> f x >>= g))		(co-induction)
 -        == NewVar i m >>= (\x -> f x >>= g)			(bind def)
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
----------------------------------- Monad Subclass ----------------------------
-------------------------------------------------------------------------------

infixl 2 \/

-- | Generalization of the search tree data type,
--   allowing monad transformer decoration.
class (Monad m, Solver (TreeSolver m)) => MonadTree m where
  type TreeSolver m :: * -> *
  addTo   :: Constraint (TreeSolver m) -> m a -> m a
  false   :: m a
  (\/)    :: m a -> m a -> m a
  exists  :: Term (TreeSolver m) t => (t -> m a) -> m a
  label   :: (TreeSolver m) (m a) -> m a

instance Solver solver => MonadTree (Tree solver) where
  type TreeSolver (Tree solver)  = solver
  addTo   =  Add
  false   =  Fail
  (\/)    =  Try
  exists  =  NewVar
  label   =  Label

instance (MonadTree m, Solver (TreeSolver m)) => MonadTree (ContT r m) where
  type TreeSolver (ContT r m) = TreeSolver m
  addTo constraint cm = ContT $ \k -> addTo constraint (runContT cm k) 
  false               = lift false
  l \/ r              = ContT $ \k -> (runContT l k) \/ (runContT r k)
  exists f            = ContT $ \k -> exists (\t -> runContT (f t) k)
  label scm           = ContT $ \k -> label (scm >>= \cm -> return $ runContT cm k)

-------------------------------------------------------------------------------
----------------------------------- Sugar -------------------------------------
-------------------------------------------------------------------------------
 
infixr 3 /\
(/\) :: MonadTree tree => tree a -> tree b -> tree b
(/\) = (>>)
 
true :: MonadTree tree  => tree ()
true = return ()

disj :: MonadTree tree => [tree a] -> tree a
disj [] = false
disj a = foldr1 (\/) a

conj :: MonadTree tree => [tree ()] -> tree ()
conj [] = true
conj a = foldr1 (/\) a

disj2 :: MonadTree tree => [tree a] -> tree a
disj2 (x:  [])  = x
disj2 l        = let (xs,ys)      = split l
                     split []     = ([],[])
                     split (a:as) = let (bs,cs) = split as
                                    in  (a:cs,bs)
                 in  (disj2 xs) \/ (disj2 ys)

prim :: MonadTree tree => TreeSolver tree a -> tree a
prim action = label (action >>= return . return)

addC :: MonadTree tree => Constraint (TreeSolver tree) -> tree ()
addC c = c `addTo` true

addT :: MonadTree tree => Constraint (TreeSolver tree) -> tree Bool
addT c = c `addTo` (return True)

exist :: (MonadTree tree, Term (TreeSolver tree) t) => Int -> ([t] -> tree a) -> tree a
exist n ftree = f n []
         where f 0 acc  = ftree $ reverse acc
               f n acc  = exists $ \v -> f (n-1) (v:acc)

forall :: (MonadTree tree, Term (TreeSolver tree) t)  => [t] -> (t -> tree ()) -> tree ()
forall list ftree = conj $ map ftree list

-- Shortcut the search procedure for a Tree that does not contain Try nodes.
-- create a solver monad that returns the result of the Tree, or a specified
-- value upon failure
untree :: Solver s => v -> Tree s v -> s v
untree _ (Return x) = return x
untree _ (Try _ _) = error "convertion of Try nodes to solver is not supported"
untree e (Fail) = return e
untree e (Label s) = s >>= untree e
untree e (Add c t) = (add c) >>= (\x -> if x then untree e t else return e)
untree e (NewVar f) = do
    v <- newvar
    untree e (f v)

-- | show

indent :: Int -> String
indent l = replicate (2*l) ' '

showTree :: (Show (Constraint s), Show a, Solver s) => Int -> Tree s a -> s String
showTree l Fail = return $ indent l ++ "Fail\n"
showTree l (Return x) = return $ indent l ++ "Return [" ++ (show x) ++ "]\n"
showTree l (Try a b) = do
  m <- mark
  s1 <- showTree (l+1) a
  goto m
  s2 <- showTree (l+1) b
  return $ indent l ++ "Try\n" ++ s1 ++ s2
showTree l (Add c t) = do
  s <- showTree (l+1) t
  return $ indent l ++ "Add (" ++ (show c) ++ ")\n" ++ s
showTree l (NewVar f) = do
  n <- newvar
  s <- showTree (l+1) (f n)
  return $ indent l ++ "NewVar\n" ++ s
showTree l (Label a) = do
  r <- a
  s <- showTree (l+1) r
  return $ indent l ++ "Label\n" ++ s

instance Show (Tree s a)  where
  show Fail		= "Fail"
  show (Return _)	= "Return"
  show (Try l r)	= "Try (" ++ show l ++ ") (" ++ show r ++ ")"
  show (Add _ t)	= "Add (" ++ show t ++ ")"
  show (NewVar _)	= "NewVar <function>"
  show (Label _)	= "Label <monadic value>"

----------------------------------------------------------------------
-- Monad Transformer Instances
----------------------------------------------------------------------

instance MonadTree t => MonadTree (ReaderT env t) where
  type TreeSolver (ReaderT env t) = TreeSolver t
  addTo constraint tree  = ReaderT $ \env -> addTo constraint (runReaderT tree env)
  false     = lift false
  l \/ r    = ReaderT $ \env -> runReaderT l env \/ runReaderT r env
  exists f  = ReaderT $ \env -> exists (\var -> runReaderT (f var) env)
  label p   = ReaderT $ \env -> label (p >>= \m -> return $ runReaderT m env)

instance (Monoid w, MonadTree t) => MonadTree (WriterT w t) where
  type TreeSolver (WriterT w t)  = TreeSolver t
  addTo constraint tree  = WriterT $ addTo constraint (runWriterT tree)
  false     = lift false 
  l \/ r    = WriterT $ runWriterT l \/ runWriterT r
  exists f  = WriterT $ exists (\var -> runWriterT (f var))
  label p   = WriterT $ label (p >>= \m -> return $ runWriterT m)

instance MonadTree t => MonadTree (StateT s t) where
  type TreeSolver (StateT s t) = TreeSolver t
  addTo constraint tree  = StateT $ \s -> addTo constraint (runStateT tree s)
  false     = lift false
  l \/ r    = StateT $ \s -> runStateT l s \/ runStateT r s
  exists f  = StateT $ \s -> exists (\var -> runStateT (f var) s)
  label p   = StateT $ \s -> label (p >>= \m -> return $ runStateT m s)
