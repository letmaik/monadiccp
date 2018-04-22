{-# OPTIONS -XTypeOperators -XFlexibleContexts #-}

module Control.Monatron.ZipperExamples where

import Control.Monatron.Monatron
import Control.Monatron.Zipper
import Control.Monatron.Open

-- Don't we need a bidirectional view to implement this combinator?

fmask :: (m :><: n) -> Open e f (n a) -> Open e f (m a)
fmask v evalf eval = from v . evalf (to v . eval)

type Env = [(String,Int)]

type Count = Int

data Mem e  = Store e | Retrieve

type Reg    = Int
 
evalMem2  :: (StateM Reg (t m), StateM Count m, MonadT t) 
             => Open e Mem (t m Int)
evalMem2 eval (Store e) =
  do  count <- lift $ get
      lift $ put (count + 1)
      n <- eval e
      put n
      return n
evalMem2 eval Retrieve = lift $ get

type M4 =  StateT Reg (StateT Env (ExcT String (StateT Count Id)))

data Lit a = Lit Int
data Var a = Var String
data Add e = Add e e

instance Functor Lit where
  fmap _ (Lit l)      = Lit l

instance Functor Var where
  fmap _ (Var v)      = Var v

instance Functor Add where
  fmap f (Add e1 e2)  = Add (f e1) (f e2)
  
instance Functor Mem where
  fmap f (Store x)  = Store (f x)
  fmap f Retrieve   = Retrieve
  
lit :: (Lit :<: g)  => Int -> Fix g
lit l      = inject (Lit l)

var :: (Var :<: g)  => String -> Fix g 
var v      = inject (Var v)

add :: (Add :<: g)  => Fix g -> Fix g -> Fix g
add e1 e2  = inject (Add e1 e2)

store :: (Mem :<: g) => Fix g -> Fix g
store e = inject (Store e)

retrieve :: (Mem :<: g) => Fix g
retrieve = inject Retrieve

type Expr3  = Fix (Mem :+: Var :+: Lit)

evalLit _ (Lit n) = return n 

evalVar _ (Var v) = do env <- get
                       case lookup v env of
                         Just n -> return n
                         Nothing -> throw "undefined variable"

eval4 :: Expr3 -> M4 Int
eval4 = fix  (    fmask (i `vcomp` o `vcomp` o) evalMem2
             <@>  fmask o evalVar  
             <@>  evalLit)
        
test = runId $ runStateT 0 $ handleExc $ runStateT [] $ runStateT 0 $ eval4 (store (lit 3))

handleExc :: Monad m => ExcT a m b -> m b
handleExc = liftM (either (error "Error!") id) . runExcT
