{-
 - The Solver class, a generic interface for constraint solvers.
 -
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers
 -}

{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.CP.Solver (
  Solver,
  Constraint,
  Label,
  add,
  run,
  mark, markn,
  goto,
  Term,
  newvar,
  Help,
  help,
) where 

import Control.Monad.Writer
import Data.Monoid

class Monad solver => Solver solver where
	-- | the constraints
	type Constraint solver 	:: *
 	-- | the labels
	type Label solver	:: *
	-- | add a constraint to the current state, and
	--   return whether the resulting state is consistent
	add		:: Constraint solver -> solver Bool
	-- | run a computation
	run		:: solver a -> a
	-- | mark the current state, and return its label
	mark		:: solver (Label solver)
	-- | mark the current state as discontinued, yet return a label that is usable n times
	markn		:: Int -> solver (Label solver)
	-- | go to the state with given label
	goto		:: Label solver -> solver ()
	
	markn _ = mark

class (Solver solver) => Term solver term where
	-- | produce a fresh constraint variable
	newvar 	:: solver term

        -- see note [Solver-Specific Term Operations]
        type Help solver term
        help :: solver () -> term -> Help solver term

-- [Solver-Specific Term Operations]
--
-- Terms of solvers in general only support the 'newvar' operation.
-- However, for specific solvers, all terms may support additional
-- operations.
--
-- The 'Help'/'help' infrastructure allows accessing this solver-specific
-- term operations.

-- | WriterT decoration of a solver
--   useful for producing statistics during solving
instance (Monoid w, Solver s) => Solver (WriterT w s) where
  type Constraint (WriterT w s)  = Constraint s
  type Label (WriterT w s)       = Label s
  add  = lift . add
  run  = fst . run . runWriterT
  mark = lift mark
  markn = lift . markn
  goto = lift . goto 

instance (Monoid w, Term s t) => Term (WriterT w s) t where
  newvar  = lift newvar
  type Help (WriterT w s) t = ()
  help _ _ = ()
