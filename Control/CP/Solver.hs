{-# OPTIONS_GHC -fglasgow-exts #-}
{-
 - The Solver class, a generic interface for constraint solvers.
 -
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers
 -}
module Control.CP.Solver where 

class Monad solver => Solver solver where
	-- the constraints
	type Constraint solver 	:: *
	-- the terms
	type Term solver 	:: *
 	-- the labels
	type Label solver	:: *
	-- produce a fresh constraint variable
	newvar 	:: solver (Term solver)
	-- add a constraint to the current state, and
	-- return whethe the resulting state is consistent
	add		:: Constraint solver -> solver Bool
	-- run a computation
	run		:: solver a -> a
	-- mark the current state, and return its label
	mark		:: solver (Label solver)
	-- go to the state with given label
	goto		:: Label solver -> solver ()
