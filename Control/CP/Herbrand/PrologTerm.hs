{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Control.CP.Herbrand.PrologTerm  where 

import Data.List (intersperse)

import Control.CP.Herbrand.Herbrand

data PrologTerm = PTerm String [PrologTerm] | PVar VarId
     deriving Eq

instance HTerm PrologTerm where
  mkVar           = PVar
  isVar (PVar v)  = Just v
  isVar _         = Nothing
  children (PTerm f args) 
                  =  (args,\args' -> PTerm f args')
  children t      =  ([],  \[]    -> t)
  nonvar_unify (PTerm f1 args1) (PTerm f2 args2)
                  | f1 == f2   = unify_lists args1 args2
                  | otherwise  = failure
                  where unify_lists []     []      = success
                        unify_lists (x:xs) (y:ys)  =
                          do b <- unify x y
                             if b then unify_lists xs ys
                                  else failure
                        unify_lists _      _       = failure

instance Show PrologTerm where
  show (PVar v)        = 'V' : show v
  show (PTerm f args)  = f ++ "(" ++ (concat $ intersperse "," $ map show args) ++ ")"
