{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TransformListComp #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.CP.EnumTerm (
  EnumTerm,
  TermDomain,
  get_domain_size,
  get_value,
  split_domain_partial,
  split_domain,
  split_domains,
  in_order,
  firstfail,
  middleout,
  endsout,
  interleave,
  assignment,
  assignments,
  enumerate,
  label
) where

import GHC.Exts (sortWith)

import Data.List (splitAt)
import Control.CP.SearchTree hiding (label)
import Control.CP.Solver

--------------------------------------------------------------------------------
-- ENUMERATION
--------------------------------------------------------------------------------

class (Term s t, Enum (TermDomain s t)) => EnumTerm s t where
	type TermDomain s t :: *
	get_domain_size :: t -> s Int
	get_value :: t -> s (Maybe (TermDomain s t))
	split_domain_partial :: t -> s [Tree s ()]
	
	split_domain :: t -> s (Tree s ())
	split_domain v = do
	  let rec tree = do
	        tree
	        Label $ do
	          x <- get_value v
	          case x of
	            Nothing -> split_domain v
	            Just _ -> return $ return ()
	  lst <- split_domain_partial v
	  return $ levelList $ map rec lst
	
	split_domains :: [t] -> s (Tree s ())
	split_domains [] = return $ return ()
	split_domains [a] = split_domain a
	split_domains (a:b) = do
	  ta <- split_domain a
	  tb <- split_domains b
	  return $ ta /\ tb
	
	label :: ([t] -> s [t]) -> [t] -> Tree s ()
	label o l = Label $ do
	  x <- o l
	  split_domains x
	
	enumerate :: [t] -> Tree s ()
	enumerate l = label firstfail l

levelList :: Solver s => [Tree s ()] -> Tree s ()
levelList [] = Fail
levelList [a] = a
levelList l = 
  let len = length l
      (p1,p2) = splitAt (len `div` 2) l
      in Try (levelList p1) (levelList p2)


in_order :: Monad m => a -> m a
in_order = return 

firstfail qs = do ds <- mapM get_domain_size qs 
                  return [ q | (d,q) <- zip ds qs 
                             , then sortWith by d ]

middleout l = let n = (length l) `div` 2 in
              interleave (drop n l) (reverse $ take n l)

endsout  l = let n = (length l) `div` 2 in
              interleave (reverse $ drop n l) (take n l)

interleave []     ys = ys
interleave (x:xs) ys = x:interleave ys xs

--------------------------------------------------------------------------------
-- RESULT
--------------------------------------------------------------------------------

assignment ::  EnumTerm s t => t -> Tree s (TermDomain s t)
assignment q = Label $ get_value q >>= \(Just x) -> return $ Return x

assignments :: EnumTerm s t => [t] -> Tree s [TermDomain s t]
assignments = mapM assignment
