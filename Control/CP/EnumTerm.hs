{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TransformListComp #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleContexts #-}

module Control.CP.EnumTerm (
  EnumTerm(..),
  assignment, assignments,
  inOrder, firstFail, middleOut, endsOut,
  labelling, levelList, enumerate
) where

import GHC.Exts (sortWith)

import Control.CP.Solver
import Control.CP.SearchTree

class (Solver s, Term s t, Show (TermBaseType s t)) => EnumTerm s t where
  type TermBaseType s t :: *

  getDomainSize :: t -> s (Int)
  getDomain :: t -> s [TermBaseType s t]
  setValue :: t -> TermBaseType s t -> s [Constraint s]
  splitDomain :: t -> s ([[Constraint s]],Bool)
  splitDomains :: [t] -> s ([[Constraint s]],[t])
  getValue :: t -> s (Maybe (TermBaseType s t))
  defaultOrder :: [t] -> s [t]
  enumerator :: (MonadTree m, TreeSolver m ~ s) => Maybe ([t] -> m ())

  getDomainSize x = do
    r <- getDomain x
    return $ length r

  getValue x = do
    d <- getDomain x
    return $ case d of
      [v] -> Just v
      _ -> Nothing
  splitDomain x = do
    d <- getDomain x
    case d of
      [] ->  return ([],True)
      [_] -> return ([[]],True)
      _ ->   do
        rr <- mapM (setValue x) d
        return (rr,True)

  splitDomains [] = return ([[]],[])
  splitDomains (a@(x:b)) = do
    s <- getDomainSize x
    if s==0
      then return ([],[])
      else if s==1 
        then splitDomains b
        else do
          (r,v) <- splitDomain x
          if v
            then return (r,b)
            else return (r,a)

  defaultOrder = firstFail
  enumerator = Nothing

enumerate :: (MonadTree m, TreeSolver m ~ s, EnumTerm s t) => [t] -> m ()
enumerate = case enumerator of
  Nothing -> labelling defaultOrder
  Just x -> x

assignment :: (EnumTerm s t, MonadTree m, TreeSolver m ~ s) => t -> m (TermBaseType s t)
assignment q = label $ getValue q >>= \y -> (case y of Just x -> return $ return x; _ -> return false)

assignments :: (EnumTerm s t, MonadTree m, TreeSolver m ~ s) => [t] -> m [TermBaseType s t]
assignments = mapM assignment

firstFail :: EnumTerm s t => [t] -> s [t]
firstFail qs = do ds <- mapM getDomainSize qs 
                  return [ q | (d,q) <- zip ds qs 
                             , then sortWith by d ]

inOrder :: EnumTerm s t => [t] -> s [t]
inOrder = return

middleOut :: EnumTerm s t => [t] -> s [t]
middleOut l = let n = (length l) `div` 2 in
              return $ interleave (drop n l) (reverse $ take n l)

endsOut :: EnumTerm s t => [t] -> s [t]
endsOut  l = let n = (length l) `div` 2 in
             return $ interleave (reverse $ drop n l) (take n l)

interleave []     ys = ys
interleave (x:xs) ys = x:interleave ys xs

levelList :: (Solver s, MonadTree m, TreeSolver m ~ s) => [m ()] -> m ()
levelList [] = false
levelList [a] = a
levelList l = 
  let len = length l
      (p1,p2) = splitAt (len `div` 2) l
      in (levelList p1) \/ (levelList p2)
--levelList [] = false
--levelList [a] = a
--levelList (a:b) = a \/ levelList b

labelling :: (MonadTree m, TreeSolver m ~ s, EnumTerm s t) => ([t] -> s [t]) -> [t] -> m ()
labelling _ [] = true
labelling o l = label $ do 
  ll <- o l
  (cl,c) <- splitDomains ll
  let ml = map (\l -> foldr (/\) true $ map addC l) cl
  return $ do
    levelList ml
    labelling return c
