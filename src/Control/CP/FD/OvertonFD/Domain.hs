{- 
 - Origin:
 -     Constraint Programming in Haskell 
 -     http://overtond.blogspot.com/2008/07/pre.html
 -     author: David Overton, Melbourne Australia
 -
 - Modifications:
 -     Monadic Constraint Programming
 -     http://www.cs.kuleuven.be/~toms/Haskell/
 -     Tom Schrijvers
 -} 

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Control.CP.FD.OvertonFD.Domain (
    Domain,
    ToDomain,
    toDomain,
    member,
    isSubsetOf,
    elems,
    intersection,
    difference,
    union,
    empty,
    null,
    singleton,
    isSingleton,
    filterLessThan,
    filterGreaterThan,
    findMax,
    findMin,
    size,
    shiftDomain,
    mapDomain,
    absDomain
) where

import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)
import Prelude hiding (null)
import Control.CP.Debug

data Domain
    = Set IntSet
    | Range !Int !Int
    deriving Show

size :: Domain -> Int
size (Range l u) = u - l + 1
size (Set set)   = IntSet.size set

-- Domain constructors
class ToDomain a where
    toDomain :: a -> Domain

instance ToDomain Domain where
    toDomain = id

instance ToDomain IntSet where
    toDomain = Set

instance Integral a => ToDomain [a] where
    toDomain = toDomain . IntSet.fromList . map fromIntegral

instance (Integral a, Integral b) => ToDomain (a, b) where
    toDomain (a, b) = Range (fromIntegral a) (fromIntegral b)

instance ToDomain () where
    toDomain () = Range (-1000000000) 1000000000 -- minBound maxBound (too sensitive to overflow, e.g. 2 * minBound == 0)

instance Integral a => ToDomain a where
    toDomain a = toDomain (a, a)

-- Operations on Domains
instance Eq Domain where
    (Range xl xh) == (Range yl yh) = xl == yl && xh == yh
    xs == ys = elems xs == elems ys

member :: Int -> Domain -> Bool
member n x@(Set xs) = debugDom "[Domain.member]" x $ n `IntSet.member` xs
member n x@(Range xl xh) = debugDom "[Domain.member]" x $ n >= xl && n <= xh

isSubsetOf :: Domain -> Domain -> Bool
isSubsetOf x@(Set xs) (Set ys) = debugDom "[Domain.isso]" x $ xs `IntSet.isSubsetOf` ys
isSubsetOf x@(Range xl xh) (Range yl yh) = debugDom "[Domain.isso]" x $ xl >= yl && xh <= yh
isSubsetOf x@(Set xs) yd@(Range yl yh) = debugDom "[Domain.isso]" x $ 
    isSubsetOf (Range xl xh) yd where
        xl = IntSet.findMin xs
        xh = IntSet.findMax xs
isSubsetOf (Range xl xh) x@(Set ys) = debugDom "[Domain.isso]" x $ 
    all (`IntSet.member` ys) [xl..xh]

elems :: Domain -> [Int]
elems x@(Set xs) = debugDom "[Domain.elems]" x $ IntSet.elems xs
elems x@(Range xl xh) = debugDom "[Domain.elems]" x $ [xl..xh]

intersection :: Domain -> Domain -> Domain
intersection x@(Set xs) (Set ys) = debugDom "[Domain.intersection]" x $ Set (xs `IntSet.intersection` ys)
intersection x@(Range xl xh) (Range yl yh) = debugDom "[Domain.intersection]" x $ Range (max xl yl) (min xh yh)
intersection x@(Set xs) (Range yl yh) = debugDom "[Domain.intersection]" x $ 
    Set $ IntSet.filter (\x -> x >= yl && x <= yh) xs
intersection x y = intersection y x

union :: Domain -> Domain -> Domain
union x@(Set xs) (Set ys) = debugDom "[Domain.union]" x $ Set (xs `IntSet.union` ys)
union x@(Range xl xh) (Range yl yh) 
      | xh + 1 >= yl || yh+1 >= xl = debugDom "[Domain.union]" x $ Range (min xl yl) (max xh yh)
      | otherwise = debugDom "[Domain.union]" x $ union (Set $ IntSet.fromList [xl..xh]) (Set $ IntSet.fromList [yl..yh]) 
union x@(Set xs) y@(Range yl yh) = debugDom "[Domain.union]" x $ 
      if null x then y 
      else
      let xmin = IntSet.findMin xs
          xmax = IntSet.findMax xs
      in 
      if (xmin + 1 >= yl && xmax - 1 <= yh) 
         then Range (min xmin yl) (max xmax yh)
         else union (Set xs) (Set $ IntSet.fromList [yl..yh])
union x y = union y x

difference :: Domain -> Domain -> Domain
difference (x@(Set xs)) (y@(Set ys)) = debugDom "[Domain.difference]" x $ Set (xs `IntSet.difference` ys)
difference xd@(Range xl xh) (Range yl yh)
    | yl > xh || yh < xl = debugDom "[Domain.difference]" xd $ xd
    | otherwise = debugDom "[Domain.difference]" xd $ Set $ IntSet.fromList [x | x <- [xl..xh], x < yl || x > yh]
difference (x@(Set xs)) (Range yl yh) =
    debugDom "[Domain.difference]" x $ Set $ IntSet.filter (\x -> x < yl || x > yh) xs
difference (x@(Range xl xh)) (Set ys)
    | IntSet.findMin ys > xh || IntSet.findMax ys < xl = debugDom "[Domain.difference]" x $ Range xl xh
    | otherwise = debugDom "[Domain.difference]" x $ Set $
        IntSet.fromList [x | x <- [xl..xh], not (x `IntSet.member` ys)]

null :: Domain -> Bool
null (x@(Set xs)) = debug ("[Domain.null] " ++ printDom x) $ IntSet.null xs
null (x@(Range xl xh)) = debug ("[Domain.null] " ++ printDom x) $ xl > xh

singleton :: Int -> Domain
singleton x = Range x x

isSingleton :: Domain -> Bool
isSingleton (x@(Set xs)) = debugDom "[Domain.isSingleton]" x $ (IntSet.size xs)==1
isSingleton (x@(Range xl xh)) = debug ("[Domain.isSingleton] " ++ printDom x) $ xl == xh

filterLessThan :: Int -> Domain -> Domain
filterLessThan n (x@(Set xs)) = debug ("[Domain.filterLess] " ++ printDom x) $ Set $ IntSet.filter (< n) xs
filterLessThan n (x@(Range xl xh)) = debug ("[Domain.filterLess] " ++ printDom x) $ Range xl (min (n-1) xh)

filterGreaterThan :: Int -> Domain -> Domain
filterGreaterThan n (x@(Set xs)) = debug ("[Domain.filterGreater] " ++ printDom x) $ Set $ IntSet.filter (> n) xs
filterGreaterThan n (x@(Range xl xh)) = debug ("[Domain.filterGreater] " ++ printDom x) $ Range (max (n+1) xl) xh

findMax :: Domain -> Int
findMax (x@(Set xs)) = debug ("[Domain.findMax] " ++ printDom x) $ IntSet.findMax xs
findMax (x@(Range xl xh)) = debug ("[Domain.findMax] " ++ printDom x) $ xh

findMin :: Domain -> Int
findMin (Set xs) = IntSet.findMin xs
findMin (Range xl xh) = xl

empty :: Domain
empty = Range 1 0

shiftDomain :: Domain -> Int -> Domain
shiftDomain (x@(Range l u)) d = debug ("[Domain.shift] " ++ printDom x) $ Range (l + d) (u + d)
shiftDomain (x@(Set xs)) d = debug ("[Domain.shift] " ++ printDom x) $ Set $ IntSet.fromList $ map (+d) (IntSet.elems xs)

mapDomain :: Domain -> (Int -> [Int]) -> Domain
mapDomain d f = debug ("[Domain.map] " ++ printDom d) $ Set $ IntSet.fromList $ concatMap f $ elems d

absDomain :: Domain -> Domain
absDomain d@(Range l u)  | l >= 0     = d
                         | u <  0     = Range (abs u) (abs l)
                         | otherwise  = Range 0 (max (abs l) u)
absDomain d@(Set s)      | IntSet.findMin s >= 0  = d
                         | otherwise              = Set $ IntSet.map abs s

mirrorDomain :: Domain -> Domain
mirrorDomain d@(Range l u)   | l <= 0 && u >= 0  = Range (min l (-u)) (max (-l) u)

printDom :: Domain -> String
printDom (Set cs) = "dom:Set(#" ++ (show $ IntSet.size cs) ++ ")"
printDom (Range l h) = "dom:Range(#" ++ (show $ h-l+1) ++ ":" ++ (show l) ++ "-" ++ (show h) ++ ")"

debugDom :: String -> Domain -> a -> a
debugDom s d a = debug ("[Domain.findMax] " ++ printDom d) a
