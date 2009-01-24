{- 
 - Origin:
 - 	Constraint Programming in Haskell 
 - 	http://overtond.blogspot.com/2008/07/pre.html
 - 	author: David Overton, Melbourne Australia
 -
 - Modifications:
 - 	Monadic Constraint Programming
 - 	http://www.cs.kuleuven.be/~toms/Haskell/
 - 	Tom Schrijvers
 -} 

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE IncoherentInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Domain (
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
    Domain.null,
    singleton,
    isSingleton,
    filterLessThan,
    filterGreaterThan,
    findMax,
    findMin,
    size,
    shiftDomain
) where

import qualified Data.IntSet as IntSet
import Data.IntSet (IntSet)

data Domain
    = Set IntSet
    | Range Int Int
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
    toDomain () = Range minBound maxBound

instance Integral a => ToDomain a where
    toDomain a = toDomain (a, a)

-- Operations on Domains
instance Eq Domain where
    (Range xl xh) == (Range yl yh) = xl == yl && xh == yh
    xs == ys = elems xs == elems ys

member :: Int -> Domain -> Bool
member n (Set xs) = n `IntSet.member` xs
member n (Range xl xh) = n >= xl && n <= xh

isSubsetOf :: Domain -> Domain -> Bool
isSubsetOf (Set xs) (Set ys) = xs `IntSet.isSubsetOf` ys
isSubsetOf (Range xl xh) (Range yl yh) = xl >= yl && xh <= yh
isSubsetOf (Set xs) yd@(Range yl yh) =
    isSubsetOf (Range xl xh) yd where
        xl = IntSet.findMin xs
        xh = IntSet.findMax xs
isSubsetOf (Range xl xh) (Set ys) =
    all (`IntSet.member` ys) [xl..xh]

elems :: Domain -> [Int]
elems (Set xs) = IntSet.elems xs
elems (Range xl xh) = [xl..xh]

intersection :: Domain -> Domain -> Domain
intersection (Set xs) (Set ys) = Set (xs `IntSet.intersection` ys)
intersection (Range xl xh) (Range yl yh) = Range (max xl yl) (min xh yh)
intersection (Set xs) (Range yl yh) =
    Set $ IntSet.filter (\x -> x >= yl && x <= yh) xs
intersection x y = intersection y x

union :: Domain -> Domain -> Domain
union (Set xs) (Set ys) = Set (xs `IntSet.union` ys)
union (Range xl xh) (Range yl yh) 
      | xh + 1 >= yl || yh+1 >= xl = Range (min xl yl) (max xh yh)
      | otherwise = union (Set $ IntSet.fromList [xl..xh]) 
                          (Set $ IntSet.fromList [yl..yh]) 
union x@(Set xs) y@(Range yl yh) =
      if Domain.null x then y 
      else
      let xmin = IntSet.findMin xs
          xmax = IntSet.findMax xs
      in 
      if (xmin + 1 >= yl && xmax - 1 <= yh) 
         then Range (min xmin yl) (max xmax yh)
         else union (Set xs) (Set $ IntSet.fromList [yl..yh])
union x y = union y x

difference :: Domain -> Domain -> Domain
difference (Set xs) (Set ys) = Set (xs `IntSet.difference` ys)
difference xd@(Range xl xh) (Range yl yh)
    | yl > xh || yh < xl = xd
    | otherwise = Set $ IntSet.fromList [x | x <- [xl..xh], x < yl || x > yh]
difference (Set xs) (Range yl yh) =
    Set $ IntSet.filter (\x -> x < yl || x > yh) xs
difference (Range xl xh) (Set ys)
    | IntSet.findMin ys > xh || IntSet.findMax ys < xl = Range xl xh
    | otherwise = Set $
        IntSet.fromList [x | x <- [xl..xh], not (x `IntSet.member` ys)]

null :: Domain -> Bool
null (Set xs) = IntSet.null xs
null (Range xl xh) = xl > xh

singleton :: Int -> Domain
singleton x = Set (IntSet.singleton x)

isSingleton :: Domain -> Bool
isSingleton (Set xs) = case IntSet.elems xs of
    [x] -> True
    _   -> False
isSingleton (Range xl xh) = xl == xh

filterLessThan :: Int -> Domain -> Domain
filterLessThan n (Set xs) = Set $ IntSet.filter (< n) xs
filterLessThan n (Range xl xh) = Range xl (min (n-1) xh)

filterGreaterThan :: Int -> Domain -> Domain
filterGreaterThan n (Set xs) = Set $ IntSet.filter (> n) xs
filterGreaterThan n (Range xl xh) = Range (max (n+1) xl) xh

findMax :: Domain -> Int
findMax (Set xs) = IntSet.findMax xs
findMax (Range xl xh) = xh

findMin :: Domain -> Int
findMin (Set xs) = IntSet.findMin xs
findMin (Range xl xh) = xl

empty :: Domain
empty = Range 1 0

shiftDomain :: Domain -> Int -> Domain
shiftDomain (Range l u) d = Range (l + d) (u + d)
shiftDomain (Set xs) d = Set $ IntSet.fromList $ map (+d) (IntSet.elems xs)
