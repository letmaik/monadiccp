{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Linear (
  Linear,
  integerToLinear,
  constToLinear,
  termToLinear,
--  linearOpLinear,
--  linearOpLinears,
  linearToConst,
  linearToTerm,
  linearMultiply,
  linearMult,
  linearToList, linearToListEx,
  getCoef,
) where

import qualified Data.Map as Map
import Data.Map(Map)

data (Ord t, Num v) => Linear t v = Linear v (Map t v)

deriving instance (Num v, Eq v, Ord t, Eq t) => Eq (Linear t v)
deriving instance (Num v, Ord v, Ord t, Eq t) => Ord (Linear t v)
deriving instance (Num v, Show v, Ord t, Show t) => Show (Linear t v)

termToLinear :: (Num v, Ord t) => t -> Linear t v
termToLinear x = Linear 0 $ Map.singleton x 1

integerToLinear :: (Num v, Ord t) => Integer -> Linear t v
integerToLinear = constToLinear . fromInteger

constToLinear :: (Num v, Ord t) => v -> Linear t v
constToLinear x = Linear x Map.empty

-- linearOpLinear :: (Num v, Ord t) => v -> Linear t v -> v -> Linear t v -> Linear t v
-- linearOpLinear a (Linear ac am) b (Linear bc bm) = Linear (a*ac+b*bc) $ Map.filter (/=0) $ Map.unionWith (\ax bx -> ax*a+bx*b) am bm

-- linearOpLinears :: (Num v, Ord t) => [(v,Linear t v)] -> Linear t v
-- linearOpLinears l = foldr (\(c,t) a -> linearOpLinear 1 a c t) (integerToLinear 0) l

linearToList :: (Ord t, Num v) => Linear t v -> [(Maybe t,v)]
linearToList (Linear c m) = [(Nothing,c)] ++ (map (\(a,b) -> (Just a,b)) $ Map.toList m)

linearToListEx :: (Ord t, Num v) => Linear t v -> (v,[(t,v)])
linearToListEx (Linear c m) = (c,Map.toList m)

getCoef :: (Num v, Ord t) => Maybe t -> Linear t v -> v
getCoef Nothing (Linear c _) = c
getCoef (Just t) (Linear _ m) = Map.findWithDefault 0 t m

linearMult :: (Num v, Eq v, Ord t) => v -> Linear t v -> Linear t v
linearMult m (Linear ac am) = Linear (m*ac) $ if (m==0) then Map.empty else Map.filter (/=0) $ Map.map (m*) am

linearMultiply :: (Num v, Eq v, Ord t) => Linear t v -> Linear t v -> Maybe (Linear t v)
linearMultiply (Linear ac am) bl | (Map.null am) = Just $ linearMult ac bl
linearMultiply bl (Linear ac am) | (Map.null am) = Just $ linearMult ac bl
linearMultiply _ _ = Nothing

linearToConst :: (Num v, Ord t) => Linear t v -> Maybe v
linearToConst (Linear c m) | Map.null m = Just c
linearToConst _ = Nothing

linearToTerm :: (Num v, Eq v, Ord t) => Linear t v -> Maybe t
linearToTerm (Linear c m) | (c==0 && (Map.size m)==1) = 
  let (t,v) = Map.findMin m
      in if (v==1) then Just t else Nothing
linearToTerm _ = Nothing

instance (Num v, Eq v, Ord t, Eq t, Show t) => Num (Linear t v) where
  (Linear ac am) + (Linear bc bm) = Linear (ac+bc) $ Map.filter (/=0) $ Map.unionWith (+) am bm
  (Linear ac am) - (Linear bc bm) = Linear (ac-bc) $ Map.filter (/=0) $ Map.unionWith (+) am $ Map.map negate bm
  a * b = case linearMultiply a b of Just x -> x; Nothing -> error "Cannot multiply generic linear expressions"
  negate (Linear ac am) = Linear (-ac) $ Map.map negate am
  abs (Linear ac am) | (Map.null am) = Linear (abs ac) Map.empty
  abs _ = error "Cannot take abs of generic linear expressions"
  signum (Linear ac am) | (Map.null am) = Linear (signum ac) Map.empty
  signum _ = error "Cannot take signum of generic linear expressions"
  fromInteger x = integerToLinear x
