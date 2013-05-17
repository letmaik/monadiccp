{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Search.Stat
  ( appStat
  , constStat
  , depthStat
  , nodesStat
  , discrepancyStat
  , solutionsStat
  , failsStat
  , timeStat
  , notStat
  , Stat(..), IValue, varStat
  , (#>), (#<), (#>=), (#<=), (#=), (#/)
  , readStat, evalStat
  ) where

import Text.PrettyPrint hiding (space)

import Control.Search.Language
import Control.Search.GeneratorInfo
import Control.Search.Memo
import Control.Search.Generator

-- ========================================================================== --
-- IVALUE
-- ========================================================================== --

type IValue = Info -> Value

instance Show (Info -> Value) where
  show x  = "<IValue>"
instance Eq (Info -> Value) where
  x == y  = False

instance Num (Info -> Value) where
  x - y          = \i -> x i - y i
  fromInteger x  = \i -> IVal (fromInteger x)
  x + y          = \i -> x i + y i
  x * y          = \i -> x i * y i
  abs x          = \i -> abs (x i)
  signum x       = \i -> signum (x i)

-- ========================================================================== --
-- STATS
-- ========================================================================== --

data Stat =   Stat (forall m. Evalable m => Eval m -> Eval m) (forall m. Evalable m => m IValue)

instance Show Stat where
  show _  = "<Stat>"

instance Eq Stat where
  _ == _ = False

readStat :: Evalable m => Stat -> m IValue
readStat (Stat _ r) = r

evalStat :: Evalable m => Stat -> Eval m -> Eval m
evalStat (Stat e _) = e

-- -------------------------------------------------------------------------- --

instance Num Stat where
  x - y          = liftStat (-) x y
  fromInteger    = constStat . fromInteger
  x + y          = liftStat (+) x y
  x * y          = liftStat (*) x y
  abs            = appStat abs
  signum         = appStat signum

instance Bounded Stat where
  maxBound       = constStat $ const MaxVal
  minBound       = constStat $ const MinVal

appStat :: (Value -> Value) -> Stat -> Stat
appStat f (Stat e r) = Stat e (r >>= \x -> return (\i -> f (x i)))

liftStat :: (Value -> Value -> Value) -> Stat -> Stat -> Stat
liftStat op (Stat e1 x) (Stat e2 y) = Stat (e1 . e2) (x >>= \xv -> y >>= \yv -> return (\i -> xv i `op` yv i))

constStat :: IValue -> Stat
constStat x = Stat id (return x)

(#>) :: Stat -> Stat -> Stat
(#>) = liftStat (@>)

(#=) :: Stat -> Stat -> Stat
(#=) = liftStat (@==)

(#<) :: Stat -> Stat -> Stat
(#<) = liftStat (@<)

(#>=) :: Stat -> Stat -> Stat
(#>=) = liftStat (@>=)

(#<=) :: Stat -> Stat -> Stat
(#<=)  = liftStat (@<=)

(#/) :: Stat -> Stat -> Stat
(#/)   = liftStat (divValue)

notStat :: Stat -> Stat
notStat = appStat Not
-- -------------------------------------------------------------------------- --

depthStat :: Stat
depthStat = 
  Stat (\super -> 
               let push dir = \i -> dir super (i `onCommit` mkUpdate i "depth" (\x -> x + 1))
	       in commentEval $ super
                     { treeState_ = entry ("depth",Int,assign $ 0) : treeState_ super
		     , pushLeftH   = push pushLeft
                     , pushRightH  = push pushRight
                     , toString   = "stat_depth:" ++ toString super
                     })
       (return (\info -> tstate info @-> "depth"))

discrepancyStat :: Stat
discrepancyStat = 
  Stat 
    (\super -> commentEval $
       super
         { treeState_ = entry ("discrepancy",Int,assign 0) : treeState_ super
         , pushLeftH   = \i -> pushLeft  super (i `onCommit` mkCopy i "discrepancy")
         , pushRightH  = \i -> pushRight super (i `onCommit` mkUpdate i "discrepancy" (\x -> x + 1))
         , toString = "stat_discr:" ++ toString super
         })
    (return (\info -> tstate info @-> "discrepancy"))

nodesStat :: Stat
nodesStat = 
  eStat ("nodes", Int, const 0) $
          \super -> super { bodyH = \i -> return (inc (estate i @=> "nodes")) @>>>@ bodyE super i }

solutionsStat :: Stat
solutionsStat = 
  eStat ("solutions", Int, const 0) $
           \super -> super {returnH  = \i -> returnE super (i `onCommit` inc (solutions i))}
  where solutions i = estate i @=> "solutions"

varStat :: VarId -> Stat
varStat v@(VarId i) = Stat id (do inf <- lookupVarInfo v
                                  return (const $ estate inf @=> ("var" ++ show i))
                              )

failsStat :: Stat
failsStat = 
  eStat ("fails", Int, const 0) $
          \super -> super { failH = \i -> returnH super i @>>>@ return (inc (fails i)) }
  where fails i = estate i @=> "fails"

eStat :: (String, Type, Info -> Value) -> (forall m. Evalable m => Eval m -> Eval m) -> Stat
eStat (name,typ,val) f =
   Stat (\super -> commentEval $ f $ super { evalState_ = (name,typ,\i -> return (val i)) : evalState_ super, toString = "stat_" ++ name ++ ":" ++ toString super })
        (return (\i -> estate i @=> name))

-- TIMER STATISTIC
--
-- Based on Gecode::Support::Timer.
--
--
--
timeStat :: Stat
timeStat =
   Stat (\super -> commentEval $
		super { evalState_ = ("total",Int, const $ return 0) : 
                                     ("timer",THook "Gecode::Support::Timer",const $ return Null) :
                                     ("running",Bool,const $ return false) :
                                     evalState_ super 
		      , nextDiffH   = \i ->
			return (ifthen (running i) 
			               ((running i <== false) >>> 
	                                (total i <== (total i + (VHook (render $ text "static_cast<int>" <> parens (pretty (timer i) <> text ".stop()"))))))) 
	              , bodyH      = \i -> 
			return (ifthen (Not $ running i) 
			               ((running i <== true) >>> SHook ((render $ pretty $ timer i) ++ ".start();"))) 
		        @>>>@ bodyE super i
                      , toString = "stat_time:" ++ toString super
                      })
       (return (\i -> total i + Cond (running i) (VHook (render $ text "static_cast<int>" <> parens (pretty (timer i) <> text ".stop()"))) 0))
  where running i = estate i @=> "running"
        timer   i = estate i @=> "timer"
        total   i = estate i @=> "total"
