{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}

-- A kid goes into a grocery store and buys four items. The cashier charges $7.11. 
-- The kid pays and is about to leave when the cashier calls the kid back, and says 
-- "Hold on, I multiplied the four items instead of adding them; I'll try again... 
-- Gosh, with adding them the price still comes to $7.11"! What were the prices of 
-- the four items?

import Data.Char (ord)

import Control.CP.FD.Example
import Control.CP.FD.Interface
import Control.CP.FD.Model
import Control.CP.SearchTree
import Control.CP.Solver


(@==) :: (MonadTree m, TreeSolver m ~ s, Constraint s ~ Either Model q) => ModelInt -> ModelInt -> m ()
(@==) = (@=)


word :: ModelCol -> String -> ModelInt
word lst = foldr (\x -> (lst!(cte $ ord x - ord 'a')+)) (cte 0)

model :: ExampleModel ()
model _ = exists $ \col -> do
  size col @= cte 26
  allDiff col
  col `allin` (cte 1,cte 26)
  word col "ballet"    @== 45
  word col "cello"     @== 43
  word col "concert"   @== 74
  word col "flute"     @== 30
  word col "fugue"     @== 50
  word col "glee"      @== 66
  word col "jazz"      @== 58
  word col "lyre"      @== 47
  word col "oboe"      @== 53
  word col "opera"     @== 65
  word col "polka"     @== 59
  word col "quartet"   @== 50
  word col "saxophone" @== 134
  word col "scale"     @== 51
  word col "solo"      @== 37
  word col "song"      @== 61
  word col "soprano"   @== 82
  word col "theme"     @== 72
  word col "violin"    @== 100
  word col "waltz"     @== 34
  return col

main = example_sat_main_void model
