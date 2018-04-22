-- | Module with basic infrastructure for function inheritance
--   based on open rercusion.
--
--   See the work of William Cook.
--
--   We use the following terminology.
--
--     * A /closed/ function is an ordinary function. 
--
--     * A /mixin/ function is an open function that can be
--       inherited from, or that extends another open function.
--
--   We obtain a closed function from a base mixin 'base'
--   and a number of mixin extensions 'e1',...,'en' as follows:
--
-- >  mixin (en <@> ... <@> e1 <@> base)
--  
module Control.Mixin.Mixin (
  Mixin,
  (<@>),
  mixin,
  mixinId,
  mixinLift
) where

infixl 5 <@>

-- | Type of mixin functions.
type Mixin a =  a -- the 'super' function
	     -> a -- the 'this'  function
	     -> a -- the current function

-- | Mixin composition.
(<@>) :: Mixin a -> Mixin a -> Mixin a
(f1 <@> f2) super this = f1 (f2 super this) this

-- | Turn a mixin into a closed function.
mixin :: Mixin a -> a
mixin openF 
  = let closedF = openF errorF closedF 
        errorF  = error $ "super called in base mixin"
    in closedF

-- | Mixin identity function.
--
-- Identity for mixin composition:
-- 
--   
-- > mixinId <@> f  ==  f
-- > f <@> mixinId  ==  f
--  
mixinId :: Mixin a
mixinId super this = super

-- | Mixin lift function
--
-- > mixin . mixinLift = id

mixinLift :: (a -> b) -> Mixin (a -> b)
mixinLift f _ _ = f
