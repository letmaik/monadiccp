module Control.CP.Mixin (
  Mixin,
  (<@>),
  mixin,
  mixinConst,
  mixinId
) where

type Mixin a = a -> a -> a

infixl 5 <@>
(<@>) :: Mixin a -> Mixin a -> Mixin a
(f1 <@> f2) s t = f1 (f2 s t) t

mixin :: Mixin a -> a
mixin f = let 
  x = f (error "super called in top-level mixin") x 
  in x

mixinConst :: a -> a -> a -> a
mixinConst _ _ c = c

mixinId :: Mixin a
mixinId s _ = s
