-- {-# OPTIONS -fglasgow-exts -XNoMonomorphismRestriction -XOverlappingInstances #-}

{-# LANGUAGE NoMonomorphismRestriction #-}
{-# LANGUAGE OverlappingInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Monatron.Open where

import Control.Monatron.Monatron ()
import Control.Monatron.AutoLift

infixr 9 :+:
infixr 9 <@>

data (:+:) f g a = Inl (f a) | Inr (g a)

newtype Fix f = In {out :: f (Fix f)}

type Open e f r = (e -> r) -> (f e -> r)

(<@>) :: Open e f r -> Open e g r -> Open e (f :+: g) r
evalf <@> evalg = \eval e -> 
  case e of
    Inl el  -> evalf eval el
    Inr er  -> evalg eval er       
    
fix :: Open (Fix f) f r -> (Fix f -> r)
fix f =  let this = f this . out 
         in this
            
-- Borrowed from Data types \`a la Carte

class (f :<: g) where
  inj :: f a -> g a
 
instance Functor f => (:<:) f f where
  inj = id
 
instance  (Functor g, Functor f) 
          => (:<:) f (f :+: g) where
  inj = Inl
 
instance  (Functor g, Functor h, Functor f, f :<: g) 
          => (:<:) f (h :+: g) where 
  inj = Inr . inj

inject :: (f :<: g) => f (Fix g) -> Fix g
inject = In . inj

instance (Functor f, Functor g) => 
 Functor (f :+: g) where
  fmap f (Inl x)  = Inl (fmap f x)
  fmap f (Inr y)  = Inr (fmap f y)
  
foldFix :: Functor f => (f a -> a) ->  Fix f -> a
foldFix f = f . fmap (foldFix f) . out 
