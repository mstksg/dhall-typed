{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Dhall.Typed.Prod (
    Prod(..)
  , traverseProd
  , zipProd
  , singProd
  ) where

import           Data.Kind
import           Data.Singletons.Prelude.List
import           GHC.Generics

data Prod :: (k -> Type) -> [k] -> Type where
    Ø    :: Prod f '[]
    (:<) :: f a -> Prod f as -> Prod f (a ': as)

infixr 5 :<

traverseProd
    :: forall f g h as. Applicative h
    => (forall x. f x -> h (g x))
    -> Prod f as
    -> h (Prod g as)
traverseProd f = go
  where
    go  :: Prod f bs -> h (Prod g bs)
    go = \case
      Ø -> pure Ø
      x :< xs -> (:<) <$> f x <*> go xs

zipProd
    :: Prod f as
    -> Prod g as
    -> Prod (f :*: g) as
zipProd = \case
    Ø -> \case
      Ø -> Ø
    x :< xs -> \case
      y :< ys -> (x :*: y) :< zipProd xs ys

singProd
    :: Sing as
    -> Prod Sing as
singProd = \case
    SNil -> Ø
    x `SCons` xs -> x :< singProd xs
