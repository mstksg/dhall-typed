{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}


module Dhall.Typed.Type.Sum (
    Sum(..)
  , anySum
  , sumAny
  ) where

import           Data.Kind
import           Data.Type.Universe
import           Data.Singletons

data Sum :: (k -> Type) -> [k] -> Type where
    Sum :: Index as a -> f a -> Sum f as

-- this Show instance is not general enough
deriving instance (forall a. Show (f a)) => Show (Sum f as)

anySum :: WitAny [] (TyCon1 f) as -> Sum f as
anySum (WitAny e f) = Sum e f

sumAny :: Sum f as -> WitAny [] (TyCon1 f) as
sumAny (Sum e f) = WitAny e f
