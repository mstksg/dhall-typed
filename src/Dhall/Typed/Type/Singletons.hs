{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}

module Dhall.Typed.Type.Singletons (
    PolySing
  -- , PolySingOf
  , PolySingI(..)
  -- , SingSing(..)
  ) where

import           Data.Kind
import           Data.Proxy

type family PolySing k = (s :: k -> Type) | s -> k

-- type family PolySingOf (s :: k -> Type) (x :: k) = (y :: s x) | y -> x

class PolySingI (x :: k) where
    -- type PolySingOf x = (y :: s x) | y -> x
    polySing :: PolySing k x

-- newtype SingSing k x :: PolySing k x -> Type where
--     SingSing :: forall k (x :: k) (s :: PolySing k x). PolySing k x -> SingSing k x s

-- type instance PolySing (SingSing k x p) = SingSing (SingSing k x p) x

-- SingSing qq pp rr
