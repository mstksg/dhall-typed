{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}

module Dhall.Typed.Type.Singletons (
    PolySing
  , PolySingOf
  , PolySingI(..)
  ) where

import           Data.Kind

type family PolySing k = (s :: k -> Type) | s -> k

type family PolySingOf (s :: k -> Type) (x :: k) = (y :: s x) | y -> x

class PolySingI (x :: k) where
    polySing :: PolySing k x
