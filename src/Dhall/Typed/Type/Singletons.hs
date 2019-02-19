{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}

module Dhall.Typed.Type.Singletons (
    PolySing
  , PolySingI(..)
  , PolySingKind(..)
  , SomePolySing(..)
  , WrappedSing(..)
  , SingSing(..)
  , PolySingOfI
  ) where

import           Control.Applicative
import           Data.Kind
import           Dhall.Typed.Internal.TH
import           Dhall.Typed.Type.Singletons.Internal
import           GHC.TypeLits
import           Numeric.Natural

genPolySing ''Const


-- data FatNat :: Type where
--     FatNat = Vk
-- type family

-- data SNatural :: Natural -> Type where
    -- SNatural :: KnownNat n => SNatural n
-- type instance Sing
-- genPolySing ''Natural
