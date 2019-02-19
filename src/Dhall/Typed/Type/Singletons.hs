{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Dhall.Typed.Type.Singletons (
    PolySing
  , PolySingI(..)
  , PolySingKind(..)
  , SomePolySing(..)
  , WrappedSing(..)
  , SingSing(..)
  , PolySingOfI
  -- * Instances
  , SNatural(..)
  ) where

import           Control.Applicative
import           Data.Kind
import           Data.Proxy
import           Data.Type.Equality
import           Dhall.Typed.Internal.TH
import           Dhall.Typed.Type.Singletons.Internal
import           GHC.TypeNats
import           Numeric.Natural
import           Unsafe.Coerce

genPolySing ''Const
genPolySing ''Maybe


-- data FatNat :: Type where
--     FatNat :: Natural -> FatNat

-- data SFatNat :: FatNat -> Type where
--     SFN :: SFatNat ('FatNat n)

type family NatuNat (n :: Natural) = (m :: Nat) | m -> n
type family NatNatu (m :: Nat)     = (n :: Natural) | n -> m

natunat :: n :~: NatuNat (NatNatu n)
natunat = unsafeCoerce Refl

data SNatural :: Natural -> Type where
    SNatural :: KnownNat (NatuNat n) => SNatural n

type instance PolySing Natural = SNatural

instance KnownNat (NatuNat n) => PolySingI (n :: Natural) where
    polySing = SNatural

instance PolySingKind Natural where
    fromPolySing :: forall n. SNatural n -> Natural
    fromPolySing = \case
      SNatural -> fromIntegral (natVal (Proxy @(NatuNat n)))
  
    toPolySing :: Natural -> SomePolySing Natural
    toPolySing n = case someNatVal n of
      SomeNat (Proxy :: Proxy n) -> case natunat @n of
        Refl -> SomePS $ SNatural @(NatNatu n)
