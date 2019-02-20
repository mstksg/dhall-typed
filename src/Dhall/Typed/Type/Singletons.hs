{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# OPTIONS_GHC -Wno-orphans        #-}

module Dhall.Typed.Type.Singletons (
    PolySing
  , PolySingI(..)
  , PolySingKind(..)
  , SomePolySing(..)
  , WrappedSing(..)
  , SingSing(..)
  , PolySingOfI
  -- * Instances
  , SConst(..), SMaybe(..), SList(..), STup(..), SBool(..), SProxy(..)
  -- ** Natural
  , ToNat, FromNat
  , SNatural(..)
  , withKnownNatural
  -- ** Text
  , ToSym, FromSym
  , SText(..)
  , withKnownText
  ) where

import           Control.Applicative
import           Data.Kind
import           Data.Proxy
import           Data.Text                            (Text)
import           Data.Type.Equality
import           Dhall.Typed.Internal.TH
import           Dhall.Typed.Type.Singletons.Internal
import           GHC.TypeLits                         (Symbol, KnownSymbol, SomeSymbol(..), someSymbolVal, symbolVal)
import           GHC.TypeNats
import           Numeric.Natural
import           Unsafe.Coerce
import qualified Data.Text                            as T

genPolySing ''Const
genPolySing ''Maybe
genPolySing ''Proxy

type family ToNat (n :: Natural) = (m :: Nat) | m -> n where
type family FromNat (m :: Nat)     = (n :: Natural) | n -> m where

withKnownNatural
    :: forall n r. KnownNat n
    => (KnownNat (ToNat (FromNat n)) => r)
    -> r
withKnownNatural x = case natnat @n of
    Refl -> x

natnat :: n :~: ToNat (FromNat n)
natnat = unsafeCoerce Refl

data SNatural :: Natural -> Type where
    SNat :: KnownNat (ToNat n) => SNatural n

type instance PolySing Natural = SNatural

instance KnownNat (ToNat n) => PolySingI (n :: Natural) where
    polySing = SNat

instance PolySingKind Natural where
    fromPolySing :: forall n. SNatural n -> Natural
    fromPolySing = \case
      SNat -> natVal $ Proxy @(ToNat n)

    toPolySing :: Natural -> SomePolySing Natural
    toPolySing n = case someNatVal n of
      SomeNat (Proxy :: Proxy n) -> case natnat @n of
        Refl -> SomePS $ SNat @(FromNat n)

type family ToSym (t :: Text) = (s :: Symbol) | s -> t where
type family FromSym (s :: Symbol) = (t :: Text) | t -> s where

withKnownText
    :: forall n r. KnownSymbol n
    => (KnownSymbol (ToSym (FromSym n)) => r)
    -> r
withKnownText x = case symsym @n of
    Refl -> x

symsym :: n :~: ToSym (FromSym n)
symsym = unsafeCoerce Refl

data SText :: Text -> Type where
    SText :: KnownSymbol (ToSym t) => SText t

type instance PolySing Text = SText

instance KnownSymbol (ToSym t) => PolySingI (t :: Text) where
    polySing = SText

instance PolySingKind Text where
    fromPolySing :: forall t. SText t -> Text
    fromPolySing = \case
      SText -> T.pack . symbolVal $ Proxy @(ToSym t)

    toPolySing :: Text -> SomePolySing Text
    toPolySing t = case someSymbolVal (T.unpack t) of
      SomeSymbol (Proxy :: Proxy t) -> case symsym @t of
        Refl -> SomePS $ SText @(FromSym t)
