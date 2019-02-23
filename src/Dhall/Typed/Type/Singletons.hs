{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
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
  , SingEq(..)
  -- * Instances
  , SConst(..), SMaybe(..), SList(..), STup2(..), SBool(..), SProxy(..), STup0(..)
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
import           Data.Singletons.Decide               (Decision(..))
import           Data.Text                            (Text)
import           Data.Type.Equality
import           Dhall.Typed.Type.Singletons.Internal
import           Dhall.Typed.Type.Singletons.TH
import           GHC.TypeLits                         (Symbol, KnownSymbol, SomeSymbol(..), someSymbolVal, symbolVal, sameSymbol)
import           GHC.TypeNats
import           Numeric.Natural
import           Unsafe.Coerce
import qualified Data.Text                            as T

genPolySingWith defaultGPSO
  { gpsoPSK    = GOHead [d| instance PolySingKind a => PolySingKind (Const a b) |]
  , gpsoSingEq = GOHead [d| instance SingEq a b => SingEq (Const a c) (Const b c) |]
  } ''Const

genPolySingWith defaultGPSO
  { gpsoPSK    = GOHead [d| instance PolySingKind a => PolySingKind (Maybe a) |]
  , gpsoSingEq = GOHead [d| instance SingEq a a => SingEq (Maybe a) (Maybe a) |]
  } ''Maybe

genPolySingWith defaultGPSO
  { gpsoPSK    = GOHead [d| instance PolySingKind (Proxy a) |]
  , gpsoSingEq = GOHead [d| instance SingEq (Proxy a) (Proxy a) |]
  } ''Proxy


-- instance SingEq a c => SingEq (Const a b) (Const c b) where
--     singEq = \case
--       SConst x -> \case
--         SConst y -> case singEq x y of
--           Proved HRefl -> Proved HRefl

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

natnat' :: n :~: FromNat (ToNat n)
natnat' = unsafeCoerce Refl

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

instance SingEq Natural Natural where
    singEq = \case
      (SNat :: SNatural n) -> \case
        (SNat :: SNatural m) -> case sameNat (Proxy @(ToNat n)) (Proxy @(ToNat m)) of
          Just Refl -> case natnat' @n of
            Refl -> case natnat' @m of
              Refl -> Proved HRefl
          Nothing   -> Disproved unsafeCoerce

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

symsym' :: n :~: FromSym (ToSym n)
symsym' = unsafeCoerce Refl

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

instance SingEq Text Text where
    singEq = \case
      (SText :: SText n) -> \case
        (SText :: SText m) -> case sameSymbol (Proxy @(ToSym n)) (Proxy @(ToSym m)) of
          Just Refl -> case symsym' @n of
            Refl -> case symsym' @m of
              Refl -> Proved HRefl
          Nothing   -> Disproved unsafeCoerce
