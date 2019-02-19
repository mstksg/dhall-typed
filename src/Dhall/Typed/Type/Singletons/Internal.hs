{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE UndecidableInstances   #-}

module Dhall.Typed.Type.Singletons.Internal (
    PolySing
  , PolySingI(..)
  , PolySingKind(..)
  , SomePolySing(..)
  , WrappedSing(..)
  , SingSing(..)
  , PolySingOfI
  ) where

import           Data.Kind
import           Data.Proxy

type family PolySing k = (s :: k -> Type) | s -> k

-- type family PolySingOf (s :: k -> Type) (x :: k) = (y :: s x) | y -> x

class PolySingI (x :: k) where
    polySing :: PolySing k x

type PolySingOfI (x :: PolySing k y) = PolySingI y

data SomePolySing k where
    SomePS :: PolySing k x -> SomePolySing k

class PolySingKind k where
    fromPolySing :: PolySing k x -> k
    toPolySing :: k -> SomePolySing k




newtype WrappedSing k (x :: k) = WS { getWS :: PolySing k x }

newtype SingSing k x :: WrappedSing k x -> Type where
    SiSi :: forall k x (ws :: WrappedSing k x). ()
         => { getSiSi :: PolySing k x } -> SingSing k x ws

type instance PolySing (WrappedSing k b) = SingSing k b

-- type instance PolySing (WrappedSing (SingSing k x ('WS y)) ('SiSi y)) =
--       SingSing (SingSing k x ('WS y)) ('SiSi y)

instance PolySingI x => PolySingI ('WS (y :: PolySing k x)) where
    polySing = SiSi polySing

instance PolySingKind (WrappedSing k b) where
    fromPolySing (SiSi x) = WS x
    toPolySing (WS x) = SomePS (SiSi x)

-- type PolySingSingI (x :: SingSing k b ('WS q)) = PolySingI b



data SBool :: Bool -> Type where
    SFalse :: SBool 'False
    STrue  :: SBool 'True

type instance PolySing Bool = SBool

instance PolySingKind Bool where
    fromPolySing = \case
      SFalse -> False
      STrue  -> True
    toPolySing = \case
      False -> SomePS SFalse
      True  -> SomePS STrue


data PoopyButt :: Type where
    PB :: SBool b -> PoopyButt

data SPoopyButt :: PoopyButt -> Type where
    SPB :: SingSing Bool b ('WS bb) -> SPoopyButt ('PB bb)

foo :: SPoopyButt ('PB 'STrue)
foo = SPB $ SiSi STrue

type instance PolySing PoopyButt = SPoopyButt

instance PolySingI b => PolySingI ('PB (q :: SBool b)) where
    polySing = SPB polySing

instance PolySingKind PoopyButt where
    fromPolySing = \case
      SPB x -> PB (getWS (fromPolySing x))
    toPolySing = \case
      PB x -> case toPolySing (WS x) of
        SomePS (SiSi y) -> SomePS (SPB (SiSi y))

data SSPoopyButt pb :: SPoopyButt pb -> Type where
    SSPB :: SingSing (WrappedSing Bool b) ('WS bb) ('WS bbb) -> SSPoopyButt ('PB bb) ('SPB bbb)

-- data SMaybe a :: Maybe a -> Type where
--     SJust :: PolySing a x -> SMaybe a ('Just x)
--     SNothing :: SMaybe a 'Nothing

-- type instance PolySing (Maybe a) = SMaybe a

-- data Floop :: Type where
--     FP :: SMaybe a b -> Floop

-- data SFloop :: Floop -> Type where
--     SFP :: SingSing (Maybe a) b ('WS bb) -> SFloop ('FP bb)

    -- SingSing (SingSing Bool b ('WS bb)) b ('WS bbb) -> SSPoopyButt ('PB bb) ('SPB bbb)

-- newtype SingSing k x :: PolySing k x -> Type where
--     SingSing :: forall k (x :: k) (s :: PolySing k x). ()
--              => PolySing k x
--              -> SingSing k x s

-- type instance PolySing (SBool b) = SingSing Bool b

-- type instance PolySing (SingSing Bool b bb) = SingSing (SBool b) bb


-- type instance PolySing (SingSing k x ('WS y)) = Int
    -- SingSing k x y
-- ('WS (PolySing k x))

-- newtype SingSing k x :: PolySing k x -> Type where
--     SingSing :: forall k (x :: k) (s :: PolySing k x). PolySing k x -> SingSing k x s

-- type instance PolySing (SingSing k x p) = SingSing (SingSing k x p) x

-- SingSing qq pp rr
