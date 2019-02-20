{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Dhall.Typed.Type.Singletons.Internal (
    PolySing
  , PolySingI(..)
  , PolySingKind(..)
  , SomePolySing(..)
  , WrappedSing(..)
  , SingSing(..)
  , PolySingOfI
  , SameSingSing(..)
  , sameSingSing
  -- * Instances
  , SBool(..), SList(..), STup(..)
  ) where

import           Data.Kind
import           Data.Proxy
import           Data.Singletons.Decide (Decision(..), (:~:)(..))
import           Unsafe.Coerce

type family PolySing k = (s :: k -> Type) | s -> k

class PolySingI (x :: k) where
    polySing :: PolySing k x

type PolySingOfI (x :: PolySing k y) = PolySingI y

data SomePolySing k where
    SomePS :: PolySing k x -> SomePolySing k

class PolySingKind k where
    fromPolySing :: PolySing k x -> k
    toPolySing   :: k -> SomePolySing k
    eqPS         :: PolySing k x -> PolySing k y -> Decision (x :~: y)


newtype WrappedSing k (x :: k) = WS { getWS :: PolySing k x }

newtype SingSing k x :: WrappedSing k x -> Type where
    SiSi :: forall k x (ws :: WrappedSing k x). ()
         => { getSiSi :: PolySing k x } -> SingSing k x ws

type instance PolySing (WrappedSing k b) = SingSing k b

instance PolySingI x => PolySingI ('WS (y :: PolySing k x)) where
    polySing = SiSi polySing

instance PolySingKind k => PolySingKind (WrappedSing k b) where
    fromPolySing (SiSi x) = WS x
    toPolySing (WS x) = SomePS (SiSi x)
    eqPS x y = case sameSingSing x y of
      Proved SiSiRefl -> Proved Refl
      Disproved v     -> Disproved $ \case Refl -> v SiSiRefl

data SameSingSing k a b :: WrappedSing k a -> WrappedSing k b -> Type where
    SiSiRefl :: SameSingSing k a a x x

sameSingSing
    :: PolySingKind k
    => SingSing k a x
    -> SingSing k b y
    -> Decision (SameSingSing k a b x y)
sameSingSing = \case
    SiSi x -> \case
      SiSi y -> case eqPS x y of
        Proved Refl -> Proved $ unsafeCoerce Refl
        Disproved v -> Disproved $ \case SiSiRefl -> v Refl
--         Proved Refl -> Proved SiSiRefl
--         -- Disproved v -> Disproved $ \case Refl -> v Refl

-- sameSingSing'
--     :: PolySingKind k
--     => SingSing k a x
--     -> SingSing k b y
--     -> Decision (a :~: b)
-- sameSingSing' = \case
--     SiSi x -> \case
--       SiSi y -> case eqPS x y of
--         Proved Refl -> Proved Refl
--         Disproved v -> Disproved $ \case Refl -> v Refl





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
    eqPS = \case
      SFalse -> \case
        SFalse -> Proved Refl
        STrue  -> Disproved $ \case {}
      STrue  -> \case
        SFalse -> Disproved $ \case {}
        STrue  -> Proved Refl

data SList k :: [k] -> Type where
    (:%) :: PolySing k x -> SList k xs -> SList k (x ': xs)
    SNil :: SList k '[]

infixr 5 :%

type instance PolySing [a] = SList a

instance PolySingI '[] where
    polySing = SNil

instance (PolySingI a, PolySingI as) => PolySingI (a ': as) where
    polySing = polySing :% polySing

instance PolySingKind a => PolySingKind [a] where
    fromPolySing = \case
      SNil -> []
      x :% xs -> fromPolySing x : fromPolySing xs

    toPolySing = \case
      []     -> SomePS SNil
      x : xs -> case toPolySing x of
        SomePS x' -> case toPolySing xs of
          SomePS xs' -> SomePS (x' :% xs')

    eqPS = \case
      SNil -> \case
        SNil -> Proved Refl
        _ :% _ -> Disproved $ \case {}
      x :% xs -> \case
        SNil -> Disproved $ \case {}
        y :% ys -> case eqPS x y of
          Proved Refl -> case eqPS xs ys of
            Proved Refl -> Proved Refl
            Disproved v -> Disproved $ \case Refl -> v Refl
          Disproved v -> Disproved $ \case Refl -> v Refl


data STup a b :: (a, b) -> Type where
    STup :: PolySing a x -> PolySing b y -> STup a b '(x, y)

type instance PolySing (a, b) = STup a b

instance (PolySingI x, PolySingI y) => PolySingI '(x, y) where
    polySing = STup polySing polySing

instance (PolySingKind a, PolySingKind b) => PolySingKind (a, b) where
    fromPolySing = \case
      STup x y -> (fromPolySing x, fromPolySing y)
    toPolySing (x, y) = case toPolySing x of
      SomePS x' -> case toPolySing y of
        SomePS y' -> SomePS (STup x' y')
    eqPS = \case
      STup x y -> \case
        STup x' y' -> case eqPS x x' of
          Proved Refl -> case eqPS y y' of
            Proved Refl -> Proved Refl
            Disproved v -> Disproved $ \case Refl -> v Refl
          Disproved v -> Disproved $ \case Refl -> v Refl



data PoolyBing :: Type where
    PB :: SBool b -> PoolyBing

data SPoolyBing :: PoolyBing -> Type where
    SPB :: SingSing Bool b ('WS bb) -> SPoolyBing ('PB bb)

foo :: SPoolyBing ('PB 'STrue)
foo = SPB $ SiSi STrue

type instance PolySing PoolyBing = SPoolyBing

instance PolySingI b => PolySingI ('PB (q :: SBool b)) where
    polySing = SPB polySing

instance PolySingKind PoolyBing where
    fromPolySing = \case
      SPB x -> PB (getWS (fromPolySing x))
    toPolySing = \case
      PB x -> case toPolySing (WS x) of
        SomePS (SiSi y) -> SomePS (SPB (SiSi y))
    eqPS = \case
      SPB x -> \case
        SPB y -> case sameSingSing x y of
          Proved SiSiRefl -> Proved Refl
          Disproved v     -> Disproved $ \case Refl -> v SiSiRefl

data SSPoolyBing pb :: SPoolyBing pb -> Type where
    SSPB :: SingSing (WrappedSing Bool b) ('WS bb) ('WS bbb)
         -> SSPoolyBing ('PB bb) ('SPB bbb)

-- data SMaybe a :: Maybe a -> Type where
--     SJust :: PolySing a x -> SMaybe a ('Just x)
--     SNothing :: SMaybe a 'Nothing

-- type instance PolySing (Maybe a) = SMaybe a

-- data Floop :: Type where
--     FP :: SMaybe a b -> Floop

-- data SFloop :: Floop -> Type where
--     SFP :: SingSing (Maybe a) b ('WS bb) -> SFloop ('FP bb)

    -- SingSing (SingSing Bool b ('WS bb)) b ('WS bbb) -> SSPoolyBing ('PB bb) ('SPB bbb)

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
