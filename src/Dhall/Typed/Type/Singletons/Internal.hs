{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE QuantifiedConstraints  #-}
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
  , SingEq(..)
  -- , EqTest(..)
  -- , SameSingSing(..)
  -- , sameSingSing
  -- * Instances
  , SBool(..), SList(..), STup2(..), STup0(..)
  ) where

import           Data.Kind
import           Data.Proxy
import           Data.Singletons.Decide (Decision(..), (:~:)(..))
import           Data.Type.Equality
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
    -- eqPS         :: PolySing k x -> PolySing k y -> Decision (x :~: y)

-- data SameSingSing k a b :: WrappedSing k a -> WrappedSing k b -> Type where
--     SiSiRefl :: SameSingSing k a a x x

-- sameSingSing
--     :: PolySingKind k
--     => SingSing k a x
--     -> SingSing k b y
--     -> Decision (SameSingSing k a b x y)
-- sameSingSing = \case
--     SiSi x -> \case
--       SiSi y -> case eqPS x y of
--         Proved Refl -> Proved $ unsafeCoerce Refl
--         Disproved v -> Disproved $ \case SiSiRefl -> v Refl

newtype WrappedSing k (x :: k) = WS { getWS :: PolySing k x }

newtype SingSing k x :: WrappedSing k x -> Type where
    SiSi :: forall k x (ws :: WrappedSing k x). ()
         => { getSiSi :: PolySing k x } -> SingSing k x ws

type instance PolySing (WrappedSing k b) = SingSing k b

instance PolySingI x => PolySingI ('WS (y :: PolySing k x)) where
    polySing = SiSi polySing

instance PolySingKind (WrappedSing k b) where
    fromPolySing (SiSi x) = WS x
    toPolySing (WS x) = SomePS (SiSi x)
    -- eqPS x y = case sameSingSing x y of
    --   Proved SiSiRefl -> Proved Refl
    --   Disproved v     -> Disproved $ \case Refl -> v SiSiRefl

class SingEq f g where
    singEq :: forall x y. PolySing f x -> PolySing g y -> Decision (x :~~: y)

instance SingEq k j => SingEq (WrappedSing k b) (WrappedSing j c) where
    singEq = \case
      SiSi x -> \case
        SiSi y -> case singEq x y of
          Proved HRefl -> Proved $ unsafeCoerce HRefl
          Disproved v -> Disproved $ \case HRefl -> v HRefl


-- class EqTest (f :: k -> Type) (g :: j -> Type) where
--     testEq :: forall a b. f a -> g b -> Decision (a :~~: b)

-- instance EqTest (PolySing k) (PolySing k)
--       => EqTest (SingSing k a) (SingSing k b) where
--     testEq = \case
--       SiSi x -> \case
--         SiSi y -> case testEq x y of
--           Proved HRefl -> Proved $ unsafeCoerce HRefl
--           Disproved v -> Disproved $ \case HRefl -> v HRefl
    --   SiSi x -> \case
    --     SiSi y -> case testEq x y of
    --       Proved Refl -> Proved $ unsafeCoerce Refl
    --       Disproved v  -> Disproved $ \case Refl -> v Refl





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

instance SingEq Bool Bool where
    singEq = \case
      SFalse -> \case
        SFalse -> Proved HRefl
        STrue  -> Disproved $ \case {}
      STrue  -> \case
        SFalse -> Disproved $ \case {}
        STrue  -> Proved HRefl

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

-- instance (SingEq a b, a ~ b) => SingEq [a] [b] where
instance SingEq a a => SingEq [a] [a] where
    singEq = \case
      SNil -> \case
        SNil -> Proved HRefl
        _ :% _ -> Disproved $ \case {}
      x :% xs -> \case
        SNil -> Disproved $ \case {}
        y :% ys -> case singEq x y of
          Proved HRefl -> case singEq xs ys of
            Proved HRefl -> Proved HRefl
            Disproved v -> Disproved $ \case HRefl -> v HRefl
          Disproved v -> Disproved $ \case HRefl -> v HRefl

data STup2 a b :: (a, b) -> Type where
    STup2 :: PolySing a x -> PolySing b y -> STup2 a b '(x, y)

type instance PolySing (a, b) = STup2 a b

instance (PolySingI x, PolySingI y) => PolySingI '(x, y) where
    polySing = STup2 polySing polySing

instance (PolySingKind a, PolySingKind b) => PolySingKind (a, b) where
    fromPolySing = \case
      STup2 x y -> (fromPolySing x, fromPolySing y)
    toPolySing (x, y) = case toPolySing x of
      SomePS x' -> case toPolySing y of
        SomePS y' -> SomePS (STup2 x' y')

data STup0 :: () -> Type where
    STup0 :: STup0 '()

type instance PolySing () = STup0

instance PolySingI '() where
    polySing = STup0

instance PolySingKind () where
    fromPolySing _ = ()
    toPolySing _ = SomePS STup0

instance SingEq () () where
    singEq = \case
      STup0 -> \case
        STup0 -> Proved HRefl



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

instance SingEq PoolyBing PoolyBing where
    singEq = \case
      SPB x -> \case
        SPB y -> case singEq x y of
          Proved HRefl -> Proved HRefl
          Disproved v  -> Disproved $ \case HRefl -> v HRefl
    -- eqPS = \case
    --   SPB x -> \case
    --     SPB y -> case sameSingSing x y of
    --       Proved SiSiRefl -> Proved Refl
    --       Disproved v     -> Disproved $ \case Refl -> v SiSiRefl

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
