{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}

module Dhall.Typed.Type.Prod (
    Prod(..)
  , traverseProd
  , mapProd
  , zipProd
  , singProd
  , prodSing
  , allProd
  , prodAll
  , ixProd
  , SeqListEq(..)
  , IxProd
  , SProd(..) -- , SProdOf
  , sIxProd
  , ProdList
  -- * BiProd
  , BiProd(..), SBiProd(..) -- , SBiProdOf
  ) where

import           Control.Applicative
import           Data.Kind
import           Data.Sequence                (Seq(..))
import           Data.Singletons
import           Data.Singletons.Prelude.List
import           Data.Type.Universe
import           Dhall.Typed.Internal.TH
import           Dhall.Typed.Type.Index
import           Dhall.Typed.Type.Singletons
import           GHC.Generics

data Prod :: (k -> Type) -> [k] -> Type where
    Ø    :: Prod f '[]
    (:<) :: f a -> Prod f as -> Prod f (a ': as)

infixr 5 :<

-- genPolySingWith defaultGPSO { gpsoPSK = False } ''Prod
genPolySingWith defaultGPSO ''Prod

data BiProd :: (k -> Type) -> (j -> Type) -> [k] -> [j] -> Type where
    BØ    :: BiProd f g '[] '[]
    (:<<) :: (f a, g b) -> BiProd f g as bs -> BiProd f g (a ': as) (b ': bs)

infixr 5 :<<

genPolySingWith defaultGPSO { gpsoPSK = False } ''BiProd

-- data SProd f as :: Prod f as -> Type where
--     SØ    :: SProd f '[] 'Ø
--     (:%<) :: PolySing (f a) x
--           -> SProd f as xs
--           -> SProd f (a ': as) (x ':< xs)

-- type instance PolySingOf (SProd f '[]      ) 'Ø         = 'SØ
-- type instance PolySingOf (SProd f (a ': as)) (x ':< xs) = PolySingOf (PolySing (f a)) x ':%< PolySingOf (SProd f as) xs

-- type instance PolySingOf (SIndex (a ': as) b) ('IS i) = 'SIS (PolySingOf (SIndex as b) i)

-- type family SProdOf f as (xs :: Prod f as) = (ys :: SProd f as xs) | ys -> xs where
--     SProdOf f '[]       'Ø         = SØ
--     SProdOf f (a ': as) (x ':< xs) = x :%< SProdOf f as xs


-- this Show instance is not general enough
-- deriving instance (forall a. Show (f a)) => Show (Prod f as)

traverseProd
    :: forall f g h as. Applicative h
    => (forall x. f x -> h (g x))
    -> Prod f as
    -> h (Prod g as)
traverseProd f = go
  where
    go  :: Prod f bs -> h (Prod g bs)
    go = \case
      Ø -> pure Ø
      x :< xs -> (:<) <$> f x <*> go xs

mapProd
    :: forall f g as. ()
    => (forall x. f x -> g x)
    -> Prod f as
    -> Prod g as
mapProd f = go
  where
    go  :: Prod f bs -> Prod g bs
    go = \case
      Ø       -> Ø
      x :< xs -> f x :< go xs

zipProd
    :: Prod f as
    -> Prod g as
    -> Prod (f :*: g) as
zipProd = \case
    Ø -> \case
      Ø -> Ø
    x :< xs -> \case
      y :< ys -> (x :*: y) :< zipProd xs ys

singProd
    :: Sing as
    -> Prod Sing as
singProd = \case
    SNil -> Ø
    x `SCons` xs -> x :< singProd xs

prodSing
    :: Prod Sing as
    -> Sing as
prodSing = \case
    Ø -> SNil
    x :< xs -> x `SCons` prodSing xs

allProd :: Sing as -> WitAll [] (TyCon1 f) as -> Prod f as
allProd = \case
    SNil         -> \_ -> Ø
    _ `SCons` xs -> \a -> runWitAll a IZ :< allProd xs (WitAll (runWitAll a . IS))

prodAll :: Prod f as -> WitAll [] (TyCon1 f) as
prodAll = \case
    Ø       -> WitAll $ \case
    x :< xs -> WitAll $ \case
      IZ   -> x
      IS i -> runWitAll (prodAll xs) i

ixProd :: Prod f as -> Index as a -> f a
ixProd = \case
    Ø       -> \case {}
    x :< xs -> \case
      IZ   -> x
      IS i -> ixProd xs i

data SeqListEq :: Seq a -> [a] -> Type where
    SeqListEq :: SeqListEq xs ys    -- TODO: define

type family IxProd f as b (p :: Prod f as) (i :: Index as b) :: f b where
    IxProd f (a ': as) a (x ':< xs) 'IZ                     = x
    IxProd f (a ': as) c (x ':< xs) ('IS (i :: Index as c)) = IxProd f as c xs i

sIxProd
    :: SProd f as xs
    -> SIndex as a i
    -> PolySing (f a) (IxProd f as a xs i)
sIxProd = \case
    SØ -> \case {}
    x :%< xs -> \case
      SIZ   -> x
      SIS i -> sIxProd xs i

-- genPolySing ''Const

type family ProdList (xs :: Prod (Const k) ys) :: [k] where
    ProdList 'Ø                = '[]
    ProdList ('Const x ':< xs) = x ': ProdList xs
