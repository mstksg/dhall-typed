{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module Dhall.Typed.N (
    N(..), Sing(SZ, SS), SN
  , fromNatural
  , toNatural
  , ZSym0, SSym0, SSym1
  , IsLength(..)
  , Fin(..)
  , LTE(..)
  , N0, N1, N2, N3, N4, N5
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.TH
import           Numeric.Natural

$(singletons [d|
  data N = Z | S N
    deriving (Eq, Ord, Show)
  |])

fromNatural :: Natural -> N
fromNatural 0 = Z
fromNatural n = S (fromNatural (n - 1))

toNatural :: N -> Natural
toNatural Z     = 0
toNatural (S n) = 1 + toNatural n

data IsLength :: [k] -> N -> Type where
    ILZ :: IsLength '[] 'Z
    ILS :: IsLength as n -> IsLength (a ': as) ('S n)

data Fin :: N -> Type where
    FZ :: Fin ('S n)
    FS :: Fin n -> Fin ('S n)

data LTE :: N -> N -> Type where
    LTEZ :: LTE 'Z m
    LTES :: LTE n  m -> LTE ('S n) ('S m)

type N0 = 'Z
type N1 = 'S N0
type N2 = 'S N1
type N3 = 'S N2
type N4 = 'S N3
type N5 = 'S N4
