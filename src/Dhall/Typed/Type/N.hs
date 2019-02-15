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

module Dhall.Typed.Type.N (
    N(..), Sing(SZ, SS, SFin_, getSFin_), SN
  , fromNatural
  , toNatural
  , ZSym0, SSym0, SSym1
  , IsLength(..)
  , Fin(..), SFin(..)
  , ShiftFin
  , LTE(..)
  , N0, N1, N2, N3, N4, N5
  , F0, F1, F2, F3, F4, F5
  , sf0, sf1, sf2, sf3, sf4, sf5
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Prelude.Functor
import           Data.Singletons.Prelude.Maybe
import           Data.Singletons.TH
import           Numeric.Natural
import qualified GHC.TypeLits                    as TL

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

data SFin n :: Fin n -> Type where
    SFZ :: SFin ('S n) 'FZ
    SFS :: SFin n x -> SFin ('S n) ('FS x)

data instance Sing (i :: Fin n) where
    SFin_ :: { getSFin_ :: SFin n i } -> Sing i

type family ShiftFinMaybe n (i :: Fin n) :: Maybe (Fin n) where
    ShiftFinMaybe ('S 'Z)     'FZ     = 'Nothing
    ShiftFinMaybe ('S ('S n)) 'FZ     = 'Just ('FS 'FZ)
    ShiftFinMaybe ('S n)      ('FS i) = Fmap (TyCon1 'FS) (ShiftFinMaybe n i)

type family ShiftFin n (i :: Fin n) :: Fin n where
    ShiftFin n i =
        FromMaybe
          (TL.TypeError (
             'TL.Text "Fin "
             'TL.:<>: 'TL.ShowType i 
             'TL.:<>: 'TL.Text " cannot be shifted beyond limit "
             'TL.:<>: 'TL.ShowType n
             )
          )
          (ShiftFinMaybe n i)

data LTE :: N -> N -> Type where
    LTEZ :: LTE 'Z m
    LTES :: LTE n  m -> LTE ('S n) ('S m)

type N0 = 'Z
type N1 = 'S N0
type N2 = 'S N1
type N3 = 'S N2
type N4 = 'S N3
type N5 = 'S N4

type F0 = 'FZ
type F1 = 'FS F0
type F2 = 'FS F1
type F3 = 'FS F2
type F4 = 'FS F3
type F5 = 'FS F4

sf0 :: SFin ('S n) F0
sf0 = SFZ

sf1 :: SFin ('S ('S n)) F1
sf1 = SFS sf0

sf2 :: SFin ('S ('S ('S n))) F2
sf2 = SFS sf1

sf3 :: SFin ('S ('S ('S ('S n)))) F3
sf3 = SFS sf2

sf4 :: SFin ('S ('S ('S ('S ('S n))))) F4
sf4 = SFS sf3

sf5 :: SFin ('S ('S ('S ('S ('S ('S n)))))) F5
sf5 = SFS sf4
