{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PartialTypeSignatures  #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# OPTIONS_GHC -fno-warn-orphans   #-}

module Dhall.Typed.Type.Index (
  -- * Index
    Index(..), SIndex(..)
    -- , sSameIx, fromSIndex -- , SIndexOf
  -- , SSIndex(..)
  , indexN
  -- * Delete
  , Delete(..)
  -- , del, ISMaybe, Del, SDelete(..), sDel, GetDeleted(..)
  -- * Insert
  , Insert(..)
  -- , insert, Ins, sIns, SInsert(..)
  -- -- * Singletons
  -- , Sing(SIx, getSIx)
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Type.Equality
import           Data.Type.List.Edit
import           Data.Type.Universe
import           Dhall.Typed.Type.N
import           Dhall.Typed.Type.Singletons
import           Dhall.Typed.Type.Singletons.TH
import qualified GHC.TypeLits                   as TL

type instance PolySing (Index as a) = SIndex as a
type instance PolySing (Insert as bs a) = SInsert as bs a
type instance PolySing (Delete as bs a) = SDelete as bs a

genPolySingWith defaultGPSO
  { gpsoSing   = False
  , gpsoPSK    = GOHead [d| instance PolySingKind (Index as a) |]
  , gpsoSingEq = GOHead [d| instance SingEq (Index as a) (Index as b) |]
  } ''Index

genPolySingWith defaultGPSO
  { gpsoSing   = False
  } ''Insert

genPolySingWith defaultGPSO
  { gpsoSing   = False
  } ''Delete


indexN
    :: Index as a
    -> N
indexN = \case
    IZ -> Z
    IS i -> S (indexN i)
