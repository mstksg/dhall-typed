{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE TypeInType         #-}

-- I've split this out from "Dhall.Typed.Core.Internal" to help with
-- recompilation.  Those singletons are pretty heavy duty.

module Dhall.Typed.Core (
  -- * Expression
  -- ** Sorts
    DSort(..)
  -- ** Kinds
  , DKind(..), SomeKind(..), type (:~>), KShift, toSomeKind
  -- ** Types
  , DType(..), SomeType(..), type (:$), type (:->), Shift, toSomeType
  -- ** Terms
  , Prim(..), DTerm(..), SomeTerm(..), toSomeTerm
  -- ** Mixed
  , DExpr(..), SomeDExpr(..), dExprType, deKind, deType, deTerm
  -- ** Shared
  , AggType(..)
  -- * Type manipulation
  -- * Singletons
  , SDSort(..)
  , SDKind(..)
  , SDType(..)
  , SPrim(..), SDTerm(..)
  , SAggType(..)
  , KShiftSym, ShiftSym
  -- * Util
  , Map, MapSym
  ) where

import           Dhall.Typed.Core.Internal
import           Dhall.Typed.Type.Prod
import           Dhall.Typed.Type.Singletons

sortOfWith :: Prod SDSort ts -> SDKind ts a x -> SDSort a
sortOfWith ts = \case
    SKVar i          -> ixProd ts (fromPolySing i)
    SKLam (SiSi t) x -> t :%*> sortOfWith (t :< ts) x
    SKApp f _        -> case sortOfWith ts f of
      _ :%*> t -> t
    _ :%~> _         -> SKind
    SKPi (SiSi t) x  -> sortOfWith (t :< ts) x
    SType            -> SKind

kindOfWith :: Prod (SDKind ts 'Kind) us -> SDType ts us a x -> SDKind ts 'Kind a
kindOfWith us = \case
    STVar i          -> ixProd us (fromPolySing i)
    STLam (SiSi u) x -> u :%~> kindOfWith (u :< us) x
    STApp f _        -> case kindOfWith us f of
      _ :%~> u -> u
    -- STPoly t x       -> case kindOfWith 
    -- STInts x t       -> case kindOfWith 
    _ :%-> _         -> SType
    SPi (SiSi u) x   -> kindOfWith (u :< us) x
    SBool            -> SType
    SNatural         -> SType
    SList            -> SType :%~> SType
    SOptional        -> SType :%~> SType

    -- TPoly :: SingSing DSort t ('WS tt)
    --       -> DType (t ': ts) (Map (KShiftSym ts (t ': ts) t 'Kind 'InsZ) us) a
    --       -> DType ts us ('KPi tt a)
    -- TInst :: DType ts us ('KPi tt b)
    --       -> SDKind ts t a
    --       -> DType ts us (KSub (t ': ts) ts t 'Kind 'DelZ a b)

