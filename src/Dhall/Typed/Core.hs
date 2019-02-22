{-# LANGUAGE EmptyCase          #-}
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
  , sortOf, kindOf, typeOf
  , sortOfWith, kindOfWith, typeOfWith
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
import           Dhall.Typed.Type.Index
import           Dhall.Typed.Type.Prod
import           Dhall.Typed.Type.Singletons

sortOf :: DKind '[] a -> SDSort a
sortOf = sortOfWith Ø

sortOfWith :: Prod SDSort ts -> DKind ts a -> SDSort a
sortOfWith ts = \case
    KVar i   -> ixProd ts i
    KLam t x -> t :%*> sortOfWith (t :< ts) x
    KApp f _ -> case sortOfWith ts f of
                  _ :%*> t -> t
    _ :~> _  -> SKind
    KPi t x  -> sortOfWith (t :< ts) x
    Type     -> SKind

kindOf :: DType ts '[] a -> SDKind ts 'Kind a
kindOf = kindOfWith Ø

kindOfWith :: Prod (SDKind ts 'Kind) us -> DType ts us a -> SDKind ts 'Kind a
kindOfWith us = \case
    TVar i   -> ixProd us i
    TLam u x -> u :%~> kindOfWith (u :< us) x
    TApp f _ -> case kindOfWith us f of
                  _ :%~> u -> u
    -- STPoly t x       -> case kindOfWith 
    -- TPoly :: SingSing DSort t ('WS tt)
    --       -> DType (t ': ts) (Map (KShiftSym ts (t ': ts) t 'Kind 'InsZ) us) a
    --       -> DType ts us ('KPi tt a)
    -- STInts x t       -> case kindOfWith 
    -- TInst :: DType ts us ('KPi tt b)
    --       -> SDKind ts t a
    --       -> DType ts us (KSub (t ': ts) ts t 'Kind 'DelZ a b)
    _ :-> _  -> SType
    Pi u x   -> kindOfWith (u :< us) x
    Bool     -> SType
    Natural  -> SType
    List     -> SType :%~> SType
    Optional -> SType :%~> SType

primType :: Prim ts us as a -> (Prod (SDType ts us 'Type) as, SDType ts us 'Type a)
primType = \case
    BoolLit _     -> (Ø, SBool   )
    NaturalLit _  -> (Ø, SNatural)
    NaturalFold   -> (Ø, polySing)
    NaturalBuild  -> (Ø, polySing)
    NaturalPlus   -> (SNatural :< SNatural :< Ø, SNatural)
    NaturalTimes  -> (SNatural :< SNatural :< Ø, SNatural)
    NaturalIsZero -> (Ø, SNatural :%-> SBool)
    ListFold      -> (Ø, polySing)
    ListBuild     -> (Ø, polySing)
    ListAppend t  -> let l = SList `STApp` t in (l :< l :< Ø, l)
    ListHead      -> (Ø, polySing)
    ListLast      -> (Ø, polySing)
    ListReverse   -> (Ø, polySing)
    Some t        -> (t :< Ø, SOptional `STApp` t)
    None          -> (Ø, SPi (SiSi SType) (SOptional `STApp` STVar SIZ))

typeOf :: DTerm ts us '[] a -> SDType ts us 'Type a
typeOf = typeOfWith Ø

typeOfWith :: Prod (SDType ts us 'Type) vs -> DTerm ts us vs a -> SDType ts us 'Type a
typeOfWith vs = \case
    Var i           -> ixProd vs i
    Lam v x         -> v :%-> typeOfWith (v :< vs) x
    App f _         -> case typeOfWith vs f of
      _ :%-> v -> v
    P p _           -> snd $ primType p
    ListLit t _     -> SList `STApp` t
    OptionalLit t _ -> SOptional `STApp` t

