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
  , DKind(..), SomeKind(..), type (:~>), KShift, toSomeKind, KNormalize, NDKind(..)
  , skNormalize
  -- ** Types
  , DType(..), SomeType(..), type (:$), type (:->), Shift, toSomeType, TNormalize, NDType(..)
  , stNormalize
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
  , SDKind(..), SNDKind(..)
  , SDType(..), SNDType(..)
  , SPrim(..), SDTerm(..)
  , SAggType(..)
  , KShiftSym, ShiftSym
  -- * Util
  , Map, MapSym
  ) where

import           Data.Kind
import           Dhall.Typed.Core.Internal
import           Dhall.Typed.Type.Index
import           Dhall.Typed.Type.N
import           Dhall.Typed.Type.Prod
import           Dhall.Typed.Type.Singletons

skNormalize :: SDKind ts a x -> SDKind ts a (KNormalize ts a x)
skNormalize = undefined

stNormalize :: SDType ts us a x -> SDType ts us a (TNormalize ts us a x)
stNormalize = undefined

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
    TLam (NDK u) x -> let u' = skNormalize u
                       in  u' :%~> kindOfWith (u' :< us) x
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
    Pi (NDK u) x   -> kindOfWith (skNormalize u :< us) x
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
    -- ListAppend (NDT t) -> let l = SList `STApp` stNormalize t in (l :< l :< Ø, l)
    ListAppend t -> let l = SList `STApp` t in (l :< l :< Ø, l)
    ListHead      -> (Ø, polySing)
    ListLast      -> (Ø, polySing)
    ListReverse   -> (Ø, polySing)
    Some t        -> (t :< Ø, SOptional `STApp` t)
    None          -> (Ø, polySing)
    -- None          -> (Ø, SPi _ (SOptional `STApp` STVar SIZ))

typeOf :: DTerm ts us '[] a -> SDType ts us 'Type a
typeOf = typeOfWith Ø

typeOfWith :: Prod (SDType ts us 'Type) vs -> DTerm ts us vs a -> SDType ts us 'Type a
typeOfWith vs = \case
    Var i           -> ixProd vs i
    Lam (NDT v) x   -> let v' = stNormalize v
                       in  v' :%-> typeOfWith (v' :< vs) x
    App f _         -> case typeOfWith vs f of
      _ :%-> v -> v
    P p _           -> snd $ primType p
    ListLit (NDT t) _     -> SList `STApp` stNormalize t
    OptionalLit (NDT t) _ -> SOptional `STApp` stNormalize t

-- | A 'DExpr' fully covers all legal type-checking dhall terms.  A value
-- of type
--
-- @
-- 'DExpr' '[ r, s ] '[ k, j ] '[ a, b ] n
-- @
--
-- Represents a dhall expression on level @n@ (@'FZ@ = term, @'FS 'FZ@
-- = type, etc.) with potential:
--
-- * Kind variables of sort @r@, @s@
-- * Type variables of kind @k@, @j@
-- * Term variables of type @a@, @b@
--
-- A value of type @'DExpr' '[] '[] '[] n@ represents a typed dhall
-- expression with no free variables.
--
-- You can pattern match on it to get a value of one of the "levels" of the
-- dhall type hierarchy, and also to get the "type" and representation of
-- it.
--
-- The number of level goes up to 4 :
--
-- * @F0@: term
-- * @F1@: type
-- * @F2@: kind
-- * @F3@: sort
-- * @F4@: order
--
-- Note that you can restrict this to only 'DExpr' past a given "level" by
-- asking for or returning a @'DExpr' ts us vs ('FS n)@, for instance.
-- Such a value will only contain types, kinds, sorts, or order  A @'DExpr'
-- ts us vs ('FS ('FS n))@ will only contain kinds, sorts, or order, etc.
data DExpr ts us :: [DType ts us 'Type] -> Fin N5 -> Type where
    DEOrder ::                      DExpr ts us vs F4
    DESort  :: DSort             -> DExpr ts us vs F3
    DEKind  :: SomeKind ts       -> DExpr ts us vs F2
    DEType  :: SomeType ts us    -> DExpr ts us vs F1
    DETerm  :: SomeTerm ts us vs -> DExpr ts us vs F0

-- | Hides the "level" of a 'DExpr'.  Pattern match to find it.  Can be
-- useful when returning a 'DExpr' of level unknown until runtime, or
-- storing 'DExpr' of multiple levels in a container.
data SomeDExpr ts us :: [DType ts us 'Type] -> Type where
    SomeDExpr :: DExpr ts us vs l -> SomeDExpr ts us vs

-- | Get the meta-level "type" of a 'DExpr'.  If it's a term, this will
-- return its type.  If it's a type, this returns its type, etc.  It
-- essentially goes up one "level" of the Dhall type hierarchy.
--
-- This will not typecheck if given a "Level 4" fin, so you cannot pass in
-- 'DEOrder'.

-- TODO: move to taking witness
dExprType :: DExpr ts us vs n -> DExpr ts us vs (ShiftFin N5 n)
dExprType = \case
    DEOrder               ->
      errorWithoutStackTrace "dExprType: Inaccessible; this should not be allowed by GHC"
    DESort _              -> DEOrder
    DEKind (SomeKind t _) -> DESort (fromPolySing t)
    DEType (SomeType (NDK t) _) -> DEKind (SomeKind SKind (fromPolySing t))
    DETerm (SomeTerm (NDT t) _) -> DEType (SomeType (NDK SType) (fromPolySing t))

deKind :: PolySingI a => DKind ts a -> DExpr ts us vs F2
deKind = DEKind . toSomeKind

deType
    :: (PolySingI a, KNormalize ts 'Kind a ~ a)
    => DType ts us a
    -> DExpr ts us vs F1
deType = DEType . toSomeType

deTerm :: (PolySingI a, TNormalize ts us 'Type a ~ a) => DTerm ts us vs a -> DExpr ts us vs F0
deTerm = DETerm . toSomeTerm
