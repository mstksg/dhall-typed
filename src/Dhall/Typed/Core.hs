{-# LANGUAGE EmptyCase          #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeInType         #-}
{-# LANGUAGE TypeOperators      #-}

-- I've split this out from "Dhall.Typed.Core.Internal" to help with
-- recompilation.  Those singletons are pretty heavy duty.

module Dhall.Typed.Core (
  -- * Expression
  -- ** Sorts
    DSort(..)
  -- ** Kinds
  , KBindings(..)
  , DKind(..)
  , SomeKind(..)
  , type (:~>), KShift, toSomeKind, KNormalize, NDKind(..), KSub, SubbedKind(..)
  -- ** Types
  , TBindings(..)
  , DType(..)
  , SomeType(..)
  , type (:$), type (:->), Shift, toSomeType, TNormalize, NDType(..), Sub, ShiftSort
  , normalizeKindOf
  -- ** Terms
  , Prim(..), DTerm(..), SomeTerm(..), toSomeTerm
  , normalizeTypeOf
  -- ** Mixed
  , DExpr(..), SomeDExpr(..), dExprType, deKind, deType, deTerm
  -- ** Shared
  , AggType(..), Bindings(..)
  -- * Type manipulation
  , sortOf, kindOf, typeOf
  , sortOfWith, kindOfWith, typeOfWith
  -- * Singletons
  -- ** Types
  , SDSort(..)
  , SDKind(..), SNDKind(..), SSubbedKind(..)
  , SDType(..), SNDType(..)
  , SPrim(..), SDTerm(..)
  , SAggType(..)
  -- ** Singleton Functions
  , sShift, sShift1
  , sSub, sSub1
  , skSub, skSub1
  , skNormalize
  , stNormalize
  -- ** Defunctionalization Symbols
  , KShiftSym, ShiftSym, ShiftSortSym
  -- * Util
  , Map, MapSym
  ) where

import           Data.Kind
import           Data.Type.List.Edit
import           Dhall.Typed.Core.Internal
import           Dhall.Typed.Type.Index
import           Dhall.Typed.Type.N
import           Dhall.Typed.Type.Prod
import           Dhall.Typed.Type.Singletons
import           Unsafe.Coerce

skNormalize :: SDKind ts a x -> SDKind ts a (KNormalize ts a x)
skNormalize = \case
    SKVar i -> SKVar i
    SKLam tt x -> SKLam tt (skNormalize x)
    SKApp f x -> case f of
      SKLam _ f' -> skNormalize (skSub SDelZ x f')
      -- _           -> SKApp (skNormalize f) (skNormalize x)  -- this is a problem
    x :%~> y -> skNormalize x :%~> skNormalize y
    SKPi tt x -> SKPi tt (skNormalize x)
    SType -> SType

stNormalize :: SDType ts us a x -> SDType ts us a (TNormalize ts us a x)
stNormalize = undefined

sShift
    :: SInsert us qs a ins
    -> SDType ts us b x
    -> SDType ts qs b (Shift ts us qs a b ins x)
sShift = undefined

sShift1
    :: SDType ts us b x
    -> SDType ts (a ': us) b (Shift ts us (a ': us) a b 'InsZ x)
sShift1 = sShift SInsZ

sSub
    :: SDelete us qs a del
    -> SDType ts qs a x
    -> SDType ts us b r
    -> SDType ts qs b (Sub ts us qs a b del x r)
sSub = undefined

sSub1
    :: SDType ts us a x
    -> SDType ts (a ': us) b r
    -> SDType ts us b (Sub ts (a ': us) us a b 'DelZ x r)
sSub1 = sSub SDelZ

skSub
    :: SDelete ts rs a del
    -> SDKind rs a x
    -> SDKind ts b r
    -> SDKind rs b (KSub ts rs a b del x r)
skSub = undefined

skSub1
    :: SDKind ts        a x
    -> SDKind (a ': ts) b r
    -> SDKind ts        b (KSub (a ': ts) ts a b 'DelZ x r)
skSub1 = skSub SDelZ

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
    BoolAnd       -> (SBool :< SBool :< Ø, SBool)
    BoolOr        -> (SBool :< SBool :< Ø, SBool)
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

normalizeKindOf :: DType ts us a -> DType ts us (KNormalize ts 'Kind a)
normalizeKindOf = unsafeCoerce

normalizeTypeOf :: DTerm ts us vs a -> DTerm ts us vs (TNormalize ts us 'Type a)
normalizeTypeOf = unsafeCoerce
