{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}

module Dhall.Typed.LC where

-- module Dhall.Typed.LC (
--   ) where

import           Data.Kind
import           Dhall.Typed.Prod
import           Dhall.Typed.Index

data DSort = Kind | DSort :*> DSort

data SDSort :: DSort -> Type where
    SKind :: SDSort 'Kind
    (:%*>) :: SDSort s -> SDSort t -> SDSort (s ':*> t)

type family SDSortOf (k :: DSort) = (s :: SDSort k) | s -> k where
    SDSortOf 'Kind = 'SKind
    SDSortOf (a ':*> b) = SDSortOf a ':%*> SDSortOf b

data KPrim :: [DSort] -> DSort -> Type where
    KApp :: KPrim '[a ':*> b, a] b
    KFun :: KPrim '[ 'Kind, 'Kind ] 'Kind
    Type :: KPrim '[] 'Kind

data DKind :: [DSort] -> DSort -> Type where
    KVar :: Index ts a -> DKind ts a
    KLam :: SDSort t -> DKind (t ': ts) a -> DKind ts (t ':*> a)
    KP   :: KPrim as a -> Prod (DKind ts) as -> DKind ts a

data SKPrim as a :: KPrim as a -> Type where
    SKApp :: SKPrim '[ a ':*> b, a ] b 'KApp
    SKFun :: SKPrim '[ 'Kind, 'Kind ] 'Kind 'KFun
    SType :: SKPrim '[] 'Kind 'Type

data SDKind ts a :: DKind ts a -> Type where
    SKVar :: SIndex ts a i -> SDKind ts a ('KVar i)
    SKLam :: SDSort t -> SDKind (t ': ts) a x -> SDKind ts (t ':*> a) ('KLam (SDSortOf t) x)
    SKP   :: SKPrim as a x -> SProd (DKind ts) as p -> SDKind ts a ('KP x p)

type a :~> b = 'KP 'KFun (a ':< b ':< 'Ø)
type KType   = 'KP 'Type 'Ø

type family SDKindOf ts k (x :: DKind ts k) = (y :: SDKind ts k x) | y -> x where
    SDKindOf ts k          ('KVar i  ) = 'SKVar (SIndexOf ts k i)

data TPrim ts :: [DKind ts 'Kind] -> DKind ts 'Kind -> Type where
    TApp :: TPrim ts '[a :~> b, a] b
    TFun :: TPrim ts '[KType, KType] KType
    Bool :: TPrim ts '[] KType

data DType ts :: [DKind ts 'Kind] -> DKind ts 'Kind -> Type where
    TVar  :: Index us a -> DType ts us a
    TLam  :: SDKind ts 'Kind u -> DType ts (u ': us) a -> DType ts us (u :~> a)
    TP    :: TPrim ts as a -> Prod (DType ts us) as -> DType ts us a

data STPrim ts as a :: TPrim ts as a -> Type where
    STApp :: STPrim ts '[ a :~> b, a ] b 'TApp
    STFun :: STPrim ts '[ KType, KType ] KType 'TFun
    SBool :: STPrim ts '[] KType 'Bool

data SDType ts us a :: DType ts us a -> Type where
    STVar  :: SIndex us a i -> SDType ts us a ('TVar i)
    STLam  :: SDKind ts 'Kind u
           -> SDType ts (u ': us) a x
           -> SDType ts us (u :~> a) ('TLam (SDKindOf ts 'Kind u) x)
    STP    :: STPrim ts as a x -> SProd (DType ts us) as p -> SDType ts us a ('TP x p)

type a :-> b = 'TP 'TFun (a ':< b ':< 'Ø)
type TBool   = 'TP 'Bool 'Ø

data Prim ts us :: [DType ts us KType] -> DType ts us KType -> Type where
    BoolLit :: Bool -> Prim ts us '[] TBool
    BoolAnd :: Prim ts us '[TBool, TBool] TBool
    BoolNot :: Prim ts us '[] (TBool :-> TBool)

data DTerm ts (us :: [DKind ts 'Kind]) :: [DType ts us KType] -> DType ts us KType -> Type where
    Var  :: Index vs a -> DTerm ts us vs a
    Lam  :: SDType ts us KType v -> DTerm ts us (v ': vs) a -> DTerm ts us vs (v :-> a)
    P    :: Prim ts us as a -> Prod (DTerm ts us vs) as -> DTerm ts us vs a
