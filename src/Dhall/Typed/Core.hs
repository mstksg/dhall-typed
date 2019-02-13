{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE RecordWildCards        #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ViewPatterns           #-}

module Dhall.Typed.Core (
  -- * Kinds
    DKind(..), SDKind(..), SDKindI(..), sameDKind
  -- * Types
  , DType(..), SDType(..), SDTypeI(..), sameDType, sameDTypeWith, kindOf, kindOfWith
  , Sub, Shift
  -- * Terms
  , DTerm(..), Bindings(..), SDTerm(..), SeqListEq(..), typeOf, typeOfWith
  -- * Evaluation
  , DTypeRep, Forall(..), ForallTC(..), DTypeRepVal(..)
  , fromTerm, fromTermWith, toTerm
  -- * Manipulation
  , sShift, sShift_, subIns, subIns2, sSub, sSub_
  -- * Singletons
  , Sing(SDK, getSDK, SDTy, getSDTy, SDTe, getSDTe)
  ) where

import           Data.Kind
import           Data.Sequence                (Seq(..))
import           Data.Singletons.Prelude.List (Sing(..))
import           Data.Singletons.TH hiding    (Sum)
import           Data.Type.Equality
import           Data.Type.Universe
import           Dhall.Typed.Index
import           Dhall.Typed.Option
import           Dhall.Typed.Prod
import           Numeric.Natural
import           Unsafe.Coerce                (unsafeCoerce)
import qualified Data.Sequence                as Seq
import qualified GHC.TypeLits                 as TL

-- | Represents the possible kinds encountered in Dhall.
data DKind = Type | DKind :~> DKind
  deriving (Eq, Ord, Show)

-- | Singletons for 'DKind'.  These are defined independently of 'Sing' to
-- avoid limitations of data family instances.
--
-- Note that at the moment, kind variables are not yet supported.
data SDKind :: DKind -> Type where
    SType  :: SDKind 'Type
    (:%~>) :: SDKind a -> SDKind b -> SDKind (a ':~> b)

deriving instance Show (SDKind k)

data instance Sing (k :: DKind) where
    SDK :: { getSDK :: SDKind k } -> Sing k

type family SDKindOf (k :: DKind) = (s :: SDKind k) | s -> k where
    SDKindOf 'Type = 'SType
    SDKindOf (a ':~> b) = SDKindOf a ':%~> SDKindOf b

-- | Typeclass for automatically generating singletons for a 'DType'.
-- Analogous to 'SingI' for 'Sing'.
class SDKindI (k :: DKind) where
    sdKind :: SDKind k

instance SDKindI 'Type where
    sdKind = SType
instance (SDKindI a, SDKindI b) => SDKindI (a ':~> b) where
    sdKind = sdKind :%~> sdKind

-- | Compare two type-level 'DKind' for equality.
sameDKind :: SDKind k -> SDKind j -> Maybe (k :~: j)
sameDKind = \case
    SType -> \case
      SType -> Just Refl
      _     -> Nothing
    a :%~> b -> \case
      SType    -> Nothing
      c :%~> d -> do
        Refl <- sameDKind a c
        Refl <- sameDKind b d
        pure Refl

-- | Matches a 'DKind' to the actual Haskell Kind that it represents.
type family DKindRep (x :: DKind) where
    DKindRep 'Type      = Type
    DKindRep (a ':~> b) = DKindRep a -> DKindRep b

-- | A non-empty series of /Let/ bindings.
data Bindings k :: ([k] -> k -> Type) -> [k] -> [k] -> Type where
    BNil  :: f vs a -> Bindings k f vs (a ': vs)
    (:<?) :: f vs a -> Bindings k f (a ': vs) us -> Bindings k f vs us

infixr 5 :<?

-- | Represents the possible types encountered in Dhall.  A value of type
--
-- @
-- 'DType' '[k1, k2, k3] k
-- @
--
-- Describes a type of kind @k@ possibly containing free type variables of
-- kind @k1@, @k2@, and @k3@.
--
-- Something of type @'DType' '[] k@ is a type of kind @k@ with no free
-- variables.
data DType :: [DKind] -> DKind -> Type where
    TVar     :: Index us a
             -> DType us a
    Pi       :: SDKind a
             -> DType (a ': us) b
             -> DType us b
    (:$)     :: DType us (a ':~> b)
             -> DType us a
             -> DType us b
    (:->)    :: DType us 'Type
             -> DType us 'Type
             -> DType us 'Type
    TLet     :: Bindings DKind DType vs us
             -> DType us a
             -> DType vs a
    Bool     :: DType us 'Type
    Natural  :: DType us 'Type
    List     :: DType us ('Type ':~> 'Type)
    Optional :: DType us ('Type ':~> 'Type)

infixr 0 :->
infixl 9 :$

-- | A value of a polymorphic type.
data Forall us p k :: DType (k ': us) 'Type -> Type where
    FA :: { runForall :: forall r. ()
                      => SDType us k r
                      -> DTypeRep us p 'Type (Sub (k ': us) us k 'Type 'DZ r a)
          }
       -> Forall us p k a

-- | A value of a polymorphic type, lifted to take a type constructor as
-- a parameter.
data ForallTC us p j k :: DType (k ': us) (j ':~> 'Type) -> DKindRep j -> Type where
    FATC :: { runForallTCC
                :: forall r. ()
                => SDType us k r
                -> DTypeRep us p (j ':~> 'Type) (Sub (k ': us) us k (j ':~> 'Type) 'DZ r a) x
            }
         -> ForallTC us p j k a x

-- type family IxProd f as b c (p :: Prod f as) (i :: Index as b) :: f c where

-- | Matches a 'DType' to the actual Haskell type that it represents.
type family DTypeRep us (p :: Prod (DType us) us) k (x :: DType us k) :: DKindRep k where
    DTypeRep us p k                  ('TVar i)                   = DTypeRep us p k (IxProd (DType us) us k p i)
    DTypeRep us p 'Type              ('Pi (u :: SDKind a) t)     = Forall us p a t
    DTypeRep us p (k ':~> 'Type)     ('Pi (u :: SDKind a) t)     = ForallTC us p k a t
    DTypeRep us p k                  ((f :: DType us (r ':~> k)) ':$ (x :: DType us r))
        = DTypeRep us p (r ':~> k) f (DTypeRep us p r x)
    DTypeRep us p 'Type              (a ':-> b) = DTypeRep us p 'Type a -> DTypeRep us p 'Type b
    DTypeRep us p 'Type              'Bool      = Bool
    DTypeRep us p 'Type              'Natural   = Natural
    DTypeRep us p ('Type ':~> 'Type) 'List      = Seq
    DTypeRep us p ('Type ':~> 'Type) 'Optional  = Maybe
    DTypeRep us p k                  x          = TL.TypeError ('TL.Text "No DTypeRep: " 'TL.:<>: 'TL.ShowType '(k, x))

type family MaybeVar a b (x :: DType vs a) (i :: Maybe (Index vs b)) :: DType vs b where
    MaybeVar a a x 'Nothing  = x
    MaybeVar a b x ('Just i) = 'TVar i
    MaybeVar a b x i = TL.TypeError ('TL.Text "No Maybe: " 'TL.:<>: 'TL.ShowType '(x, i))

-- | Shift all variables to accomodate for a new bound variable.
type family Shift as bs a b (ins :: Insert as bs a) (x :: DType as b) :: DType bs b where
    Shift as bs a b   ins ('TVar i) = 'TVar (Ins as bs a b ins i)
    Shift as bs a b   ins ('Pi (u :: SDKind k) e) = 'Pi u (Shift (k ': as) (k ': bs) a b ('InsS ins) e)
    Shift as bs a r i ((u :: DType as (k ':~> r)) ':$ (v :: DType as k))
        = Shift as bs a (k ':~> r) i u ':$ Shift as bs a k i v
    Shift as bs a 'Type              i (u ':-> v) = Shift as bs a 'Type i u ':-> Shift as bs a 'Type i v
    Shift as bs a 'Type              i 'Bool     = 'Bool
    Shift as bs a 'Type              i 'Natural  = 'Natural
    Shift as bs a ('Type ':~> 'Type) i 'List     = 'List
    Shift as bs a ('Type ':~> 'Type) i 'Optional = 'Optional
    Shift as bs a b ins x = TL.TypeError ('TL.Text "No Shift: " 'TL.:<>: 'TL.ShowType '(as, bs, a, b, ins, x))

-- | Substitute in a value for a given variable.
type family Sub as bs a b (d :: Delete as bs a) (x :: DType bs a) (r :: DType as b) :: DType bs b where
    Sub as bs a b                  d x ('TVar i)
        = MaybeVar a b x (Del as bs a b d i)
    Sub as bs a b                  d x ('Pi (u :: SDKind k) e)
        = 'Pi u (Sub (k ': as) (k ': bs) a b ('DS d) (Shift bs (k ': bs) k a 'InsZ x) e)
    Sub as bs a b                  d x ((i :: DType as (k ':~> b)) ':$ (j :: DType as k))
        = Sub as bs a (k ':~> b) d x i ':$ Sub as bs a k d x j
    Sub as bs a 'Type              d x (i ':-> j)
        = Sub as bs a 'Type d x i ':-> Sub as bs a 'Type d x j
    Sub as bs a 'Type              d x 'Bool
        = 'Bool
    Sub as bs a 'Type              d x 'Natural
        = 'Natural
    Sub as bs a ('Type ':~> 'Type) d x 'List
        = 'List
    Sub as bs a ('Type ':~> 'Type) d x 'Optional
        = 'Optional
    Sub as bs a b d x r
        = TL.TypeError ('TL.Text "No Sub: " 'TL.:<>: 'TL.ShowType '(as, bs, a, b, d, x, r))

-- | Singletons for 'DType'.  These are defined independently of 'Sing'
-- mostly to move the kind parameters to the front, to make them more easy
-- to use.

-- TODO: TLet
data SDType us k :: DType us k -> Type where
    STVar     :: SIndex us a i -> SDType us a ('TVar i)
    SPi       :: SDKind a -> SDType (a ': us) b x -> SDType us b ('Pi (SDKindOf a) x)
    (:%$)     :: SDType us (a ':~> b) f -> SDType us a x -> SDType us b (f ':$ x)
    (:%->)    :: SDType us 'Type x -> SDType us 'Type y -> SDType us 'Type (x ':-> y)
    SBool     :: SDType us 'Type 'Bool
    SNatural  :: SDType us 'Type 'Natural
    SList     :: SDType us ('Type ':~> 'Type) 'List
    SOptional :: SDType us ('Type ':~> 'Type) 'Optional

infixr 0 :%->
infixl 9 :%$
infixl 3 `App`
infixl 3 `TApp`

deriving instance Show (SDType us k a)

data instance Sing (a :: DType us k) where
    SDTy :: { getSDTy :: SDType us k a } -> Sing a

type family SDTypeOf us k (a :: DType us k) = (s :: SDType us k a) | s -> a where

-- | Typeclass for automatically generating singletons for a 'DType'.
-- Analogous to 'SingI' for 'Sing', but with explicit kind parameters.
class SDTypeI us k (a :: DType us k) where
    sdType :: SDType us k a

instance SIndexI us a i => SDTypeI us a ('TVar i) where
    sdType = STVar sIndex
instance (SDKindI a, SDTypeI (a ': us) b x, u ~ SDKindOf a) => SDTypeI us b ('Pi u x) where
    sdType = SPi sdKind sdType
instance (SDTypeI us (r ':~> k) f, SDTypeI us r x) => SDTypeI us k (f ':$ x) where
    sdType = sdType :%$ sdType
instance (SDTypeI us 'Type a, SDTypeI us 'Type b) => SDTypeI us 'Type (a ':-> b) where
    sdType = sdType :%-> sdType
instance SDTypeI us 'Type 'Bool where
    sdType = SBool
instance SDTypeI us 'Type 'Natural where
    sdType = SNatural
instance SDTypeI us ('Type ':~> 'Type) 'List where
    sdType = SList
instance SDTypeI us ('Type ':~> 'Type) 'Optional where
    sdType = SOptional

-- | Compare two type-level 'DType' with no free variables for equality.
sameDType
    :: SDType '[] k a
    -> SDType '[] k b
    -> Maybe (a :~: b)
sameDType = sameDTypeWith Ø

-- | Compare two type-level 'DType' with free variables for equality by
-- providing the kinds of each of the free variables.
sameDTypeWith
    :: Prod SDKind us
    -> SDType us k a
    -> SDType us k b
    -> Maybe (a :~: b)
sameDTypeWith vs a = \case
    STVar i
      | STVar j   <- a
      , Just Refl <- sSameIx i j
      -> Just Refl
    SPi u x
      | SPi v y   <- a
      , Just Refl <- sameDKind u v
      , Just Refl <- sameDTypeWith (u :< vs) x y
      -> Just Refl
    f :%$ x
      | g :%$ y   <- a
      , Just Refl <- sameDKind (kindOfWith vs f) (kindOfWith vs g)
      , Just Refl <- sameDKind (kindOfWith vs x) (kindOfWith vs y)
      , Just Refl <- sameDTypeWith vs f g
      , Just Refl <- sameDTypeWith vs x y
      -> Just Refl
    x :%-> y
      | u :%-> v  <- a
      , Just Refl <- sameDTypeWith vs x u
      , Just Refl <- sameDTypeWith vs y v
      -> Just Refl
    SBool     | SBool     <- a -> Just Refl
    SNatural  | SNatural  <- a -> Just Refl
    SList     | SList     <- a -> Just Refl
    SOptional | SOptional <- a -> Just Refl
    _       -> Nothing

-- | Find the kind of a type singleton with no free variables.
kindOf :: SDType '[] k t -> SDKind k
kindOf = kindOfWith Ø

-- | Find the kind of a type singleton with free variables by providing the
-- kinds of each free variable.
kindOfWith :: Prod SDKind us -> SDType us k t -> SDKind k
kindOfWith vs = \case
    STVar i -> ixProd vs (fromSIndex i)
    SPi u e -> kindOfWith (u :< vs) e
    f :%$ _ -> case kindOfWith vs f of
      _ :%~> r -> r
    _ :%-> _ -> SType
    SBool -> SType
    SNatural -> SType
    SList -> SType :%~> SType
    SOptional -> SType :%~> SType

type family MapShift (k :: DKind) (us :: [DKind]) (vs :: [DType us 'Type]) :: [DType (k ': us) 'Type] where
    MapShift k us '[]       = '[]
    MapShift k us (v ': vs) = Shift us (k ': us) k 'Type 'InsZ v ': MapShift k us vs

-- | Represents the possible terms encountered in Dhall.  A value of type
--
-- @
-- 'DTerm' '[a, b, c] d
-- @
--
-- Describes a value of type @d@ possibly containing free variables of type
-- @a@, @b@, and @c@.
--
-- Something of type @'DTerm' '[] a@ is a term of type @a@ with no free
-- variables.
data DTerm (us :: [DKind]) :: [DType us 'Type] -> DType us 'Type -> Type where
    Var           :: Index    vs a
                  -> DTerm us vs a
    Lam           :: SDType us 'Type     a
                  -> DTerm  us (a ': vs) b
                  -> DTerm  us vs        (a ':-> b)
    App           :: DTerm  us vs (a ':-> b)
                  -> DTerm  us vs a
                  -> DTerm  us vs b
    Let           :: Bindings (DType us 'Type) (DTerm us) vs qs
                  -> DTerm us qs a
                  -> DTerm us vs a
    TLam          :: SDKind k
                  -> DTerm (k ': us) (MapShift k us vs) b
                  -> DTerm  us       vs                 ('Pi (SDKindOf k) b)
    TApp          :: DTerm  us       vs ('Pi (SDKindOf k) b)
                  -> SDType us       k  a
                  -> DTerm  us       vs (Sub (k ': us) us k 'Type 'DZ a b)
    BoolLit       :: Bool
                  -> DTerm us vs 'Bool
    NaturalLit    :: Natural
                  -> DTerm us vs 'Natural
    NaturalFold   :: DTerm us vs ('Natural ':-> 'Pi 'SType (('TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ))
    NaturalBuild  :: DTerm us vs ('Pi 'SType (('TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'Natural)
    NaturalPlus   :: DTerm us vs 'Natural
                  -> DTerm us vs 'Natural
                  -> DTerm us vs 'Natural
    NaturalTimes  :: DTerm us vs 'Natural
                  -> DTerm us vs 'Natural
                  -> DTerm us vs 'Natural
    NaturalIsZero :: DTerm us vs ('Natural ':-> 'Bool)
    ListLit       :: SDType us 'Type a
                  -> Seq (DTerm us vs a)
                  -> DTerm us vs ('List ':$ a)         -- we should force evaluation to list a
    ListFold      :: DTerm us vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ)))
    ListBuild     :: DTerm us vs ('Pi 'SType ('Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'List ':$ 'TVar 'IZ))
    ListAppend    :: DTerm us vs ('List ':$ a)
                  -> DTerm us vs ('List ':$ a)
                  -> DTerm us vs ('List ':$ a)
    ListHead      :: DTerm us vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Optional ':$ 'TVar 'IZ))
    ListLast      :: DTerm us vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Optional ':$ 'TVar 'IZ))
    ListReverse   :: DTerm us vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'List     ':$ 'TVar 'IZ))
    OptionalLit   :: SDType us 'Type a
                  -> Maybe (DTerm us vs a)
                  -> DTerm us vs ('Optional ':$ a)
    Some          :: DTerm us vs a
                  -> DTerm us vs ('Optional ':$ a)
    None          :: DTerm us vs ('Pi 'SType ('Optional ':$ 'TVar 'IZ))

-- -- | Syntax tree for expressions
-- data Expr s a
--     = Const Const
--     | Var Var
--     | Lam Text (Expr s a) (Expr s a)
--     | Pi  Text (Expr s a) (Expr s a)
--     | App (Expr s a) (Expr s a)
--     | Let (NonEmpty (Binding s a)) (Expr s a)
--     | Annot (Expr s a) (Expr s a)
--     | BoolAnd (Expr s a) (Expr s a)
--     | BoolOr  (Expr s a) (Expr s a)
--     | BoolEQ  (Expr s a) (Expr s a)
--     | BoolNE  (Expr s a) (Expr s a)
--     | BoolIf (Expr s a) (Expr s a) (Expr s a)
--     | NaturalEven
--     | NaturalOdd
--     | NaturalToInteger
--     | NaturalShow
--     | Integer
--     | IntegerLit Integer
--     | IntegerShow
--     | IntegerToDouble
--     | Double
--     | DoubleLit Double
--     | DoubleShow
--     | Text
--     | TextLit (Chunks s a)
--     | TextAppend (Expr s a) (Expr s a)
--     | ListLength
--     | ListIndexed
--     | OptionalFold
--     | OptionalBuild
--     | Record    (Map Text (Expr s a))
--     | RecordLit (Map Text (Expr s a))
--     | Union     (Map Text (Expr s a))
--     | UnionLit Text (Expr s a) (Map Text (Expr s a))
--     | Combine (Expr s a) (Expr s a)
--     | CombineTypes (Expr s a) (Expr s a)
--     | Prefer (Expr s a) (Expr s a)
--     | Merge (Expr s a) (Expr s a) (Maybe (Expr s a))
--     | Constructors (Expr s a)
--     | Field (Expr s a) Text
--     | Project (Expr s a) (Set Text)
--     | Note s (Expr s a)
--     | ImportAlt (Expr s a) (Expr s a)
--     | Embed a
--     deriving (Eq, Foldable, Generic, Traversable, Show, Data)


-- | Singletons for 'DTerm'.  These are defined independently of 'Sing'
-- mostly to move the kind parameters to the front, to make them more easy
-- to use.
--
-- Note that there is currently no singleton implemented for the 'TLam'
-- constructor.
data SDTerm us (vs :: [DType us 'Type]) a :: DTerm us vs a -> Type where
    SVar           :: SIndex vs a i
                   -> SDTerm us vs a ('Var i)
    SLam           :: SDType us 'Type a
                   -> SDTerm us (a ': vs) b x
                   -> SDTerm us vs (a ':-> b) ('Lam (SDTypeOf us 'Type a) x)
    SApp           :: SDTerm us vs (a ':-> b) f
                   -> SDTerm us vs a x
                   -> SDTerm us vs b ('App f x)
    STLam          :: SDKind k
                   -> SDTerm (k ': us) (MapShift k us vs) b                    x
                   -> SDTerm us        vs                 ('Pi (SDKindOf k) b) ('TLam (SDKindOf k) x)
    STApp          :: SDTerm us        vs ('Pi (SDKindOf k) b)               f
                   -> SDType us        k  a
                   -> SDTerm us        vs (Sub (k ': us) us k 'Type 'DZ a b) ('TApp f (SDTypeOf us k a))
    SBoolLit       :: Sing b
                   -> SDTerm us vs 'Bool ('BoolLit b)
    SNaturalLit    :: Sing n
                   -> SDTerm us vs 'Natural ('NaturalLit n)
    SNaturalFold   :: SDTerm us vs ('Natural ':-> 'Pi 'SType (('TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ)) 'NaturalFold
    SNaturalBuild  :: SDTerm us vs ('Pi 'SType (('TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'Natural) 'NaturalBuild
    SNaturalPlus   :: SDTerm us vs 'Natural x
                   -> SDTerm us vs 'Natural y
                   -> SDTerm us vs 'Natural ('NaturalPlus x y)
    SNaturalTimes  :: SDTerm us vs 'Natural x
                   -> SDTerm us vs 'Natural y
                   -> SDTerm us vs 'Natural ('NaturalTimes x y)
    SNaturalIsZero :: SDTerm us vs ('Natural ':-> 'Bool) 'NaturalIsZero
    SListLit       :: SeqListEq xs xs'
                   -> SDType us 'Type a
                   -> Prod (SDTerm us vs a) xs'
                   -> SDTerm us vs ('List ':$ a) ('ListLit (SDTypeOf us 'Type a) xs)
    SListFold      :: SDTerm us vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ))) 'ListFold
    SListBuild     :: SDTerm us vs ('Pi 'SType ('Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'List ':$ 'TVar 'IZ)) 'ListBuild
    SListAppend    :: SDTerm us vs ('List ':$ a) xs
                   -> SDTerm us vs ('List ':$ a) ys
                   -> SDTerm us vs ('List ':$ a) ('ListAppend xs ys)
    SListHead      :: SDTerm us vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Optional ':$ 'TVar 'IZ)) 'ListHead
    SListLast      :: SDTerm us vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Optional ':$ 'TVar 'IZ)) 'ListLast
    SListReverse   :: SDTerm us vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'List     ':$ 'TVar 'IZ)) 'ListReverse
    SOptionalLit   :: SDType us 'Type a
                   -> Option (SDTerm us vs a) o
                   -> SDTerm us vs ('Optional ':$ a) ('OptionalLit (SDTypeOf us 'Type a) o)
    SSome          :: SDTerm us vs a x -> SDTerm us vs ('Optional ':$ a) ('Some x)
    SNone          :: SDTerm us vs ('Pi 'SType ('Optional ':$ 'TVar 'IZ)) 'None

data instance Sing (x :: DTerm us vs a) where
    SDTe :: { getSDTe :: SDTerm us vs a x } -> Sing x

-- | Find the type of a term singleton with no free variables.
typeOf :: SDTerm '[] '[] a x -> SDType '[] 'Type a
typeOf = typeOfWith Ø

-- | Find the type of a term singleton with free variables by providing the
-- type of each free variable.
typeOfWith :: Prod (SDType us 'Type) vs -> SDTerm us vs a x -> SDType us 'Type a
typeOfWith vs = \case
    SVar i            -> ixProd vs (fromSIndex i)
    SLam t x          -> t :%-> typeOfWith (t :< vs) x
    SApp f _          -> case typeOfWith vs f of
      _ :%-> r -> r
    STLam u x         -> SPi u $ typeOfWith (shiftProd vs) x
    STApp f x         -> case typeOfWith vs f of
      SPi _ g  -> sSub x g
    SBoolLit _        -> SBool
    SNaturalLit _     -> SNatural
    SNaturalFold      -> SNatural :%-> SPi SType ((STVar SIZ :%-> STVar SIZ) :%-> STVar SIZ :%-> STVar SIZ)
    SNaturalBuild     -> SPi SType ((STVar SIZ :%-> STVar SIZ) :%-> STVar SIZ :%-> STVar SIZ) :%-> SNatural
    SNaturalPlus _ _  -> SNatural
    SNaturalTimes _ _ -> SNatural
    SNaturalIsZero    -> SNatural :%-> SBool
    SListLit _ a _    -> SList :%$ a
    SListFold         -> SPi SType (SList :%$ STVar SIZ :%-> SPi SType ((STVar (SIS SIZ) :%-> STVar SIZ :%-> STVar SIZ) :%-> STVar SIZ :%-> STVar SIZ))
    SListBuild        -> SPi SType (SPi SType ((STVar (SIS SIZ) :%-> STVar SIZ :%-> STVar SIZ) :%-> STVar SIZ :%-> STVar SIZ) :%-> SList :%$ STVar SIZ)
    SListAppend xs _  -> typeOfWith vs xs
    SListHead         -> SPi SType (SList :%$ STVar SIZ :%-> SOptional :%$ STVar SIZ)
    SListLast         -> SPi SType (SList :%$ STVar SIZ :%-> SOptional :%$ STVar SIZ)
    SListReverse      -> SPi SType (SList :%$ STVar SIZ :%-> SList     :%$ STVar SIZ)
    SOptionalLit a _  -> SOptional :%$ a
    SSome x           -> SOptional :%$ typeOfWith vs x
    SNone             -> SPi SType (SOptional :%$ STVar SIZ)

shiftProd
    :: forall us vs k. ()
    => Prod (SDType us        'Type) vs
    -> Prod (SDType (k ': us) 'Type) (MapShift k us vs)
shiftProd = \case
    Ø       -> Ø
    x :< xs -> sShift x :< shiftProd xs


-- | Turn a 'DTerm' with no free variables into a Haskell value of the
-- appropriate type.
fromTerm :: DTerm '[] '[] a -> DTypeRep '[] 'Ø 'Type a
fromTerm = fromTermWith Ø

type family ShiftProd as bs k (p :: Prod (DType bs) as) :: Prod (DType (k ': bs)) as where
    ShiftProd '[]       bs k 'Ø         = 'Ø
    ShiftProd (a ': as) bs k (x ':< xs) = Shift bs (k ': bs) k a 'InsZ x ':< ShiftProd as bs k xs

type family Reassign as bs a (p :: Prod (DType bs) as) (r :: DType as a) :: DType bs a where
    Reassign as bs a p ('TVar i) = IxProd (DType bs) as a p i
    Reassign as bs a p ('Pi (u :: SDKind k) e)
        = 'Pi u (Reassign (k ': as) (k ': bs) a ('TVar 'IZ ':< ShiftProd as bs k p) e)
    Reassign as bs k p ((i :: DType as (r ':~> k)) ':$ (j :: DType as r))
        = Reassign as bs (r ':~> k) p i ':$ Reassign as bs r p j
    Reassign as bs 'Type p (i ':-> j)
        = Reassign as bs 'Type p i ':-> Reassign as bs 'Type p j
    Reassign as bs 'Type p 'Bool = 'Bool
    Reassign as bs 'Type p 'Natural = 'Natural
    Reassign as bs ('Type ':~> 'Type) p 'List = 'List
    Reassign as bs ('Type ':~> 'Type) p 'Optional = 'Optional

type family MapReassign as bs a (p :: Prod (DType bs) as) (rs :: [DType as a]) :: [DType bs a] where
    MapReassign as bs a p '[]       = '[]
    MapReassign as bs a p (x ': xs) = Reassign as bs a p x ': MapReassign as bs a p xs

reassignIndex
    :: forall us vs qs a p. ()
    => Index vs a
    -> Index (MapReassign us qs 'Type p vs) (Reassign us qs 'Type p a)
reassignIndex = \case
    IZ   -> IZ
    IS i -> IS (reassignIndex @_ @_ @_ @_ @p i)

shiftSProd
    :: SProd (DType qs) us p
    -> SProd (DType (a ': qs)) us (ShiftProd us qs a p)
shiftSProd = \case
    SØ -> SØ
    SDTy x :%< xs -> SDTy (sShift x) :%< shiftSProd xs

reTyVar
    :: SProd (DType qs) us p
    -> SDType us k a
    -> SDType qs k (Reassign us qs k p a)
reTyVar p = \case
    STVar i   -> getSDTy $ sIxProd p i
    SPi u x   -> SPi u (reTyVar (SDTy (STVar SIZ) :%< shiftSProd p) x)
    f :%$ x   -> reTyVar p f :%$ reTyVar p x
    x :%-> y  -> reTyVar p x :%-> reTyVar p y
    SBool     -> SBool
    SNatural  -> SNatural
    SList     -> SList
    SOptional -> SOptional

reTyVarBindings
    :: SProd (DType qs) us p
    -> Bindings (DType us 'Type) (DTerm us) vs rs
    -> Bindings (DType qs 'Type) (DTerm qs) (MapReassign us qs 'Type p vs) (MapReassign us qs 'Type p rs)
reTyVarBindings qs = \case
    BNil x   -> BNil $ reTyVarTerm qs x
    x :<? xs -> reTyVarTerm qs x :<? reTyVarBindings qs xs

reTyVarTerm
    :: forall us vs qs a p. ()
    => SProd (DType qs) us p
    -> DTerm us vs a
    -> DTerm qs (MapReassign us qs 'Type p vs) (Reassign us qs 'Type p a)
reTyVarTerm qs = \case
    Var i            -> Var (reassignIndex @_ @_ @_ @_ @p i)
    Lam t f          -> Lam (reTyVar qs t) (reTyVarTerm qs f)
    App f x          -> App (reTyVarTerm qs f) (reTyVarTerm qs x)
    TLam u f         -> TLam u . unsafeCoerce $ reTyVarTerm (SDTy (STVar SIZ) :%< shiftSProd qs) f  -- !!
    TApp f x         -> unsafeCoerce $ TApp (reTyVarTerm qs f) (reTyVar qs x)                       -- !!
    Let bs x         -> Let (reTyVarBindings qs bs) (reTyVarTerm qs x)
    BoolLit b        -> BoolLit b
    NaturalLit n     -> NaturalLit n
    NaturalFold      -> NaturalFold
    NaturalBuild     -> NaturalBuild
    NaturalPlus x y  -> NaturalPlus (reTyVarTerm qs x) (reTyVarTerm qs y)
    NaturalTimes x y -> NaturalTimes (reTyVarTerm qs x) (reTyVarTerm qs y)
    NaturalIsZero    -> NaturalIsZero
    ListLit t xs     -> ListLit (reTyVar qs t) (reTyVarTerm qs <$> xs)
    ListFold         -> ListFold
    ListBuild        -> ListBuild
    ListAppend xs ys -> ListAppend (reTyVarTerm qs xs) (reTyVarTerm qs ys)
    ListHead         -> ListHead
    ListLast         -> ListLast
    ListReverse      -> ListReverse
    OptionalLit t xs -> OptionalLit (reTyVar qs t) (reTyVarTerm qs <$> xs)
    Some x           -> Some (reTyVarTerm qs x)
    None             -> None

-- | Newtype wrapper over a Haskell value of the 'DTypeRep' of that term.
newtype DTypeRepVal us p (a :: DType us 'Type) = DTRV { getDTRV :: DTypeRep us p 'Type a }

fromBindings
    :: Prod (DTypeRepVal '[] 'Ø) vs
    -> Bindings (DType '[] 'Type) (DTerm '[]) vs us
    -> Prod (DTypeRepVal '[] 'Ø) us
fromBindings vs = \case
    BNil b   -> DTRV (fromTermWith vs b) :< vs
    b :<? bs -> fromBindings (DTRV (fromTermWith vs b) :< vs) bs

-- | Turn a 'DTerm' with free variables into a Haskell value of the
-- appropriate type by providing values for each free variable.
fromTermWith
    :: forall vs a. ()
    => Prod (DTypeRepVal '[] 'Ø) vs
    -> DTerm '[] vs a
    -> DTypeRep '[] 'Ø 'Type a
fromTermWith vs = \case
    Var i            -> getDTRV $ ixProd vs i
    Lam _ x          -> \y -> fromTermWith (DTRV y :< vs) x
    Let bs x         -> fromTermWith (fromBindings vs bs) x
    App f x          -> fromTermWith vs f (fromTermWith vs x)
    TLam _ f         -> FA $ \t -> unsafeCoerce $
        fromTermWith (unsafeCoerce vs) (reTyVarTerm (SDTy t :%< SØ) f)
    TApp f x         -> runForall (fromTermWith vs f) x
    BoolLit b        -> b
    NaturalLit n     -> n
    NaturalFold      -> \n -> FA $ \_ s z -> naturalFold n s z
    NaturalBuild     -> \f -> runForall f SNatural (+ 1) 0
    NaturalPlus x y  -> fromTermWith vs x + fromTermWith vs y
    NaturalTimes x y -> fromTermWith vs x * fromTermWith vs y
    NaturalIsZero    -> (== 0)
    ListLit _ xs     -> fromTermWith vs <$> xs
    ListFold         -> FA $ \a xs -> FA $ \l cons nil -> case subIns a l of
                          Refl -> foldr cons nil xs
    -- TODO: we need new way to encode FA, since this is gross now with new
    -- system
    ListBuild        -> FA $ \a f -> case subIns a (SList :%$ a) of
        Refl -> runForall f (SList :%$ a) (Seq.<|) Seq.empty
    ListAppend xs ys -> fromTermWith vs xs <> fromTermWith vs ys
    ListHead         -> FA $ \_ -> \case x Seq.:<| _ -> Just x
                                         Seq.Empty   -> Nothing
    ListLast         -> FA $ \_ -> \case _ Seq.:|> x -> Just x
                                         Seq.Empty   -> Nothing
    ListReverse      -> FA $ \_ -> Seq.reverse
    OptionalLit _ x  -> fromTermWith vs <$> x
    Some x           -> Just $ fromTermWith vs x
    None             -> FA $ \_ -> Nothing

-- | Attempt to convert a Haskell value into a 'DTerm' with no free
-- variables.  This will fail if you attempt to convert any Haskell
-- functions @a -> b@, since we cannot encode these in general into
-- a finite language like Dhall.
toTerm :: SDType '[] 'Type a -> DTypeRep '[] 'Ø 'Type a -> Maybe (DTerm '[] '[] a)
toTerm = \case
    STVar i         -> \_ -> Just $ case i of {}
    SPi _ _         -> \_ -> Nothing
    _ :%-> _        -> \_ -> Nothing
    SBool           -> Just . BoolLit
    SNatural        -> Just . NaturalLit
    f :%$ x         -> toTermT f x

toTermT
    :: SDType '[] (k ':~> 'Type) f
    -> SDType '[] k              b
    -> DTypeRep '[] 'Ø 'Type (f ':$ b)
    -> Maybe (DTerm '[] '[] (f ':$ b))
toTermT = \case
    STVar i   -> \_ -> const $ Just (case i of {})
    SPi _ _   -> \_ -> const Nothing
    SList     -> \a -> fmap (ListLit a) . traverse (toTerm a)
    SOptional -> \a -> maybe (Just (None `TApp` a)) (fmap Some . toTerm a)
    _ :%$ _   -> \_ -> const Nothing        -- ??

naturalFold :: Natural -> (a -> a) -> a -> a
naturalFold n s = go n
  where
    go 0 !x = x
    go i !x = go (i - 1) (s x)

-- | Required equality witness for using a type variable under a 'TLam'.
--
-- This is automatically resolved if you turn on the typechecker plugin.
--
-- @
-- {-# OPTIONS_GHC -fplugin Dhall.Typed.Plugin #-}
-- @
subIns
    :: forall k j a b. ()
    => SDType '[] k a
    -> SDType '[] j b
    -> (a :~: Sub '[j] '[] j k ('DZ :: Delete '[j] '[] j) b (Shift '[] '[j] j k ('InsZ :: Insert '[] '[j] j) a))
subIns _ _ = unsafeCoerce $ Refl @a

-- | Like 'subIns', but for two layers of 'TLam'.
--
-- This is automatically resolved if you turn on the typechecker plugin.
-- The typechecker plugin will solve arbitrarily nested layers.
--
-- @
-- {-# OPTIONS_GHC -fplugin Dhall.Typed.Plugin #-}
-- @
subIns2
    :: SDType '[] k a
    -> SDType '[] j b
    -> SDType '[] l c
    -> (a :~:
        Sub '[ l ] '[] l k 'DZ c
          (Sub '[l, j] '[ l ] j k ('DS 'DZ) (Shift '[] '[ l ] l j 'InsZ b)
              (Shift '[ j ] '[ l, j ] l k 'InsZ
                 (Shift '[] '[ j ] j k 'InsZ a)
              )
          )
       )
subIns2 _ _ _ = unsafeCoerce $ Refl

-- | Allows you to use a type variable "under" a 'TLam'.
sShift
    :: SDType as k x
    -> SDType (a ': as) k (Shift as (a ': as) a k 'InsZ x)
sShift = sShift_ SInsZ

-- | Like 'sShift', but can shift a type variable under multiple 'TLam's.
--
-- Providing 'SInsZ' will shift a single layer, @'SInsS' 'SInsZ'@ will
-- shift two layers, etc.
sShift_
    :: SInsert as bs a ins
    -> SDType as b x
    -> SDType bs b (Shift as bs a b ins x)
sShift_ ins = \case
    STVar i   -> STVar (sInsert ins i)
    SPi u e   -> SPi u (sShift_ (SInsS ins) e)
    u :%$ v   -> sShift_ ins u :%$ sShift_ ins v
    u :%-> v  -> sShift_ ins u :%-> sShift_ ins v
    SBool     -> SBool
    SNatural  -> SNatural
    SList     -> SList
    SOptional -> SOptional

-- | Substitute a type into the first free variable of a type expression.
sSub
    :: SDType bs a x
    -> SDType (a ': bs) b r
    -> SDType bs b (Sub (a ': bs) bs a b 'DZ x r)
sSub = sSub_ SDZ

-- | Substitute a type into the Nth free variable of a type expression.
-- Providing 'DZ' will substitute in the first free variable, providing
-- @'DS' 'DZ'@ will substitute in the second free variable, etc.
sSub_
    :: SDelete as bs c del
    -> SDType bs c x
    -> SDType as b r
    -> SDType bs b (Sub as bs c b del x r)
sSub_ del x = \case
    STVar i -> case sDelete del i of
      GotDeleted Refl -> x
      ThatsToxic j    -> STVar j
    SPi u e -> SPi u $ sSub_ (SDS del) (sShift x) e
    u :%$  v  -> sSub_ del x u :%$  sSub_ del x v
    u :%-> v  -> sSub_ del x u :%-> sSub_ del x v
    SBool     -> SBool
    SNatural  -> SNatural
    SList     -> SList
    SOptional -> SOptional

-- -- | Syntax tree for expressions
-- data Expr s a
--     = Const Const
--     | Var Var
--     | Lam Text (Expr s a) (Expr s a)
--     | Pi  Text (Expr s a) (Expr s a)
--     | App (Expr s a) (Expr s a)
--     | Let (NonEmpty (Binding s a)) (Expr s a)
--     | Annot (Expr s a) (Expr s a)
--     | Bool
--     | BoolLit Bool
--     | BoolAnd (Expr s a) (Expr s a)
--     | BoolOr  (Expr s a) (Expr s a)
--     | BoolEQ  (Expr s a) (Expr s a)
--     | BoolNE  (Expr s a) (Expr s a)
--     | BoolIf (Expr s a) (Expr s a) (Expr s a)
--     | Natural
--     | NaturalLit Natural
--     | NaturalFold
--     | NaturalBuild
--     | NaturalIsZero
--     | NaturalEven
--     | NaturalOdd
--     | NaturalToInteger
--     | NaturalShow
--     | NaturalPlus (Expr s a) (Expr s a)
--     | NaturalTimes (Expr s a) (Expr s a)
--     | Integer
--     | IntegerLit Integer
--     | IntegerShow
--     | IntegerToDouble
--     | Double
--     | DoubleLit Double
--     | DoubleShow
--     | Text
--     | TextLit (Chunks s a)
--     | TextAppend (Expr s a) (Expr s a)
--     | List
--     | ListLit (Maybe (Expr s a)) (Seq (Expr s a))
--     | ListAppend (Expr s a) (Expr s a)
--     | ListBuild
--     | ListFold
--     | ListLength
--     | ListIndexed
--     | OptionalFold
--     | OptionalBuild
--     | Record    (Map Text (Expr s a))
--     | RecordLit (Map Text (Expr s a))
--     | Union     (Map Text (Expr s a))
--     | UnionLit Text (Expr s a) (Map Text (Expr s a))
--     | Combine (Expr s a) (Expr s a)
--     | CombineTypes (Expr s a) (Expr s a)
--     | Prefer (Expr s a) (Expr s a)
--     | Merge (Expr s a) (Expr s a) (Maybe (Expr s a))
--     | Constructors (Expr s a)
--     | Field (Expr s a) Text
--     | Project (Expr s a) (Set Text)
--     | Note s (Expr s a)
--     | ImportAlt (Expr s a) (Expr s a)
--     | Embed a
--     deriving (Eq, Foldable, Generic, Traversable, Show, Data)



-- -- | Syntax tree for expressions
-- data Expr s a
--     -- | > Const c                                  ~  c
--     = Const Const
--     -- | > Var (V x 0)                              ~  x
--     --   > Var (V x n)                              ~  x@n
--     | Var Var
--     -- | > Lam x     A b                            ~  λ(x : A) -> b
--     | Lam Text (Expr s a) (Expr s a)
--     -- | > Pi "_" A B                               ~        A  -> B
--     --   > Pi x   A B                               ~  ∀(x : A) -> B
--     | Pi  Text (Expr s a) (Expr s a)
--     -- | > App f a                                  ~  f a
--     | App (Expr s a) (Expr s a)
--     -- | > Let [Binding x Nothing  r] e             ~  let x     = r in e
--     --   > Let [Binding x (Just t) r] e             ~  let x : t = r in e
--     | Let (NonEmpty (Binding s a)) (Expr s a)
--     -- | > Annot x t                                ~  x : t
--     | Annot (Expr s a) (Expr s a)
--     -- | > Bool                                     ~  Bool
--     | Bool
--     -- | > BoolLit b                                ~  b
--     | BoolLit Bool
--     -- | > BoolAnd x y                              ~  x && y
--     | BoolAnd (Expr s a) (Expr s a)
--     -- | > BoolOr  x y                              ~  x || y
--     | BoolOr  (Expr s a) (Expr s a)
--     -- | > BoolEQ  x y                              ~  x == y
--     | BoolEQ  (Expr s a) (Expr s a)
--     -- | > BoolNE  x y                              ~  x != y
--     | BoolNE  (Expr s a) (Expr s a)
--     -- | > BoolIf x y z                             ~  if x then y else z
--     | BoolIf (Expr s a) (Expr s a) (Expr s a)
--     -- | > Natural                                  ~  Natural
--     | Natural
--     -- | > NaturalLit n                             ~  n
--     | NaturalLit Natural
--     -- | > NaturalFold                              ~  Natural/fold
--     | NaturalFold
--     -- | > NaturalBuild                             ~  Natural/build
--     | NaturalBuild
--     -- | > NaturalIsZero                            ~  Natural/isZero
--     | NaturalIsZero
--     -- | > NaturalEven                              ~  Natural/even
--     | NaturalEven
--     -- | > NaturalOdd                               ~  Natural/odd
--     | NaturalOdd
--     -- | > NaturalToInteger                         ~  Natural/toInteger
--     | NaturalToInteger
--     -- | > NaturalShow                              ~  Natural/show
--     | NaturalShow
--     -- | > NaturalPlus x y                          ~  x + y
--     | NaturalPlus (Expr s a) (Expr s a)
--     -- | > NaturalTimes x y                         ~  x * y
--     | NaturalTimes (Expr s a) (Expr s a)
--     -- | > Integer                                  ~  Integer
--     | Integer
--     -- | > IntegerLit n                             ~  ±n
--     | IntegerLit Integer
--     -- | > IntegerShow                              ~  Integer/show
--     | IntegerShow
--     -- | > IntegerToDouble                          ~  Integer/toDouble
--     | IntegerToDouble
--     -- | > Double                                   ~  Double
--     | Double
--     -- | > DoubleLit n                              ~  n
--     | DoubleLit Double
--     -- | > DoubleShow                               ~  Double/show
--     | DoubleShow
--     -- | > Text                                     ~  Text
--     | Text
--     -- | > TextLit (Chunks [(t1, e1), (t2, e2)] t3) ~  "t1${e1}t2${e2}t3"
--     | TextLit (Chunks s a)
--     -- | > TextAppend x y                           ~  x ++ y
--     | TextAppend (Expr s a) (Expr s a)
--     -- | > List                                     ~  List
--     | List
--     -- | > ListLit (Just t ) [x, y, z]              ~  [x, y, z] : List t
--     --   > ListLit  Nothing  [x, y, z]              ~  [x, y, z]
--     | ListLit (Maybe (Expr s a)) (Seq (Expr s a))
--     -- | > ListAppend x y                           ~  x # y
--     | ListAppend (Expr s a) (Expr s a)
--     -- | > ListBuild                                ~  List/build
--     | ListBuild
--     -- | > ListFold                                 ~  List/fold
--     | ListFold
--     -- | > ListLength                               ~  List/length
--     | ListLength
--     -- | > ListHead                                 ~  List/head
--     | ListHead
--     -- | > ListLast                                 ~  List/last
--     | ListLast
--     -- | > ListIndexed                              ~  List/indexed
--     | ListIndexed
--     -- | > ListReverse                              ~  List/reverse
--     | ListReverse
--     -- | > Optional                                 ~  Optional
--     | Optional
--     -- | > OptionalLit t (Just e)                   ~  [e] : Optional t
--     --   > OptionalLit t Nothing                    ~  []  : Optional t
--     | OptionalLit (Expr s a) (Maybe (Expr s a))
--     -- | > Some e                                   ~  Some e
--     | Some (Expr s a)
--     -- | > None                                     ~  None
--     | None
--     -- | > OptionalFold                             ~  Optional/fold
--     | OptionalFold
--     -- | > OptionalBuild                            ~  Optional/build
--     | OptionalBuild
--     -- | > Record       [(k1, t1), (k2, t2)]        ~  { k1 : t1, k2 : t1 }
--     | Record    (Map Text (Expr s a))
--     -- | > RecordLit    [(k1, v1), (k2, v2)]        ~  { k1 = v1, k2 = v2 }
--     | RecordLit (Map Text (Expr s a))
--     -- | > Union        [(k1, t1), (k2, t2)]        ~  < k1 : t1 | k2 : t2 >
--     | Union     (Map Text (Expr s a))
--     -- | > UnionLit k v [(k1, t1), (k2, t2)]        ~  < k = v | k1 : t1 | k2 : t2 >
--     | UnionLit Text (Expr s a) (Map Text (Expr s a))
--     -- | > Combine x y                              ~  x ∧ y
--     | Combine (Expr s a) (Expr s a)
--     -- | > CombineTypes x y                         ~  x ⩓ y
--     | CombineTypes (Expr s a) (Expr s a)
--     -- | > Prefer x y                               ~  x ⫽ y
--     | Prefer (Expr s a) (Expr s a)
--     -- | > Merge x y (Just t )                      ~  merge x y : t
--     --   > Merge x y  Nothing                       ~  merge x y
--     | Merge (Expr s a) (Expr s a) (Maybe (Expr s a))
--     -- | > Constructors e                           ~  constructors e
--     | Constructors (Expr s a)
--     -- | > Field e x                                ~  e.x
--     | Field (Expr s a) Text
--     -- | > Project e xs                             ~  e.{ xs }
--     | Project (Expr s a) (Set Text)
--     -- | > Note s x                                 ~  e
--     | Note s (Expr s a)
--     -- | > ImportAlt                                ~  e1 ? e2
--     | ImportAlt (Expr s a) (Expr s a)
--     -- | > Embed import                             ~  import
--     | Embed a
--     deriving (Eq, Foldable, Generic, Traversable, Show, Data)


