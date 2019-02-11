{-# LANGUAGE BangPatterns                   #-}
{-# LANGUAGE EmptyCase                      #-}
{-# LANGUAGE FlexibleContexts               #-}
{-# LANGUAGE FlexibleInstances              #-}
{-# LANGUAGE GADTs                          #-}
{-# LANGUAGE InstanceSigs                   #-}
{-# LANGUAGE KindSignatures                 #-}
{-# LANGUAGE LambdaCase                     #-}
{-# LANGUAGE OverloadedStrings              #-}
{-# LANGUAGE PolyKinds                      #-}
{-# LANGUAGE RankNTypes                     #-}
{-# LANGUAGE RecordWildCards                #-}
{-# LANGUAGE ScopedTypeVariables            #-}
{-# LANGUAGE StandaloneDeriving             #-}
{-# LANGUAGE TemplateHaskell                #-}
{-# LANGUAGE TypeApplications               #-}
{-# LANGUAGE TypeFamilies                   #-}
{-# LANGUAGE TypeFamilyDependencies         #-}
{-# LANGUAGE TypeInType                     #-}
{-# LANGUAGE TypeOperators                  #-}
{-# LANGUAGE TypeSynonymInstances           #-}
{-# LANGUAGE UndecidableInstances           #-}
{-# LANGUAGE ViewPatterns                   #-}
-- {-# OPTIONS_GHC -fplugin Dhall.Typed.Plugin #-}

module Dhall.Typed.Core (
  -- * Kinds
    DKind(..), SDKind(..)
  -- * Types
  , DType(..), SDType(..), kindOf
  , Sub, Shift
  -- * Terms
  , DTerm(..), SDTerm(..), SeqListEq(..), typeOf
  -- * Evaluation
  , DTypeRep, Forall(..), ForallTC(..), DTypeRepVal(..)
  , fromTerm
  -- * Manipulation
  , sShift, sShift_, subIns
  -- * Samples
  , ident, konst, konst2, natBuild, listBuild
  ) where

import           Control.Applicative hiding                (Const(..))
import           Control.Monad
import           Data.Foldable
import           Data.Functor
import           Data.Functor.Identity
import           Data.Kind
import           Data.List hiding                          (delete)
import           Data.List.NonEmpty                        (NonEmpty(..))
import           Data.Maybe
import           Data.Profunctor
import           Data.Sequence                             (Seq(..))
import           Data.Sequence                             (Seq)
import           Data.Singletons
import           Data.Singletons.Prelude.List              (Sing(..))
import           Data.Singletons.Prelude.Maybe
import           Data.Singletons.Prelude.Tuple
import           Data.Singletons.Sigma
import           Data.Singletons.TH hiding                 (Sum)
import           Data.Singletons.TypeLits
import           Data.Text                                 (Text)
import           Data.Traversable
import           Data.Type.Equality
import           Data.Type.Universe
import           Data.Void
import           Debug.Trace
import           Dhall.Typed.Index
import           Dhall.Typed.N
import           Dhall.Typed.Option
import           Dhall.Typed.Prod
import           Dhall.Typed.Sum
import           GHC.Generics
import           GHC.TypeLits                              (Symbol)
import           Numeric.Natural
import           Text.Printf
import           Unsafe.Coerce                             (unsafeCoerce)
import qualified Control.Applicative                       as P
import qualified Data.List.NonEmpty                        as NE
import qualified Data.Sequence                             as Seq
import qualified Data.Text                                 as T
import qualified Dhall                         as D hiding (Type)
import qualified Dhall.Context                             as D
import qualified Dhall.Core                                as D
import qualified Dhall.Map                                 as M
import qualified Dhall.TypeCheck                           as D
import qualified GHC.TypeLits                              as TL

data DKind = Type | DKind :~> DKind
  deriving (Eq, Ord, Show)

data SDKind :: DKind -> Type where
    SType  :: SDKind 'Type
    (:%~>) :: SDKind a -> SDKind b -> SDKind (a ':~> b)

deriving instance Show (SDKind k)

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
    Bool     :: DType us 'Type
    Natural  :: DType us 'Type
    List     :: DType us ('Type ':~> 'Type)
    Optional :: DType us ('Type ':~> 'Type)

infixr 0 :->
infixl 9 :$

type family DKindRep (x :: DKind) where
    DKindRep 'Type      = Type
    DKindRep (a ':~> b) = DKindRep a -> DKindRep b

data Forall k :: DType '[k] 'Type -> Type where
    FA :: { runForall :: forall r. SDType '[] k r -> DTypeRep 'Type (Sub '[k] '[] k 'Type 'DZ r a) }
       -> Forall k a

data ForallTC j k :: DType '[k] (j ':~> 'Type) -> DKindRep j -> Type where
    FATC :: { runForallTCC
                :: forall r. ()
                => SDType '[] k r
                -> DTypeRep (j ':~> 'Type) (Sub '[k] '[] k (j ':~> 'Type) 'DZ r a) x
            }
         -> ForallTC j k a x

type family DTypeRep k (x :: DType '[] k) :: DKindRep k where
    DTypeRep k                  ('TVar i)                   = TL.TypeError ('TL.Text "Free variable in type expression")
    DTypeRep 'Type              ('Pi (u :: SDKind a) t)     = Forall a t
    DTypeRep (k ':~> 'Type)     ('Pi (u :: SDKind a) t) = ForallTC k a t
    DTypeRep k                  ((f :: DType '[] (r ':~> k)) ':$ (x :: DType '[] r))
        = DTypeRep (r ':~> k) f (DTypeRep r x)
    DTypeRep 'Type              (a ':-> b) = DTypeRep 'Type a -> DTypeRep 'Type b
    DTypeRep 'Type              'Bool      = Bool
    DTypeRep 'Type              'Natural   = Natural
    DTypeRep ('Type ':~> 'Type) 'List      = Seq
    DTypeRep ('Type ':~> 'Type) 'Optional  = Maybe
    DTypeRep k                  x          = TL.TypeError ('TL.Text "No DTypeRep: " 'TL.:<>: 'TL.ShowType '(k, x))

type family MaybeVar a b (x :: DType vs a) (i :: Maybe (Index vs b)) :: DType vs b where
    MaybeVar a a x 'Nothing  = x
    MaybeVar a b x 'Nothing  = TL.TypeError ('TL.Text "What happened?")
    MaybeVar a b x ('Just i) = 'TVar i
    MaybeVar a b x i = TL.TypeError ('TL.Text "No Maybe: " 'TL.:<>: 'TL.ShowType '(x, i))

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

data SDType us k :: DType us k -> Type where
    STVar     :: SIndex us a i -> SDType us a ('TVar i)
    SPi       :: SDKind a -> SDType (a ': us) b x -> SDType us b ('Pi (u :: SDKind a) x)
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

deriving instance Show (SDType us k t)

kindOf :: Prod SDKind us -> SDType us k t -> SDKind k
kindOf vs = \case
    STVar i -> ixProd vs (fromSIndex i)
    SPi u e -> kindOf (u :< vs) e
    f :%$ _ -> case kindOf vs f of
      _ :%~> r -> r
    _ :%-> _ -> SType
    SBool -> SType
    SNatural -> SType
    SList -> SType :%~> SType
    SOptional -> SType :%~> SType

data DTerm :: [DType '[] 'Type] -> DType '[] 'Type -> Type where
    Var           :: Index vs a
                  -> DTerm vs a
    Lam           :: SDType '[] 'Type a
                  -> DTerm (a ': vs) b
                  -> DTerm vs (a ':-> b)
    App           :: DTerm vs (a ':-> b)
                  -> DTerm vs a
                  -> DTerm vs b
    TLam          :: SDKind k
                  -> (forall a. SDType '[] k a -> DTerm vs (Sub '[k] '[] k 'Type 'DZ a b))
                  -> DTerm vs ('Pi (u :: SDKind k) b)
    TApp          :: DTerm vs ('Pi (u :: SDKind k) b)
                  -> SDType '[] k a
                  -> DTerm vs (Sub '[k] '[] k 'Type 'DZ a b)
    BoolLit       :: Bool
                  -> DTerm vs 'Bool
    NaturalLit    :: Natural
                  -> DTerm vs 'Natural
    NaturalFold   :: DTerm vs ('Natural ':-> 'Pi 'SType (('TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ))
    NaturalBuild  :: DTerm vs ('Pi 'SType (('TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'Natural)
    NaturalPlus   :: DTerm vs 'Natural
                  -> DTerm vs 'Natural
                  -> DTerm vs 'Natural
    NaturalTimes  :: DTerm vs 'Natural
                  -> DTerm vs 'Natural
                  -> DTerm vs 'Natural
    NaturalIsZero :: DTerm vs ('Natural ':-> 'Bool)
    ListLit       :: SDType '[] 'Type a
                  -> Seq (DTerm vs a)
                  -> DTerm vs ('List ':$ a)
    ListFold      :: DTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ)))
    ListBuild     :: DTerm vs ('Pi 'SType ('Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'List ':$ 'TVar 'IZ))
    ListAppend    :: DTerm vs ('List ':$ a)
                  -> DTerm vs ('List ':$ a)
                  -> DTerm vs ('List ':$ a)
    ListHead      :: DTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Optional ':$ 'TVar 'IZ))
    ListLast      :: DTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Optional ':$ 'TVar 'IZ))
    ListReverse   :: DTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'List     ':$ 'TVar 'IZ))
    OptionalLit   :: SDType '[] 'Type a
                  -> Maybe (DTerm vs a)
                  -> DTerm vs ('Optional ':$ a)
    Some          :: DTerm vs a -> DTerm vs ('Optional ':$ a)
    None          :: DTerm vs ('Pi 'SType ('Optional ':$ 'TVar 'IZ))

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


data SeqListEq :: Seq a -> [a] -> Type where
    SeqListEq :: SeqListEq xs ys    -- TODO: define

data SDTerm vs t :: DTerm vs t -> Type where
    SVar           :: SIndex vs a i
                   -> SDTerm vs a ('Var i)
    SLam           :: SDType '[] 'Type a
                   -> SDTerm (a ': vs) b x
                   -> SDTerm vs (a ':-> b) ('Lam (u :: SDType '[] 'Type a) x)
    SApp           :: SDTerm vs (a ':-> b) f
                   -> SDTerm vs a x
                   -> SDTerm vs b ('App f x)
    -- TLam          :: SDKind k
    --               -> (forall a. SDType '[] k a -> DTerm vs (Sub '[k] '[] k 'Type k 'DZ a b))
    --               -> DTerm vs ('Pi (u :: SDKind k) b)
    STApp          :: SDTerm vs ('Pi (u :: SDKind k) b) x
                   -> SDType '[] k a
                   -> SDTerm vs (Sub '[k] '[] k 'Type 'DZ a b) ('TApp x (q :: SDType '[] k a))
    SBoolLit       :: Sing b
                   -> SDTerm vs 'Bool ('BoolLit b)
    SNaturalLit    :: Sing n
                   -> SDTerm vs 'Natural ('NaturalLit n)
    SNaturalFold   :: SDTerm vs ('Natural ':-> 'Pi 'SType (('TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ)) 'NaturalFold
    SNaturalBuild  :: SDTerm vs ('Pi 'SType (('TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'Natural) 'NaturalBuild
    SNaturalPlus   :: SDTerm vs 'Natural x
                   -> SDTerm vs 'Natural y
                   -> SDTerm vs 'Natural ('NaturalPlus x y)
    SNaturalTimes  :: SDTerm vs 'Natural x
                   -> SDTerm vs 'Natural y
                   -> SDTerm vs 'Natural ('NaturalTimes x y)
    SNaturalIsZero :: SDTerm vs ('Natural ':-> 'Bool) 'NaturalIsZero
    SListLit       :: SeqListEq xs xs'
                   -> SDType '[] 'Type a
                   -> Prod (SDTerm vs a) xs'
                   -> SDTerm vs ('List ':$ a) ('ListLit (u :: SDType '[] 'Type a) xs)
    SListFold      :: SDTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ))) 'ListFold
    SListBuild     :: SDTerm vs ('Pi 'SType ('Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'List ':$ 'TVar 'IZ)) 'ListBuild
    SListAppend    :: SDTerm vs ('List ':$ a) xs
                   -> SDTerm vs ('List ':$ a) ys
                   -> SDTerm vs ('List ':$ a) ('ListAppend xs ys)
    SListHead      :: SDTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Optional ':$ 'TVar 'IZ)) 'ListHead
    SListLast      :: SDTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Optional ':$ 'TVar 'IZ)) 'ListLast
    SListReverse   :: SDTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'List     ':$ 'TVar 'IZ)) 'ListReverse
    SOptionalLit   :: SDType '[] 'Type a
                   -> Option (SDTerm vs a) o
                   -> SDTerm vs ('Optional ':$ a) ('OptionalLit (u :: SDType '[] 'Type a) o)
    SSome          :: SDTerm vs a x -> SDTerm vs ('Optional ':$ a) ('Some x)
    SNone          :: SDTerm vs ('Pi 'SType ('Optional ':$ 'TVar 'IZ)) 'None

typeOf :: Prod (SDType '[] 'Type) vs -> SDTerm vs a x -> SDType '[] 'Type a
typeOf vs = \case
    SVar i            -> ixProd vs (fromSIndex i)
    SLam t x          -> t :%-> typeOf (t :< vs) x
    SApp f _          -> case typeOf vs f of
      _ :%-> r -> r
    STApp f x         -> case typeOf vs f of
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
    SListAppend xs _  -> typeOf vs xs
    SListHead         -> SPi SType (SList :%$ STVar SIZ :%-> SOptional :%$ STVar SIZ)
    SListLast         -> SPi SType (SList :%$ STVar SIZ :%-> SOptional :%$ STVar SIZ)
    SListReverse      -> SPi SType (SList :%$ STVar SIZ :%-> SList     :%$ STVar SIZ)
    SOptionalLit a _  -> SOptional :%$ a
    SSome x           -> SOptional :%$ typeOf vs x
    SNone             -> SPi SType (SOptional :%$ STVar SIZ)

ident :: DTerm vs ('Pi 'SType ('TVar 'IZ ':-> 'TVar 'IZ))
ident = TLam SType $ \a -> Lam a (Var IZ)

-- Couldn't match type ‘a’
--   with ‘Sub '[ 'Type] '[] 'Type 'Type 'Type 'DZ b (Shift '[] '[ 'Type] 'Type 'Type 'InsZ a)’

newtype DTypeRepVal a = DTRV { getDTRV :: DTypeRep 'Type a }

fromTerm :: Prod DTypeRepVal vs -> DTerm vs a -> DTypeRep 'Type a
fromTerm vs = \case
    Var i            -> getDTRV $ ixProd vs i
    Lam _ x          -> \y -> fromTerm (DTRV y :< vs) x
    App f x          -> fromTerm vs f (fromTerm vs x)
    TLam _ f         -> FA (fromTerm vs . f)
    TApp f x         -> runForall (fromTerm vs f) x
    BoolLit b        -> b
    NaturalLit n     -> n
    NaturalFold      -> \n -> FA $ \_ s z -> naturalFold n s z
    NaturalBuild     -> \f -> runForall f SNatural (+ 1) 0
    NaturalPlus x y  -> fromTerm vs x + fromTerm vs y
    NaturalTimes x y -> fromTerm vs x * fromTerm vs y
    NaturalIsZero    -> (== 0)
    ListLit _ xs     -> fromTerm vs <$> xs
    ListFold         -> FA $ \a xs -> FA $ \l cons nil -> case subIns a l of
                          Refl -> foldr cons nil xs
    -- example of sub-ins living under a type family (DTypeRep
    ListBuild        -> FA $ \a f -> case subIns a (SList :%$ a) of
                          Refl -> runForall f (SList :%$ a) (Seq.<|) Seq.empty
    ListAppend xs ys -> fromTerm vs xs <> fromTerm vs ys
    -- TODO: any way to not require dummy argument?
    ListHead         -> FA $ \_ -> \case x Seq.:<| _ -> Just x
                                         Seq.Empty   -> Nothing
    ListLast         -> FA $ \_ -> \case _ Seq.:|> x -> Just x
                                         Seq.Empty   -> Nothing
    ListReverse      -> FA $ \_ -> Seq.reverse
    OptionalLit _ x  -> fromTerm vs <$> x
    Some x           -> Just $ fromTerm vs x
    None             -> FA $ \_ -> Nothing

-- -- toTerm might not be possible.
-- toTerm :: SDType '[] 'Type a -> DTypeRep 'Type a -> DTerm '[] a
-- toTerm = \case
--     STVar i         -> case i of {}
--     gPi u b         -> \f -> TLam u $ \a -> toTerm (sSub SDZ a b) $ runForall f a
--     a :%-> b        -> \f -> Lam a $ toTerm b $ f undefined
--     SBool           -> BoolLit
--     SNatural        -> NaturalLit
--     f :%$ x         -> toTermT f x

-- toTermT
--     :: SDType '[] (k ':~> 'Type) f
--     -> SDType '[] k              b
--     -> DTypeRep 'Type (f ':$ b)
--     -> DTerm vs (f ':$ b)
-- toTermT = \case
--     STVar i   -> case i of {}
--     SPi _ _   -> undefined
--     SList     -> \a -> ListLit a . fmap (toTerm a)
--     SOptional -> \a -> maybe (None `TApp` a) (Some . toTerm a)
--     _ :%$ _   -> \_ -> undefined

naturalFold :: Natural -> (a -> a) -> a -> a
naturalFold n s = go n
  where
    go 0 !x = x
    go i !x = go (i - 1) (s x)

subIns
    :: forall k j a b. ()
    => SDType '[] k a
    -> SDType '[] j b
    -> (a :~: Sub '[j] '[] j k 'DZ b (Shift '[] '[j] j k 'InsZ a))
subIns _ _ = unsafeCoerce $ Refl @a

konst :: DTerm vs ('Pi 'SType ('Pi 'SType ('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar ('IS 'IZ))))
konst = TLam SType $ \a ->
          TLam SType $ \b ->
            case subIns a b of
              Refl -> Lam a (Lam b (Var (IS IZ)))

konst2 :: DTerm vs ('Pi 'SType ('TVar 'IZ ':-> 'Pi 'SType ('TVar 'IZ ':-> 'TVar ('IS 'IZ))))
konst2 = TLam SType $ \a ->
    Lam a $ TLam SType $ \b ->
      case subIns a b of
        Refl -> Lam b (Var (IS IZ))

natBuild
    :: DTerm vs ('Pi 'SType (('TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'Natural)
natBuild = Lam (SPi SType ((STVar SIZ :%-> STVar SIZ) :%-> STVar SIZ :%-> STVar SIZ)) $
           Var IZ
    `TApp` SNatural
     `App` Lam SNatural (NaturalPlus (Var IZ) (NaturalLit 1))
     `App` NaturalLit 0

-- there is asymmetry between Lam and TLam.  maybe use type variables to
-- address, instead of functions?

listBuild
    :: DTerm vs ('Pi 'SType ('Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'List ':$ 'TVar 'IZ))
listBuild = TLam SType $ \a ->
    Lam (SPi SType ((sShift a :%-> STVar SIZ :%-> STVar SIZ) :%-> STVar SIZ :%-> STVar SIZ)) $
      case subIns a (SList :%$ a) of
        Refl ->   Var IZ
          `TApp` (SList :%$ a)
           `App` Lam a (Lam (SList :%$ a) (ListAppend (ListLit a (Seq.singleton (Var (IS IZ)))) (Var IZ)))
           `App` ListLit a Seq.empty

sShift
    :: SDType as k x
    -> SDType (a ': as) k (Shift as (a ': as) a k 'InsZ x)
sShift = sShift_ SInsZ

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

sSub
    :: SDType bs a x
    -> SDType (a ': bs) b r
    -> SDType bs b (Sub (a ': bs) bs a b 'DZ x r)
sSub = sSub_ SDZ

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


