{-# LANGUAGE BangPatterns           #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
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

module Dhall.Typed where

-- module Dhall.Typed (
--   ) where

import           Control.Applicative hiding                (Const(..))
import           Control.Monad
import           Data.Foldable
import           Data.Functor
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
import           Dhall.Typed.Prod
import           Dhall.Typed.Sum
import           GHC.Generics
import           GHC.TypeLits                              (Symbol)
import           Numeric.Natural
import           Text.Printf
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

data DKind = Type | DKind :~> DKind
  deriving (Eq, Ord, Show)

data SDKind :: DKind -> Type where
    SType  :: SDKind 'Type
    (:%~>) :: SDKind a -> SDKind b -> SDKind (a ':~> b)

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

type family MaybeVar a b where
    MaybeVar a 'Nothing  = a
    MaybeVar a ('Just i) = 'TVar i

type family Sub as bs a b (d :: Delete as bs a) x (r :: DType as b) :: DType bs b where
    Sub as bs a b                  d x ('TVar i)
        = MaybeVar x (Del as bs a b d i)
    Sub as bs a b                  d x ('Pi (u :: SDKind k) e)
        = 'Pi u (Sub (k ': as) (k ': bs) a b ('DS d) x e)
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

data instance Sing (i :: Index as a) where
    SIZ :: Sing 'IZ
    SIS :: Sing i -> Sing ('IS i)

data instance Sing (a :: DType us k) where
    STVar     :: Sing i -> Sing ('TVar i)
    (:%$)     :: Sing f -> Sing x -> Sing (f ':$ x)
    (:%->)    :: Sing x -> Sing y -> Sing (x ':-> y)
    SBool     :: Sing 'Bool
    SNatural  :: Sing 'Natural
    SList     :: Sing 'List
    SOptional :: Sing 'Optional

data DTerm :: [DType '[] 'Type] -> DType '[] 'Type -> Type where
    Var           :: Index vs a
                  -> DTerm vs a
    Lam           :: DTerm (a ': vs) b
                  -> DTerm vs (a ':-> b)
    App           :: DTerm vs (a ':-> b)
                  -> DTerm vs a
                  -> DTerm vs b
    TApp          :: DTerm vs ('Pi (u :: SDKind k) b)
                  -> Sing (a :: DType '[] k)
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
    NaturalIsZero :: DTerm vs ('Natural ':-> 'Natural)
    ListLit       :: Sing a
                  -> Seq (DTerm vs a)
                  -> DTerm vs ('List ':$ a)
    ListFold      :: DTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ)))
    ListBuild     :: DTerm vs ('Pi 'SType ('Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'List ':$ 'TVar 'IZ))
    ListHead      :: DTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Optional ':$ 'TVar 'IZ))
    ListLast      :: DTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Optional ':$ 'TVar 'IZ))
    ListReverse   :: DTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'List     ':$ 'TVar 'IZ))
    OptionalLit   :: Sing a
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
--     | ListAppend (Expr s a) (Expr s a)
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


data Delete :: [k] -> [k] -> k -> Type where
    DZ :: Delete (a ': as) as a
    DS :: Delete as bs c -> Delete (a ': as) (a ': bs) c

delete :: forall as bs a b. Delete as bs a -> Index as b -> Maybe (Index bs b)
delete = \case
    DZ -> \case
      IZ   -> Nothing
      IS i -> Just i
    DS d -> \case
      IZ   -> Just IZ
      IS i -> IS <$> delete d i

type family ISMaybe a where
    ISMaybe 'Nothing = 'Nothing
    ISMaybe ('Just i) = 'Just ('IS i)

type family Del as bs a b (d :: Delete as bs a) (i :: Index as b) :: Maybe (Index bs b) where
    Del (a ': as) as        a a 'DZ     'IZ     = 'Nothing
    Del (a ': as) (a ': bs) b a ('DS d) 'IZ     = 'Just 'IZ
    Del (a ': as) as        a b 'DZ     ('IS i) = 'Just i
    Del (a ': as) (a ': bs) b c ('DS d) ('IS i) = ISMaybe (Del as bs b c d i)


-- sub :: Delete as bs b -> b -> Index as a -> Either (Index bs a) a
-- sub = \case
--     RZ -> \x -> \case
--       IZ   -> Right x
--       IS i -> Left (IS i)
      -- Left i -> case i of
      --   IZ   -> Right x
        -- IS i -> Left  _



-- okay, being able to state (forall r. (r -> r) -> (r -> r)) symbolically
-- is a good reason why we need to have an expression language instead of
-- just first classing things.

-- So apparently, we need to somehow link:
--
-- (r .:. ((r -> r) -> (r -> r))) Natural
--
-- with
--
-- (forall r. (r -> r) -> (r -> r)) -> Natural
--
-- Problem is that user can instnatiate with specific r, so we need it to
-- be rank-n as well.  So maybe
--
-- (forall r. DType r -> DType ((r -> r) -> (r -> r))) -> Natural
-- ^-------------------------------------------------^
-- \- that's exactly what foo is.
--
-- Rep MyFun -> (forall r. TyFun MyFun r) -> Natural

-- wouldn't it be nice if we could define a type family where
--
-- Forall "a" (Embed "a" -> [Embed "a"])
--
-- evaluates to (forall a. (a -> [a]))
--

-- data family Embed :: N -> a

-- reEmbed :: Embed a -> b
-- reEmbed = undefined

-- type family CompN n m a b c where
--     CompN 'Z     'Z     a b c = b
--     CompN 'Z     ('S m) a b c = c
--     CompN ('S n) 'Z     a b c = a
--     CompN ('S n) ('S m) a b c = CompN n m a b c

-- type family UnEmbed a n t where
--     UnEmbed a 'Z     (Embed 'Z)     = a
--     UnEmbed a 'Z     (Embed ('S m)) = Embed m
--     UnEmbed a ('S n) (Embed 'Z)     = Embed 'Z
--     UnEmbed a ('S n) (Embed ('S m)) = CompN n m (Embed ('S m)) a (Embed m)
--     UnEmbed a n      (Forall k e)   = Forall k (UnEmbed a ('S n) e)
--     UnEmbed a n      (b -> c)       = UnEmbed a n b -> UnEmbed a n c
--     UnEmbed a n      (Seq b)        = Seq (UnEmbed a n b)
--     UnEmbed a n      (Maybe b)      = Maybe (UnEmbed a n b)
--     UnEmbed a n      b              = b
--     -- UnEmbed a n      (f b c)        = f (UnEmbed a n b) (UnEmbed a n c)
--     -- UnEmbed a n      (f b)          = f (UnEmbed a n b)

-- data Forall k e = Forall { runForall :: forall r. DType k r -> UnEmbed r 'Z e }

-- data DKind :: Type -> Type where
--     KType     :: DKind Type
--     (:~>)     :: DKind a -> DKind b -> DKind (a :~> b)

-- -- data FA = FA
-- data a :~> b = FA b

-- data SomeDKind :: Type where
--     SDK :: DKind k -> SomeDKind

-- data FA :: (Type -> Type) -> Type -> Type -> Type where
--     FAType :: f b -> FA f a b

-- type family Sub (a :: k) (b :: k) where

-- type family ($$) (a :: j -> k)

-- data VIx :: N -> [SomeDKind] -> DKind k -> Type where
--     VIZ :: VIx 'Z ('SDK k ': vs) k
--     VIS :: VIx n vs k -> VIx ('S n) (v ': vs) k

-- deriving instance Show (VIx n ks k)

-- data family Embed :: N -> DKind k -> k

-- data Forall k e = Forall { runForall :: forall r. DType k r -> UnEmbed r 'Z e }

-- data SomeDType :: [SomeDKind] -> DKind k -> Type where
--     SDT :: DType vs k a -> SomeDType vs k

-- data FA vs v k = FA { runForall :: SomeDType vs v -> SomeDType vs k }

-- type family CompN n m a b c where
--     CompN 'Z     'Z     a b c = b
--     CompN 'Z     ('S m) a b c = c
--     CompN ('S n) 'Z     a b c = a
--     CompN ('S n) ('S m) a b c = CompN n m a b c

-- type family UnEmbed k a n (t :: k) :: k where
--     UnEmbed k         a 'Z     (Embed 'Z     v) = a
--     UnEmbed k         a 'Z     (Embed ('S m) v) = Embed m v
--     UnEmbed k         a ('S n) (Embed 'Z     v) = Embed 'Z v
--     UnEmbed k         a ('S n) (Embed ('S m) v) = CompN n m (Embed ('S m) v) a (Embed m v)
--     UnEmbed (l :~> u) a n      ('FA e)          = 'FA (UnEmbed u a n e)
--     -- UnEmbed a n      (Forall vs k e)   = Forall vs k (UnEmbed a ('S n) e)
--     -- UnEmbed a n      (Forall '[] k e) = TL.TypeError ('TL.Text "hey")
--     -- UnEmbed a n      (Forall (v ': vs) k e)   = Forall vs k (UnEmbed a ('S n) e)
--     -- UnEmbed Type a n      (Forall (v ': vs) k e)   = Forall vs k (UnEmbed k a ('S n) e)
--     UnEmbed Type a n      (b -> c)       = UnEmbed Type a n b -> UnEmbed Type a n c
--     UnEmbed Type a n      (Seq b)        = Seq (UnEmbed Type a n b)
--     UnEmbed Type a n      (Maybe b)      = Maybe (UnEmbed Type a n b)
--     UnEmbed Type a n      b              = b

-- data Forall :: [SomeDKind] -> DKind k -> Type -> Type where
--     Forall :: { runForall :: forall r. DType vs v r -> UnEmbed Type r 'Z a }
--            -> Forall vs v a

-- -- what about TV TZ :$ TBool ?
-- data DType :: forall k. [SomeDKind] -> DKind k -> k -> Type where
--     TV        :: VIx n vs k -> DType vs k (Embed n k)
--     Pi        :: DType ('SDK v ': vs) k a -> DType vs (v ':~> k) ('FA a)
--     (:$)      :: forall k' (k :: DKind k') vs v a b. ()
--               => DType vs (v ':~> k) ('FA a)
--               -> DType vs v b
--               -> DType vs k (UnEmbed k' b 'Z a)
--     Poly      :: DType vs (v ':~> 'KType) ('FA a)
--               -> DType vs 'KType          (Forall vs v a)
--     -- Poly      :: DType vs (v ':~> 'KType) ('FA a) -> DType vs 'KType (Forall vs v a)
--     -- (:$)      :: DType ('SDK v ': vs) k      a -> DType vs v b -> DType vs k (UnEmbed b 'Z a)
--     -- Poly      :: DType ('SDK v ': vs) 'KType a -> DType vs 'KType (Forall vs v a)
--     (:->)     :: DType vs 'KType a -> DType vs 'KType b  -> DType vs 'KType (a -> b)
--     TBool     :: DType vs 'KType Bool
--     TNatural  :: DType vs 'KType Natural
--     TInteger  :: DType vs 'KType Integer
--     TDouble   :: DType vs 'KType Double
--     TText     :: DType vs 'KType Text
--     -- TList     :: DType ('KType ':~> 'KType) Seq
--     -- TOptional :: DType ('KType ':~> 'KType) Maybe
--     TList     :: DType vs 'KType a -> DType vs 'KType (Seq a)
--     TOptional :: DType vs 'KType a -> DType vs 'KType (Maybe a)

-- deriving instance Show (DType vs k a)

-- infixr 3 :->

-- compN :: SN n -> SN m -> f a -> f b -> f c -> f (CompN n m a b c)
-- compN SZ     SZ     _ y _ = y
-- compN SZ     (SS _) _ _ z = z
-- compN (SS _) SZ     x _ _ = x
-- compN (SS n) (SS m) x y z = compN n m x y z

-- unEmbed :: DType a -> SN n -> DType t -> DType (UnEmbed a n t)
-- unEmbed x n = \case
--     TV m -> case (n, m) of
--       (SZ   , SZ   ) -> x
--       (SZ   , SS m') -> TV m'
--       (SS _ , SZ   ) -> TV SZ
--       (SS n', SS m') -> compN n' m' (TV m) x (TV m')
--     FA y        -> FA (unEmbed x (SS n) y)
--     y :-> z     -> unEmbed x n y :-> unEmbed x n z
--     TType       -> TType
--     TBool       -> TBool
--     TNatural    -> TNatural
--     TInteger    -> TInteger
--     TDouble     -> TDouble
--     TText       -> TText
--     TList y     -> TList (unEmbed x n y)
--     TOptional y -> TOptional (unEmbed x n y)

-- -- new big deal: All function types in dhall are pi types??

-- -- infixr 2 :.

-- tv :: SingI i => DType (Embed i)
-- tv = TV sing

-- tv0 :: DType (Embed 'Z)
-- tv0 = tv
-- tv1 :: DType (Embed ('S 'Z))
-- tv1 = tv
-- tv2 :: DType (Embed ('S ('S 'Z)))
-- tv2 = tv

-- data SomeDType :: Type where
--     SomeDType :: DType a -> SomeDType

-- deriving instance Show (SomeDType)

-- data DTerm :: [SomeDKind] -> Type where
--     DTerm :: DType vs 'KType a -> a -> DTerm vs

-- ident :: DTerm vs
-- ident = DTerm (Poly (TV VIZ :-> TV VIZ)) $
--           Forall $ \_ -> id

-- konst :: DTerm '[]
-- konst = DTerm (Poly $ Pi $ Poly $ Pi $ TV (VIS VIZ) :-> TV VIZ :-> TV (VIS VIZ)) $
--     Forall $ \_ -> Forall $ \_ -> _

--       -- Forall $ \_ -> Forall _
-- -- -- -- (FA $ FA $ TV (SS SZ) :-> TV SZ :-> TV (SS SZ)) $
-- -- --           -- Forall $ \_ -> Forall $ \_ -> const

-- natBuild :: DTerm
-- natBuild = DTerm ((FA ((tv0 :-> tv0) :-> tv0 :-> tv0)) :-> TNatural) $ \f ->
--     runForall f TNatural (+1) 0

-- noEmbed :: p a -> DType r -> UnEmbed a 'Z r -> r
-- noEmbed t0 = \case
--     TV SZ       -> error "Internal error: Cannot be unembedded."  -- todo: fix
--     TV (SS _)   -> reEmbed
--     FA _        -> error "Unimplemented."
--     t :-> u     -> dimap (liftEmbed t0 t) (noEmbed t0 u)
--     TType       -> id
--     TBool       -> id
--     TNatural    -> id
--     TInteger    -> id
--     TDouble     -> id
--     TText       -> id
--     TList t     -> fmap (noEmbed t0 t)
--     TOptional t -> fmap (noEmbed t0 t)

-- liftEmbed :: p a -> DType r -> r -> UnEmbed a 'Z r
-- liftEmbed t0 = \case
--     TV _        -> reEmbed
--     FA _        -> error "Unimplemented."
--     t :-> u     -> dimap (noEmbed t0 t) (liftEmbed t0 u)
--     TType       -> id
--     TBool       -> id
--     TNatural    -> id
--     TInteger    -> id
--     TDouble     -> id
--     TText       -> id
--     TList t     -> fmap (liftEmbed t0 t)
--     TOptional t -> fmap (liftEmbed t0 t)

-- foo :: Forall (Forall ((Embed ('S 'Z) -> Embed 'Z) -> Embed 'Z -> Embed 'Z) -> Maybe (Embed 'Z))
-- foo = Forall $ \case
--     t -> \f -> runForall f (TOptional t) (Just . noEmbed (TOptional t) t) Nothing

-- optBuild :: DTerm
-- optBuild = DTerm (FA (FA ((tv1 :-> tv0) :-> tv0 :-> tv0) :-> TOptional tv0)) $
--     Forall $ \t f -> runForall f (TOptional t) (Just . noEmbed (TOptional t) t) Nothing

-- (~#)
--     :: DType a
--     -> DType b
--     -> Maybe (a :~: b)
-- (~#) = \case
--   TV s -> \case
--     TV t
--       | Proved Refl <- s %~ t
--       -> Just Refl
--     _ -> Nothing
--   FA a -> \case
--     FA b
--       | Just Refl <- a ~# b
--       -> Just Refl
--     _ -> Nothing
--   a :-> b -> \case
--     c :-> d
--       | Just Refl <- a ~# c
--       , Just Refl <- b ~# d -> Just Refl
--     _ -> Nothing
--   TType -> \case
--     TType -> Just Refl
--     _     -> Nothing
--   TBool -> \case
--     TBool -> Just Refl
--     _     -> Nothing
--   TNatural -> \case
--     TNatural -> Just Refl
--     _        -> Nothing
--   TInteger -> \case
--     TInteger -> Just Refl
--     _        -> Nothing
--   TDouble -> \case
--     TDouble -> Just Refl
--     _       -> Nothing
--   TText -> \case
--     TText -> Just Refl
--     _     -> Nothing
--   TList a -> \case
--     TList b
--       | Just Refl <- a ~# b -> Just Refl
--     _       -> Nothing
--   TOptional a -> \case
--     TOptional b
--       | Just Refl <- a ~# b -> Just Refl
--     _       -> Nothing

-- dhallType
--     :: forall s. Show s
--     => D.Context DTerm
--     -> D.Expr s D.X
--     -> Maybe SomeDType
-- dhallType ctx = either (const Nothing) (fromDhall ctx TType)
--               . D.typeWith ctxTypes
--   where
--     ctxTypes :: D.Context (D.Expr s D.X)
--     ctxTypes = flip fmap ctx $ \(DTerm t _) -> toDhallType t

-- fromSomeDhall
--     :: forall s. Show s
--     => D.Context DTerm
--     -> D.Expr s D.X
--     -> Maybe DTerm
-- fromSomeDhall ctx x = do
--     SomeDType t <- dhallType ctx x
--     y           <- fromDhall ctx t x
--     pure $ DTerm t y

-- fromDhall
--     :: forall a s. Show s
--     => D.Context DTerm
--     -> DType 'KType a
--     -> D.Expr s D.X
--     -> Maybe a
-- fromDhall ctx a = \case
--     -- D.Const D.Type
--     --   | TType <- a -> Just (SomeDType TType)  -- should expect TKind
--     -- D.Var (D.V v i) -> do
--     --   DTerm b x <- D.lookup v i ctx
--     --   Refl      <- a ~# b
--     --   pure x
--     -- D.Lam v t y -> do
--     --   b :-> c     <- Just a
--     --   SomeDType d <- fromDhall ctx TType t
--     --   Refl        <- b ~# d
--     --   yType       <- either (const Nothing) Just $
--     --                     D.typeWith (D.insert v t ctxTypes) y
--     --   SomeDType e <- fromDhall ctx TType yType
--     --   Refl        <- c ~# e
--     --   pure $ \x -> fromMaybe (errorWithoutStackTrace "fromDhall: typecheck failure") $
--     --     fromDhall (D.insert v (DTerm b x) ctx) c y
--     -- D.Pi l t x | TType <- a -> do
--     --   -- TODO: what happens if t is Type -> Type, or Sort?
--     --   SomeDType u <- fromDhall ctx TType t
--     --   case u of
--     --     TType -> fromDhall (D.insert l (DTerm TType (SomeDType (TV SZ))) ctx)
--     --                   TType x <&> \(SomeDType q) -> SomeDType (FA q)
--     --     _     -> do
--     --       SomeDType v <- fromDhall ctx TType x
--     --       pure $ SomeDType (u :-> v)
--     -- D.App f x -> traceShow (D.toList ctxTypes) . traceShow f . traceShow x $ do
--     --   DTerm t x' <- fromSomeDhall ctx x
--     --   case t of
--     --   --   TType -> do
--     --   --     SomeDType y <- Just x'
--     --   --     Just $ _ y
--     --       -- Forall g    <- fromDhll ctx TType f
--     --       -- SomeDType (FA e) <- dhallType ctx TType f
--     --       -- _ e y
--     --       -- _ $ f y
--     --       -- -- DTerm
--     --       -- SomeDType (FA e) <- dhallType ctx f
--     --       -- Forall g         <- fromDhall ctx (FA e) f
--     --       -- Just $ g y
--     --     _     -> ($ x') <$> fromDhall ctx (t :-> a) f
--     -- D.Let xs x -> fromLet ctx a (toList xs) x
--     -- D.Annot x t -> (<|> fromDhall ctx a x) $ do
--     --    SomeDType b <- fromDhall ctx TType t     -- we don't need to check, but why not?
--     --    Refl        <- a ~# b
--     --    fromDhall ctx b x
--     -- D.Bool        | TType <- a -> Just (SomeDType TBool)
--     D.BoolLit b   | TBool <- a -> Just b
--     D.BoolAnd x y | TBool <- a ->
--       (&&) <$> fromDhall ctx TBool x <*> fromDhall ctx TBool y
--     D.BoolOr  x y | TBool <- a ->
--       (||) <$> fromDhall ctx TBool x <*> fromDhall ctx TBool y
--     D.BoolEQ  x y | TBool <- a ->
--       (==) <$> fromDhall ctx TBool x <*> fromDhall ctx TBool y
--     D.BoolNE  x y | TBool <- a ->
--       (/=) <$> fromDhall ctx TBool x <*> fromDhall ctx TBool y
--     D.BoolIf  b x y -> do
--       b'    <- fromDhall ctx TBool b
--       case b' of
--         True  -> fromDhall ctx a x
--         False -> fromDhall ctx a y
--     -- D.Natural      | TType    <- a -> Just (SomeDType TNatural)
--     D.NaturalLit n | TNatural <- a -> Just n
--     -- D.NaturalFold
--     --   | TNatural :-> FA ((TV SZ :-> TV SZ) :-> TV SZ :-> TV SZ) <- a
--     --   -> Just $ \n -> Forall $ \_ f x -> foldNatural n f x
--     -- D.NaturalBuild
--     --   | FA ((TV SZ :-> TV SZ) :-> TV SZ :-> TV SZ) :-> TNatural <- a
--     --   -> Just $ \(Forall f) -> f TNatural (+1) 0
--     D.NaturalIsZero    | TNatural :-> TBool    <- a -> Just (== 0)
--     D.NaturalEven      | TNatural :-> TBool    <- a -> Just even
--     D.NaturalOdd       | TNatural :-> TBool    <- a -> Just odd
--     D.NaturalToInteger | TNatural :-> TInteger <- a -> Just fromIntegral
--     D.NaturalShow      | TNatural :-> TText    <- a -> Just (T.pack . show)
--     D.NaturalPlus x y  | TNatural              <- a ->
--       (+) <$> fromDhall ctx TNatural x <*> fromDhall ctx TNatural y
--     D.NaturalTimes x y | TNatural              <- a ->
--       (*) <$> fromDhall ctx TNatural x <*> fromDhall ctx TNatural y
--     -- D.Integer         | TType                <- a -> Just (SomeDType TInteger)
--     D.IntegerLit n    | TInteger             <- a -> Just n
--     D.IntegerShow     | TInteger :-> TText   <- a -> Just (T.pack . printf "%+d")
--     D.IntegerToDouble | TInteger :-> TDouble <- a -> Just fromIntegral
--     -- D.Double          | TType                <- a -> Just (SomeDType TDouble)
--     D.DoubleLit n     | TDouble              <- a -> Just n
--     D.DoubleShow      | TDouble  :-> TText   <- a -> Just (T.pack . show)
--     -- D.Text            | TType                <- a -> Just (SomeDType TText)
--     D.TextLit (D.Chunks xs x) -> do
--       TText <- Just a
--       xs' <- for xs $ \(t, y) -> (t <>) <$> fromDhall ctx TText y
--       pure $ fold xs' <> x
--     D.TextAppend x y | TText    <- a ->
--       (<>) <$> fromDhall ctx TText x <*> fromDhall ctx TText y
--     -- D.List           | FA TType <- a -> Just $ Forall (SomeDType . TList)
--     D.ListLit _ xs   | TList b  <- a -> traverse (fromDhall ctx b) xs
--     D.ListAppend x y | TList _  <- a ->
--       (<>) <$> fromDhall ctx a x <*> fromDhall ctx a y
--     -- D.ListBuild
--     --   | FA (FA ((TV (SS SZ) :-> TV SZ :-> TV SZ) :-> TV SZ :-> TV SZ) :-> TList (TV SZ)) <- a
--     --   -> Just $ Forall $ \t f ->
--     --       runForall f (TList t) ((Seq.<|) . noEmbed (TList t) t) Seq.empty
--     -- D.ListFold
--     --   | FA (TList (TV SZ) :-> FA ((TV (SS SZ) :-> TV SZ :-> TV SZ) :-> TV SZ :-> TV SZ)) <- a
--     --   -> Just $ Forall $ \t xs -> Forall $ \u cons nil ->
--     --        foldr (cons . liftEmbed u t) nil xs
--     -- D.ListLength
--     --   | FA (TList (TV SZ) :-> TNatural) <- a
--     --   -> Just $ Forall $ \_ -> fromIntegral . length
--     -- D.ListHead
--     --   | FA (TList (TV SZ) :-> TOptional (TV SZ)) <- a
--     --   -> Just $ Forall $ \_ -> \case Empty -> Nothing; x :<| _ -> Just x
--     -- D.ListLast
--     --   | FA (TList (TV SZ) :-> TOptional (TV SZ)) <- a
--     --   -> Just $ Forall $ \_ -> \case Empty -> Nothing; _ :|> x -> Just x
--     -- D.ListReverse
--     --   | FA (TList (TV SZ) :-> TList (TV SZ)) <- a
--     --   -> Just $ Forall $ \_ -> Seq.reverse
-- --     -- | > ListIndexed                              ~  List/indexed
-- --     | ListIndexed
--     -- D.Optional         | FA TType    <- a -> Just $ Forall (SomeDType . TOptional)
--     D.OptionalLit _ xs | TOptional b <- a -> traverse (fromDhall ctx b) xs
--     D.Some x           | TOptional b <- a -> Just <$> fromDhall ctx b x
--     -- D.None
--     --   | FA (TOptional (TV SZ)) <- a
--     --   -> Just $ Forall $ \_ -> Nothing
--     -- D.OptionalFold
--     --   | FA (TOptional (TV SZ) :-> FA ((TV (SS SZ) :-> TV SZ) :-> TV SZ :-> TV SZ)) <- a
--     --   -> Just $ Forall $ \t m -> Forall $ \u j n ->
--     --        maybe n (j . liftEmbed u t) m
--     -- D.OptionalBuild
--     --   | FA (FA ((TV (SS SZ) :-> TV SZ) :-> TV SZ :-> TV SZ) :-> TOptional (TV SZ)) <- a
--     --   -> Just $ Forall $ \t f ->
--     --       runForall f (TOptional t) (Just . noEmbed (TOptional t) t) Nothing
-- --     -- | > Record       [(k1, t1), (k2, t2)]        ~  { k1 : t1, k2 : t1 }
-- --     | Record    (Map Text (Expr s a))
-- --     -- | > RecordLit    [(k1, v1), (k2, v2)]        ~  { k1 = v1, k2 = v2 }
-- --     | RecordLit (Map Text (Expr s a))
-- --     -- | > Union        [(k1, t1), (k2, t2)]        ~  < k1 : t1 | k2 : t2 >
-- --     | Union     (Map Text (Expr s a))
-- --     -- | > UnionLit k v [(k1, t1), (k2, t2)]        ~  < k = v | k1 : t1 | k2 : t2 >
-- --     | UnionLit Text (Expr s a) (Map Text (Expr s a))
-- --     -- | > Combine x y                              ~  x ∧ y
-- --     | Combine (Expr s a) (Expr s a)
-- --     -- | > CombineTypes x y                         ~  x ⩓ y
-- --     | CombineTypes (Expr s a) (Expr s a)
-- --     -- | > Prefer x y                               ~  x ⫽ y
-- --     | Prefer (Expr s a) (Expr s a)
-- --     -- | > Merge x y (Just t )                      ~  merge x y : t
-- --     --   > Merge x y  Nothing                       ~  merge x y
-- --     | Merge (Expr s a) (Expr s a) (Maybe (Expr s a))
--     D.Constructors t -> fromDhall ctx a t
-- --     -- | > Field e x                                ~  e.x
-- --     | Field (Expr s a) Text
-- --     -- | > Project e xs                             ~  e.{ xs }
-- --     | Project (Expr s a) (Set Text)
--     D.Note      _ x -> fromDhall ctx a x
--     D.ImportAlt x _ -> fromDhall ctx a x    -- should we check lhs too?
--     _               -> Nothing
--   -- where
--   --   ctxTypes :: D.Context (D.Expr s D.X)
--   --   ctxTypes = flip fmap ctx $ \(DTerm t _) -> toDhallType t

-- fromLet
--     :: Show s
--     => D.Context DTerm
--     -> DType a
--     -> [D.Binding s D.X]
--     -> D.Expr s D.X
--     -> Maybe a
-- fromLet ctx a []                     x = fromDhall ctx a x
-- fromLet ctx a (D.Binding v t y : bs) x = do
--     SomeDType t' <- (fromDhall ctx TType =<< t) <|> dhallType ctx y
--     y'           <- fromDhall ctx t' y
--     fromLet (D.insert v (DTerm t' y') ctx) a bs x

-- toDhallType
--     :: DType a
--     -> D.Expr s D.X
-- toDhallType = toDhallType_ 0

-- toDhallType_
--     :: Integer
--     -> DType a
--     -> D.Expr s D.X
-- toDhallType_ n = \case
--     TV i        -> D.Var (D.V "_" (fromIntegral (toNatural (fromSing i)) + n))
--     FA t        -> D.Pi "_" (D.Const D.Type  ) (toDhallType_ n t)
--     a :-> b     -> D.Pi "_" (toDhallType_ n a) (toDhallType_ (n + 1) b)   -- add 1 to b
--     TType       -> D.Const D.Type
--     TBool       -> D.Bool
--     TNatural    -> D.Natural
--     TInteger    -> D.Integer
--     TDouble     -> D.Double
--     TText       -> D.Text
--     TList t     -> D.List `D.App` toDhallType t
--     TOptional t -> D.Optional `D.App` toDhallType t

-- -- toDhall
-- --     :: DType a
-- --     -> a
-- --     -> D.Expr () D.X
-- -- toDhall = \case
-- --     TV _        -> reEmbed
-- --     FA _        -> undefined
-- --     _ :-> _     -> undefined        -- this is a problem.
-- --     TType       -> \(SomeDType t) -> toDhallType t
-- --     TBool       -> D.BoolLit
-- --     TNatural    -> D.NaturalLit
-- --     TInteger    -> D.IntegerLit
-- --     TDouble     -> D.DoubleLit
-- --     TText       -> D.TextLit . D.Chunks []
-- --     TList t     -> D.ListLit (Just (toDhallType t)) . fmap (toDhall t)
-- --     TOptional t -> maybe (D.None `D.App` toDhallType t) (D.Some . toDhall t)

-- foldNatural
--     :: Natural
--     -> (a -> a)
--     -> a
--     -> a
-- foldNatural n f = go n
--   where
--     go !i !x
--       | i <= 0    = x
--       | otherwise = let !y = f x in go (i - 1) y

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

