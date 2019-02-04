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
import           Data.List
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

-- todo: allow for polykindedness
data Embed :: N -> Type

reEmbed :: Embed a -> b
reEmbed = \case {}

type family CompN n m a b c where
    CompN 'Z     'Z     a b c = b
    CompN 'Z     ('S m) a b c = c
    CompN ('S n) 'Z     a b c = a
    CompN ('S n) ('S m) a b c = CompN n m a b c

type family UnEmbed a n t where
    UnEmbed a 'Z     (Embed 'Z)     = a
    UnEmbed a 'Z     (Embed ('S m)) = Embed m
    UnEmbed a ('S n) (Embed 'Z)     = Embed 'Z
    UnEmbed a ('S n) (Embed ('S m)) = CompN n m (Embed ('S m)) a (Embed m)
    UnEmbed a n      (Forall e)     = Forall (UnEmbed a ('S n) e)
    UnEmbed a n      (b -> c)       = UnEmbed a n b -> UnEmbed a n c
    UnEmbed a n      (Seq b)        = Seq (UnEmbed a n b)
    UnEmbed a n      (Maybe b)      = Maybe (UnEmbed a n b)
    UnEmbed a n      b              = b
    -- UnEmbed a n      (f b c)        = f (UnEmbed a n b) (UnEmbed a n c)
    -- UnEmbed a n      (f b)          = f (UnEmbed a n b)

data Forall e = Forall { runForall :: forall r. DType r -> UnEmbed r 'Z e }

data DType :: Type -> Type where
    TV        :: SN n -> DType (Embed n)
    FA        :: DType e -> DType (Forall e)
    (:->)     :: DType a -> DType b -> DType (a -> b)     -- can we restrict a to not be SomeDType ?
    TType     :: DType SomeDType  -- todo: kind?
    TBool     :: DType Bool
    TNatural  :: DType Natural
    TInteger  :: DType Integer
    TDouble   :: DType Double
    TText     :: DType Text
    TList     :: DType a -> DType (Seq a)
    TOptional :: DType a -> DType (Maybe a)

compN :: SN n -> SN m -> f a -> f b -> f c -> f (CompN n m a b c)
compN SZ     SZ     _ y _ = y
compN SZ     (SS _) _ _ z = z
compN (SS _) SZ     x _ _ = x
compN (SS n) (SS m) x y z = compN n m x y z

unEmbed :: DType a -> SN n -> DType t -> DType (UnEmbed a n t)
unEmbed x n = \case
    TV m -> case (n, m) of
      (SZ   , SZ   ) -> x
      (SZ   , SS m') -> TV m'
      (SS _ , SZ   ) -> TV SZ
      (SS n', SS m') -> compN n' m' (TV m) x (TV m')
    FA y        -> FA (unEmbed x (SS n) y)
    y :-> z     -> unEmbed x n y :-> unEmbed x n z
    TType       -> TType
    TBool       -> TBool
    TNatural    -> TNatural
    TInteger    -> TInteger
    TDouble     -> TDouble
    TText       -> TText
    TList y     -> TList (unEmbed x n y)
    TOptional y -> TOptional (unEmbed x n y)

-- new big deal: All function types in dhall are pi types??

infixr 3 :->
-- infixr 2 :.

tv :: SingI i => DType (Embed i)
tv = TV sing

tv0 :: DType (Embed 'Z)
tv0 = tv
tv1 :: DType (Embed ('S 'Z))
tv1 = tv
tv2 :: DType (Embed ('S ('S 'Z)))
tv2 = tv

data SomeDType :: Type where
    SomeDType :: DType a -> SomeDType

data DTerm :: Type where
    DTerm :: DType a -> a -> DTerm

ident :: DTerm
ident = DTerm (FA (tv0 :-> tv0)) $
          Forall (\_ -> id)

konst :: DTerm
konst = DTerm (FA $ FA $ tv1 :-> tv0 :-> tv1) $
          Forall $ \_ -> Forall $ \_ -> const

natBuild :: DTerm
natBuild = DTerm ((FA ((tv0 :-> tv0) :-> tv0 :-> tv0)) :-> TNatural) $ \f ->
    runForall f TNatural (+1) 0

noEmbed :: p a -> DType r -> UnEmbed a 'Z r -> r
noEmbed t0 = \case
    TV SZ       -> error "Internal error: Cannot be unembedded."  -- todo: fix
    TV (SS _)   -> reEmbed
    FA _        -> error "Unimplemented."
    t :-> u     -> dimap (liftEmbed t0 t) (noEmbed t0 u)
    TType       -> id
    TBool       -> id
    TNatural    -> id
    TInteger    -> id
    TDouble     -> id
    TText       -> id
    TList t     -> fmap (noEmbed t0 t)
    TOptional t -> fmap (noEmbed t0 t)

liftEmbed :: p a -> DType r -> r -> UnEmbed a 'Z r
liftEmbed t0 = \case
    TV _        -> reEmbed
    FA _        -> error "Unimplemented."
    t :-> u     -> dimap (noEmbed t0 t) (liftEmbed t0 u)
    TType       -> id
    TBool       -> id
    TNatural    -> id
    TInteger    -> id
    TDouble     -> id
    TText       -> id
    TList t     -> fmap (liftEmbed t0 t)
    TOptional t -> fmap (liftEmbed t0 t)

foo :: Forall (Forall ((Embed ('S 'Z) -> Embed 'Z) -> Embed 'Z -> Embed 'Z) -> Maybe (Embed 'Z))
foo = Forall $ \case
    t -> \f -> runForall f (TOptional t) (Just . noEmbed (TOptional t) t) Nothing

optBuild :: DTerm
optBuild = DTerm (FA (FA ((tv1 :-> tv0) :-> tv0 :-> tv0) :-> TOptional tv0)) $
    Forall $ \t f -> runForall f (TOptional t) (Just . noEmbed (TOptional t) t) Nothing

(~#)
    :: DType a
    -> DType b
    -> Maybe (a :~: b)
(~#) = \case
  TV s -> \case
    TV t
      | Proved Refl <- s %~ t
      -> Just Refl
    _ -> Nothing
  FA a -> \case
    FA b
      | Just Refl <- a ~# b
      -> Just Refl
    _ -> Nothing
  a :-> b -> \case
    c :-> d
      | Just Refl <- a ~# c
      , Just Refl <- b ~# d -> Just Refl
    _ -> Nothing
  TType -> \case
    TType -> Just Refl
    _     -> Nothing
  TBool -> \case
    TBool -> Just Refl
    _     -> Nothing
  TNatural -> \case
    TNatural -> Just Refl
    _        -> Nothing
  TInteger -> \case
    TInteger -> Just Refl
    _        -> Nothing
  TDouble -> \case
    TDouble -> Just Refl
    _       -> Nothing
  TText -> \case
    TText -> Just Refl
    _     -> Nothing
  TList a -> \case
    TList b
      | Just Refl <- a ~# b -> Just Refl
    _       -> Nothing
  TOptional a -> \case
    TOptional b
      | Just Refl <- a ~# b -> Just Refl
    _       -> Nothing

fromDhall
    :: forall a s. ()
    => D.Context DTerm
    -> DType a
    -> D.Expr s D.X
    -> Maybe a
fromDhall ctx a = \case
    D.Const _ -> Nothing
    D.Var (D.V v i) -> do
      DTerm b x <- D.lookup v i ctx
      Refl      <- a ~# b
      pure x
    D.Lam v t y -> do
      b :-> c     <- Just a
      SomeDType d <- fromDhall ctx TType t
      Refl        <- b ~# d
      yType       <- either (const Nothing) Just $
                        D.typeWith (D.insert v t ctx') y
      SomeDType e <- fromDhall ctx TType yType
      Refl        <- c ~# e
      pure $ \x -> fromMaybe (errorWithoutStackTrace "fromDhall: typecheck failure") $
        fromDhall (D.insert v (DTerm b x) ctx) c y
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
    D.Bool        | TType <- a -> Just (SomeDType TBool)
    D.BoolLit b   | TBool <- a -> Just b
    D.BoolAnd x y | TBool <- a ->
      (&&) <$> fromDhall ctx TBool x <*> fromDhall ctx TBool y
    D.BoolOr  x y | TBool <- a ->
      (||) <$> fromDhall ctx TBool x <*> fromDhall ctx TBool y
    D.BoolEQ  x y | TBool <- a ->
      (==) <$> fromDhall ctx TBool x <*> fromDhall ctx TBool y
    D.BoolNE  x y | TBool <- a ->
      (/=) <$> fromDhall ctx TBool x <*> fromDhall ctx TBool y
    D.BoolIf  b x y -> do
      b'    <- fromDhall ctx TBool b
      case b' of
        True  -> fromDhall ctx a x
        False -> fromDhall ctx a y
    D.Natural      | TType    <- a -> Just (SomeDType TNatural)
    D.NaturalLit n | TNatural <- a -> Just n
    D.NaturalFold
      | TNatural :-> FA ((TV SZ :-> TV SZ) :-> TV SZ :-> TV SZ) <- a
      -> Just $ \n -> Forall $ \_ f x -> foldNatural n f x
    D.NaturalBuild
      | FA ((TV SZ :-> TV SZ) :-> TV SZ :-> TV SZ) :-> TNatural <- a
      -> Just $ \(Forall f) -> f TNatural (+1) 0
    D.NaturalIsZero    | TNatural :-> TBool    <- a -> Just (== 0)
    D.NaturalEven      | TNatural :-> TBool    <- a -> Just even
    D.NaturalOdd       | TNatural :-> TBool    <- a -> Just odd
    D.NaturalToInteger | TNatural :-> TInteger <- a -> Just fromIntegral
    D.NaturalShow      | TNatural :-> TText    <- a -> Just (T.pack . show)
    D.NaturalPlus x y  | TNatural              <- a ->
      (+) <$> fromDhall ctx TNatural x <*> fromDhall ctx TNatural y
    D.NaturalTimes x y | TNatural              <- a ->
      (*) <$> fromDhall ctx TNatural x <*> fromDhall ctx TNatural y
    D.Integer         | TType                <- a -> Just (SomeDType TInteger)
    D.IntegerLit n    | TInteger             <- a -> Just n
    D.IntegerShow     | TInteger :-> TText   <- a -> Just (T.pack . printf "%+d")
    D.IntegerToDouble | TInteger :-> TDouble <- a -> Just fromIntegral
    D.Double          | TType                <- a -> Just (SomeDType TDouble)
    D.DoubleLit n     | TDouble              <- a -> Just n
    D.DoubleShow      | TDouble  :-> TText   <- a -> Just (T.pack . show)
    D.Text            | TType                <- a -> Just (SomeDType TText)
    D.TextLit (D.Chunks xs x) -> do
      TText <- Just a
      xs' <- for xs $ \(t, y) -> (t <>) <$> fromDhall ctx TText y
      pure $ fold xs' <> x
    D.TextAppend x y | TText    <- a ->
      (<>) <$> fromDhall ctx TText x <*> fromDhall ctx TText y
    D.List           | FA TType <- a -> Just $ Forall (SomeDType . TList)
    D.ListLit _ xs   | TList b  <- a -> traverse (fromDhall ctx b) xs
    D.ListAppend x y | TList _  <- a ->
      (<>) <$> fromDhall ctx a x <*> fromDhall ctx a y
    D.ListBuild
      | FA (FA ((TV (SS SZ) :-> TV SZ :-> TV SZ) :-> TV SZ :-> TV SZ) :-> TList (TV SZ)) <- a
      -> Just $ Forall $ \t f ->
          runForall f (TList t) ((Seq.<|) . noEmbed (TList t) t) Seq.empty
    D.ListFold
      | FA (TList (TV SZ) :-> FA ((TV (SS SZ) :-> TV SZ :-> TV SZ) :-> TV SZ :-> TV SZ)) <- a
      -> Just $ Forall $ \t xs -> Forall $ \u cons nil ->
           foldr (cons . liftEmbed u t) nil xs
    D.ListLength
      | FA (TList (TV SZ) :-> TNatural) <- a
      -> Just $ Forall $ \_ -> fromIntegral . length
    D.ListHead
      | FA (TList (TV SZ) :-> TOptional (TV SZ)) <- a
      -> Just $ Forall $ \_ -> \case Empty -> Nothing; x :<| _ -> Just x
    D.ListLast
      | FA (TList (TV SZ) :-> TOptional (TV SZ)) <- a
      -> Just $ Forall $ \_ -> \case Empty -> Nothing; _ :|> x -> Just x
    D.ListReverse
      | FA (TList (TV SZ) :-> TList (TV SZ)) <- a
      -> Just $ Forall $ \_ -> Seq.reverse
--     -- | > ListIndexed                              ~  List/indexed
--     | ListIndexed
    D.Optional         | FA TType    <- a -> Just $ Forall (SomeDType . TOptional)
    D.OptionalLit _ xs | TOptional b <- a -> traverse (fromDhall ctx b) xs
    D.Some x | TOptional b <- a -> Just <$> fromDhall ctx b x
    D.None
      | FA (TOptional (TV SZ)) <- a
      -> Just $ Forall $ \_ -> Nothing
    D.OptionalFold
      | FA (TOptional (TV SZ) :-> FA ((TV (SS SZ) :-> TV SZ) :-> TV SZ :-> TV SZ)) <- a
      -> Just $ Forall $ \t m -> Forall $ \u j n ->
           maybe n (j . liftEmbed u t) m
    D.OptionalBuild
      | FA (FA ((TV (SS SZ) :-> TV SZ) :-> TV SZ :-> TV SZ) :-> TOptional (TV SZ)) <- a
      -> Just $ Forall $ \t f ->
          runForall f (TOptional t) (Just . noEmbed (TOptional t) t) Nothing
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
    D.Constructors t -> fromDhall ctx a t
--     -- | > Field e x                                ~  e.x
--     | Field (Expr s a) Text
--     -- | > Project e xs                             ~  e.{ xs }
--     | Project (Expr s a) (Set Text)
    D.Note _ x -> fromDhall ctx a x
--     -- | > ImportAlt                                ~  e1 ? e2
--     | ImportAlt (Expr s a) (Expr s a)
    _ -> Nothing
  where
    ctx' :: D.Context (D.Expr s D.X)
    ctx' = fmap undefined ctx

toDhallType
    :: DType a
    -> D.Expr () D.X
toDhallType = \case
    TV n        -> D.Var (D.V "_" (fromIntegral (toNatural (fromSing n))))
    FA t        -> D.Pi "_" (D.Const D.Type) (toDhallType t)
    a :-> b     -> D.Pi "_" (toDhallType a) (toDhallType b)
    TType       -> D.Const D.Type
    TBool       -> D.Bool
    TNatural    -> D.Natural
    TInteger    -> D.Integer
    TDouble     -> D.Double
    TText       -> D.Text
    TList t     -> D.List `D.App` toDhallType t
    TOptional t -> D.Optional `D.App` toDhallType t

toDhall
    :: DType a
    -> a
    -> D.Expr () D.X
toDhall = \case
    TV _        -> reEmbed
    FA _        -> undefined
    _ :-> _     -> undefined        -- this is a problem.
    TType       -> \(SomeDType t) -> toDhallType t
    TBool       -> D.BoolLit
    TNatural    -> D.NaturalLit
    TInteger    -> D.IntegerLit
    TDouble     -> D.DoubleLit
    TText       -> D.TextLit . D.Chunks []
    TList t     -> D.ListLit (Just (toDhallType t)) . fmap (toDhall t)
    TOptional t -> maybe (D.None `D.App` toDhallType t) (D.Some . toDhall t)


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

foldNatural
    :: Natural
    -> (a -> a)
    -> a
    -> a
foldNatural n f = go n
  where
    go !i !x
      | i <= 0    = x
      | otherwise = let !y = f x in go (i - 1) y
