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
import           Dhall.Typed.Index
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

type family MaybeVar (x :: DType vs a) (i :: Maybe (Index vs a)) :: DType vs a where
    MaybeVar x 'Nothing  = x
    MaybeVar x ('Just i) = 'TVar i
    MaybeVar x i = TL.TypeError ('TL.Text "No Maybe: " 'TL.:<>: 'TL.ShowType '(x, i))

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

type family Sub as bs a b c (d :: Delete as bs a) (x :: DType bs c) (r :: DType as b) :: DType bs b where
    Sub as bs a b                  b d x ('TVar i)
        = MaybeVar x (Del as bs a b d i)
    Sub as bs a b                  c d x ('Pi (u :: SDKind k) e)
        -- = 'Pi u (Sub (k ': as) (k ': bs) a b c ('DS d) (AddVar k bs c x) e)
        = 'Pi u (Sub (k ': as) (k ': bs) a b c ('DS d) (Shift bs (k ': bs) k c 'InsZ x) e)
    Sub as bs a b                  c d x ((i :: DType as (k ':~> b)) ':$ (j :: DType as k))
        = Sub as bs a (k ':~> b) c d x i ':$ Sub as bs a k c d x j
    Sub as bs a 'Type              c d x (i ':-> j)
        = Sub as bs a 'Type c d x i ':-> Sub as bs a 'Type c d x j
    Sub as bs a 'Type              c d x 'Bool
        = 'Bool
    Sub as bs a 'Type              c d x 'Natural
        = 'Natural
    Sub as bs a ('Type ':~> 'Type) c d x 'List
        = 'List
    Sub as bs a ('Type ':~> 'Type) c d x 'Optional
        = 'Optional
    Sub as bs a b c d x r
        = TL.TypeError ('TL.Text "No Sub: " 'TL.:<>: 'TL.ShowType '(as, bs, a, b, c, d, x, r))

data instance Sing (i :: Index as a) where
    SIZ :: Sing 'IZ
    SIS :: Sing i -> Sing ('IS i)

data SDType us k :: DType us k -> Type where
    STVar     :: Sing (i :: Index us a) -> SDType us a ('TVar i)
    SPi       :: SDKind a -> SDType (a ': us) b x -> SDType us b ('Pi (u :: SDKind a) x)    -- ???
    (:%$)     :: SDType us (a ':~> b) f -> SDType us a x -> SDType us b (f ':$ x)
    (:%->)    :: SDType us 'Type x -> SDType us 'Type y -> SDType us 'Type (x ':-> y)
    SBool     :: SDType us 'Type 'Bool
    SNatural  :: SDType us 'Type 'Natural
    SList     :: SDType us ('Type ':~> 'Type) 'List
    SOptional :: SDType us ('Type ':~> 'Type) 'Optional

infixr 0 :%->
infixl 9 :%$

-- sAddVar
--     :: SDKind c
--     -> Prod SDKind as
--     -> SDKind b
--     -> SDType as b x
--     -> SDType (c ': as) b (AddVar c as b x)
-- sAddVar c as b = \case
--     STVar i   -> STVar (SIS i)
--     -- SPi (u :: SDKind q) a   -> SPi u _
--     -- i :%$ j   -> sAddVar a :%$ sAddVar b
--     i :%-> j  -> sAddVar c as SType i :%-> sAddVar c as SType j
--     SBool     -> SBool
--     SNatural  -> SNatural
--     SList     -> SList
--     SOptional -> SOptional

-- type family AddVar c as b (x :: DType as b) :: DType (c ': as) b where
--     AddVar c as b ('TVar i) = 'TVar ('IS i)
--     AddVar c as b ('Pi u a) = 'Pi u (AddVar c (c ': as) b a)         -- ???
--     AddVar c as r ((a :: DType as (k ':~> r)) ':$ (b :: DType as k))
--         = AddVar c as (k ':~> r) a ':$ AddVar c as k b
--     AddVar c as 'Type (a ':-> b) = AddVar c as 'Type a ':-> AddVar c as 'Type b
--     AddVar c as 'Type 'Bool = 'Bool
--     AddVar c as 'Type 'Natural = 'Natural
--     AddVar c as ('Type ':~> 'Type) 'List = 'List
--     AddVar c as ('Type ':~> 'Type) 'Optional = 'Optional
--     AddVar c as b x = TL.TypeError ('TL.Text "No AddVar: " 'TL.:<>: 'TL.ShowType '(c, as, b, x))



    -- AddVar ('TVar i) = 'TVar ('IS i)
    -- AddVar ('Pi u a) = 'Pi u (AddVar a)         -- ???
    -- AddVar (a ':$ b)  = AddVar a ':$ AddVar b
    -- AddVar (a ':-> b) = AddVar a ':-> AddVar b
    -- AddVar 'Bool = 'Bool
    -- AddVar 'Natural = 'Natural
    -- AddVar 'List = 'List
    -- AddVar 'Optional = 'Optional
    -- AddVar x = TL.TypeError ('TL.Text "No AddVar: " 'TL.:<>: 'TL.ShowType x)


data DTerm :: [DType '[] 'Type] -> DType '[] 'Type -> Type where
    Var           :: Index vs a
                  -> DTerm vs a
    Lam           :: SDType '[] 'Type a
                  -> DTerm (a ': vs) b
                  -> DTerm vs (a ':-> b)
    App           :: DTerm vs (a ':-> b)
                  -> DTerm vs a
                  -> DTerm vs b
    TLam          :: SDType '[k] 'Type b
                  -> (forall a. SDType '[] k a -> DTerm vs (Sub '[k] '[] k 'Type k 'DZ a b))
                  -> DTerm vs ('Pi (u :: SDKind k) b)
    TApp          :: DTerm vs ('Pi (u :: SDKind k) b)
                  -> SDType '[] k a
                  -> DTerm vs (Sub '[k] '[] k 'Type k 'DZ a b)
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
    ListLit       :: SDType '[] 'Type a
                  -> Seq (DTerm vs a)
                  -> DTerm vs ('List ':$ a)
    ListFold      :: DTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ)))
    ListBuild     :: DTerm vs ('Pi 'SType ('Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'List ':$ 'TVar 'IZ))
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

ident :: DTerm vs ('Pi 'SType ('TVar 'IZ ':-> 'TVar 'IZ))
ident = TLam (STVar SIZ :%-> STVar SIZ) $ \a -> Lam a (Var IZ)

-- konst :: DTerm vs ('Pi 'SType ('Pi 'SType ('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar ('IS 'IZ))))
-- konst = TLam (SPi SType (STVar (SIS SIZ) :%-> STVar SIZ :%-> STVar (SIS SIZ))) $ \(a :: SDType '[] 'Type a) ->
--           TLam _ $ \(b :: SDType '[] 'Type b) -> Lam (Lam (Var (IS IZ)))

-- konst :: DTerm vs ('Pi 'SType ('TVar 'IZ ':-> Pi 'SType ('TVar IZ ':-> 'TVar ('IS 'IZ))))
-- konst = TLam (STVar SIZ :%-> SPi SType (STVar SIZ :%-> STVar (SIS SIZ))) $ \(a :: SDType '[] 'Type a) ->
--           Lam a $ TLam (STVar SIZ :%-> a) _
-- -- konst = TLam (SPi SType (STVar (SIS SIZ) :%-> STVar SIZ :%-> STVar (SIS SIZ))) $ \(a :: SDType '[] 'Type a) ->
-- --           TLam _ $ \(b :: SDType '[] 'Type b) -> Lam (Lam (Var (IS IZ)))



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

