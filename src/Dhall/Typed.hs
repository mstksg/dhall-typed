{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TemplateHaskell        #-}
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
import           Data.Kind
import           Data.List.NonEmpty                        (NonEmpty(..))
import           Data.Maybe
import           Data.Singletons
import           Data.Singletons.Prelude.List              (Sing(..))
import           Data.Singletons.Prelude.Maybe
import           Data.Singletons.Prelude.Tuple
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Text                                 (Text)
import           Data.Type.Equality
import           Data.Void
import           Dhall.Typed.Prod
import           GHC.Generics
import           GHC.TypeLits                              (Symbol)
import           Numeric.Natural
import qualified Control.Applicative                       as P
import qualified Data.List.NonEmpty                        as NE
import qualified Dhall                         as D hiding (Type)
import qualified Dhall.Core                                as D
import qualified Dhall.TypeCheck                           as D

$(singletons [d|
  data ExprTypeType = Type
                    | Kind
                    | Sort
    deriving (Eq, Ord, Show)

  data ExprType t = Bool
                  | Natural
                  | Integer
                  | Double
                  | Text
                  | List (ExprType t)
                  | Optional (ExprType t)
                  | Record [(t, ExprType t)]
                  | Union  [(t, ExprType t)]
                  | ExprType t :-> ExprType t
                  | ETType ExprTypeType
    deriving (Eq, Ord, Show)

  rulePairs :: ExprTypeType -> ExprTypeType -> Maybe ExprTypeType
  rulePairs a b = case b of
    Type -> Just Type
    Kind -> case a of
      Type -> Nothing
      Kind -> Just Kind
      Sort -> Just Sort
    Sort -> case a of
      Type -> Nothing
      Kind -> Nothing
      Sort -> Just Sort

  axioms :: ExprTypeType -> ExprTypeType
  axioms = \case
    Type -> Kind
    Kind -> Sort
    Sort -> error "❰Sort❱ has no type, kind, or sort"

  typeType :: ExprType t -> ExprTypeType
  typeType = \case
    Bool       -> Type
    Natural    -> Type
    Integer    -> Type
    Double     -> Type
    Text       -> Type
    List _     -> Type
    Optional _ -> Type
    Record _   -> Type
    Union _    -> Type
    a :-> b    -> case typeType a `rulePairs` typeType b of
      Nothing -> error "No dependent types"
      Just t  -> t
    ETType t -> axioms t

  data N = Z | S N
    deriving (Eq, Ord, Show)

  |])

data IxN :: [(k, v)] -> N -> k -> v -> Type where
    IZ :: IxN ('(a, b) ': as) 'Z a b
    IO :: IxN             as   n a b -> IxN ('(a, c) ': as) ('S n) a b
    IS :: IxN             as   n a b -> IxN (c       ': as)     n  a b     -- should really do a /= c

deriving instance Show (IxN as n a b)

fromNatural :: Natural -> N
fromNatural 0 = Z
fromNatural n = S (fromNatural (n - 1))

-- | Symbolic operators
data Op :: ExprType t -> Type where
    BoolAnd      :: Op 'Bool
    BoolOr       :: Op 'Bool
    BoolEQ       :: Op 'Bool
    BoolNE       :: Op 'Bool
    NaturalPlus  :: Op 'Natural
    NaturalTimes :: Op 'Natural
    TextAppend   :: Op 'Text
    ListAppend   :: Op ('List a)

deriving instance Show (Op a)

data Builtin :: ExprType t -> ExprType t -> Type where
    NaturalIsZero    :: Builtin 'Natural 'Bool
    NaturalEven      :: Builtin 'Natural 'Bool
    NaturalOdd       :: Builtin 'Natural 'Bool
    NaturalToInteger :: Builtin 'Natural 'Integer
    NaturalShow      :: Builtin 'Natural 'Text
    IntegerShow      :: Builtin 'Integer 'Text
    IntegerToDouble  :: Builtin 'Integer 'Double
    DoubleShow       :: Builtin 'Double  'Text
    Some             :: Builtin a        ('Optional a)

deriving instance Show (Builtin a b)

data Lets :: [(Symbol, ExprType Symbol)] -> ExprType Symbol -> Type where
    LØ :: Sing '(l, b) -> Expr vs b -> Expr ('(l, b) ': vs) a -> Lets vs a
    LS :: Sing '(l, b) -> Expr vs b -> Lets ('(l, b) ': vs) a -> Lets vs a

deriving instance Show (Lets vs a)

data ExprFst :: [(Symbol, ExprType Symbol)] -> (Symbol, ExprType Symbol) -> Type where
    EF :: Expr vs a -> ExprFst vs '(t, a)

data Expr :: [(Symbol, ExprType Symbol)] -> ExprType Symbol -> Type where
    ETypeLit   :: Sing (t :: ExprType Symbol) -> Expr vs ('ETType (TypeType t))
    Var        :: IxN vs n a b -> Expr vs b
    Lam        :: Sing v -> Expr (v ': vs) a -> Expr vs a
    App        :: Expr vs (a ':-> b) -> Expr vs a -> Expr vs b
    Let        :: Lets vs a -> Expr vs a
    BoolLit    :: Bool    -> Expr vs 'Bool
    NaturalLit :: Natural -> Expr vs 'Natural
    IntegerLit :: Integer -> Expr vs 'Integer
    DoubleLit  :: Double  -> Expr vs 'Double
    TextLit    :: [(Text, Expr vs 'Text)] -> Text -> Expr vs 'Text
    Op         :: Op a    -> Expr vs a -> Expr vs a -> Expr vs a
    BoolIf     :: Expr vs 'Bool -> Expr vs a -> Expr vs a -> Expr vs a
    Builtin    :: Builtin a b -> Expr vs (a ':-> b)

deriving instance Show (Expr vs a)

data SomeExpr :: [(Symbol, ExprType Symbol)] -> Type where
    SE :: Sing a
       -> Expr vs a
       -> SomeExpr vs

deriving instance Show (SomeExpr vs)

fromConst :: D.Const -> ExprTypeType
fromConst = \case
    D.Type -> Type
    D.Kind -> Kind
    D.Sort -> Sort

fromDhall
    :: Sing a
    -> Sing vs
    -> D.Expr () D.X
    -> Maybe (Expr vs a)
fromDhall t vs e = do
    SE t' e' <- fromSomeDhall vs e
    case t %~ t' of
      Proved    Refl -> pure e'
      Disproved _    -> empty

matchIxN
    :: forall k (s :: Symbol) (n :: N) (vs :: [(Symbol, k)]) r. ()
    => Sing s
    -> Sing n
    -> Sing vs
    -> (forall (v :: k). IxN vs n s v -> Sing v -> Maybe r)
    -> Maybe r
matchIxN t = go
  where
    go  :: forall (m :: N) (us :: [(Symbol, k)]). ()
        => Sing m
        -> Sing us
        -> (forall v. IxN us m s v -> Sing v -> Maybe r)
        -> Maybe r
    go m = \case
      SNil -> const Nothing
      STuple2 x r `SCons` vs -> \f -> case t %~ x of
        Proved Refl -> case m of
          SZ   -> f IZ r
          SS n -> go n vs (f . IO)
        Disproved _ -> go m vs (f . IS)

fromLets
    :: Sing vs
    -> NonEmpty (D.Binding () D.X)
    -> D.Expr () D.X
    -> (forall a. Sing a -> Lets vs a -> Maybe r)
    -> Maybe r
fromLets vs (D.Binding (FromSing b) _ x :| bs) y f = do
    SE tx x' <- fromSomeDhall vs x
    let v = STuple2 b tx
    case NE.nonEmpty bs of
      Nothing -> do
        SE ty y' <- fromSomeDhall (v `SCons` vs) y
        f ty (LØ v x' y')
      Just bs' -> fromLets (v `SCons` vs) bs' y $ \ty l ->  -- is this right? what about unknown types depending on x?
        f ty (LS v x' l)

fromSomeDhall :: forall vs. Sing vs -> D.Expr () D.X -> Maybe (SomeExpr vs)
fromSomeDhall vs = \case
    D.Const c       -> withSomeSing (fromConst c) $ Just . typeLit . SETType
    D.Var (D.V x n) -> withSomeSing x                              $ \x' ->
                       withSomeSing (fromNatural (fromIntegral n)) $ \n' ->
                       matchIxN x' n' vs                           $ \i r ->
                         Just $ SE r (Var i)
    D.Lam (FromSing x) tx y -> do
      SE _ (ETypeLit tx') <- fromSomeDhall vs tx        -- is this right? can it be anything else? maybe something not normalized?
      let v = STuple2 x tx'
      SE ty y' <- fromSomeDhall (v `SCons` vs) y
      pure $ SE ty (Lam v y')
    D.App f x -> do
      SE (a :%-> b) f' <- fromSomeDhall vs f
      x'               <- fromDhall a vs x
      pure $ SE b (App f' x')
    D.Let bs y  -> fromLets vs bs y $ \ty -> Just . SE ty . Let
    D.Annot x _ -> fromSomeDhall vs x
    D.Bool         -> Just $ typeLit SBool
    D.BoolLit b    -> Just $ SE SBool (BoolLit b)
    D.BoolAnd x y  -> SE SBool <$> op BoolOr SBool x y
    D.BoolOr x y   -> SE SBool <$> op BoolOr SBool x y
    D.BoolEQ x y   -> SE SBool <$> op BoolEQ SBool x y
    D.BoolNE x y   -> SE SBool <$> op BoolNE SBool x y
    D.BoolIf b x y -> do
      b'          <- fromDhall SBool vs b
      SE t     x' <- fromSomeDhall   vs x
      y'          <- fromDhall t     vs y
      pure $ SE t (BoolIf b' x' y')
    D.Natural          -> Just $ typeLit SNatural
    D.NaturalLit n     -> Just $ SE SNatural (NaturalLit n)
    D.NaturalIsZero    -> Just $ builtin SNatural SBool    NaturalIsZero
    D.NaturalEven      -> Just $ builtin SNatural SBool    NaturalEven
    D.NaturalOdd       -> Just $ builtin SNatural SBool    NaturalOdd
    D.NaturalToInteger -> Just $ builtin SNatural SInteger NaturalToInteger
    D.NaturalShow      -> Just $ builtin SNatural SText    NaturalShow
    D.NaturalPlus x y  -> SE SNatural <$> op NaturalPlus   SNatural x y
    D.NaturalTimes x y -> SE SNatural <$> op NaturalTimes  SNatural x y
    D.Integer          -> Just $ typeLit SInteger
    D.IntegerLit i     -> Just $ SE SInteger (IntegerLit i)
    D.IntegerShow      -> Just $ builtin SInteger SText    IntegerShow
    D.IntegerToDouble  -> Just $ builtin SInteger SDouble  IntegerToDouble
    D.Double           -> Just $ typeLit SDouble
    D.DoubleLit f      -> Just $ SE SDouble  (DoubleLit f)
    D.DoubleShow       -> Just $ builtin SDouble  SText    DoubleShow
    D.Text             -> Just $ typeLit SText
    D.TextLit (D.Chunks ts t0) -> do
      ts' <- (traverse . traverse) (fromDhall SText vs) ts
      pure $ SE SText (TextLit ts' t0)
    _ -> undefined
  where
    typeLit :: Sing t -> SomeExpr vs
    typeLit t = SE (SETType (sTypeType t)) (ETypeLit t)
    op :: Op a -> Sing a -> D.Expr () D.X -> D.Expr () D.X -> Maybe (Expr vs a)
    op o t x y = Op o <$> fromDhall t vs x <*> fromDhall t vs y
    builtin :: Sing a -> Sing b -> Builtin a b -> SomeExpr vs
    builtin a b bi = SE (a :%-> b) (Builtin bi)

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

-- -- | The body of an interpolated @Text@ literal
-- data Chunks s a = Chunks [(Text, Expr s a)] Text
--     deriving (Functor, Foldable, Generic, Traversable, Show, Eq, Data)
