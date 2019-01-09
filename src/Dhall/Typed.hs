{-# LANGUAGE EmptyCase              #-}
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

module Dhall.Typed where

-- module Dhall.Typed (
--   ) where

import           Control.Applicative hiding   (Const(..))
import           Control.Monad
import           Data.Kind
import           Data.Singletons
import           Data.Singletons.Sigma
import           Data.Singletons.TH
import           Data.Type.Equality
import           Data.Void
import           Dhall.Typed.Prod
import           GHC.Generics
import           GHC.TypeLits                 (Symbol)
import           Numeric.Natural
import qualified Control.Applicative          as P
import qualified Dhall                        as D
import qualified Dhall.Core                   as D
import qualified Dhall.TypeCheck              as D

$(singletons [d|
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
    deriving (Eq, Show)
  |])

data N = Z | S N

data IxN :: [(k, v)] -> N -> k -> v -> Type where
    IZ :: IxN ('(a, b) ': as) 'Z a b
    IO :: IxN             as   n a b -> IxN ('(a, c) ': as) ('S n) a b
    IS :: IxN             as   n a b -> IxN (c       ': as)     n  a b     -- should really do a /= c

deriving instance Show (IxN as n a b)

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

data ExprFst :: [(Symbol, ExprType Symbol)] -> (Symbol, ExprType Symbol) -> Type where
    EF :: Expr vs a -> ExprFst vs '(t, a)

data Expr :: [(Symbol, ExprType Symbol)] -> ExprType Symbol -> Type where
    Var        :: IxN vs n a b -> Expr vs b
    Lam        :: Expr vs a -> Expr (v ': vs) a
    BoolLit    :: Bool    -> Expr vs 'Bool
    NaturalLit :: Natural -> Expr vs 'Natural
    IntegerLit :: Integer -> Expr vs 'Integer
    DoubleLit  :: Double  -> Expr vs 'Double
    Op         :: Op a    -> Expr vs a -> Expr vs a -> Expr vs a
    BoolIf     :: Expr vs 'Bool -> Expr vs a -> Expr vs a -> Expr vs a
    Builtin    :: Builtin a b -> Expr vs (a :-> b)

deriving instance Show (Expr vs a)

data SomeExpr :: [(Symbol, ExprType Symbol)] -> Type where
    SE :: Sing a
       -> Expr vs a
       -> SomeExpr vs

deriving instance Show (SomeExpr vs)

data Bindings :: [(Symbol, ExprType Symbol)] -> Type where
    BØ   :: Bindings '[]
    (:?) :: Expr vs a -> Bindings ( '(s, a) ': vs)

infixr 5 :?

fromDhall
    :: Sing a
    -> Bindings vs
    -> D.Expr () D.X
    -> Maybe (Expr vs a)
fromDhall t bs e = do
    SE t' e' <- fromSomeDhall bs e
    case t %~ t' of
      Proved    Refl -> pure e'
      Disproved _    -> empty

fromSomeDhall :: forall vs. Bindings vs -> D.Expr () D.X -> Maybe (SomeExpr vs)
fromSomeDhall bs = \case
    D.BoolLit    b -> Just $ SE SBool (BoolLit b)
    D.NaturalLit n -> Just $ SE SNatural (NaturalLit n)
    D.IntegerLit i -> Just $ SE SInteger (IntegerLit i)
    D.DoubleLit  f -> Just $ SE SDouble  (DoubleLit f)
    D.BoolAnd x y  -> SE SBool <$> op BoolOr sing x y
    D.BoolOr x y   -> SE SBool <$> op BoolOr sing x y
    D.BoolEQ x y   -> SE SBool <$> op BoolEQ sing x y
    D.BoolNE x y   -> SE SBool <$> op BoolNE sing x y
    D.BoolIf b x y -> do
      SE SBool b' <- fromSomeDhall bs b
      SE t     x' <- fromSomeDhall bs x
      SE u     y' <- fromSomeDhall bs y
      case t %~ u of
        Proved   Refl -> pure . SE t $ BoolIf b' x' y'
        Disproved _   -> empty
    D.NaturalIsZero    -> Just $ SE (SNatural :%-> SBool   ) (Builtin NaturalIsZero   )
    D.NaturalEven      -> Just $ SE (SNatural :%-> SBool   ) (Builtin NaturalEven     )
    D.NaturalOdd       -> Just $ SE (SNatural :%-> SBool   ) (Builtin NaturalOdd      )
    D.NaturalToInteger -> Just $ SE (SNatural :%-> SInteger) (Builtin NaturalToInteger)
    D.NaturalShow      -> Just $ SE (SNatural :%-> SText   ) (Builtin NaturalShow     )
    D.NaturalPlus x y  -> SE SNatural <$> op NaturalPlus  sing x y
    D.NaturalTimes x y -> SE SNatural <$> op NaturalTimes sing x y
    D.IntegerShow      -> Just $ SE (SInteger :%-> SText  ) (Builtin IntegerShow    )
    D.IntegerToDouble  -> Just $ SE (SInteger :%-> SDouble) (Builtin IntegerToDouble)
    D.DoubleShow       -> Just $ SE (SDouble  :%-> SText  ) (Builtin DoubleShow     )
  where
    op :: Op a -> Sing a -> D.Expr () D.X -> D.Expr () D.X -> Maybe (Expr vs a)
    op o t x y = Op o <$> fromDhall t bs x <*> fromDhall t bs y

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


