{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE InstanceSigs           #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE PolyKinds              #-}
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
import           Data.Foldable
import           Data.Functor
import           Data.Kind
import           Data.List
import           Data.List.NonEmpty                        (NonEmpty(..))
import           Data.Maybe
import           Data.Sequence                             (Seq(..))
import           Data.Singletons
import           Data.Singletons.Prelude.List              (Sing(..))
import           Data.Singletons.Prelude.Maybe
import           Data.Singletons.Prelude.Tuple
import           Data.Singletons.Sigma
import           Data.Singletons.TH hiding                 (Sum)
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
import qualified Control.Applicative                       as P
import qualified Data.List.NonEmpty                        as NE
import qualified Data.Sequence                             as Seq
import qualified Dhall                         as D hiding (Type)
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


-- data DSort

-- data DKind :: Type -> Type where
--     KType :: DKind

-- data DKind

-- data Forall a b

-- problem: cannot test for equality?
data DType :: Type -> Type where
    TPi       :: Lam (DType a) (DType b) -> DType (DType a, b)
    TFunction :: DType a -> DType b -> DType (Lam a b)
    TType     :: DType (DType a)
    TBool     :: DType Bool
    TNatural  :: DType Natural
    TInteger  :: DType Integer
    TDouble   :: DType Double
    TText     :: DType Text
    TList     :: DType a -> DType [a]
    TOptional :: DType a -> DType (Maybe a)

data IxN :: [(k, v)] -> N -> k -> v -> Type where
    IZN :: IxN ('(a, b) ': as) 'Z a b
    ION :: IxN             as   n a b -> IxN ('(a, c) ': as) ('S n) a b
    ISN :: Refuted (a :~: c)
        -> IxN             as   n a b -> IxN ('(c, d) ': as)     n  a b

data DTerm :: [(Symbol, Type)] -> Type -> Type where
    TVar  :: IxN vs n s a -> DTerm vs a
    TTerm :: a -> DTerm vs a

data SomeDTerm :: [(Symbol, Type)] -> Type where
    SDT :: DType a -> DTerm vs a -> SomeDTerm vs

data Lam :: Type -> Type -> Type where
    Lam :: Env ( '(s, a) ': vs )
        -> DTerm ( '(s, a) ': vs ) b
        -> Lam a b

-- data Forall :: Type -> Type -> Type where
--     Forall
--         :: Env ( '(s, DType a) ': vs )
--         -> DTerm ( '(s, DType a) ': vs ) (DType b)
--         -> Forall a b

data Env :: [(Symbol, Type)] -> Type where
    EØ   :: Env '[]
    (:<?) :: (Sing s, DType a) -> Env vs -> Env ( '(s, a) ': vs)

infixr 5 :<?

matchIxN
    :: forall (s :: Symbol) (n :: N) (vs :: [(Symbol, Type)]) r. ()
    => Sing s
    -> Sing n
    -> Env vs
    -> (forall a. IxN vs n s a -> DType a -> Maybe r)
    -> Maybe r
matchIxN t = go
  where
    go  :: forall (m :: N) (us :: [(Symbol, Type)]). ()
        => Sing m
        -> Env us
        -> (forall a. IxN us m s a -> DType a -> Maybe r)
        -> Maybe r
    go m = \case
      EØ -> const Nothing
      (x, r) :<? vs -> \f -> case t %~ x of
        Proved Refl -> case m of
          SZ   -> f IZN r
          SS n -> go n vs (f . ION)
        Disproved v -> go m vs (f . ISN v)

substitute
    :: DTerm vs a
    -> DTerm ( '(t, a) ': vs ) b
    -> DTerm vs b
substitute x = \case
    TVar v -> case v of
      IZN     -> x
      ION   i -> TVar i
      ISN _ i -> TVar i
    TTerm e -> TTerm e

fromSomeDhall
    :: forall vs. ()
    => Env vs
    -> D.Expr () D.X
    -> Maybe (SomeDTerm vs)
fromSomeDhall vs = \case
    D.Var (D.V x n) -> withSomeSing x $ \x' ->
                       withSomeSing (fromNatural (fromIntegral n)) $ \n' ->
                       matchIxN x' n' vs $ \i r ->
                         Just $ SDT r (TVar i)
    D.Lam x tx y -> withSomeSing x $ \x' -> do
      SDT TType tx' <- fromSomeDhall vs tx
      case tx' of
        TTerm e -> do
          SDT ty    y'  <- fromSomeDhall ((x', e) :<? vs) y
          pure . SDT (TFunction e ty) . TTerm $
            Lam ((x', e) :<? vs) y'
        TVar (v :: IxN vs n s (DType a)) -> undefined
          -- SDT _
        -- undefined
            -- SDT _
            --     (TTerm (Lam _ _))
            -- SDT (TPi (Lam ((x', TType) :<? vs) (TVar IZN)))
            --     _
        -- TVar v -> pure $ SDT (TPi (Lam _ _)) _
    _ -> undefined

-- -- fromSomeDhall = \case
-- --     -- D.Var _ -> Left "No free variables"
-- --     D.Lam x tx y -> do
-- --       SomeDT (t ::: TType) <- fromSomeDhall tx
-- --       -- pure $ SomeDT (_ ::: TFunction t _)
-- -- --     | Lam Text (Expr s a) (Expr s a)

-- fromSomeDhall vs = \case
--     D.Const c       -> withSomeSing (fromConst c) $ Just . typeLit . SETT
--     D.Var (D.V x n) -> withSomeSing x                              $ \x' ->
--                        withSomeSing (fromNatural (fromIntegral n)) $ \n' ->
--                        matchIxN x' n' vs                           $ \i r ->
--                          Just $ SE r (Var i)
--     D.Lam (FromSing x) tx y -> do
--       SE (SETT _) tx' <- fromSomeDhall vs tx
--       FromSing tx''   <- pure $ dhallTypeExpr tx'
--       let v = STuple2 x tx''
--       SE ty y' <- fromSomeDhall (v `SCons` vs) y
--       pure $ SE ty (Lam v y')
--     D.App f x -> do
--       SE (a :%-> b) f' <- fromSomeDhall vs f
--       x'               <- fromDhall a vs x
--       pure $ SE b (App f' x')
--     D.Let bs y  -> fromLets vs bs y $ \ty -> Just . SE ty . Let
--     D.Annot x _ -> fromSomeDhall vs x
--     D.Bool         -> Just $ typeLit SBool
--     D.BoolLit b    -> Just $ SE SBool (BoolLit b)
--     D.BoolAnd x y  -> op BoolOr SBool x y
--     D.BoolOr x y   -> op BoolOr SBool x y
--     D.BoolEQ x y   -> op BoolEQ SBool x y
--     D.BoolNE x y   -> op BoolNE SBool x y
--     D.BoolIf b x y -> do
--       b'          <- fromDhall SBool vs b
--       SE t     x' <- fromSomeDhall   vs x
--       y'          <- fromDhall t     vs y
--       pure $ SE t (BoolIf b' x' y')
--     D.Natural          -> Just $ typeLit SNatural
--     D.NaturalLit n     -> Just $ SE SNatural (NaturalLit n)
--     D.NaturalIsZero    -> Just $ builtin SNatural SBool    NaturalIsZero
--     D.NaturalEven      -> Just $ builtin SNatural SBool    NaturalEven
--     D.NaturalOdd       -> Just $ builtin SNatural SBool    NaturalOdd
--     D.NaturalToInteger -> Just $ builtin SNatural SInteger NaturalToInteger
--     D.NaturalShow      -> Just $ builtin SNatural SText    NaturalShow
--     D.NaturalPlus x y  -> op NaturalPlus   SNatural x y
--     D.NaturalTimes x y -> op NaturalTimes  SNatural x y
--     D.Integer          -> Just $ typeLit SInteger
--     D.IntegerLit i     -> Just $ SE SInteger (IntegerLit i)
--     D.IntegerShow      -> Just $ builtin SInteger SText    IntegerShow
--     D.IntegerToDouble  -> Just $ builtin SInteger SDouble  IntegerToDouble
--     D.Double           -> Just $ typeLit SDouble
--     D.DoubleLit f      -> Just $ SE SDouble  (DoubleLit f)
--     D.DoubleShow       -> Just $ builtin SDouble  SText    DoubleShow
--     D.Text             -> Just $ typeLit SText
--     D.TextLit (D.Chunks ts t0) -> do
--       ts' <- (traverse . traverse) (fromDhall SText vs) ts
--       pure $ SE SText (TextLit ts' t0)
--     D.TextAppend x y   -> op TextAppend SText x y
--     D.List             -> Just $ builtin (SETT SType) (SETT SType) ListBI
--     D.ListLit mt xs    -> case mt of
--       Nothing -> do
--         y :<| ys <- pure xs
--         SE t y'  <- fromSomeDhall vs y
--         ys'      <- traverse (fromDhall t vs) ys
--         pure $ SE (SList t) $ ListLit (y' :<| ys')
--       Just t  -> do
--         FromSing t' <- dhallTypeExpr <$> fromDhall (SETT SType) vs t
--         xs'         <- traverse (fromDhall t' vs) xs
--         pure $ SE (SList t') $ ListLit xs'
--     D.ListAppend x y   -> do
--       SE t@(SList _) x' <- fromSomeDhall vs x
--       y'                <- fromDhall t   vs y
--       pure $ SE t (Op ListAppend x' y')
--     D.Optional         -> Just $ builtin (SETT SType) (SETT SType) OptionalBI
--     D.OptionalLit t x  -> do
--       FromSing t' <- dhallTypeExpr <$> fromDhall (SETT SType) vs t
--       x'          <- traverse (fromDhall t' vs) x
--       pure $ SE (SOptional t') $ OptionalLit x'
--     D.Record ts        -> do
--       FromSing ts' <- flip (traverse . traverse) (M.toList ts) $ \y -> do
--         SE (SETT _) y' <- fromSomeDhall vs y
--         pure $ dhallTypeExpr y'
--       pure $ typeLit (SRecord ts')
--     D.RecordLit fs -> fromFields vs (M.toList fs) $ \t xs ->
--       Just . SE (SRecord t) $ RecordLit xs
--     D.Union ts        -> do
--       FromSing ts' <- flip (traverse . traverse) (M.toList ts) $ \y -> do
--         SE (SETT _) y' <- fromSomeDhall vs y
--         pure $ dhallTypeExpr y'
--       pure $ typeLit (SUnion ts')
--     D.UnionLit k v ts -> withSomeSing k $ \k' -> do
--       FromSing ts' <- flip (traverse . traverse) (M.toList ts) $ \y -> do
--         SE (SETT _) y' <- fromSomeDhall vs y
--         pure $ dhallTypeExpr y'
--       SE t v' <- fromSomeDhall vs v
--       insertUnion k' t v' ts' $ \ts'' s ->
--         Just $ SE (SUnion ts'') (UnionLit s)
--     D.CombineTypes x y -> do
--       SE t@(SETT _) x' <- fromSomeDhall vs x
--       y'               <- fromDhall t   vs y
--       pure $ SE t (Op CombineTypes x' y')
--     D.Field x (FromSing s) -> do
--       SE (SRecord fs) x' <- fromSomeDhall vs x
--       lookupSymbol s fs $ \i t -> Just . SE t $ Field x' i
--     D.Project x (toList->FromSing ss) -> do
--       SE (SRecord fs) x' <- fromSomeDhall vs x
--       projectSymbols ss fs $ \i p ->
--         Just . SE (SRecord (prodSing (projectProd p))) $ Project x' i
--     D.Note _ x -> fromSomeDhall vs x
--     _ -> undefined
--   where
--     typeLit :: Sing t -> SomeExpr vs
--     typeLit t = SE (SETT (sTypeType t)) (ETypeLit t)
--     op :: Op a -> Sing a -> D.Expr () D.X -> D.Expr () D.X -> Maybe (SomeExpr vs)
--     op o t x y = SE t <$> (Op o <$> fromDhall t vs x <*> fromDhall t vs y)
--     builtin :: Sing a -> Sing b -> Builtin a b -> SomeExpr vs
--     builtin a b bi = SE (a :%-> b) (Builtin bi)


-- $(singletons [d|
--   data ExprTypeType = Type
--                     | Kind
--                     | Sort
--     deriving (Eq, Ord, Show)

--   data ExprType t = Bool
--                   | Natural
--                   | Integer
--                   | Double
--                   | Text
--                   | List (ExprType t)       -- we should be able to disallow passing in ETT
--                   | Optional (ExprType t)
--                   | Record [(t, ExprType t)]
--                   | Union  [(t, ExprType t)]
--                   | ExprType t :-> ExprType t
--                   | ETT ExprTypeType
--     deriving (Eq, Ord, Show)

--   rulePairs :: ExprTypeType -> ExprTypeType -> Maybe ExprTypeType
--   rulePairs a b = case b of
--     Type -> Just Type
--     Kind -> case a of
--       Type -> Nothing
--       Kind -> Just Kind
--       Sort -> Just Sort
--     Sort -> case a of
--       Type -> Nothing
--       Kind -> Nothing
--       Sort -> Just Sort

--   axioms :: ExprTypeType -> ExprTypeType
--   axioms = \case
--     Type -> Kind
--     Kind -> Sort
--     Sort -> error "❰Sort❱ has no type, kind, or sort"

--   typeType :: ExprType t -> ExprTypeType
--   typeType = \case
--     Bool       -> Type
--     Natural    -> Type
--     Integer    -> Type
--     Double     -> Type
--     Text       -> Type
--     List _     -> Type
--     Optional _ -> Type
--     Record _   -> Type
--     Union _    -> Type
--     a :-> b    -> case typeType a `rulePairs` typeType b of
--       Nothing -> error "No dependent types"
--       Just t  -> t
--     ETT t      -> axioms t

--   insert :: Ord a => a -> b -> [(a, b)] -> [(a, b)]
--   insert k v [] = [(k, v)]
--   insert k v kvs0@((k', v') : kvs) = case compare k k' of
--     LT -> (k, v) : kvs0
--     EQ -> error "insert equal"
--     GT -> (k', v') : insert k v kvs

--   data N = Z | S N
--     deriving (Eq, Ord, Show)

--   |])

-- data IxN :: [(k, v)] -> N -> k -> v -> Type where
--     IZN :: IxN ('(a, b) ': as) 'Z a b
--     ION :: IxN             as   n a b -> IxN ('(a, c) ': as) ('S n) a b
--     ISN :: IxN             as   n a b -> IxN (c       ': as)     n  a b     -- should really do a /= c

-- deriving instance Show (IxN as n a b)

-- fromNatural :: Natural -> N
-- fromNatural 0 = Z
-- fromNatural n = S (fromNatural (n - 1))

-- -- | Symbolic operators
-- data Op :: ExprType t -> Type where
--     BoolAnd      :: Op 'Bool
--     BoolOr       :: Op 'Bool
--     BoolEQ       :: Op 'Bool
--     BoolNE       :: Op 'Bool
--     NaturalPlus  :: Op 'Natural
--     NaturalTimes :: Op 'Natural
--     TextAppend   :: Op 'Text
--     ListAppend   :: Op ('List a)
--     CombineTypes :: Op ('ETT  a)

-- deriving instance Show (Op a)

-- data Builtin :: ExprType t -> ExprType t -> Type where
--     NaturalIsZero    :: Builtin 'Natural 'Bool
--     NaturalEven      :: Builtin 'Natural 'Bool
--     NaturalOdd       :: Builtin 'Natural 'Bool
--     NaturalToInteger :: Builtin 'Natural 'Integer
--     NaturalShow      :: Builtin 'Natural 'Text
--     IntegerShow      :: Builtin 'Integer 'Text
--     IntegerToDouble  :: Builtin 'Integer 'Double
--     DoubleShow       :: Builtin 'Double  'Text
--     Some             :: Builtin a        ('Optional a)
--     ListBI           :: Builtin ('ETT 'Type) ('ETT 'Type)
--     OptionalBI       :: Builtin ('ETT 'Type) ('ETT 'Type)

-- deriving instance Show (Builtin a b)

-- data Lets :: [(Symbol, ExprType Symbol)] -> ExprType Symbol -> Type where
--     LØ :: Sing '(l, b) -> Expr vs b -> Expr ('(l, b) ': vs) a -> Lets vs a
--     LS :: Sing '(l, b) -> Expr vs b -> Lets ('(l, b) ': vs) a -> Lets vs a

-- deriving instance Show (Lets vs a)

-- data Fld :: [(Symbol, ExprType Symbol)] -> (Symbol, ExprType Symbol) -> Type where
--     Fld :: Expr vs a -> Fld vs '(l, a)

-- deriving instance Show (Fld vs a)

-- data ExprFst :: [(Symbol, ExprType Symbol)] -> (Symbol, ExprType Symbol) -> Type where
--     EF :: Expr vs a -> ExprFst vs '(t, a)

-- data Expr :: [(Symbol, ExprType Symbol)] -> ExprType Symbol -> Type where
--     ETypeLit    :: Sing (t :: ExprType Symbol) -> Expr vs ('ETT (TypeType t))
--     Var         :: IxN vs n a b -> Expr vs b
--     Lam         :: Sing v -> Expr (v ': vs) a -> Expr vs a
--     App         :: Expr vs (a ':-> b) -> Expr vs a -> Expr vs b
--     Let         :: Lets vs a -> Expr vs a
--     BoolLit     :: Bool    -> Expr vs 'Bool
--     NaturalLit  :: Natural -> Expr vs 'Natural
--     IntegerLit  :: Integer -> Expr vs 'Integer
--     DoubleLit   :: Double  -> Expr vs 'Double
--     TextLit     :: [(Text, Expr vs 'Text)] -> Text -> Expr vs 'Text
--     ListLit     :: D.Seq (Expr vs a) -> Expr vs ('List a)
--     OptionalLit :: Maybe (Expr vs a) -> Expr vs ('Optional a)
--     Op          :: Op a    -> Expr vs a -> Expr vs a -> Expr vs a
--     BoolIf      :: Expr vs 'Bool -> Expr vs a -> Expr vs a -> Expr vs a
--     Builtin     :: Builtin a b -> Expr vs (a ':-> b)
--     RecordLit   :: Prod (Fld vs) as   -> Expr vs ('Record as)
--     UnionLit    :: Sum  (Fld vs) as   -> Expr vs ('Union  as)
--     Field       :: Expr vs ('Record as) -> Index as '(s, a) -> Expr vs a
--     Project     :: Expr vs ('Record as) -> Prod (Index as) bs -> Expr vs ('Record bs)

-- deriving instance Show (Expr vs a)

-- data SomeExpr :: [(Symbol, ExprType Symbol)] -> Type where
--     SE :: Sing a
--        -> Expr vs a
--        -> SomeExpr vs

-- deriving instance Show (SomeExpr vs)

-- fromConst :: D.Const -> ExprTypeType
-- fromConst = \case
--     D.Type -> Type
--     D.Kind -> Kind
--     D.Sort -> Sort

-- fromDhall
--     :: Sing a
--     -> Sing vs
--     -> D.Expr () D.X
--     -> Maybe (Expr vs a)
-- fromDhall t vs e = do
--     SE t' e' <- fromSomeDhall vs e
--     case t %~ t' of
--       Proved    Refl -> pure e'
--       Disproved _    -> empty

-- matchIxN
--     :: forall k (s :: Symbol) (n :: N) (vs :: [(Symbol, k)]) r. ()
--     => Sing s
--     -> Sing n
--     -> Sing vs
--     -> (forall (v :: k). IxN vs n s v -> Sing v -> Maybe r)
--     -> Maybe r
-- matchIxN t = go
--   where
--     go  :: forall (m :: N) (us :: [(Symbol, k)]). ()
--         => Sing m
--         -> Sing us
--         -> (forall (v :: k). IxN us m s v -> Sing v -> Maybe r)
--         -> Maybe r
--     go m = \case
--       SNil -> const Nothing
--       STuple2 x r `SCons` vs -> \f -> case t %~ x of
--         Proved Refl -> case m of
--           SZ   -> f IZN r
--           SS n -> go n vs (f . ION)
--         Disproved _ -> go m vs (f . ISN)

-- lookupSymbol
--     :: forall k (s :: Symbol) (vs :: [(Symbol, k)]) r. ()
--     => Sing s
--     -> Sing vs
--     -> (forall (v :: k). Index vs '(s, v) -> Sing v -> Maybe r)
--     -> Maybe r
-- lookupSymbol t = go
--   where
--     go  :: forall (us :: [(Symbol, k)]). ()
--         => Sing us
--         -> (forall (v :: k). Index us '(s, v) -> Sing v -> Maybe r)
--         -> Maybe r
--     go = \case
--       SNil -> const Nothing
--       STuple2 x r `SCons` vs -> \f -> case t %~ x of
--         Proved Refl -> f IZ r
--         Disproved _ -> go vs (f . IS)

-- data Projected :: ((Symbol, k) -> Type) -> [(Symbol, k)] -> [Symbol] -> [k] -> Type where
--     PrØ   :: Projected f '[] '[] '[]
--     (:<?) :: f '(a, b) -> Projected f abs as bs -> Projected f ( '(a, b) ': abs ) (a ': as) (b ': bs)

-- projectProd :: Projected f abs as bs -> Prod f abs
-- projectProd = \case
--     PrØ      -> Ø
--     x :<? xs -> x :< projectProd xs

-- projectSymbols
--     :: forall k (as :: [Symbol]) (bs :: [(Symbol, k)]) r. ()
--     => Sing as
--     -> Sing bs
--     -> (forall (cs :: [(Symbol, k)]) (rs :: [k]). Prod (Index bs) cs -> Projected Sing cs as rs -> Maybe r)
--     -> Maybe r
-- projectSymbols = \case
--     SNil -> \_ f -> f Ø PrØ
--     t0@(t `SCons` ts) -> \case
--       SNil -> const Nothing
--       xr@(STuple2 x _) `SCons` xs -> \f -> case t %~ x of
--         Proved Refl -> projectSymbols ts xs $ \ixs prs -> f (IZ :< mapProd IS ixs) (xr :<? prs)
--         Disproved _ -> projectSymbols t0 xs $ \ixs prs  -> f (mapProd IS ixs) prs

-- fromLets
--     :: Sing vs
--     -> NonEmpty (D.Binding () D.X)
--     -> D.Expr () D.X
--     -> (forall a. Sing a -> Lets vs a -> Maybe r)
--     -> Maybe r
-- fromLets vs (D.Binding (FromSing b) _ x :| bs) y f = do
--     SE tx x' <- fromSomeDhall vs x
--     let v = STuple2 b tx
--     case NE.nonEmpty bs of
--       Nothing -> do
--         SE ty y' <- fromSomeDhall (v `SCons` vs) y
--         f ty (LØ v x' y')
--       Just bs' -> fromLets (v `SCons` vs) bs' y $ \ty l ->  -- is this right? what about unknown types depending on x?
--         f ty (LS v x' l)

-- fromFields
--     :: forall (vs :: [(Symbol, ExprType Symbol)]) r. ()
--     => Sing vs
--     -> [(Text, D.Expr () D.X)]
--     -> (forall (as :: [(Symbol, ExprType Symbol)]). Sing as -> Prod (Fld vs) as -> Maybe r)
--     -> Maybe r
-- fromFields vs = \case
--     []        -> \f -> f SNil Ø
--     (l,x):lxs -> \f -> withSomeSing l $ \l' -> do
--       SE t x' <- fromSomeDhall vs x
--       fromFields vs lxs $ \us fs -> f (STuple2 l' t `SCons` us) (Fld x' :< fs)

-- insertUnion
--     :: forall (t :: Symbol) (vs :: [(Symbol, ExprType Symbol)]) (bs :: [(Symbol, ExprType Symbol)]) (a :: ExprType Symbol) r. ()
--     => Sing t
--     -> Sing a
--     -> Expr vs a
--     -> Sing bs
--     -> (forall (as :: [(Symbol, ExprType Symbol)]). Sing as -> Sum (Fld vs) as -> Maybe r)
--     -> Maybe r
-- insertUnion t a x = go
--   where
--     go  :: forall (cs :: [(Symbol, ExprType Symbol)]). ()
--         => Sing cs
--         -> (forall (as :: [(Symbol, ExprType Symbol)]). Sing as -> Sum (Fld vs) as -> Maybe r)
--         -> Maybe r
--     go = \case
--       SNil -> \f -> f (STuple2 t a `SCons` SNil) (Sum IZ (Fld x))
--       cs0@(ub@(STuple2 u _) `SCons` cs) -> \f -> case sCompare t u of
--         SLT -> f (STuple2 t a `SCons` cs0) (Sum IZ (Fld x))
--         SEQ -> Nothing
--         SGT -> go cs $ \cs' (Sum i y) -> f (ub `SCons` cs') (Sum (IS i) y)

-- fromSomeDhall :: forall vs. Sing vs -> D.Expr () D.X -> Maybe (SomeExpr vs)
-- fromSomeDhall vs = \case
--     D.Const c       -> withSomeSing (fromConst c) $ Just . typeLit . SETT
--     D.Var (D.V x n) -> withSomeSing x                              $ \x' ->
--                        withSomeSing (fromNatural (fromIntegral n)) $ \n' ->
--                        matchIxN x' n' vs                           $ \i r ->
--                          Just $ SE r (Var i)
--     D.Lam (FromSing x) tx y -> do
--       SE (SETT _) tx' <- fromSomeDhall vs tx
--       FromSing tx''   <- pure $ dhallTypeExpr tx'
--       let v = STuple2 x tx''
--       SE ty y' <- fromSomeDhall (v `SCons` vs) y
--       pure $ SE ty (Lam v y')
--     D.App f x -> do
--       SE (a :%-> b) f' <- fromSomeDhall vs f
--       x'               <- fromDhall a vs x
--       pure $ SE b (App f' x')
--     D.Let bs y  -> fromLets vs bs y $ \ty -> Just . SE ty . Let
--     D.Annot x _ -> fromSomeDhall vs x
--     D.Bool         -> Just $ typeLit SBool
--     D.BoolLit b    -> Just $ SE SBool (BoolLit b)
--     D.BoolAnd x y  -> op BoolOr SBool x y
--     D.BoolOr x y   -> op BoolOr SBool x y
--     D.BoolEQ x y   -> op BoolEQ SBool x y
--     D.BoolNE x y   -> op BoolNE SBool x y
--     D.BoolIf b x y -> do
--       b'          <- fromDhall SBool vs b
--       SE t     x' <- fromSomeDhall   vs x
--       y'          <- fromDhall t     vs y
--       pure $ SE t (BoolIf b' x' y')
--     D.Natural          -> Just $ typeLit SNatural
--     D.NaturalLit n     -> Just $ SE SNatural (NaturalLit n)
--     D.NaturalIsZero    -> Just $ builtin SNatural SBool    NaturalIsZero
--     D.NaturalEven      -> Just $ builtin SNatural SBool    NaturalEven
--     D.NaturalOdd       -> Just $ builtin SNatural SBool    NaturalOdd
--     D.NaturalToInteger -> Just $ builtin SNatural SInteger NaturalToInteger
--     D.NaturalShow      -> Just $ builtin SNatural SText    NaturalShow
--     D.NaturalPlus x y  -> op NaturalPlus   SNatural x y
--     D.NaturalTimes x y -> op NaturalTimes  SNatural x y
--     D.Integer          -> Just $ typeLit SInteger
--     D.IntegerLit i     -> Just $ SE SInteger (IntegerLit i)
--     D.IntegerShow      -> Just $ builtin SInteger SText    IntegerShow
--     D.IntegerToDouble  -> Just $ builtin SInteger SDouble  IntegerToDouble
--     D.Double           -> Just $ typeLit SDouble
--     D.DoubleLit f      -> Just $ SE SDouble  (DoubleLit f)
--     D.DoubleShow       -> Just $ builtin SDouble  SText    DoubleShow
--     D.Text             -> Just $ typeLit SText
--     D.TextLit (D.Chunks ts t0) -> do
--       ts' <- (traverse . traverse) (fromDhall SText vs) ts
--       pure $ SE SText (TextLit ts' t0)
--     D.TextAppend x y   -> op TextAppend SText x y
--     D.List             -> Just $ builtin (SETT SType) (SETT SType) ListBI
--     D.ListLit mt xs    -> case mt of
--       Nothing -> do
--         y :<| ys <- pure xs
--         SE t y'  <- fromSomeDhall vs y
--         ys'      <- traverse (fromDhall t vs) ys
--         pure $ SE (SList t) $ ListLit (y' :<| ys')
--       Just t  -> do
--         FromSing t' <- dhallTypeExpr <$> fromDhall (SETT SType) vs t
--         xs'         <- traverse (fromDhall t' vs) xs
--         pure $ SE (SList t') $ ListLit xs'
--     D.ListAppend x y   -> do
--       SE t@(SList _) x' <- fromSomeDhall vs x
--       y'                <- fromDhall t   vs y
--       pure $ SE t (Op ListAppend x' y')
--     D.Optional         -> Just $ builtin (SETT SType) (SETT SType) OptionalBI
--     D.OptionalLit t x  -> do
--       FromSing t' <- dhallTypeExpr <$> fromDhall (SETT SType) vs t
--       x'          <- traverse (fromDhall t' vs) x
--       pure $ SE (SOptional t') $ OptionalLit x'
--     D.Record ts        -> do
--       FromSing ts' <- flip (traverse . traverse) (M.toList ts) $ \y -> do
--         SE (SETT _) y' <- fromSomeDhall vs y
--         pure $ dhallTypeExpr y'
--       pure $ typeLit (SRecord ts')
--     D.RecordLit fs -> fromFields vs (M.toList fs) $ \t xs ->
--       Just . SE (SRecord t) $ RecordLit xs
--     D.Union ts        -> do
--       FromSing ts' <- flip (traverse . traverse) (M.toList ts) $ \y -> do
--         SE (SETT _) y' <- fromSomeDhall vs y
--         pure $ dhallTypeExpr y'
--       pure $ typeLit (SUnion ts')
--     D.UnionLit k v ts -> withSomeSing k $ \k' -> do
--       FromSing ts' <- flip (traverse . traverse) (M.toList ts) $ \y -> do
--         SE (SETT _) y' <- fromSomeDhall vs y
--         pure $ dhallTypeExpr y'
--       SE t v' <- fromSomeDhall vs v
--       insertUnion k' t v' ts' $ \ts'' s ->
--         Just $ SE (SUnion ts'') (UnionLit s)
--     D.CombineTypes x y -> do
--       SE t@(SETT _) x' <- fromSomeDhall vs x
--       y'               <- fromDhall t   vs y
--       pure $ SE t (Op CombineTypes x' y')
--     D.Field x (FromSing s) -> do
--       SE (SRecord fs) x' <- fromSomeDhall vs x
--       lookupSymbol s fs $ \i t -> Just . SE t $ Field x' i
--     D.Project x (toList->FromSing ss) -> do
--       SE (SRecord fs) x' <- fromSomeDhall vs x
--       projectSymbols ss fs $ \i p ->
--         Just . SE (SRecord (prodSing (projectProd p))) $ Project x' i
--     D.Note _ x -> fromSomeDhall vs x
--     _ -> undefined
--   where
--     typeLit :: Sing t -> SomeExpr vs
--     typeLit t = SE (SETT (sTypeType t)) (ETypeLit t)
--     op :: Op a -> Sing a -> D.Expr () D.X -> D.Expr () D.X -> Maybe (SomeExpr vs)
--     op o t x y = SE t <$> (Op o <$> fromDhall t vs x <*> fromDhall t vs y)
--     builtin :: Sing a -> Sing b -> Builtin a b -> SomeExpr vs
--     builtin a b bi = SE (a :%-> b) (Builtin bi)

---- | This might not even be possible.  We might need a 'Bindings' thing to
---- fill in holes.
----
---- Or, at least, we can return a "function to reveal an ExprType", so
---- basically a delayed type.
--dhallTypeExpr :: Expr vs ('ETT t) -> ExprType Text
--dhallTypeExpr = undefined

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
