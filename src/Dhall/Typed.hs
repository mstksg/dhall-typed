{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE ViewPatterns        #-}

-- {-# OPTIONS_GHC -fplugin Dhall.Typed.Plugin #-}

module Dhall.Typed (
    toTyped
  , fromTyped
  , fromDTerm
  , fromDType
  , fromDKind
  , fromDSort
  ) where

-- module Dhall.Typed (
--   -- * Conversion
--   -- ** To
--     toTypedKind, toTypedType, toTypedTerm, toSomeTerm
--   -- ** From
--   , fromTypedKind, fromTypedType, fromTypedTerm
--   -- ** Typechecking
--   , typeOfExpr
--   -- ** Context
--   , TermCtx(..), ctxKinds, ctxTypes, toContext, TermCtxItem(..), lookupCtx
--   -- * Convenience
--   , kindcheckType, typecheckTerm
--   -- * Samples
--   , ident, konst, konst', konst3, konst4, natBuild, listBuild
--   ) where

-- import qualified Language.Haskell.TH.Desugar.Lift as TH
-- import qualified Language.Haskell.TH.Lift         as TH
import           Control.Applicative
import           Control.Monad
import           Control.Monad.Except
import           Data.Foldable
import           Data.Functor
import           Data.Functor.Product
import           Data.Kind
import           Data.Sequence                       (Seq(..))
import           Data.Singletons
import           Data.Singletons.Decide
import           Data.Text                           (Text)
import           Data.Traversable
import           Data.Type.Equality
import           Data.Type.Predicate
import           Dhall.Typed.Context
import           Dhall.Typed.Core
import           Dhall.Typed.Type.Either
import           Dhall.Typed.Type.Index
import           Dhall.Typed.Type.N
import           Dhall.Typed.Type.Prod
import           Dhall.Typed.Type.Singletons
import           GHC.Generics                        ((:*:)(..))
import           Unsafe.Coerce
import qualified Data.Sequence                       as Seq
import qualified Data.Text                           as T
import qualified Dhall.Context                       as D
import qualified Dhall.Core                          as D
import qualified Dhall.Map                           as DM
import qualified Dhall.TypeCheck                     as D
import qualified Language.Haskell.TH                 as TH
import qualified Language.Haskell.TH.Desugar         as TH

data TypeMessage = TM (D.TypeMessage () D.X)
                 | TMNoPolyKind
                 | TMUnexpected
  deriving Show

m2e :: MonadError e m => e -> Maybe a -> m a
m2e n = maybe (throwError n) pure

toTyped
    :: forall ts us vs. ()
    => Context ts us vs
    -> D.Expr () D.X
    -> Either TypeMessage (SomeDExpr ts us vs)
toTyped ctx = \case
    D.Const D.Sort -> pure . SomeDExpr $ DEOrder
    D.Const D.Kind -> pure . SomeDExpr . DESort $ Kind
    D.Const D.Type -> pure . SomeDExpr . deKind $ Type
    D.Var (D.V l i) -> m2e (TM (D.UnboundVariable l)) (lookupCtx l i ctx) <&> \case
      TCISort j t -> SomeDExpr . DEKind $ SomeKind t (KVar j)
      TCIKind j u -> SomeDExpr . DEType $ SomeType u (TVar j)
      TCIType j v -> SomeDExpr . DETerm $ SomeTerm v (Var  j)
    D.Lam l m x    -> lamToTyped ctx l m x
    D.Pi  l m x    -> piToTyped ctx l m x
    D.App f x      -> appToTyped ctx f x
    D.Annot x t    -> runEitherFail TMUnexpected $ liftEF (toTyped ctx x) >>= \case
      SomeDExpr DEOrder -> throwError $ TM D.Untyped
      SomeDExpr (DESort x') -> do
        SomeDExpr DEOrder <- liftEF (toTyped ctx t) <?>
              TM (D.AnnotMismatch x t (D.Const D.Sort))
        pure . SomeDExpr . DESort $ x'
      SomeDExpr (DEKind (SomeKind t' x')) ->
            (<?> TM (D.AnnotMismatch x (D.normalize t) (fromDSort (fromPolySing t')))) $ do
        SomeDExpr (DESort (toPolySing->SomePS t'')) <- liftEF (toTyped ctx t)
        Proved _ <- pure $ singEq t' t''
        pure . SomeDExpr . DEKind $ SomeKind t' x'
      SomeDExpr (DEType (SomeType (NDK t') x')) -> do
        let nt' = skNormalize t'
            nt'Dhall = fromDKind . fromPolySing $ nt'
        SomeDExpr (DEKind (SomeKind _ (toPolySing->SomePS t''))) <- liftEF (toTyped ctx t)
          <?> TM (D.AnnotMismatch x (D.normalize t) nt'Dhall)
        let nt'' = skNormalize t''
        Proved _ <- pure (singEq t' t'')
          <?> TM (D.AnnotMismatch x (fromDKind (fromPolySing nt'')) nt'Dhall)
        pure . SomeDExpr . DEType $ SomeType (NDK t') x'
      SomeDExpr (DETerm (SomeTerm (NDT t') x')) -> do
        let nt' = stNormalize t'
            nt'Dhall = fromDType . fromPolySing $ nt'
        SomeDExpr (DEType (SomeType _ (toPolySing->SomePS t''))) <- liftEF (toTyped ctx t)
          <?> TM (D.AnnotMismatch x (D.normalize t) nt'Dhall)
        let nt'' = stNormalize t''
        Proved _ <- pure (singEq t' t'')
          <?> TM (D.AnnotMismatch x (fromDType (fromPolySing nt'')) nt'Dhall)
        pure . SomeDExpr . DETerm $ SomeTerm (NDT t') x'
    D.Bool         -> pure . SomeDExpr . deType $ Bool
    D.BoolLit b    -> pure . SomeDExpr . deTerm $ P (BoolLit b) Ø
    D.BoolAnd x y -> runEitherFail (TM (D.CantAnd x y)) $
      SomeDExpr . deTerm <$> toPrim ctx BoolAnd ( Const x :< Const y :< Ø )
    D.BoolOr x y -> runEitherFail (TM (D.CantOr x y)) $
      SomeDExpr . deTerm <$> toPrim ctx BoolOr ( Const x :< Const y :< Ø )
    D.Natural      -> pure . SomeDExpr . deType $ Natural
    D.NaturalLit n -> pure . SomeDExpr . deTerm $ P (NaturalLit n) Ø
    D.NaturalFold  -> pure . SomeDExpr . deTerm $ P NaturalFold Ø
    D.NaturalBuild -> pure . SomeDExpr . deTerm $ P NaturalBuild Ø
    D.NaturalPlus x y -> runEitherFail (TM (D.CantAdd x y)) $
      SomeDExpr . deTerm <$> toPrim ctx NaturalPlus ( Const x :< Const y :< Ø )
    D.NaturalTimes x y -> runEitherFail (TM (D.CantMultiply x y)) $
      SomeDExpr . deTerm <$> toPrim ctx NaturalTimes ( Const x :< Const y :< Ø )
    D.NaturalIsZero -> pure . SomeDExpr . deTerm $ P NaturalIsZero Ø
    D.List          -> pure . SomeDExpr . deType $ List
    D.ListLit t xs -> listLitToTyped ctx t (toList xs) $ \t' xs' ->
      pure . SomeDExpr . DETerm $ SomeTerm (NDT (SList `STApp` t')) xs'
    D.ListFold      -> pure . SomeDExpr . deTerm $ P ListFold Ø
    D.ListBuild     -> pure . SomeDExpr . deTerm $ P ListBuild Ø
    D.ListAppend x y -> runEitherFail (TM (D.CantListAppend x y)) $ do
      SomeDExpr (DETerm (SomeTerm (NDT t1) x')) <- liftEF $ toTyped ctx x
      SomeDExpr (DETerm (SomeTerm (NDT t2) y')) <- liftEF $ toTyped ctx y
      SList `STApp` a <- pure $ stNormalize t1
      SList `STApp` b <- pure $ stNormalize t2
      Proved HRefl <- pure $ singEq a b
      pure . SomeDExpr . DETerm . SomeTerm (NDT t1) $
        P (ListAppend a) (x' :< y' :< Ø)
    D.ListHead      -> pure . SomeDExpr . deTerm $ P ListHead Ø
    D.ListLast      -> pure . SomeDExpr . deTerm $ P ListLast Ø
    D.ListReverse   -> pure . SomeDExpr . deTerm $ P ListReverse Ø
    D.Optional      -> pure . SomeDExpr . deType $ Optional
    D.OptionalLit t xs -> runEitherFail TMUnexpected $ liftEF (toTyped ctx t) >>= \case
      SomeDExpr (DEType (SomeType (NDK k) (toPolySing->SomePS (t' :: SDType ts us k a)))) -> do
        SType <- pure (skNormalize k) <?> TM (D.InvalidOptionalType t)
        let t'' = stNormalize t'
        xs' <- for xs $ \y -> liftEF (toTyped ctx y) >>= \case
          SomeDExpr (DETerm (SomeTerm (NDT t2) y')) -> do
            let t2' = stNormalize t2
            Proved HRefl <- pure (singEq t'' t2') <?>
              TM (D.InvalidOptionalElement t y (fromDType (fromPolySing t2)))
            pure y'
          SomeDExpr (DEType (SomeType (NDK t2) _)) -> throwError . TM $
            D.InvalidOptionalElement t y (fromDKind (fromPolySing t2))
          SomeDExpr (DEKind (SomeKind t2 _)) -> throwError . TM $
            D.InvalidOptionalElement t y (fromDSort (fromPolySing t2))
          SomeDExpr (DESort _) -> throwError . TM $
            D.InvalidOptionalElement t y (D.Const D.Sort)
          SomeDExpr DEOrder -> throwError . TM $ D.Untyped
        pure . SomeDExpr . DETerm $ SomeTerm (NDT (SOptional `STApp` t')) $
          OptionalLit (NDT t') xs'
      SomeDExpr DEOrder -> throwError . TM $ D.Untyped
      SomeDExpr _       -> throwError . TM $ D.InvalidOptionalType t
    D.Some x        -> toTyped ctx x >>= \case
      SomeDExpr (DETerm (SomeTerm (NDT a) x'))
        -> pure . SomeDExpr . DETerm
         . SomeTerm (NDT (SOptional `STApp` a))
         $ P (Some (stNormalize a)) (x' :< Ø)
      SomeDExpr (DEType (SomeType (NDK a) _))
        -> Left . TM $ D.InvalidSome x (fromDKind (fromPolySing a)) (D.Const D.Kind)
      SomeDExpr (DEKind (SomeKind a _))
        -> Left . TM $ D.InvalidSome x (fromDSort (fromPolySing a)) (D.Const D.Sort)
      SomeDExpr _ -> Left $ TM D.Untyped
    D.None          -> pure . SomeDExpr . deTerm $ P None Ø
    D.Note _ x      -> toTyped ctx x
    D.ImportAlt x _ -> toTyped ctx x
    D.Embed v       -> D.absurd v

toPrim
    :: forall ts us vs as a. PolySingI as
    => Context ts us vs
    -> Prim ts us as a
    -> Prod (Const (D.Expr () D.X)) as
    -> EitherFail TypeMessage (DTerm ts us vs a)
toPrim ctx p xs = P p <$> traverseProd go (zipProd xs (singProd polySing))
  where
    go  :: (Const (D.Expr () D.X) :*: SDType ts us 'Type) x
        -> EitherFail TypeMessage (DTerm ts us vs x)
    go (Const x :*: t) = do
      SomeDExpr (DETerm (SomeTerm (NDT t') x')) <- liftEF $ toTyped ctx x
      Proved HRefl <- pure $ t `singEq` stNormalize t'
      pure x'

listLitToTyped
    :: forall ts us vs r. ()
    => Context ts us vs
    -> Maybe (D.Expr () D.X)
    -> [D.Expr () D.X]
    -> (forall a. SDType ts us 'Type a
               -> DTerm ts us vs ('List :$ TNormalize ts us 'Type a)
               -> Either TypeMessage r
       )
    -> Either TypeMessage r
listLitToTyped ctx mt xs f = runEitherFail TMUnexpected $ case mt of
    Nothing -> do
      y : ys <- pure xs <?> TM D.MissingListType
      liftEF (toTyped ctx y) >>= \case
        SomeDExpr (DETerm (SomeTerm (NDT t1) (y' :: DTerm ts us vs a))) -> do
          let t1' = stNormalize t1
              t1Dhall = fromDType (fromPolySing t1')
          ys' :: [DTerm ts us vs a] <- for (zip [1..] ys) $ \(i :: Int, z) -> liftEF (toTyped ctx z) >>= \case
            SomeDExpr (DETerm (SomeTerm (NDT t2) z')) -> do
              let t2' = stNormalize t2
              Proved HRefl <- pure (singEq t1' t2') <?>
                TM (D.MismatchedListElements i
                      t1Dhall z (fromDType (fromPolySing t2))
                   )
              pure z'
            SomeDExpr (DEType (SomeType (NDK t2) _)) -> throwError . TM $
              D.MismatchedListElements i t1Dhall z (fromDKind (fromPolySing t2))
            SomeDExpr (DEKind (SomeKind t2 _)) -> throwError . TM $
              D.MismatchedListElements i t1Dhall z (fromDSort (fromPolySing t2))
            SomeDExpr (DESort _) -> throwError . TM $
              D.MismatchedListElements i t1Dhall z (D.Const D.Sort)
            SomeDExpr DEOrder -> throwError $ TM D.Untyped
          liftEF . f t1 $ ListLit (NDT t1) (y' : ys')
        SomeDExpr (DEType (SomeType (NDK t) _)) -> throwError . TM $
          D.InvalidListType (fromDKind (fromPolySing t))
        SomeDExpr (DEKind (SomeKind t _)) -> throwError . TM $
          D.InvalidListType (fromDSort (fromPolySing t))
        SomeDExpr _ -> throwError $ TM D.Untyped
    Just t -> liftEF (toTyped ctx t) >>= \case
      SomeDExpr (DEType (SomeType (NDK k) (toPolySing->SomePS (t' :: SDType ts us k a)))) -> do
        SType <- pure (skNormalize k) <?> TM (D.InvalidListType t)
        let t'' = stNormalize t'
        xs' <- for (zip [0..] xs) $ \(i :: Int, y) -> liftEF (toTyped ctx y) >>= \case
          SomeDExpr (DETerm (SomeTerm (NDT t2) y')) -> do
            let t2' = stNormalize t2
            Proved HRefl <- pure (singEq t'' t2') <?>
                TM (D.MismatchedListElements i
                      t y (fromDType (fromPolySing t2))
                   )
            pure y'
          SomeDExpr (DEType (SomeType (NDK t2) _)) -> throwError . TM $
            D.MismatchedListElements i t y (fromDKind (fromPolySing t2))
          SomeDExpr (DEKind (SomeKind t2 _)) -> throwError . TM $
            D.MismatchedListElements i t y (fromDSort (fromPolySing t2))
          SomeDExpr (DESort _) -> throwError . TM $
            D.MismatchedListElements i t y (D.Const D.Sort)
          SomeDExpr DEOrder -> throwError $ TM D.Untyped
        liftEF . f t' $ ListLit (NDT t') xs'
      SomeDExpr DEOrder -> throwError $ TM D.Untyped
      SomeDExpr _ -> throwError . TM $ D.InvalidListType t

lamToTyped
    :: forall ts us vs. ()
    => Context ts us vs
    -> T.Text
    -> D.Expr () D.X
    -> D.Expr () D.X
    -> Either TypeMessage (SomeDExpr ts us vs)
lamToTyped ctx l m x = runEitherFail TMUnexpected $ liftEF (toTyped ctx m) >>= \case
    SomeDExpr DEOrder -> throwError $ TM D.Untyped
    SomeDExpr (DESort (toPolySing->SomePS t)) -> liftEF (toTyped (ConsSort l t ctx) x) >>= \case
      SomeDExpr DEOrder -> throwError $ TM D.Untyped
      SomeDExpr (DESort _) -> throwError $ TM D.Untyped
      SomeDExpr (DEKind (SomeKind t' x'')) -> pure $
        SomeDExpr . DEKind $ SomeKind (t :%*> t') (KLam t x'')
      SomeDExpr (DEType (SomeType (NDK u) x'')) -> pure $
        SomeDExpr . DEType $ SomeType (NDK (SKPi (SiSi t) u)) $
          TPoly (SiSi t) x''
      SomeDExpr (DETerm _) -> throwError TMNoPolyKind
    SomeDExpr (DEKind (SomeKind t (toPolySing->SomePS u))) -> do
      SKind <- pure t <?> TM (D.InvalidInputType m)
      liftEF (toTyped (ConsKind l (NDK u) ctx) x) >>= \case
        SomeDExpr DEOrder -> throwError . TM $ D.Untyped
        SomeDExpr (DESort _) -> throwError . TM $ D.Untyped
        SomeDExpr (DEKind (SomeKind t' _)) -> throwError . TM $ D.NoDependentTypes m $
          fromDSort (fromPolySing t')
        SomeDExpr (DEType (SomeType (NDK u') x')) -> pure $
          SomeDExpr . DEType $ SomeType (NDK (u :%~> u')) $
            TLam (NDK u) x'
        SomeDExpr (DETerm (SomeTerm (NDT v) x')) -> pure $
          SomeDExpr . DETerm $ SomeTerm (NDT (SPi (SNDK (SiSi u)) v)) $
            Poly (SNDK (SiSi u)) x'
    SomeDExpr (DEType (SomeType (NDK u) (toPolySing->SomePS v))) -> do
      SType <- pure (skNormalize u) <?> TM (D.InvalidInputType m)
      liftEF (toTyped (ConsType l (NDT v) ctx) x) >>= \case
        SomeDExpr DEOrder -> throwError . TM $ D.Untyped
        SomeDExpr (DESort _) -> throwError . TM $ D.Untyped
        SomeDExpr (DEKind (SomeKind t _)) -> throwError . TM $ D.NoDependentTypes m $
          fromDSort (fromPolySing t)
        SomeDExpr (DEType (SomeType (NDK u') _)) -> throwError . TM $ D.NoDependentTypes m $
          fromDKind (fromPolySing u')
        SomeDExpr (DETerm (SomeTerm (NDT v') x')) -> pure $
          SomeDExpr . DETerm $ SomeTerm (NDT (v :%-> v')) $
            Lam (NDT v) x'
    SomeDExpr (DETerm _) -> throwError . TM $ D.InvalidInputType m

piToTyped
    :: forall ts us vs. ()
    => Context ts us vs
    -> T.Text
    -> D.Expr () D.X
    -> D.Expr () D.X
    -> Either TypeMessage (SomeDExpr ts us vs)
piToTyped ctx l m x = runEitherFail TMUnexpected $ liftEF (toTyped ctx m) >>= \case
    SomeDExpr DEOrder -> throwError $ TM D.Untyped
    SomeDExpr (DESort t0@(toPolySing->SomePS t)) -> liftEF (toTyped (ConsSort l t ctx) x) >>= \case
      SomeDExpr DEOrder -> throwError $ TM D.Untyped
      SomeDExpr (DESort x') -> pure . SomeDExpr $ DESort (t0 :*> x')
      SomeDExpr (DEKind (SomeKind tx x')) -> pure . SomeDExpr . DEKind $
        SomeKind tx (KPi t x')
      SomeDExpr (DEType _) -> throwError TMNoPolyKind
      SomeDExpr (DETerm _) -> throwError . TM $ D.InvalidOutputType x
    SomeDExpr (DEKind (SomeKind t u0@(toPolySing->SomePS u))) -> do
      SKind <- pure t <?> TM (D.InvalidInputType m)
      liftEF (toTyped (ConsKind l (NDK u) ctx) x) >>= \case
        SomeDExpr DEOrder -> throwError $ TM D.Untyped
        SomeDExpr (DESort _) -> throwError . TM $ D.NoDependentTypes m x
        SomeDExpr (DEKind (SomeKind tx x')) -> do
          SKind <- pure tx <?> TM (D.InvalidOutputType x)
          pure . SomeDExpr . DEKind $
            SomeKind SKind (u0 :~> x')
        SomeDExpr (DEType (SomeType (NDK tx) x')) -> pure . SomeDExpr . DEType $
          SomeType (NDK tx) (Pi (NDK u) x')
        SomeDExpr (DETerm _) -> throwError . TM $ D.InvalidOutputType x
    SomeDExpr (DEType (SomeType (NDK u) v0@(toPolySing->SomePS v))) -> do
      SType <- pure (skNormalize u) <?> TM (D.InvalidInputType m)
      liftEF (toTyped (ConsType l (NDT v) ctx) x) >>= \case
        SomeDExpr DEOrder -> throwError . TM $ D.Untyped
        SomeDExpr (DESort _) -> throwError . TM $ D.NoDependentTypes m x
        SomeDExpr (DEKind _) -> throwError . TM $ D.NoDependentTypes m x
        SomeDExpr (DEType (SomeType (NDK tx) x')) -> do
          SType <- pure (skNormalize tx) <?> TM (D.InvalidOutputType x)
          pure . SomeDExpr . DEType $
            SomeType (NDK SType) (v0 :-> x')
        SomeDExpr (DETerm _) -> throwError . TM $ D.InvalidOutputType x
    SomeDExpr (DETerm _) -> throwError . TM $ D.InvalidInputType m

appToTyped
    :: forall ts us vs. ()
    => Context ts us vs
    -> D.Expr () D.X
    -> D.Expr () D.X
    -> Either TypeMessage (SomeDExpr ts us vs)
appToTyped ctx f x = runEitherFail TMUnexpected $ liftEF (toTyped ctx f) >>= \case
    SomeDExpr DEOrder -> throwError . TM $ D.Untyped
    SomeDExpr (DESort _) -> throwError . TM $ D.NotAFunction f (D.Const D.Sort)
    SomeDExpr (DEKind (SomeKind tf f')) -> do
      tx :%*> ty <- pure tf <?> TM (D.NotAFunction f (fromDSort (fromPolySing tf)))
      let txDhall = fromDSort . fromPolySing $ tx
      x' <- liftEF (toTyped ctx x) >>= \case
        SomeDExpr DEOrder -> throwError . TM $ D.Untyped
        SomeDExpr (DESort _) -> throwError . TM $
          D.TypeMismatch f txDhall x (D.Const D.Sort)
        SomeDExpr (DEKind (SomeKind tx' x')) -> do
          Proved HRefl <- pure (singEq tx tx') <?> TM
              (D.TypeMismatch f txDhall x (fromDSort (fromPolySing tx')))
          pure x'
        SomeDExpr (DEType (SomeType (NDK tx') _)) -> throwError . TM $
          D.TypeMismatch f txDhall x (fromDKind (fromPolySing tx'))
        SomeDExpr (DETerm (SomeTerm (NDT tx') _)) -> throwError . TM $
          D.TypeMismatch f txDhall x (fromDType (fromPolySing tx'))
      pure . SomeDExpr . DEKind $ SomeKind ty (KApp f' x')
    SomeDExpr (DEType (SomeType (NDK tf) f')) -> case skNormalize tf of
      (tx :: SDKind ts 'Kind tx) :%~> (ty :: SDKind ts 'Kind ty) -> do
        let txDhall = fromDKind . fromPolySing $ tx
        liftEF (toTyped ctx x) >>= \case
          SomeDExpr DEOrder -> throwError . TM $ D.Untyped
          SomeDExpr (DESort _) -> throwError . TM $
            D.TypeMismatch f txDhall x (D.Const D.Sort)
          SomeDExpr (DEKind (SomeKind tx' _)) -> throwError . TM $
            D.TypeMismatch f txDhall x (fromDSort (fromPolySing tx'))
          SomeDExpr (DEType (SomeType (NDK tx') x')) -> do
            Proved HRefl <- pure (singEq tx (skNormalize tx')) <?> TM
              (D.TypeMismatch f txDhall x (fromDKind (fromPolySing tx')))
            pure . SomeDExpr . DEType . SomeType (NDK ty) . normalizeKindOf $
              TApp f' x'
          SomeDExpr (DETerm (SomeTerm (NDT tx') _)) -> throwError . TM $
            D.TypeMismatch f txDhall x (fromDType (fromPolySing tx'))
      SKPi (SiSi tt) (tx :: SDKind (t ': ts) 'Kind tx) -> do
        let ttDhall = fromDSort . fromPolySing $ tt
        liftEF (toTyped ctx x) >>= \case
          SomeDExpr DEOrder -> throwError . TM $ D.Untyped
          SomeDExpr (DESort _) -> throwError . TM $
            D.TypeMismatch f ttDhall x (D.Const D.Sort)
          SomeDExpr (DEKind (SomeKind tx' x')) -> do
            Proved HRefl <- pure (singEq tt tx')
            SomePS x'' <- pure (toPolySing x')
            let subbed = skSub1 x'' tx
            pure . SomeDExpr . DEType .  SomeType (NDK subbed) . normalizeKindOf $
              TInst (SiSi tx') f' (SbKd x'')
          SomeDExpr (DEType (SomeType (NDK tx') _)) -> throwError . TM $
            D.TypeMismatch f ttDhall x (fromDKind (fromPolySing tx'))
          SomeDExpr (DETerm (SomeTerm (NDT tx') _)) -> throwError . TM $
            D.TypeMismatch f ttDhall x (fromDType (fromPolySing tx'))
      -- TODO: what about SKVar?
      _   -> throwError . TM $ D.NotAFunction f (fromDKind (fromPolySing tf))
    SomeDExpr (DETerm (SomeTerm (NDT tf) f')) -> case stNormalize tf of
      (tx :: SDType ts us 'Type tx) :%-> (ty :: SDType ts us 'Type ty) -> do
        let txDhall = fromDType . fromPolySing $ tx
        liftEF (toTyped ctx x) >>= \case
          SomeDExpr DEOrder -> throwError . TM $ D.Untyped
          SomeDExpr (DESort _) -> throwError . TM $
            D.TypeMismatch f txDhall x (D.Const D.Sort)
          SomeDExpr (DEKind (SomeKind tx' _)) -> throwError . TM $
            D.TypeMismatch f txDhall x (fromDSort (fromPolySing tx'))
          SomeDExpr (DEType (SomeType (NDK tx') _)) -> throwError . TM $
            D.TypeMismatch f txDhall x (fromDKind (fromPolySing tx'))
          SomeDExpr (DETerm (SomeTerm (NDT tx') x')) -> do
            Proved HRefl <- pure (singEq tx (stNormalize tx')) <?> TM
              (D.TypeMismatch f txDhall x (fromDType (fromPolySing tx')))
            pure . SomeDExpr . DETerm . SomeTerm (NDT ty) . normalizeTypeOf $
              App f' x'
      -- SPi (SNDK (SiSi tt)) (tx :: SDType ts (u ': us) 'Type tx) -> do
      SPi (SNDK (SiSi tt)) (_ :: SDType ts (u ': us) 'Type tx) -> do
        let ttDhall = fromDKind . fromPolySing $ tt
        liftEF (toTyped ctx x) >>= \case
          SomeDExpr DEOrder -> throwError . TM $ D.Untyped
          SomeDExpr (DESort _) -> throwError . TM $
            D.TypeMismatch f ttDhall x (D.Const D.Sort)
          SomeDExpr (DEKind (SomeKind tx' _)) -> throwError . TM $
            D.TypeMismatch f ttDhall x (fromDSort (fromPolySing tx'))
          SomeDExpr (DEType _) -> undefined
          -- SomeDExpr (DEType (SomeType (NDK tx') x')) -> do
          --   Proved HRefl <- pure (singEq tt (skNormalize tx'))
          --   SomePS x'' <- pure (toPolySing x')
          --   let subbed = sSub1 x'' tx
          --   pure . SomeDExpr . DETerm .  SomeTerm (NDT subbed) . normalizeTypeOf $
          --     Inst (SNDK _) f' x''
          SomeDExpr (DETerm (SomeTerm (NDT tx') _)) -> throwError . TM $
            D.TypeMismatch f ttDhall x (fromDType (fromPolySing tx'))
      -- TODO: what about STVar?
      _   -> throwError . TM $ D.NotAFunction f (fromDType (fromPolySing tf))

fromTyped
    :: DExpr ts us vs n
    -> D.Expr () D.X
fromTyped = \case
    DEOrder               -> D.Const D.Sort
    DESort x              -> fromDSort x
    DEKind (SomeKind _ x) -> fromDKind x
    DEType (SomeType _ x) -> fromDType x
    DETerm (SomeTerm _ x) -> fromDTerm x

fromDTerm
    :: DTerm ts us vs a
    -> D.Expr () D.X
fromDTerm = \case
    Var i -> D.Var $ D.V "v" (fromIntegral (toNatural (indexN i)))
    Lam (NDT t) x -> D.Lam "v" (fromDType (fromPolySing t)) (fromDTerm x)
    App f x -> D.App (fromDTerm f) (fromDTerm x)
    Poly (SNDK (SiSi t)) x -> D.Lam "u" (fromDKind (fromPolySing t)) (fromDTerm x)
    Inst _ f x -> D.App (fromDTerm f) (fromDType (fromPolySing x))
    P p xs -> fromPrim p xs
    ListLit (NDT t) xs -> D.ListLit (Just $ fromDType (fromPolySing t))
                                    (Seq.fromList $ fromDTerm <$> xs)
    OptionalLit (NDT t) xs -> D.OptionalLit (fromDType (fromPolySing t))
                                            (fromDTerm <$> xs)
    RecordLit at xs -> D.RecordLit $ foldMapAggTypeProd
        (\t _ x -> DM.singleton t (fromDTerm x))
        (fromPolySing at) xs
    UnionLit (fromPolySing->at) i x ->
        let l = ixAggTypeLabel i at const
        in  D.UnionLit l (fromDTerm x) $ (`foldMapAggType` at) $ \t y ->
              if t == l
                then mempty
                else DM.singleton t (fromDType y)

fromPrim
    :: Prim ts us as a
    -> Prod (DTerm ts us vs) as
    -> D.Expr () D.X
fromPrim = \case
    BoolLit b -> \_ -> D.BoolLit b
    BoolAnd   -> \case x :< y :< Ø -> D.BoolAnd (fromDTerm x) (fromDTerm y)
    BoolOr    -> \case x :< y :< Ø -> D.BoolOr  (fromDTerm x) (fromDTerm y)
    NaturalLit n -> \_ -> D.NaturalLit n
    NaturalFold -> \_ -> D.NaturalFold
    NaturalBuild -> \_ -> D.NaturalBuild
    NaturalPlus  -> \case x :< y :< Ø -> D.NaturalPlus  (fromDTerm x) (fromDTerm y)
    NaturalTimes -> \case x :< y :< Ø -> D.NaturalTimes (fromDTerm x) (fromDTerm y)
    NaturalIsZero -> \_ -> D.NaturalIsZero
    ListAppend _ -> \case x :< y :< Ø -> D.ListAppend (fromDTerm x) (fromDTerm y)
    ListFold -> \_ -> D.ListFold
    ListBuild -> \_ -> D.ListBuild
    ListHead -> \_ -> D.ListHead
    ListLast -> \_ -> D.ListLast
    ListReverse -> \_ -> D.ListReverse
    Some _ -> \case x :< Ø -> D.Some (fromDTerm x)
    None   -> \_ -> D.None


fromDType
    :: DType ts us a
    -> D.Expr () D.X
fromDType = \case
    TVar i -> D.Var $ D.V "u" (fromIntegral (toNatural (indexN i)))
    TLam (NDK t) x -> D.Lam "u" (fromDKind (fromPolySing t)) (fromDType x)
    TApp f x -> D.App (fromDType f) (fromDType x)
    TPoly (SiSi t) x -> D.Lam "t" (fromDSort (fromPolySing t)) (fromDType x)
    TInst _ f (SbKd x) -> D.App (fromDType f) (fromDKind (fromPolySing x))
    x :-> y -> D.Pi "_" (fromDType x) (fromDType y)
    Pi (NDK t) x -> D.Pi "u" (fromDKind (fromPolySing t)) (fromDType x)
    Bool -> D.Bool
    Natural -> D.Natural
    List -> D.List
    Optional -> D.Optional
    Record at -> D.Record $ (`foldMapAggType` at) $ \t x ->
      DM.singleton t (fromDType x)
    Union  at -> D.Union $ (`foldMapAggType` at) $ \t x ->
      DM.singleton t (fromDType x)
    TRecordLit at xs -> D.RecordLit $ foldMapAggTypeProd
        (\t _ x -> DM.singleton t (fromDType x))
        (fromPolySing at) xs
    TUnionLit (fromPolySing->at) i x ->
        let l = ixAggTypeLabel i at const
        in  D.UnionLit l (fromDType x) $ (`foldMapAggType` at) $ \t y ->
              if t == l
                then mempty
                else DM.singleton t (fromDKind y)

fromDKind
    :: DKind ts a
    -> D.Expr () D.X
fromDKind = \case
    KVar i  -> D.Var $ D.V "t" (fromIntegral (toNatural (indexN i)))
    KLam t x -> D.Lam "t" (fromDSort (fromPolySing t)) (fromDKind x)
    KApp f x -> D.App (fromDKind f) (fromDKind x)
    KPi t x -> D.Pi "t" (fromDSort (fromPolySing t)) (fromDKind x)
    Type    -> D.Const D.Type
    x :~> y -> D.Pi "_" (fromDKind x) (fromDKind y)
    TRecord at -> D.Record $ (`foldMapAggType` at) $ \t x ->
      DM.singleton t (fromDKind x)
    TUnion  at -> D.Union $ (`foldMapAggType` at) $ \t x ->
      DM.singleton t (fromDKind x)
    KRecordLit at xs -> D.RecordLit $ foldMapAggTypeProd
        (\t _ x -> DM.singleton t (fromDKind x))
        (fromPolySing at) xs
    KUnionLit (fromPolySing->at) i x ->
        let l = ixAggTypeLabel i at const
        in  D.UnionLit l (fromDKind x) $ (`foldMapAggType` at) $ \t y ->
              if t == l
                then mempty
                else DM.singleton t (fromDSort y)

fromDSort
    :: DSort
    -> D.Expr () D.X
fromDSort = \case
    Kind -> D.Const D.Kind
    x :*> y -> D.Pi "_" (fromDSort x) (fromDSort y)
    KRecord at -> D.Record $ (`foldMapAggType` at) $ \t x ->
      DM.singleton t (fromDSort x)
    KUnion  at -> D.Union $ (`foldMapAggType` at) $ \t x ->
      DM.singleton t (fromDSort x)

ixAggTypeLabel
    :: PolySingKind k
    => Index as a
    -> AggType k ls as
    -> (Text -> k -> r)
    -> r
ixAggTypeLabel = \case
    IZ -> \case
      ATS l (WS x) _ -> \f -> f (fromPolySing l) (fromPolySing x)
    IS i -> \case
      ATS _ _ xs -> ixAggTypeLabel i xs

foldMapAggType
    :: forall k ls as m. (PolySingKind k, Monoid m)
    => (Text -> k -> m)
    -> AggType k ls as
    -> m
foldMapAggType f = go
  where
    go :: AggType k ms bs -> m
    go = \case
      ATZ -> mempty
      ATS l (WS x) xs -> f (fromPolySing l) (fromPolySing x) <> go xs

foldMapAggTypeProd
    :: forall k ls as f m. Monoid m
    => (forall a. Text -> PolySing k a -> f a -> m)
    -> AggType k ls as
    -> Prod f as
    -> m
foldMapAggTypeProd f = go
  where
    go :: AggType k ms bs -> Prod f bs -> m
    go = \case
      ATZ -> \case
        Ø -> mempty
      ATS l (WS x) xs -> \case
        y :< ys -> f (fromPolySing l) x y <> go xs ys


-- -- | Syntax tree for expressions
-- data Expr s a
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
--     | ListHead
--     | ListLast
--     | ListIndexed
--     | ListReverse
--     | Optional
--     | OptionalLit (Expr s a) (Maybe (Expr s a))
--     | Some (Expr s a)
--     | None
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
--     deriving (Eq, Foldable, Generic, Traversable, Show, Data)






--fromTypedKind
--    :: DKind
--    -> D.Expr s D.X
--fromTypedKind = \case
--    Type    -> D.Const D.Type
--    a :~> b -> D.Pi "_" (fromTypedKind a) (fromTypedKind b)

--fromTypedType
--    :: DType us k
--    -> D.Expr s D.X
--fromTypedType = undefined

--fromTypedTerm
--    :: DTerm us vs a
--    -> D.Expr s D.X
--fromTypedTerm = undefined

---- | Convert an untyped Dhall expression representing a kind into a 'DKind'.
----
---- Will fail if:
----
---- *  The Dhall expression does not represent a kind
---- *  Any kind variables are involved.  Kind variables are not yet
----    supported!  But there is no fundamental reason why they wouldn't be;
----    they just have not been implemented yet.
----
---- Will behave unpredictably if the Dhall expression does not typecheck
---- within Dhall itself.
--toTypedKind
--    :: TermCtx us vs
--    -> D.Expr () D.X
--    -> Maybe DKind
--toTypedKind ctx = \case
--    D.Const D.Type -> Just Type
--    D.Pi v t y     -> (:~>) <$> toTypedKind ctx t
--                            <*> toTypedKind (ConsSort v t ctx) y
----     | Let (NonEmpty (Binding s a)) (Expr s a)
--    D.Note _ x -> toTypedKind ctx x
--    D.Embed x  -> D.absurd x
--    _          -> Nothing



---- | Convert an untyped Dhall expression into a typed one representing
---- a Dhall type of a desired kind.
----
---- Will fail if:
----
---- *  The Dhall expression does not represent a type
---- *  The kind does not match
---- *  Any kind variables are involved.  Kind variables are not yet
----    supported!  But there is no fundamental reason why they wouldn't be;
----    they just have not been implemented yet.
----
---- Will behave unpredictably if the Dhall expression does not typecheck
---- within Dhall itself.
--toTypedType
--    :: SDKind k
--    -> TermCtx us vs                -- ^ kinds and types of free variables
--    -> D.Expr () D.X
--    -> Maybe (DType us k)
--toTypedType k us = \case
----     | Var Var
----     | Lam Text (Expr s a) (Expr s a)
----     | Pi  Text (Expr s a) (Expr s a)
----     | App (Expr s a) (Expr s a)
----     | Let (NonEmpty (Binding s a)) (Expr s a)
----     | Annot (Expr s a) (Expr s a)
--    D.Annot x _ -> toTypedType k us x
--    D.Bool     -> kindcheckType k Bool
--    D.Natural  -> kindcheckType k Natural
----     | Integer
----     | Double
----     | Text
--    D.List     -> kindcheckType k List
--    D.Optional -> kindcheckType k Optional
----     | Record    (Map Text (Expr s a))
----     | RecordLit (Map Text (Expr s a))
----     | Union     (Map Text (Expr s a))
----     | UnionLit Text (Expr s a) (Map Text (Expr s a))
----     | CombineTypes (Expr s a) (Expr s a)
----     | Combine (Expr s a) (Expr s a)
----     | Prefer (Expr s a) (Expr s a)
----     | Merge (Expr s a) (Expr s a) (Maybe (Expr s a))
----     | Field (Expr s a) Text
----     | Project (Expr s a) (Set Text)
----     | Constructors (Expr s a)
----     | Note s (Expr s a)
----     | ImportAlt (Expr s a) (Expr s a)
----     | Embed a
--    _ -> Nothing

--kindcheckType
--    :: forall a b us. SDKindI b
--    => SDKind a
--    -> DType us b
--    -> Maybe (DType us a)
--kindcheckType a x = case sameDKind a (sdKind @b) of
--    Just Refl -> Just x
--    Nothing   -> Nothing


--data TermCtx us :: [DType us 'Type] -> Type where
--    TCtxNil   :: TermCtx '[] '[]
--    -- | Not supported, but might be one day.
--    ConsSort  :: Text
--              -> D.Expr () D.X    -- ^ we have to keep original sort, since we can't synthesize it
--              -> TermCtx us vs
--              -> TermCtx us vs
--    ConsKind  :: Text
--              -> SDKind u
--              -> TermCtx us vs
--              -> TermCtx (u ': us) (MapShift u us vs)
--    ConsType  :: Text
--              -> SDType us 'Type v
--              -> TermCtx us vs
--              -> TermCtx us (v ': vs)

--data TermCtxItem us :: [DType us 'Type] -> Type where
--    TCISort :: D.Expr () D.X -> TermCtxItem us vs
--    TCIKind :: Index us u -> SDKind u          -> TermCtxItem us vs
--    TCIType :: Index vs v -> SDType us 'Type v -> TermCtxItem us vs

--ctxKinds :: TermCtx us vs -> Prod SDKind us
--ctxKinds = \case
--    TCtxNil         -> Ø
--    ConsSort _ _ us -> ctxKinds us
--    ConsKind _ u us -> u :< ctxKinds us
--    ConsType _ _ us -> ctxKinds us

--ctxTypes :: TermCtx us vs -> Prod (SDType us 'Type) vs
--ctxTypes = \case
--    TCtxNil         -> Ø
--    ConsSort _ _ vs -> ctxTypes vs
--    ConsKind _ _ vs -> shiftProd $ ctxTypes vs
--    ConsType _ v vs -> v :< ctxTypes vs

--toContext :: TermCtx us vs -> D.Context (D.Expr () D.X)
--toContext = \case
--    TCtxNil         -> D.empty
--    ConsSort t x vs -> D.insert t x $ toContext vs
--    ConsKind t x vs -> D.insert t (fromTypedKind (fromSing (SDK  x))) $ toContext vs
--    ConsType t x vs -> D.insert t (fromTypedType (fromSing (SDTy x))) $ toContext vs

--lookupCtx
--    :: Text
--    -> Integer
--    -> TermCtx us vs
--    -> Maybe (TermCtxItem us vs)
--lookupCtx v = go
--  where
--    go :: Integer -> TermCtx qs rs -> Maybe (TermCtxItem qs rs)
--    go i = \case
--      TCtxNil       -> Nothing
--      ConsSort t e vs ->
--        let descend j = go j vs
--        in  case (v == t, i <= 0) of
--              (False, _    ) -> descend i
--              (True , False) -> descend (i - 1)
--              (True , True ) -> Just (TCISort e)
--      ConsKind t k vs ->
--        let descend j = go j vs <&> \case
--              TCISort e   -> TCISort e
--              TCIKind l a -> TCIKind (IS l)           a
--              TCIType l a -> TCIType (shiftIndex k l) (sShift a)
--        in  case (v == t, i <= 0) of
--              (False, _    ) -> descend i
--              (True , False) -> descend (i - 1)
--              (True , True ) -> Just (TCIKind IZ k)
--      ConsType t x vs ->
--        let descend j = go j vs <&> \case
--              TCISort e   -> TCISort e
--              TCIKind l a -> TCIKind l      a
--              TCIType l a -> TCIType (IS l) a
--        in  case (v == t, i <= 0) of
--              (False, _    ) -> descend i
--              (True , False) -> descend (i - 1)
--              (True , True ) -> Just (TCIType IZ x)

--shiftIndex
--    :: SDKind u
--    -> Index vs v
--    -> Index (MapShift u us vs) (Shift us (u ': us) u 'Type 'InsZ v)
--shiftIndex u = \case
--    IZ   -> IZ
--    IS i -> IS (shiftIndex u i)

---- | Find the 'DType' corresponding to the type of the Dhall expression
---- representing a term.
----
---- Will fail if:
----
---- *  The Dhall expression does not represent a term
---- *  Any kind variables are involved.  Kind variables are not yet
----    supported!  But there is no fundamental reason why they wouldn't be;
----    they just have not been implemented yet.
----
---- Will behave unpredictably if the Dhall expression does not typecheck
---- within Dhall itself.
--typeOfExpr
--    :: TermCtx us vs
--    -> D.Expr () D.X
--    -> Maybe (DType us 'Type)
--typeOfExpr ctx = toTypedType SType ctx
--             <=< either (const Nothing) Just . D.typeWith (toContext ctx)

---- | Convert an untyped Dhall expression representing a term into a typed
---- one, also determining the type in the process.
----
---- Will fail if:
----
---- *  The Dhall expression does not represent a term
---- *  Any kind variables are involved.  Kind variables are not yet
----    supported!  But there is no fundamental reason why they wouldn't be;
----    they just have not been implemented yet.
----
---- Will behave unpredictably if the Dhall expression does not typecheck.
--toSomeTerm
--    :: TermCtx us vs
--    -> D.Expr () D.X
--    -> Maybe (SomeTerm us vs)
--toSomeTerm ctx x = do
--    FromSing (SDTy a) <- typeOfExpr ctx x
--    x'                <- toTypedTerm a ctx x
--    pure $ SomeTerm a x'


---- | Convert an untyped Dhall expression into a typed one representing
---- a Dhall term of a desired type.
----
---- Will fail if:
----
---- *  The Dhall expression does not represent a term
---- *  The type does not match
---- *  Any kind variables are involved.  Kind variables are not yet
----    supported!  But there is no fundamental reason why they wouldn't be;
----    they just have not been implemented yet.
----
---- Will behave unpredictably if the Dhall expression does not typecheck
---- within Dhall itself.

---- TODO: make this work with unnormalized types.  Maybe we need types to
---- fill in for type variables?
--toTypedTerm
--    :: SDType us 'Type a
--    -> TermCtx us vs                -- ^ kinds and types of free variables
--    -> D.Expr () D.X
--    -> Maybe (DTerm us vs a)
--toTypedTerm a ctx = \case
--    D.Var (D.V v i) -> lookupCtx v i ctx >>= \case
--      TCISort _   -> Nothing    -- kind variables not yet supported
--      TCIKind _ _ -> Nothing    -- we want a term, not a type
--      TCIType j x -> sameDTypeWith us a x <&> \case
--        Refl -> Var j
----     | Lam Text (Expr s a) (Expr s a)
--    D.App f x -> do
--      SomeTerm b x' <- toSomeTerm ctx x
--      f'            <- toTypedTerm (b :%-> a) ctx f
--      pure $ App f' x'
----     | Let (NonEmpty (Binding s a)) (Expr s a)
--    D.Annot x _  -> toTypedTerm a ctx x
--    D.BoolLit b  -> typecheckTerm us a $ BoolLit b
----     | BoolAnd (Expr s a) (Expr s a)
----     | BoolOr  (Expr s a) (Expr s a)
----     | BoolEQ  (Expr s a) (Expr s a)
----     | BoolNE  (Expr s a) (Expr s a)
----     | BoolIf (Expr s a) (Expr s a) (Expr s a)
--    D.NaturalLit n  -> typecheckTerm us a $ NaturalLit n
--    D.NaturalFold   -> typecheckTerm us a $ NaturalFold
--    D.NaturalBuild  -> typecheckTerm us a $ NaturalBuild
--    D.NaturalIsZero -> typecheckTerm us a $ NaturalIsZero
----     | NaturalEven
----     | NaturalOdd
----     | NaturalToInteger
----     | NaturalShow
--    D.NaturalPlus x y -> do
--      Refl <- sameDTypeWith us a SNatural
--      x'   <- toTypedTerm SNatural ctx x
--      y'   <- toTypedTerm SNatural ctx y
--      pure $ NaturalPlus x' y'
--    D.NaturalTimes x y -> do
--      Refl <- sameDTypeWith us a SNatural
--      x'   <- toTypedTerm SNatural ctx x
--      y'   <- toTypedTerm SNatural ctx y
--      pure $ NaturalTimes x' y'
----     | IntegerLit Integer
----     | IntegerShow
----     | IntegerToDouble
----     | DoubleLit Double
----     | DoubleShow
----     | TextLit (Chunks s a)
----     | TextAppend (Expr s a) (Expr s a)
--    D.ListLit _ xs -> do
--      SList :%$ b <- Just a
--      xs' <- traverse (toTypedTerm b ctx) xs
--      pure $ ListLit b xs'
--    D.ListAppend xs ys -> do
--      SList :%$ _ <- Just a
--      xs' <- toTypedTerm a ctx xs
--      ys' <- toTypedTerm a ctx ys
--      pure $ ListAppend xs' ys'
--    D.ListBuild   -> typecheckTerm us a $ ListBuild
--    D.ListFold    -> typecheckTerm us a $ ListFold
--    D.ListHead    -> typecheckTerm us a $ ListHead
--    D.ListLast    -> typecheckTerm us a $ ListLast
--    D.ListReverse -> typecheckTerm  us a $ ListReverse
--    D.OptionalLit _ xs -> do
--      SOptional :%$ b <- Just a
--      xs' <- traverse (toTypedTerm b ctx) xs
--      pure $ OptionalLit b xs'
----     | OptionalFold
----     | OptionalBuild
--    D.Some x -> do
--      SOptional :%$ b <- Just a
--      x'   <- toTypedTerm b ctx x
--      pure $ Some x'
--    D.None -> typecheckTerm us a None
----     | RecordLit (Map Text (Expr s a))
----     | UnionLit Text (Expr s a) (Map Text (Expr s a))
----     | Combine (Expr s a) (Expr s a)
----     | Prefer (Expr s a) (Expr s a)
----     | Merge (Expr s a) (Expr s a) (Maybe (Expr s a))
----     | Field (Expr s a) Text
----     | Project (Expr s a) (Set Text)
--    D.Note _ x -> toTypedTerm a ctx x   -- note not yet supported
----     | ImportAlt (Expr s a) (Expr s a)
--    D.Embed x  -> D.absurd x            -- embed not yet supported
--    _ -> Nothing
--  where
--    us = ctxKinds ctx
--    -- vs = ctxTypes ctx

--typecheckTerm
--    :: forall us vs a b. SDTypeI us 'Type b
--    => Prod SDKind us
--    -> SDType us 'Type a
--    -> DTerm us vs b
--    -> Maybe (DTerm us vs a)
--typecheckTerm us a x = case sameDTypeWith us a (sdType :: SDType us 'Type b) of
--    Just Refl -> Just x
--    Nothing   -> Nothing




---- | The identity function, encoded as a 'DTerm'.  Provided as an example.
--ident :: DTerm us vs ('Pi 'SType ('TVar 'IZ ':-> 'TVar 'IZ))
--ident = TLam SType $ Lam (STVar SIZ) (Var IZ)

---- | The constant function, encoded as a 'DTerm'.  Provided as an example.
---- All of the multi-Pi functions here require the typechecker plugin.
--konst :: DTerm us vs ('Pi 'SType ('Pi 'SType ('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar ('IS 'IZ))))
--konst = TLam SType $
--          TLam SType $
--            Lam (STVar (SIS SIZ)) $
--              Lam (STVar SIZ) (Var (IS IZ))

---- | The constant function with flipped parameter order, encoded as
---- a 'DTerm'.  Provided as an example.
--konst' :: DTerm us vs ('Pi 'SType ('TVar 'IZ ':-> 'Pi 'SType ('TVar 'IZ ':-> 'TVar ('IS 'IZ))))
--konst' = TLam SType $
--           Lam (STVar SIZ) $
--             TLam SType $
--               Lam (STVar SIZ) $
--                 Var (IS IZ)


---- | The constant function with three inputs, encoded as a 'DTerm'.
---- Provided as an example.
--konst3 :: DTerm us vs ('Pi 'SType ('Pi 'SType ('Pi 'SType ('TVar ('IS ('IS 'IZ)) ':-> 'TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar ('IS ('IS 'IZ))))))
--konst3 = TLam SType $
--           TLam SType $
--             TLam SType $
--                Lam (STVar (SIS (SIS SIZ))) $
--                  Lam (STVar (SIS SIZ)) $
--                    Lam (STVar SIZ) $
--                      Var (IS (IS IZ))

---- | The constant function with four inputs, encoded as a 'DTerm'.
---- Provided as an example.
--konst4 :: DTerm us vs ('Pi 'SType ('Pi 'SType ('Pi 'SType ('Pi 'SType ('TVar ('IS ('IS ('IS 'IZ))) ':-> 'TVar ('IS ('IS 'IZ)) ':-> 'TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar ('IS ('IS ('IS 'IZ))))))))
--konst4 = TLam SType $
--           TLam SType $
--             TLam SType $
--               TLam SType $
--                 Lam (STVar (SIS (SIS (SIS SIZ)))) $
--                   Lam (STVar (SIS (SIS SIZ))) $
--                     Lam (STVar (SIS SIZ)) $
--                       Lam (STVar SIZ) $
--                         Var (IS (IS (IS IZ)))


---- | @Natural/build@, encoded as a 'DTerm'.  Provided as an example.
--natBuild
--    :: DTerm us vs ('Pi 'SType (('TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'Natural)
--natBuild = Lam (SPi SType ((STVar SIZ :%-> STVar SIZ) :%-> STVar SIZ :%-> STVar SIZ)) $
--             Var IZ
--      `TApp` SNatural
--       `App` Lam SNatural (NaturalPlus (Var IZ) (NaturalLit 1))
--       `App` NaturalLit 0

---- | @List/build@, encoded as a 'DTerm'.  Provided as an example.
--listBuild
--    :: DTerm us vs ('Pi 'SType ('Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'List ':$ 'TVar 'IZ))
--listBuild = TLam SType $
--    Lam (SPi SType ((STVar (SIS SIZ) :%-> STVar SIZ :%-> STVar SIZ) :%-> STVar SIZ :%-> STVar SIZ)) $
--            Var IZ
--     `TApp` (SList :%$ STVar SIZ)
--      `App` Lam (STVar SIZ) (
--              Lam (SList :%$ STVar SIZ) (
--                ListLit (STVar SIZ) (Seq.singleton (Var (IS IZ))) `ListAppend` Var IZ
--              )
--            )
--      `App` ListLit (STVar SIZ) Seq.empty

