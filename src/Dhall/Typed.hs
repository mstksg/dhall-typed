{-# LANGUAGE EmptyCase                      #-}
{-# LANGUAGE FlexibleContexts               #-}
{-# LANGUAGE GADTs                          #-}
{-# LANGUAGE LambdaCase                     #-}
{-# LANGUAGE OverloadedStrings              #-}
{-# LANGUAGE ScopedTypeVariables            #-}
{-# LANGUAGE TypeApplications               #-}
{-# LANGUAGE TypeInType                     #-}
{-# LANGUAGE TypeOperators                  #-}
{-# OPTIONS_GHC -fplugin Dhall.Typed.Plugin #-}

module Dhall.Typed (
  -- * Conversion
    toTypedType, toTypedTerm, toSomeTerm
  , fromTypedKind, fromTypedType, fromTypedTerm
  -- * Convenience
  , kindcheckType, typecheckTerm
  -- * Samples
  , ident, konst, konst', konst3, konst4, natBuild, listBuild
  ) where

import           Control.Monad
import           Data.Functor
import           Data.Kind
import           Data.Sequence      (Seq(..))
import           Data.Singletons
import           Data.Text          (Text)
import           Data.Type.Equality
import           Dhall.Typed.Core
import           Dhall.Typed.Index
import           Dhall.Typed.Prod
import qualified Data.Sequence      as Seq
import qualified Data.Text          as T
import qualified Dhall.Context      as D
import qualified Dhall.Core         as D
import qualified Dhall.TypeCheck    as D

fromTypedKind
    :: DKind
    -> D.Expr s D.X
fromTypedKind = \case
    Type    -> D.Const D.Type
    a :~> b -> D.Pi "_" (fromTypedKind a) (fromTypedKind b)

fromTypedType
    :: DType us k
    -> D.Expr s D.X
fromTypedType = undefined

fromTypedTerm
    :: DTerm us vs a
    -> D.Expr s D.X
fromTypedTerm = undefined

-- | Convert an untyped Dhall expression representing a kind into a 'DKind'.
--
-- Will fail if:
--
-- *  The Dhall expression does not represent a kind
-- *  Any kind variables are involved.  Kind variables are not yet
--    supported!  But there is no fundamental reason why they wouldn't be;
--    they just have not been implemented yet.
--
-- Will behave unpredictably if the Dhall expression does not typecheck
-- within Dhall itself.
toTypedKind
    :: TermCtx us vs
    -> D.Expr () D.X
    -> Maybe DKind
toTypedKind ctx = \case
    D.Const D.Type -> Just Type
    D.Pi v t y     -> (:~>) <$> toTypedKind ctx t
                            <*> toTypedKind (ConsSort v t ctx) y
--     | Let (NonEmpty (Binding s a)) (Expr s a)
    D.Note _ x -> toTypedKind ctx x
    D.Embed x  -> D.absurd x
    _          -> Nothing



-- | Convert an untyped Dhall expression into a typed one representing
-- a Dhall type of a desired kind.
--
-- Will fail if:
--
-- *  The Dhall expression does not represent a type
-- *  The kind does not match
-- *  Any kind variables are involved.  Kind variables are not yet
--    supported!  But there is no fundamental reason why they wouldn't be;
--    they just have not been implemented yet.
--
-- Will behave unpredictably if the Dhall expression does not typecheck
-- within Dhall itself.
toTypedType
    :: SDKind k
    -> TermCtx us vs                -- ^ kinds and types of free variables
    -> D.Expr () D.X
    -> Maybe (DType us k)
toTypedType k us = \case
--     | Var Var
--     | Lam Text (Expr s a) (Expr s a)
--     | Pi  Text (Expr s a) (Expr s a)
--     | App (Expr s a) (Expr s a)
--     | Let (NonEmpty (Binding s a)) (Expr s a)
--     | Annot (Expr s a) (Expr s a)
    D.Annot x _ -> toTypedType k us x
    D.Bool     -> kindcheckType k Bool
    D.Natural  -> kindcheckType k Natural
--     | Integer
--     | Double
--     | Text
    D.List     -> kindcheckType k List
    D.Optional -> kindcheckType k Optional
--     | Record    (Map Text (Expr s a))
--     | RecordLit (Map Text (Expr s a))
--     | Union     (Map Text (Expr s a))
--     | UnionLit Text (Expr s a) (Map Text (Expr s a))
--     | CombineTypes (Expr s a) (Expr s a)
--     | Combine (Expr s a) (Expr s a)
--     | Prefer (Expr s a) (Expr s a)
--     | Merge (Expr s a) (Expr s a) (Maybe (Expr s a))
--     | Field (Expr s a) Text
--     | Project (Expr s a) (Set Text)
--     | Constructors (Expr s a)
--     | Note s (Expr s a)
--     | ImportAlt (Expr s a) (Expr s a)
--     | Embed a
    _ -> Nothing

kindcheckType
    :: forall a b us. SDKindI b
    => SDKind a
    -> DType us b
    -> Maybe (DType us a)
kindcheckType a x = case sameDKind a (sdKind @b) of
    Just Refl -> Just x
    Nothing   -> Nothing


data TermCtx us :: [DType us 'Type] -> Type where
    TCtxNil   :: TermCtx '[] '[]
    -- | Not supported, but might be one day.
    ConsSort  :: Text
              -> D.Expr () D.X    -- ^ we have to keep original sort, since we can't synthesize it
              -> TermCtx us vs
              -> TermCtx us vs
    ConsKind  :: Text
              -> SDKind u
              -> TermCtx us vs
              -> TermCtx (u ': us) (MapShift u us vs)
    ConsType  :: Text
              -> SDType us 'Type v
              -> TermCtx us vs
              -> TermCtx us (v ': vs)

data TermCtxItem us :: [DType us 'Type] -> Type where
    TCISort :: D.Expr () D.X -> TermCtxItem us vs
    TCIKind :: Index us u -> SDKind u          -> TermCtxItem us vs
    TCIType :: Index vs v -> SDType us 'Type v -> TermCtxItem us vs

ctxKinds :: TermCtx us vs -> Prod SDKind us
ctxKinds = \case
    TCtxNil         -> Ø
    ConsSort _ _ us -> ctxKinds us
    ConsKind _ u us -> u :< ctxKinds us
    ConsType _ _ us -> ctxKinds us

ctxTypes :: TermCtx us vs -> Prod (SDType us 'Type) vs
ctxTypes = \case
    TCtxNil         -> Ø
    ConsSort _ _ vs -> ctxTypes vs
    ConsKind _ _ vs -> shiftProd $ ctxTypes vs
    ConsType _ v vs -> v :< ctxTypes vs

toContext :: TermCtx us vs -> D.Context (D.Expr () D.X)
toContext = \case
    TCtxNil         -> D.empty
    ConsSort t x vs -> D.insert t x $ toContext vs
    ConsKind t x vs -> D.insert t (fromTypedKind (fromSing (SDK  x))) $ toContext vs
    ConsType t x vs -> D.insert t (fromTypedType (fromSing (SDTy x))) $ toContext vs

lookupCtx
    :: Text
    -> Integer
    -> TermCtx us vs
    -> Maybe (TermCtxItem us vs)
lookupCtx v = go
  where
    go :: Integer -> TermCtx qs rs -> Maybe (TermCtxItem qs rs)
    go i = \case
      TCtxNil       -> Nothing
      ConsSort t e vs ->
        let descend j = go j vs
        in  case (v == t, i <= 0) of
              (False, _    ) -> descend i
              (True , False) -> descend (i - 1)
              (True , True ) -> Just (TCISort e)
      ConsKind t k vs ->
        let descend j = go j vs <&> \case
              TCISort e   -> TCISort e
              TCIKind l a -> TCIKind (IS l)           a
              TCIType l a -> TCIType (shiftIndex k l) (sShift a)
        in  case (v == t, i <= 0) of
              (False, _    ) -> descend i
              (True , False) -> descend (i - 1)
              (True , True ) -> Just (TCIKind IZ k)
      ConsType t x vs ->
        let descend j = go j vs <&> \case
              TCISort e   -> TCISort e
              TCIKind l a -> TCIKind l      a
              TCIType l a -> TCIType (IS l) a
        in  case (v == t, i <= 0) of
              (False, _    ) -> descend i
              (True , False) -> descend (i - 1)
              (True , True ) -> Just (TCIType IZ x)

shiftIndex
    :: SDKind u
    -> Index vs v
    -> Index (MapShift u us vs) (Shift us (u ': us) u 'Type 'InsZ v)
shiftIndex u = \case
    IZ   -> IZ
    IS i -> IS (shiftIndex u i)

-- | Find the 'DType' corresponding to the type of the Dhall expression
-- representing a term.
--
-- Will fail if:
--
-- *  The Dhall expression does not represent a term
-- *  Any kind variables are involved.  Kind variables are not yet
--    supported!  But there is no fundamental reason why they wouldn't be;
--    they just have not been implemented yet.
--
-- Will behave unpredictably if the Dhall expression does not typecheck
-- within Dhall itself.
typeOfExpr
    :: TermCtx us vs
    -> D.Expr () D.X
    -> Maybe (DType us 'Type)
typeOfExpr ctx = toTypedType SType ctx
             <=< either (const Nothing) Just . D.typeWith (toContext ctx)

-- | Convert an untyped Dhall expression representing a term into a typed
-- one, also determining the type in the process.
--
-- Will fail if:
--
-- *  The Dhall expression does not represent a term
-- *  Any kind variables are involved.  Kind variables are not yet
--    supported!  But there is no fundamental reason why they wouldn't be;
--    they just have not been implemented yet.
--
-- Will behave unpredictably if the Dhall expression does not typecheck.
toSomeTerm
    :: TermCtx us vs
    -> D.Expr () D.X
    -> Maybe (SomeTerm us vs)
toSomeTerm ctx x = do
    FromSing (SDTy a) <- typeOfExpr ctx x
    x'                <- toTypedTerm a ctx x
    pure $ SomeTerm a x'


-- | Convert an untyped Dhall expression into a typed one representing
-- a Dhall term of a desired type.
--
-- Will fail if:
--
-- *  The Dhall expression does not represent a term
-- *  The type does not match
-- *  Any kind variables are involved.  Kind variables are not yet
--    supported!  But there is no fundamental reason why they wouldn't be;
--    they just have not been implemented yet.
--
-- Will behave unpredictably if the Dhall expression does not typecheck
-- within Dhall itself.

-- TODO: make this work with unnormalized types.  Maybe we need types to
-- fill in for type variables?
toTypedTerm
    :: SDType us 'Type a
    -> TermCtx us vs                -- ^ kinds and types of free variables
    -> D.Expr () D.X
    -> Maybe (DTerm us vs a)
toTypedTerm a ctx = \case
    D.Var (D.V v i) -> lookupCtx v i ctx >>= \case
      TCISort _   -> Nothing    -- kind variables not yet supported
      TCIKind _ _ -> Nothing    -- we want a term, not a type
      TCIType j x -> sameDTypeWith us a x <&> \case
        Refl -> Var j
--     | Lam Text (Expr s a) (Expr s a)
    D.App f x -> do
      SomeTerm b x' <- toSomeTerm ctx x
      f'            <- toTypedTerm (b :%-> a) ctx f
      pure $ App f' x'
--     | Let (NonEmpty (Binding s a)) (Expr s a)
    D.Annot x _  -> toTypedTerm a ctx x
    D.BoolLit b  -> typecheckTerm us a $ BoolLit b
--     | BoolAnd (Expr s a) (Expr s a)
--     | BoolOr  (Expr s a) (Expr s a)
--     | BoolEQ  (Expr s a) (Expr s a)
--     | BoolNE  (Expr s a) (Expr s a)
--     | BoolIf (Expr s a) (Expr s a) (Expr s a)
    D.NaturalLit n  -> typecheckTerm us a $ NaturalLit n
    D.NaturalFold   -> typecheckTerm us a $ NaturalFold
    D.NaturalBuild  -> typecheckTerm us a $ NaturalBuild
    D.NaturalIsZero -> typecheckTerm us a $ NaturalIsZero
--     | NaturalEven
--     | NaturalOdd
--     | NaturalToInteger
--     | NaturalShow
    D.NaturalPlus x y -> do
      Refl <- sameDTypeWith us a SNatural
      x'   <- toTypedTerm SNatural ctx x
      y'   <- toTypedTerm SNatural ctx y
      pure $ NaturalPlus x' y'
    D.NaturalTimes x y -> do
      Refl <- sameDTypeWith us a SNatural
      x'   <- toTypedTerm SNatural ctx x
      y'   <- toTypedTerm SNatural ctx y
      pure $ NaturalTimes x' y'
--     | IntegerLit Integer
--     | IntegerShow
--     | IntegerToDouble
--     | DoubleLit Double
--     | DoubleShow
--     | TextLit (Chunks s a)
--     | TextAppend (Expr s a) (Expr s a)
    D.ListLit _ xs -> do
      SList :%$ b <- Just a
      xs' <- traverse (toTypedTerm b ctx) xs
      pure $ ListLit b xs'
    D.ListAppend xs ys -> do
      SList :%$ _ <- Just a
      xs' <- toTypedTerm a ctx xs
      ys' <- toTypedTerm a ctx ys
      pure $ ListAppend xs' ys'
    D.ListBuild   -> typecheckTerm us a $ ListBuild
    D.ListFold    -> typecheckTerm us a $ ListFold
    D.ListHead    -> typecheckTerm us a $ ListHead
    D.ListLast    -> typecheckTerm us a $ ListLast
    D.ListReverse -> typecheckTerm  us a $ ListReverse
    D.OptionalLit _ xs -> do
      SOptional :%$ b <- Just a
      xs' <- traverse (toTypedTerm b ctx) xs
      pure $ OptionalLit b xs'
--     | OptionalFold
--     | OptionalBuild
    D.Some x -> do
      SOptional :%$ b <- Just a
      x'   <- toTypedTerm b ctx x
      pure $ Some x'
    D.None -> typecheckTerm us a None
--     | RecordLit (Map Text (Expr s a))
--     | UnionLit Text (Expr s a) (Map Text (Expr s a))
--     | Combine (Expr s a) (Expr s a)
--     | Prefer (Expr s a) (Expr s a)
--     | Merge (Expr s a) (Expr s a) (Maybe (Expr s a))
--     | Field (Expr s a) Text
--     | Project (Expr s a) (Set Text)
    D.Note _ x -> toTypedTerm a ctx x   -- note not yet supported
--     | ImportAlt (Expr s a) (Expr s a)
    D.Embed x  -> D.absurd x            -- embed not yet supported
    _ -> Nothing
  where
    us = ctxKinds ctx
    -- vs = ctxTypes ctx

typecheckTerm
    :: forall us vs a b. SDTypeI us 'Type b
    => Prod SDKind us
    -> SDType us 'Type a
    -> DTerm us vs b
    -> Maybe (DTerm us vs a)
typecheckTerm us a x = case sameDTypeWith us a (sdType :: SDType us 'Type b) of
    Just Refl -> Just x
    Nothing   -> Nothing




-- | The identity function, encoded as a 'DTerm'.  Provided as an example.
ident :: DTerm us vs ('Pi 'SType ('TVar 'IZ ':-> 'TVar 'IZ))
ident = TLam SType $ Lam (STVar SIZ) (Var IZ)

-- | The constant function, encoded as a 'DTerm'.  Provided as an example.
-- All of the multi-Pi functions here require the typechecker plugin.
konst :: DTerm us vs ('Pi 'SType ('Pi 'SType ('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar ('IS 'IZ))))
konst = TLam SType $
          TLam SType $
            Lam (STVar (SIS SIZ)) $
              Lam (STVar SIZ) (Var (IS IZ))

-- | The constant function with flipped parameter order, encoded as
-- a 'DTerm'.  Provided as an example.
konst' :: DTerm us vs ('Pi 'SType ('TVar 'IZ ':-> 'Pi 'SType ('TVar 'IZ ':-> 'TVar ('IS 'IZ))))
konst' = TLam SType $
           Lam (STVar SIZ) $
             TLam SType $
               Lam (STVar SIZ) $
                 Var (IS IZ)


-- | The constant function with three inputs, encoded as a 'DTerm'.
-- Provided as an example.
konst3 :: DTerm us vs ('Pi 'SType ('Pi 'SType ('Pi 'SType ('TVar ('IS ('IS 'IZ)) ':-> 'TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar ('IS ('IS 'IZ))))))
konst3 = TLam SType $
           TLam SType $
             TLam SType $
                Lam (STVar (SIS (SIS SIZ))) $
                  Lam (STVar (SIS SIZ)) $
                    Lam (STVar SIZ) $
                      Var (IS (IS IZ))

-- | The constant function with four inputs, encoded as a 'DTerm'.
-- Provided as an example.
konst4 :: DTerm us vs ('Pi 'SType ('Pi 'SType ('Pi 'SType ('Pi 'SType ('TVar ('IS ('IS ('IS 'IZ))) ':-> 'TVar ('IS ('IS 'IZ)) ':-> 'TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar ('IS ('IS ('IS 'IZ))))))))
konst4 = TLam SType $
           TLam SType $
             TLam SType $
               TLam SType $
                 Lam (STVar (SIS (SIS (SIS SIZ)))) $
                   Lam (STVar (SIS (SIS SIZ))) $
                     Lam (STVar (SIS SIZ)) $
                       Lam (STVar SIZ) $
                         Var (IS (IS (IS IZ)))


-- | @Natural/build@, encoded as a 'DTerm'.  Provided as an example.
natBuild
    :: DTerm us vs ('Pi 'SType (('TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'Natural)
natBuild = Lam (SPi SType ((STVar SIZ :%-> STVar SIZ) :%-> STVar SIZ :%-> STVar SIZ)) $
             Var IZ
      `TApp` SNatural
       `App` Lam SNatural (NaturalPlus (Var IZ) (NaturalLit 1))
       `App` NaturalLit 0

-- | @List/build@, encoded as a 'DTerm'.  Provided as an example.
listBuild
    :: DTerm us vs ('Pi 'SType ('Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'List ':$ 'TVar 'IZ))
listBuild = TLam SType $
    Lam (SPi SType ((STVar (SIS SIZ) :%-> STVar SIZ :%-> STVar SIZ) :%-> STVar SIZ :%-> STVar SIZ)) $
            Var IZ
     `TApp` (SList :%$ STVar SIZ)
      `App` Lam (STVar SIZ) (
              Lam (SList :%$ STVar SIZ) (
                ListLit (STVar SIZ) (Seq.singleton (Var (IS IZ))) `ListAppend` Var IZ
              )
            )
      `App` ListLit (STVar SIZ) Seq.empty
