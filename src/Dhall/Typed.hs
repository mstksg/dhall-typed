{-# LANGUAGE GADTs                          #-}
{-# LANGUAGE LambdaCase                     #-}
{-# LANGUAGE TypeInType                     #-}
{-# LANGUAGE TypeOperators                  #-}
{-# OPTIONS_GHC -fplugin Dhall.Typed.Plugin #-}

module Dhall.Typed (
    toTypedType, toTypedTerm
  -- * Samples
  , ident, konst, konst', konst3, konst4, natBuild, listBuild
  ) where

import           Dhall.Typed.Core
import           Dhall.Typed.Index
import qualified Data.Sequence     as Seq
import qualified Dhall.Core        as D
import qualified Dhall.TypeCheck   as D

-- | Convert an untyped Dhall expression into a typed one with no free
-- variables representing a Dhall type of a desired kind.
--
-- Will fail if:
--
-- *  The Dhall expression does not represent a type
-- *  The kind does not match
-- *  There are any free variables
--
-- Will behave unpredictably if the Dhall expression does not typecheck
-- within Dhall itself.
toTypedType
    :: SDKind k
    -> D.Expr () D.X
    -> Maybe (DType '[] k)
toTypedType k = \case
--     | Var Var
--     | Lam Text (Expr s a) (Expr s a)
--     | Pi  Text (Expr s a) (Expr s a)
--     | App (Expr s a) (Expr s a)
--     | Let (NonEmpty (Binding s a)) (Expr s a)
--     | Annot (Expr s a) (Expr s a)
    D.Bool
      | SType <- k -> Just Bool
    D.Natural
      | SType <- k -> Just Natural
--     | Integer
--     | Double
--     | Text
    D.List
      | SType :%~> SType <- k -> Just List
    D.Optional
      | SType :%~> SType <- k -> Just Optional
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


-- | Convert an untyped dhall expression into a typed one representing
-- a Dhall term of a desired type.
--
-- Will fail if:
--
-- *  The Dhall expression does not represent a term
-- *  The type does not match
-- *  There are any free variables
--
-- Will behave unpredictably if the Dhall expression does not typecheck
-- within Dhall itself.
toTypedTerm
    :: SDType '[] 'Type a
    -> D.Expr () D.X
    -> Maybe (DTerm '[] a)
toTypedTerm a = \case
--     | Var Var
--     | Lam Text (Expr s a) (Expr s a)
--     | App (Expr s a) (Expr s a)
--     | Let (NonEmpty (Binding s a)) (Expr s a)
--     | Annot (Expr s a) (Expr s a)
    D.BoolLit b
      | SBool    <- a -> Just $ BoolLit b
--     | BoolAnd (Expr s a) (Expr s a)
--     | BoolOr  (Expr s a) (Expr s a)
--     | BoolEQ  (Expr s a) (Expr s a)
--     | BoolNE  (Expr s a) (Expr s a)
--     | BoolIf (Expr s a) (Expr s a) (Expr s a)
    D.NaturalLit n
      | SNatural <- a -> Just $ NaturalLit n
--     | NaturalFold
--     | NaturalBuild
--     | NaturalIsZero
--     | NaturalEven
--     | NaturalOdd
--     | NaturalToInteger
--     | NaturalShow
--     | NaturalPlus (Expr s a) (Expr s a)
--     | NaturalTimes (Expr s a) (Expr s a)
--     | IntegerLit Integer
--     | IntegerShow
--     | IntegerToDouble
--     | DoubleLit Double
--     | DoubleShow
--     | TextLit (Chunks s a)
--     | TextAppend (Expr s a) (Expr s a)
--     | ListLit (Maybe (Expr s a)) (Seq (Expr s a))
--     | ListAppend (Expr s a) (Expr s a)
--     | ListBuild
--     | ListFold
--     | ListLength
--     | ListIndexed
--     | OptionalFold
--     | OptionalBuild
--     | RecordLit (Map Text (Expr s a))
--     | UnionLit Text (Expr s a) (Map Text (Expr s a))
--     | Combine (Expr s a) (Expr s a)
--     | Prefer (Expr s a) (Expr s a)
--     | Merge (Expr s a) (Expr s a) (Maybe (Expr s a))
--     | Field (Expr s a) Text
--     | Project (Expr s a) (Set Text)
--     | Note s (Expr s a)
--     | ImportAlt (Expr s a) (Expr s a)
--     | Embed a
    _ -> Nothing


-- -- | Syntax tree for expressions
-- data Expr s a
--     deriving (Eq, Foldable, Generic, Traversable, Show, Data)


-- | The identity function, encoded as a 'DTerm'.  Provided as an example.
ident :: DTerm vs ('Pi 'SType ('TVar 'IZ ':-> 'TVar 'IZ))
ident = TLam SType $ \a -> Lam a (Var IZ)

-- | The constant function, encoded as a 'DTerm'.  Provided as an example.
-- All of the multi-Pi functions here require the typechecker plugin.
konst :: DTerm vs ('Pi 'SType ('Pi 'SType ('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar ('IS 'IZ))))
konst = TLam SType $ \a ->
          TLam SType $ \b -> Lam a (Lam b (Var (IS IZ)))

-- | The constant function with flipped parameter order, encoded as
-- a 'DTerm'.  Provided as an example.
konst' :: DTerm vs ('Pi 'SType ('TVar 'IZ ':-> 'Pi 'SType ('TVar 'IZ ':-> 'TVar ('IS 'IZ))))
konst' = TLam SType $ \a ->
    Lam a $ TLam SType $ \b -> Lam b (Var (IS IZ))


-- | The constant function with three inputs, encoded as a 'DTerm'.
-- Provided as an example.
konst3 :: DTerm vs ('Pi 'SType ('Pi 'SType ('Pi 'SType ('TVar ('IS ('IS 'IZ)) ':-> 'TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar ('IS ('IS 'IZ))))))
konst3 = TLam SType $ \a ->
           TLam SType $ \b ->
             TLam SType $ \c ->
                Lam a (Lam b (Lam c (Var (IS (IS IZ)))))

-- | The constant function with four inputs, encoded as a 'DTerm'.
-- Provided as an example.
konst4 :: DTerm vs ('Pi 'SType ('Pi 'SType ('Pi 'SType ('Pi 'SType ('TVar ('IS ('IS ('IS 'IZ))) ':-> 'TVar ('IS ('IS 'IZ)) ':-> 'TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar ('IS ('IS ('IS 'IZ))))))))
konst4 = TLam SType $ \a ->
           TLam SType $ \b ->
             TLam SType $ \c ->
               TLam SType $ \d ->
                 Lam a (Lam b (Lam c (Lam d (Var (IS (IS (IS IZ)))))))


-- | @Natural/build@, encoded as a 'DTerm'.  Provided as an example.
natBuild
    :: DTerm vs ('Pi 'SType (('TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'Natural)
natBuild = Lam (SPi SType ((STVar SIZ :%-> STVar SIZ) :%-> STVar SIZ :%-> STVar SIZ)) $
           Var IZ
    `TApp` SNatural
     `App` Lam SNatural (NaturalPlus (Var IZ) (NaturalLit 1))
     `App` NaturalLit 0

-- there is asymmetry between Lam and TLam.  maybe use type variables to
-- address, instead of functions?

-- | @List/build@, encoded as a 'DTerm'.  Provided as an example.
listBuild
    :: DTerm vs ('Pi 'SType ('Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'List ':$ 'TVar 'IZ))
listBuild = TLam SType $ \a ->
    Lam (SPi SType ((sShift a :%-> STVar SIZ :%-> STVar SIZ) :%-> STVar SIZ :%-> STVar SIZ)) $
            Var IZ
     `TApp` (SList :%$ a)
      `App` Lam a (Lam (SList :%$ a) (ListAppend (ListLit a (Seq.singleton (Var (IS IZ)))) (Var IZ)))
      `App` ListLit a Seq.empty
