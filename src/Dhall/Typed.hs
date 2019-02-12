{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeInType #-}

module Dhall.Typed (
    toTypedTerm
  ) where

import           Dhall.Typed.Core
import qualified Dhall.Core       as D
import qualified Dhall.TypeCheck  as D

toTypedType
    :: SDKind k
    -> D.Expr () D.X
    -> Maybe (DType '[] k)
toTypedType k = \case
    D.Bool
      | SType <- k -> Just Bool
    D.Natural
      | SType <- k -> Just Natural
    D.List
      | SType :%~> SType <- k -> Just List
    D.Optional
      | SType :%~> SType <- k -> Just Optional
    _ -> Nothing


toTypedTerm
    :: SDType '[] 'Type a
    -> D.Expr () D.X
    -> Maybe (DTerm '[] a)
toTypedTerm a = \case
    D.BoolLit b
      | SBool    <- a -> Just $ BoolLit b
    D.NaturalLit n
      | SNatural <- a -> Just $ NaturalLit n
    _ -> Nothing


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



