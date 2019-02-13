{-# LANGUAGE FlexibleContexts               #-}
{-# LANGUAGE GADTs                          #-}
{-# LANGUAGE LambdaCase                     #-}
{-# LANGUAGE ScopedTypeVariables            #-}
{-# LANGUAGE TypeApplications               #-}
{-# LANGUAGE TypeInType                     #-}
{-# LANGUAGE TypeOperators                  #-}
{-# OPTIONS_GHC -fplugin Dhall.Typed.Plugin #-}

module Dhall.Typed (
    -- toTypedType, toTypedTerm
  -- * Samples
    ident, konst, konst', konst3, konst4, natBuild, listBuild
  ) where

import           Data.Text          (Text)
import           Data.Type.Equality
import           Dhall.Typed.Core
import           Dhall.Typed.Index
import           Dhall.Typed.Prod
import qualified Data.Sequence      as Seq
import qualified Data.Text          as T
import qualified Dhall.Core         as D
import qualified Dhall.TypeCheck    as D

---- | Convert an untyped Dhall expression into a typed one with no free
---- variables representing a Dhall type of a desired kind.
----
---- Will fail if:
----
---- *  The Dhall expression does not represent a type
---- *  The kind does not match
---- *  There are any free variables
----
---- Will behave unpredictably if the Dhall expression does not typecheck
---- within Dhall itself.
--toTypedType
--    :: SDKind k
--    -> Prod SDKind us     -- kinds of free variables
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

-- kindcheckType
--     :: forall a b us. SDKindI b
--     => SDKind a
--     -> DType us b
--     -> Maybe (DType us a)
-- kindcheckType a x = case sameDKind a (sdKind @b) of
--     Just Refl -> Just x
--     Nothing   -> Nothing




---- | Convert an untyped dhall expression into a typed one representing
---- a Dhall term of a desired type.
----
---- Will fail if:
----
---- *  The Dhall expression does not represent a term
---- *  The type does not match
---- *  There are any free variables
----
---- Will behave unpredictably if the Dhall expression does not typecheck
---- within Dhall itself.
--toTypedTerm
--    :: SDType '[] 'Type a
--    -> Prod (SDType '[] 'Type) vs     -- ^ types of free variables, and original names
--    -> D.Expr () D.X
--    -> Maybe (DTerm vs a)
--toTypedTerm a vs = \case
----     | Var Var
----     | Lam Text (Expr s a) (Expr s a)
----     | App (Expr s a) (Expr s a)
----     | Let (NonEmpty (Binding s a)) (Expr s a)
--    D.Annot x _  -> toTypedTerm a vs x
--    D.BoolLit b  -> typecheckTerm a $ BoolLit b
----     | BoolAnd (Expr s a) (Expr s a)
----     | BoolOr  (Expr s a) (Expr s a)
----     | BoolEQ  (Expr s a) (Expr s a)
----     | BoolNE  (Expr s a) (Expr s a)
----     | BoolIf (Expr s a) (Expr s a) (Expr s a)
--    D.NaturalLit n  -> typecheckTerm a $ NaturalLit n
--    D.NaturalFold   -> typecheckTerm a $ NaturalFold
--    D.NaturalBuild  -> typecheckTerm a $ NaturalBuild
--    D.NaturalIsZero -> typecheckTerm a $ NaturalIsZero
----     | NaturalEven
----     | NaturalOdd
----     | NaturalToInteger
----     | NaturalShow
--    D.NaturalPlus x y -> do
--      Refl <- a `sameDType` SNatural
--      x'   <- toTypedTerm SNatural vs x
--      y'   <- toTypedTerm SNatural vs y
--      pure $ NaturalPlus x' y'
--    D.NaturalTimes x y -> do
--      Refl <- a `sameDType` SNatural
--      x'   <- toTypedTerm SNatural vs x
--      y'   <- toTypedTerm SNatural vs y
--      pure $ NaturalTimes x' y'
----     | IntegerLit Integer
----     | IntegerShow
----     | IntegerToDouble
----     | DoubleLit Double
----     | DoubleShow
----     | TextLit (Chunks s a)
----     | TextAppend (Expr s a) (Expr s a)
----     | ListLit (Maybe (Expr s a)) (Seq (Expr s a))
----     | ListAppend (Expr s a) (Expr s a)
----     | ListBuild
----     | ListFold
----     | ListLength
----     | ListIndexed
----     | OptionalLit (Expr s a) (Maybe (Expr s a))
----     | OptionalFold
----     | OptionalBuild
--    D.None -> typecheckTerm a None
----     | RecordLit (Map Text (Expr s a))
----     | UnionLit Text (Expr s a) (Map Text (Expr s a))
----     | Combine (Expr s a) (Expr s a)
----     | Prefer (Expr s a) (Expr s a)
----     | Merge (Expr s a) (Expr s a) (Maybe (Expr s a))
----     | Field (Expr s a) Text
----     | Project (Expr s a) (Set Text)
----     | Note s (Expr s a)
----     | ImportAlt (Expr s a) (Expr s a)
----     | Embed a
--    _ -> Nothing
--    -- ListLit       :: SDType '[] 'Type a
--    --               -> Seq (DTerm vs a)
--    --               -> DTerm vs ('List ':$ a)
--    -- ListFold      :: DTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ)))
--    -- ListBuild     :: DTerm vs ('Pi 'SType ('Pi 'SType (('TVar ('IS 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'TVar 'IZ ':-> 'TVar 'IZ) ':-> 'List ':$ 'TVar 'IZ))
--    -- ListAppend    :: DTerm vs ('List ':$ a)
--    --               -> DTerm vs ('List ':$ a)
--    --               -> DTerm vs ('List ':$ a)
--    -- ListHead      :: DTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Optional ':$ 'TVar 'IZ))
--    -- ListLast      :: DTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'Optional ':$ 'TVar 'IZ))
--    -- ListReverse   :: DTerm vs ('Pi 'SType ('List ':$ 'TVar 'IZ ':-> 'List     ':$ 'TVar 'IZ))
--    -- OptionalLit   :: SDType '[] 'Type a
--    --               -> Maybe (DTerm vs a)
--    --               -> DTerm vs ('Optional ':$ a)
--    -- Some          :: DTerm vs a -> DTerm vs ('Optional ':$ a)

-- typecheckTerm
--     :: forall a b vs. SDTypeI '[] 'Type b
--     => SDType '[] 'Type a
--     -> DTerm vs b
--     -> Maybe (DTerm vs a)
-- typecheckTerm a x = case sameDType a (sdType @_ @_ @b) of
--     Just Refl -> Just x
--     Nothing   -> Nothing




-- -- | Syntax tree for expressions
-- data Expr s a
--     deriving (Eq, Foldable, Generic, Traversable, Show, Data)


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

-- there is asymmetry between Lam and TLam.  maybe use type variables to
-- address, instead of functions?

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
