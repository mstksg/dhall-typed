{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Dhall.Typed.Internal.TH (
    inspector
  , unApply
  , genPolySing
  ) where

import           Control.Monad
import           Control.Monad.Trans.Writer
import           Data.Bifunctor
import           Data.List
import           Data.Traversable
import           Language.Haskell.TH
import           Language.Haskell.TH.Desugar
import           Language.Haskell.TH.Desugar.Sweeten
import           Language.Haskell.TH.Lift

-- Here we will generate singletons for GADTs in the "leading kind
-- variable" style.  Something like:
--
-- @
-- data DSort :: Type where
--     Kind     :: DSort
--     (:*>)    :: DSort -> DSort -> DSort
--     SoRecord :: AggType () '() ls as
--              -> Prod (Const DSort) as
--              -> DSort
--     SoUnion  :: AggType () '() ls as
--              -> Prod (Const DSort) as
--              -> DSort
-- @
--
-- Will become:
--
-- @
-- data SDSort :: DSort -> Type where
--     SKind     :: SDSort 'Kind
--     (:%*>)    :: SDSort s -> SDSort t -> SDSort (s ':*> t)
--     SSoRecord :: SAggType () '() ls as at
--               -> SProd (Const DSort) as p
--               -> SDSort ('SoRecord at p)
--     SSoUnion  :: SAggType () '() ls as at
--               -> SProd (Const DSort) as p
--               -> SDSort ('SoUnion at p)
-- @
--
-- For each constructor:
--  1. Find new name (add S)
--  2. Convert top-level constructors of all arguments to new name, and add
--     an type parameter x, y, z
--  3. For the final one, convert to new name, and add final type parameter
--     with the original constructor plus all of arguments x, y, z
--
-- Some special cases:
--
-- 1. If any argument is already a singleton, leave it be.  When time comes
--    to use it in the consturctor, add "-Of" to the constructor and use it
--    verbatim.
--
--    @
--    KLam  :: SDSort t -> DKind (t ': ts) a -> DKind ts (t ':*> a)
--    SKLam  :: SDSort t -> SDKind (t ': ts) a x -> SDKind ts (t ':*> a) ('KLam (SDSortOf t) x)
--    @

inspector
    :: Name
    -> Q Exp
inspector name = do
    i <- dsInfo <=< reifyWithLocals $ name
    lift $ show i

genPolySing
    :: DsMonad q
    => Name
    -> q [Dec]
genPolySing name = do
    DTyConI (DDataD nod ctx nm bndrs dk cons dervs) _ <- dsInfo <=< reifyWithLocals $ name
    decToTH <$> polySing nod ctx nm bndrs dk cons dervs

polySing
    :: forall q. ()
    => DsMonad q
    => NewOrData
    -> DCxt
    -> Name
    -> [DTyVarBndr]
    -> Maybe DKind      -- ^ What is this?
    -> [DCon]
    -> [DDerivClause]
    -> q DDec
polySing nod ctx nm bndrs dk cons _dervs = do
    bndr  <- (`DKindedTV` bndrKind) <$> newUniqueName "x"
    cons' <- traverse singCons cons
    pure $ DDataD nod ctx nm' (bndrs ++ [bndr]) dk cons' []
  where
    nm' :: Name
    nm' = mkName . singleConstr . nameBase $ nm
    bndrKind :: DKind
    bndrKind = applyDType (DConT nm) (dTyVarBndrToDType <$> bndrs)
    -- what do we do about cctx?
    singCons :: DCon -> q DCon
    singCons (DCon cbndrs cctx cnm cfs ctype) = do
      (cfs', newBndrs) <- runWriterT $ refield cfs
      (DConT _, targs) <- pure $ unApply ctype
      let ctype' = applyDType (DConT nm') $
            targs ++ [applyDType (DConT cnm) (dTyVarBndrToDType <$> newBndrs)]
      pure $ DCon (cbndrs ++ newBndrs)
                  cctx
                  (mkName (singleConstr (nameBase cnm)))
                  cfs'
                  ctype'
    refield :: DConFields -> WriterT [DTyVarBndr] q DConFields
    refield = \case
        DNormalC i bt -> DNormalC i <$> (traverse . traverse) go bt
        DRecC vbt     -> error "Singling records not yet implemented. But it's not that hard tbh."
      where
        go :: DType -> WriterT [DTyVarBndr] q DType
        go t = do
          n <- newUniqueName "x"
          tell [DPlainTV n]     -- ???
          (DConT fnm, targs) <- pure $ unApply t
          -- TODO: handle cases from different module?
          -- pure $ applyDType (DConT (mapName singleConstr fnm)) $
          pure $ applyDType (DConT (mkName (singleConstr (nameBase fnm)))) $
            targs ++ [DVarT n]
            



-- | Descend down the left hand side of applications until you reach
-- a non-application.
unApply :: DType -> (DType, [DType])
unApply = second ($ []) . go
  where
    go (DAppT x y) = second (. (y:)) $ go x
    go x           = (x, id)

mapName :: (String -> String) -> Name -> Name
mapName f n = mkName
            . maybe id (\m x -> m ++ "." ++ x) (nameModule n)
            . f
            $ nameBase n

singleConstr :: String -> String
singleConstr (':':cs) = ":%" ++ cs
singleConstr cs       = "S" ++ cs


    -- _ i
    -- pure []
    
    -- checkForRep names
    -- ddecs <- concatMapM (singInfo <=< dsInfo <=< reifyWithLocals) names
    -- return $ decsToTH ddecs
