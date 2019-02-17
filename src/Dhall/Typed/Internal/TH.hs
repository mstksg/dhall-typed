{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE ViewPatterns        #-}

module Dhall.Typed.Internal.TH (
    inspector
  , unApply
  , genPolySing
  ) where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Trans.Writer
import           Dhall.Typed.Type.Singletons
import           Data.Bifunctor
import           Data.Char
import           Data.Either
import           Data.List
import           Data.Singletons
import           Data.Traversable
import           Debug.Trace
import           Language.Haskell.TH
import           Language.Haskell.TH.Desugar
import           Language.Haskell.TH.Desugar.Sweeten
import           Language.Haskell.TH.Lift
import           Language.Haskell.TH.Syntax

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
    decsToTH <$> polySingDecs nod ctx nm bndrs dk cons dervs

-- data Index :: [k] -> k -> Type where
--     IZ :: Index (a ': as) a
--     IS :: Index bs a -> Index (b ': bs) a

polySingDecs
    :: forall q. ()
    => DsMonad q
    => NewOrData
    -> DCxt
    -> Name
    -> [DTyVarBndr]
    -> Maybe DKind      -- ^ What is this?
    -> [DCon]
    -> [DDerivClause]
    -> q [DDec]
polySingDecs nod ctx nm bndrs dk cons _dervs = do
    bndr <- (`DKindedTV` bndrKind) <$> qNewName "x"
    dd   <- polySingDataDec nod ctx nm bndrs dk cons bndr
    ofa  <- polySingOfFam nm bndrs cons bndr
    si   <- polySingSingI ctx nm bndrs cons bndr
    -- runQ . reportError $ pprint (sweeten dd)
    pure . concat $ [ dd, si, ofa ]
  where
    bndrKind :: DKind
    bndrKind = applyDType (DConT nm) (dTyVarBndrToDType <$> bndrs)

-- data SIndex as a :: Index as a -> Type where
--     SIZ :: SIndex (a ': as) a 'IZ
--     SIS :: SIndex as b i -> SIndex (a ': as) b ('IS i)
--
-- type instance PolySing (Index as a) = SIndex as a

-- TODO: fixity
polySingDataDec
    :: forall q. ()
    => DsMonad q
    => NewOrData
    -> DCxt
    -> Name
    -> [DTyVarBndr]
    -> Maybe DKind      -- ^ What is this?
    -> [DCon]
    -> DTyVarBndr
    -> q [DDec]
polySingDataDec nod ctx nm bndrs dk cons bndr = do
    cons' <- traverse singCons cons
    pure [ DDataD nod ctx nm' (bndrs ++ [bndr]) dk cons' []
         , DTySynInstD ''PolySing $
             DTySynEqn [applyDType (DConT nm ) bndrAsTypes]
                       (applyDType (DConT nm') bndrAsTypes)
         ]
  where
    bndrAsTypes = map dTyVarBndrToDType bndrs
    nm' :: Name
    nm' = mapNameBase singleConstr nm
    -- what do we do about cctx?
    singCons :: DCon -> q DCon
    singCons (DCon cbndrs cctx cnm cfs ctype) = do
      (cfs', newArgs) <- runWriterT $ refield cfs
      (DConT _, targs) <- pure $ unApply ctype
      let ctype' = applyDType (DConT nm') $     -- no DPromotedT
            targs ++ [applyDType (DConT cnm) (either id dTyVarBndrToDType <$> newArgs)]
      pure $ DCon (cbndrs ++ rights newArgs)
                  cctx
                  (mapNameBase singleConstr cnm)
                  cfs'
                  ctype'
    refield :: DConFields -> WriterT [Either DType DTyVarBndr] q DConFields
    refield = \case
        DNormalC i bt -> DNormalC i <$> (traverse . traverse) go bt
        DRecC vbt     -> fmap DRecC
                       . traverse (\(n,b,t) -> (mapNameBase singleValue n,b,) <$> go t)
                       $ vbt
      where
        go :: DType -> WriterT [Either DType DTyVarBndr] q DType
        go t = case unApply t of
          (DConT fnm, targs)
            | isSingleConstr fnm -> t <$
                tell [ Left $ applyDType (DConT (mapName ofSingle fnm)) targs ]
            | fnm == nm -> do
                n <- qNewName "x"
                tell [Right $ DPlainTV n]     -- ???
                -- TODO: handle cases from different module?
                pure . applyDType (DConT nm') $
                  targs ++ [DVarT n]
          (_, targs) -> do
            n <- qNewName "x"
            tell [Right $ DPlainTV n ]
            pure $ applyDType (DConT ''PolySing) [t, DVarT n]


-- type family SIndexOf as a (i :: Index as a) = (s :: SIndex as a i) | s -> i where
--     SIndexOf (a ': as) a 'IZ     = 'SIZ
--     SIndexOf (a ': as) b ('IS i) = 'SIS (SIndexOf as b i)

-- type SIndexOf as a (i :: Index as a) = PolySingOf (SIndex as a) i
--
-- type instance PolySingOf (SIndex (a ': as) a) 'IZ     = 'SIZ
-- type instance PolySingOf (SIndex (a ': as) b) ('IS i) = 'SIS (PolySingOf (SIndex as b) i)

-- type instance PolySingOf (SProd f '[]      ) 'Ø         = 'SØ
-- type instance PolySingOf (SProd f (a ': as)) (x ':< xs) = PolySingOf (PolySing (f a)) x ':%< PolySingOf (SProd f as) xs

polySingOfFam
    :: DsMonad q
    => Name
    -> [DTyVarBndr]
    -> [DCon]
    -> DTyVarBndr
    -> q [DDec]
polySingOfFam nm bndrs cons bndr = do
    -- y <- qNewName "y"
    eqns <- for cons $ \c@(DCon _ _ cnm _ cTy) -> do
      (sat, vs) <- saturate c
      let (_, newArgs) = unApply cTy
          res = applyDType (DConT (mapNameBase singleConstr cnm)) $
                  flip map vs $ \(anm, t) ->
                    let (topcon, tA) = unApply t
                        f = case topcon of
                          DConT q -> applyDType (DConT (mapNameBase singleConstr q)) tA
                          _       -> DConT ''PolySing `DAppT` t
                    in  applyDType (DConT ''PolySingOf)
                          [ f, DVarT anm  ]
      pure $ DTySynInstD ''PolySingOf $
                DTySynEqn [ applyDType (DConT nm') newArgs
                          , sat
                          ] res
    pure $ eqns ++ [tysyn]
  where
    nm' :: Name
    nm' = mapNameBase singleConstr nm
    newBndrs :: [DTyVarBndr]
    newBndrs = bndrs ++ [bndr]
    tysyn = DTySynD (mapNameBase ofSingle nm')
                    newBndrs
                    (applyDType (DConT ''PolySingOf)
                        [ singType
                        , dTyVarBndrToDType bndr
                        ] `DSigT` (singType `DAppT` dTyVarBndrToDType bndr)
                    )
    singType = applyDType (DConT nm') (dTyVarBndrToDType <$> bndrs)

-- type SIndexOf as a (i :: Index as a) = PolySingOf (SIndex as a) i :: SIndex as a i

-- class SIndexI as a (i :: Index as a) | i -> as a where
--     sIndex :: SIndex as a i
-- instance SIndexI (a ': as) a 'IZ where
--     sIndex = SIZ
-- instance SIndexI as b i => SIndexI (a ': as) b ('IS i) where
--     sIndex = SIS sIndex

-- instance PolySingI 'IZ where
--     polySing = SIZ
-- instance PolySingI i => PolySingI ('IS i) where
--     polySing = SIS polySing

polySingSingI :: DsMonad q => DCxt -> Name -> [DTyVarBndr] -> [DCon] -> DTyVarBndr -> q [DDec]
polySingSingI ctx nm bndrs cons bndr = for cons $ \c@(DCon _ _ cnm cfs cTy) -> do
    (sat, vs) <- saturate c
    let (_, newArgs) = unApply cTy
        cctx = flip map vs $ \(aN, _) -> DConPr ''PolySingI `DAppPr` DVarT aN
    pure $ DInstanceD Nothing cctx
      (DConT ''PolySingI `DAppT` sat)
      [ DLetDec . DFunD 'polySing $
          [ DClause [] . applyDExp (DConE (mapNameBase singleConstr cnm)) $
              case cfs of
                DNormalC _ xs -> DVarE 'polySing <$ xs
                DRecC xs      -> DVarE 'polySing <$ xs
          ]
      ]

      -- atc' <- case atc of
      --   DConT q -> pure $ mapNameBase iSingleConstr q
      --   DVarT _ -> pure ''SingI
      --   _       -> fail "polySingSingI: Bad SingI parameter?"
      -- pure . foldl' DAppPr (DConPr atc') $
      --         atarg ++ [DVarT aN]
    -- valArgs <- maybe (fail "Bad val arg") pure $ case cfs of
    --    DNormalC _ xs -> traverse (typeSingI . snd) xs
    --    DRecC xs      -> traverse (\(_,_,t) -> typeSingI t) xs
    -- pure $ DInstanceD Nothing cctx
    --   (applyDType (DConT clsNm) $ newArgs ++ [sat])
    --   [DLetDec . DFunD mthdNm $
    --      [ DClause [] . applyDExp (DConE (mapNameBase singleConstr cnm)) $
    --          map DVarE valArgs

    --      ]
    --   ]
  where
    nm' = mapNameBase singleConstr nm
    -- clsNm  = mapNameBase iSingleConstr nm
    -- mthdNm = mapNameBase iSingleValue nm
    -- cls = DClassD ctx clsNm
    --   (bndrs ++ [bndr])
    --   [FunDep [bndrName bndr] (bndrName <$> bndrs)]
    --   [DLetDec . DSigD mthdNm . applyDType (DConT nm')
    --      $ dTyVarBndrToDType <$> (bndrs ++ [bndr])
    --   ]

-- data instance Sing (i :: Index as a) where
--     SIx  :: { getSIx  :: SIndex as a i } -> Sing i

-- instance SingKind (Index as a) where
--     type Demote (Index as a) = Index as a
--     fromSing (SIx i) = case i of
--       SIZ   -> IZ
--       SIS j -> IS (fromSing (SIx j))
--     toSing = \case
--       IZ   -> SomeSing (SIx SIZ)
--       IS i -> case toSing i of
--         SomeSing (SIx j) -> SomeSing (SIx (SIS j))

-- we have a problem here. how to properly fromSing non-Sing's with their
-- names.  maybe it's just best to detach from singletons.
-- polySingSingKind
--     :: DsMonad q
--     => q [DDec]
-- polySingSingKind = do
--     -- => DCxt -> Name -> [DTyVarBndr] -> [DCon] -> DTyVarBndr -> q [DDec]


bndrName :: DTyVarBndr -> Name
bndrName (DKindedTV x _) = x
bndrName (DPlainTV x   ) = x

mkPlain :: DTyVarBndr -> DTyVarBndr
mkPlain (DKindedTV x _) = DPlainTV x
mkPlain (DPlainTV x   ) = DPlainTV x

-- typeSingI :: DType -> Maybe Name
-- typeSingI t = case fst (unApply t) of
--     DConT c -> Just $ mapNameBase iSingleValue c
--     DVarT _ -> Just $ 'sing


-- class SIndexI as a (i :: Index as a) where
--     sIndex :: SIndex as a i

-- instance SIndexI (a ': as) a 'IZ where
--     sIndex = SIZ
-- instance SIndexI as b i => SIndexI (a ': as) b ('IS i) where
--     sIndex = SIS sIndex

saturate :: Quasi q => DCon -> q (DType, [(Name, DType)])
saturate (DCon _ _ nm fs _) = do
    bndrs <- for fs' $ \f -> (, f) <$> qNewName "x"
    pure ( applyDType (DConT nm) $
             map (dTyVarBndrToDType . uncurry DKindedTV) bndrs
         , bndrs
         )
  where
    fs' = case fs of
      DNormalC _ xs -> map snd xs
      DRecC xs      -> map (\(_,_,t) -> t) xs

-- | Descend down the left hand side of applications until you reach
-- a non-application.
unApply :: DType -> (DType, [DType])
unApply = second ($ []) . go
  where
    go (DAppT x y) = second (. (y:)) $ go x
    go x           = (x, id)

singleConstr :: String -> String
singleConstr (':':cs) = ":%" ++ cs
singleConstr cs       = 'S' : cs

singleValue :: String -> String
singleValue ds@(c:cs)
  | all isSymbol ds = '%' : ds
  | otherwise       = 's' : toUpper c : cs
singleValue _ = error "Invalid value name"

-- | Will give a false positive for a type that is called "SXyyyy".
isSingleConstr :: Name -> Bool
isSingleConstr = check . nameBase
  where
    check ('S':c:_) = isUpper c
    check _         = False

mapName :: (String -> String) -> Name -> Name
mapName f n = mkName
            . maybe id (\m x -> m ++ "." ++ x) (nameModule n)
            . f
            $ nameBase n

mapNameBase :: (String -> String) -> Name -> Name
mapNameBase f = mkName . f . nameBase

ofSingle :: String -> String
ofSingle = (++ "Of")

-- iSingleConstr :: String -> String
-- iSingleConstr (':':cs) = ":%" ++ cs ++ "?"
-- iSingleConstr cs = 'S' : cs ++ "I"

-- -- | Turn a type constructor into the "SingI" method name
-- iSingleValue :: String -> String
-- iSingleValue (':':cs) = '?':cs
-- iSingleValue cs       = 's':cs

