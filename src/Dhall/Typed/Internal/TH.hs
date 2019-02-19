{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE ViewPatterns        #-}

module Dhall.Typed.Internal.TH (
    inspector
  -- , unApply
  , genPolySing
  , genPolySingWith
  , GenPolySingOpts(..), defaultGPSO
  ) where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Writer hiding         (lift)
import           Data.Bifunctor
import           Data.Char
import           Data.Containers.ListUtils
import           Data.Default
import           Data.Either
import           Data.Foldable
import           Data.List
import           Data.Map                            (Map)
import           Data.Maybe
import           Data.Ord
import           Data.Semigroup
import           Data.Sequence                       (Seq(..))
import           Data.Set                            (Set)
import           Data.Singletons
import           Data.Traversable
import           Debug.Trace
import           Dhall.Typed.Type.Singletons.Internal
import           Language.Haskell.TH
import           Language.Haskell.TH.Desugar
import           Language.Haskell.TH.Desugar.Sweeten
import           Language.Haskell.TH.Lift
import           Language.Haskell.TH.Syntax
import qualified Data.Map                            as M
import qualified Data.Sequence                       as Seq
import qualified Data.Set                            as S

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

data GenPolySingOpts = GPSO
    { gpsoSing  :: Bool
    , gpsoSingI :: Bool
    , gpsoPSK   :: Bool
    }
  deriving (Eq, Show, Ord)

instance Default GenPolySingOpts where
    def = defaultGPSO

defaultGPSO :: GenPolySingOpts
defaultGPSO = GPSO
    { gpsoSing  = True
    , gpsoSingI = True
    , gpsoPSK   = True
    }

genPolySing
    :: DsMonad q
    => Name
    -> q [Dec]
genPolySing = genPolySingWith defaultGPSO

genPolySingWith
    :: DsMonad q
    => GenPolySingOpts
    -> Name
    -> q [Dec]
genPolySingWith opts name = do
    DTyConI (DDataD _ ctx nm bndrs dk cons dervs) _ <- dsInfo <=< reifyWithLocals $ name
    decsToTH <$> polySingDecs opts ctx nm bndrs dk cons dervs

-- data Index :: [k] -> k -> Type where
--     IZ :: Index (a ': as) a
--     IS :: Index bs a -> Index (b ': bs) a

polySingDecs
    :: forall q. DsMonad q
    => GenPolySingOpts
    -> DCxt
    -> Name
    -> [DTyVarBndr]
    -> Maybe DKind      -- ^ What is this?
    -> [DCon]
    -> [DDerivClause]
    -> q [DDec]
polySingDecs GPSO{..} ctx nm bndrs dk cons _dervs = do
    bndr <- (`DKindedTV` bndrKind) <$> qNewName "x"
    execWriterT $ do
      when gpsoSing $
        tell =<< polySingDataDec ctx nm bndrs dk cons bndr
      when gpsoSingI $
        tell =<< polySingSingI nm bndrs cons bndr
      when gpsoPSK $
        -- tell . (:[]) . tracePPId =<< polySingKind nm bndrs cons bndr
        tell . (:[]) =<< polySingKind nm bndrs cons bndr

    -- dd   <- polySingDataDec ctx nm bndrs dk cons bndr
    -- si   <- polySingSingI nm bndrs cons bndr
    -- psk  <- polySingKind nm bndrs cons bndr
    -- -- let out = concat [ dd, si, ofa ]
    -- -- ofa  <- polySingOfFam nm bndrs cons bndr
    -- let out = concat [ dd, si, [psk] ]
    -- -- runQ . reportWarning $ pprint (sweeten (dd ++ si ++ ofa))
    -- trace (pprint (sweeten [psk])) $ pure out
    -- -- pure out
  where
    bndrKind :: DKind
    bndrKind = applyDType (DConT nm) (dTyVarBndrToDType <$> bndrs)
    tracePPId :: DDec -> DDec
    tracePPId x = trace (pprint (sweeten [x])) x
    tracePPId' :: [DDec] -> [DDec]
    tracePPId' x = trace (pprint (sweeten x)) x

-- data SIndex as a :: Index as a -> Type where
--     SIZ :: SIndex (a ': as) a 'IZ
--     SIS :: SIndex as b i -> SIndex (a ': as) b ('IS i)
--
-- type instance PolySing (Index as a) = SIndex as a

-- TODO: fixity
polySingDataDec
    :: forall q. DsMonad q
    => DCxt
    -> Name
    -> [DTyVarBndr]
    -> Maybe DKind      -- ^ What is this?
    -> [DCon]
    -> DTyVarBndr
    -> q [DDec]
polySingDataDec ctx nm bndrs dk cons bndr = do
    cons' <- traverse singCons cons
    pure [ DDataD Data ctx nm' (bndrs ++ [bndr]) dk cons' []
-- type instance PolySing (Maybe a) = SMaybe a
         , DTySynInstD ''PolySing $
             DTySynEqn [fullHead] fullHead'
         -- , DTySynInstD ''PolySing $
         --     DTySynEqn [applyDType (DConT ''WrappedSing) [fullHead, dTyVarBndrToDType bndr]] $
         --          applyDType (DConT ''SingSing)
         --            [ fullHead, dTyVarBndrToDType bndr ]
             -- (applyDType (DConT nm) )
-- type instance PolySing (WrappedSing Bool b) = SingSing Bool b
-- type instance PolySing (WrappedSing (Maybe a) b) = SingSing (Maybe a) b
         ]
  where
    fullHead = applyDType (DConT nm) bndrAsTypes
    fullHead' = applyDType (DConT nm') bndrAsTypes
    bndrAsTypes = map dTyVarBndrToDType bndrs
    nm' :: Name
    nm' = mapNameBase singleConstr nm
    -- what do we do about cctx?
    singCons :: DCon -> q DCon
    singCons (DCon cbndrs cctx cnm cfs ctype) = do
      (cfs', newArgs) <- runWriterT $ refield cfs
      (DConT _, targs) <- pure $ unApply ctype
      let ctype' = applyDType (DConT nm') $     -- no DPromotedT
            targs ++ [applyDType (DConT cnm) (dTyVarBndrToDType <$> newArgs)]
      pure $ DCon (cbndrs ++ newArgs)
                  cctx
                  (mapNameBase singleConstr cnm)
                  cfs'
                  ctype'
    refield :: DConFields -> WriterT [DTyVarBndr] q DConFields
    refield = \case
        DNormalC i bt -> DNormalC i <$> (traverse . traverse) go bt
        DRecC vbt     -> fmap DRecC
                       . traverse (\(n,b,t) -> (mapNameBase singleValue n,b,) <$> go t)
                       $ vbt
      where
        go :: DType -> WriterT [DTyVarBndr] q DType
        go t = do
          n <- qNewName "x"
          tell [DPlainTV n]
          t' <- expandType t
          pure $ case deSingleApplied t' of
            Just (desing, x) -> applyDType (DConT ''SingSing)
                [ desing, x, DConT 'WS `DAppT` DVarT n ]
            Nothing -> case unApply t' of
              (DConT fnm, targs)
                | fnm == nm -> applyDType (DConT nm') $
                    targs ++ [DVarT n]
              _     -> applyDType (DConT ''PolySing) [t', DVarT n]

          -- case unApply t' of
          --   (DConT fnm, targs)
          --     | Just fnm' <- isSingleConstr fnm
          --     , tinit :|> tlast <- Seq.fromList targs -> do
          --         n <- qNewName "x"
          --         tell [DPlainTV n]
          --         pure $ applyDType (DConT ''SingSing) $
          --           [ applyDType (DConT fnm') (toList tinit)
          --           , tlast
          --           , DConT 'WS `DAppT` DVarT n
          --           ]
          --           -- DConT fnm' : targs ++
          --     -- | Just fnm' <- isSingleConstr fnm -> do
          --     --     n <- qNewName "x"
          --     --     tell [DPlainTV n]
          --     --     pure $ applyDType (DConT ''SingSing) $
          --     --              DConT fnm' : targs ++ [DVarT n]
          --     | fnm == nm -> do
          --         n <- qNewName "x"
          --         tell [DPlainTV n]     -- ???
          --         -- TODO: handle cases from different module?
          --         pure . applyDType (DConT nm') $
          --           targs ++ [DVarT n]
          --   (_, targs) -> do
          --     n <- qNewName "x"
          --     tell [DPlainTV n]
          --     pure $ applyDType (DConT ''PolySing) [t', DVarT n]


-- type family SIndexOf as a (i :: Index as a) = (s :: SIndex as a i) | s -> i where
--     SIndexOf (a ': as) a 'IZ     = 'SIZ
--     SIndexOf (a ': as) b ('IS i) = 'SIS (SIndexOf as b i)

-- type SIndexOf as a (i :: Index as a) = PolySingOf (SIndex as a) i
--
-- type instance PolySingOf (SIndex (a ': as) a) 'IZ     = 'SIZ
-- type instance PolySingOf (SIndex (a ': as) b) ('IS i) = 'SIS (PolySingOf (SIndex as b) i)

-- type instance PolySingOf (SProd f '[]      ) 'Ø         = 'SØ
-- type instance PolySingOf (SProd f (a ': as)) (x ':< xs) = PolySingOf (PolySing (f a)) x ':%< PolySingOf (SProd f as) xs

-- polySingOfFam
--     :: DsMonad q
--     => Name
--     -> [DTyVarBndr]
--     -> [DCon]
--     -> DTyVarBndr
--     -> q [DDec]
-- polySingOfFam nm bndrs cons bndr = pure [tysyn]
--     -- y <- qNewName "y"
--     -- eqns <- for cons $ \c@(DCon _ _ cnm _ cTy) -> do
--     --   (sat, vs) <- saturate c
--     --   let (_, newArgs) = unApply cTy
--     --       res = applyDType (DConT (mapNameBase singleConstr cnm)) $
--     --               flip map vs $ \(anm, t) ->
--     --         let (topcon, tA) = unApply t
--     --         in  case topcon of
--     --               DConT q
--     --                 -- | isSingleConstr q -> DVarT anm
--     --                 -- | isSingleConstr q -> applyDType (DConT ''PolySingOf) [ applyDType topcon (init tA) , last tA]
--     --                 | q == nm -> applyDType (DConT ''PolySingOf)
--     --                     [ applyDType (DConT nm') tA, DVarT anm ]
--     --               _ -> applyDType (DConT ''PolySingOf)
--     --                     [ DConT ''PolySing `DAppT` t, DVarT anm ]
--     --                     -- f = case topcon of
--     --                     --   DConT q
--     --                     --     | isSingleConstr q -> _
--     --                     --     | q == nm -> applyDType (DConT nm') tA
--     --                     --   _       -> DConT ''PolySing `DAppT` t
--     --                 -- in  applyDType (DConT ''PolySingOf)
--     --                     --   [ f, DVarT anm  ]
--     --   pure $ DTySynInstD ''PolySingOf $
--     --             DTySynEqn [ applyDType (DConT nm') newArgs
--     --                       , sat
--     --                       ] res
--     -- pure $ eqns ++ [tysyn]
--   where
--     nm' :: Name
--     nm' = mapNameBase singleConstr nm
--     newBndrs :: [DTyVarBndr]
--     newBndrs = bndrs ++ [bndr]
--     tysyn = DTySynD (mapNameBase ofSingle nm')
--                     newBndrs
--                     (applyDType (DConT ''PolySingOf)
--                         [ dTyVarBndrToDType bndr
--                         ] `DSigT` (singType `DAppT` dTyVarBndrToDType bndr)
--                     )
--     singType = applyDType (DConT nm') (dTyVarBndrToDType <$> bndrs)

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

-- polySingSingI :: DsMonad q => DCxt -> Name -> [DTyVarBndr] -> [DCon] -> DTyVarBndr -> q [DDec]
-- polySingSingI ctx nm bndrs cons bndr = for cons $ \c@(DCon _ _ cnm cfs cTy) -> do
--     (sat, vs) <- saturate c
--     let cnm' = mapNameBase singleConstr cnm
--         (_, newArgs) = unApply cTy
--         cctx = flip map vs $ \(aN, aT) -> DConPr ''PolySingI `DAppPr` (DVarT aN `DSigT` aT)
--     pure $ DInstanceD Nothing cctx
--       (DConT ''PolySingI `DAppT` sat)
--       [ DLetDec . DFunD 'polySing $
--           [ DClause [] . applyDExp (DConE cnm') . flip map vs $ \(n, t) ->
--               DVarE 'polySing `DSigE` ((DConT ''PolySing `DAppT` t) `DAppT` DVarT n)
--           ]
--       ]
--   where
--     nm' = mapNameBase singleConstr nm

polySingSingI
    :: DsMonad q
    => Name
    -> [DTyVarBndr]
    -> [DCon]
    -> DTyVarBndr
    -> q [DDec]
polySingSingI nm bndrs cons bndr = for cons $ \c@(DCon _ _ cnm cfs cTy) -> do
    (_, vs) <- saturate c
    let cnm' = mapNameBase singleConstr cnm
        (_, newArgs) = unApply cTy
        cctx = flip map vs $ \(aN, aT) ->
          let pr = case deSingleApplied aT of
                Just (desing, _) -> ''PolySingOfI
                Nothing          -> ''PolySingI
          in  DConPr pr `DAppPr` DVarT aN
          -- case deSingleApplied aT of
          --   Just (desgin, x) -> DConPr ''PolySingI `DAppPr` x
          --   Nothing          -> DConPr ''PolySingI `DAppPr` DVarT aN

          -- case unApply aT of
          --   (DConT aT', ts)
          --     | Just orig <- isSingleConstr aT'
          --     -> DConPr ''PolySingI `DAppPr` last ts
          --   _ -> DConPr ''PolySingI `DAppPr` DVarT aN
    pure $ DInstanceD Nothing cctx
      -- (DConT ''PolySingI `DAppT` applyDType (DConT cnm) (map (dTyVarBndrToDType . uncurry DKindedTV) vs))
      (DConT ''PolySingI `DAppT` applyDType (DConT cnm) (map (DVarT . fst) vs))
      [ DLetDec . DFunD 'polySing $
          [ DClause [] . applyDExp (DConE cnm') $
              DVarE 'polySing <$ vs
          ]
      ]
  where
    nm' = mapNameBase singleConstr nm

-- instance PolySingKind (Index as a) where
--     fromPolySing = \case
--       SIZ   -> IZ
--       SIS i -> IS (fromPolySing i)
--     toPolySing = \case
--       IZ   -> SomePS SIZ
--       IS i -> case toPolySing i of
--         SomePS j -> SomePS (SIS j)

-- instance PolySingKind PoopyButt where
--     fromPolySing = \case
--       SPB x -> PB (getWS (fromPolySing x))
--     toPolySing = \case
--       PB x -> case toPolySing (WS x) of
--         SomePS (SiSi y) -> SomePS (SPB (SiSi y))

polySingKind
    :: forall q. DsMonad q
    => Name
    -> [DTyVarBndr]
    -> [DCon]
    -> DTyVarBndr
    -> q DDec
polySingKind nm bndrs cons bndr = do
    fps <- traverse mkFps cons
    tps <- traverse mkTps cons
    n   <- qNewName "x"
    -- pure . trace (pprint (sweeten cctx)) $ DInstanceD Nothing cctx
    pure $ DInstanceD Nothing cctx
      ( DConT ''PolySingKind `DAppT`
           applyDType (DConT nm) (dTyVarBndrToDType . mkPlain <$> bndrs)
      )
      [ DLetDec . DFunD 'fromPolySing $
          [ DClause [DVarPa n] $ DCaseE (DVarE n) fps
          ]
      , DLetDec . DFunD 'toPolySing $
          [ DClause [DVarPa n] $ DCaseE (DVarE n) tps
          ]
      ]
  where
    cctx :: [DPred]
    cctx = nubOrdOn show $ do
      c@(DCon _ _ cnm cfs cTy) <- cons
      let newBndrs :: [Maybe Name]
          newBndrs = case unApply cTy of
            (DConT _, ts) -> flip map ts $ \case
              DVarT n -> Just n
              DVarT n `DSigT` _ -> Just n
              _       -> Nothing
            _             -> error "polySingKind: Invalid return type on GADT constructor"
          bndrMap :: Map Name Name
          bndrMap = M.fromList . catMaybes $
            [ (, bndrName bO) <$> bN
            | bN <- newBndrs
            | bO <- bndrs
            ]
      t <- case cfs of
        DNormalC _ xs -> map snd xs
        DRecC xs      -> map (\(_,_,t) -> t) xs
      case unApply t of
        (DConT _, _) -> empty
        _            -> pure ()
      let (free, t') = flip (traverseDVarT S.empty) t $ \v ->
            case M.lookup v bndrMap of
              Just q  -> pure q
              Nothing -> v <$ tell [v]
      pure $ DForallPr (DPlainTV <$> nubOrd free) [] $
        DConPr ''PolySingKind `DAppPr` t'
--     fromPolySing = \case
--       SPB x -> PB (getWS (fromPolySing x))
    mkFps :: DCon -> q DMatch
    mkFps c@(DCon _ _ cnm cfs cTy) = do
        (_, vs) <- saturate c
        pure . DMatch (DConPa cnm' (map (DVarPa . fst) vs)) $
          applyDExp (DConE cnm) . flip map vs $ \(n, t) ->
            let arg = DVarE 'fromPolySing `DAppE` DVarE n
            in  case deSingleApplied t of
                  Just _ -> DVarE 'getWS `DAppE` arg
                  Nothing -> arg
      where
        cnm' = mapNameBase singleConstr cnm
--     toPolySing = \case
--       PB x -> case toPolySing (WS x) of
--         SomePS (SiSi y) -> SomePS (SPB (SiSi y))
    mkTps :: DCon -> q DMatch
    mkTps c@(DCon _ _ cnm cfs cTy) = do
        (_, vs ) <- saturate c
        (_, vs') <- saturate c
        pure . DMatch (DConPa cnm (map (DVarPa . fst) vs)) $
          foldr (uncurry go)
                (DConE 'SomePS `DAppE` applyDExp (DConE cnm') (map reSiSi vs'))
                (zip vs vs')
      where
        reSiSi (n, t) = case deSingleApplied t of
          Just _  -> DConE 'SiSi `DAppE` DVarE n
          Nothing -> DVarE n
        go (oldN, t) (newN, _) finalRes =
            DCaseE (DVarE 'toPolySing `DAppE` wrapWS (DVarE oldN))
              [ DMatch (DConPa 'SomePS [unSiSi (DVarPa newN)]) finalRes
              ]
          where
            (wrapWS, unSiSi) = case deSingleApplied t of
              Just _ -> (DAppE (DConE 'WS), DConPa 'SiSi . (:[]))
              Nothing -> (id, id)
        cnm' = mapNameBase singleConstr cnm

isVar :: Name -> Bool
isVar (nameBase->(c:_))
  | isSymbol c = c /= ':'
  | otherwise  = isLower c
isVar _ = error "empty name?"

           -- && isLower c ||
-- polySingSingI nm bndrs cons bndr = for cons $ \c@(DCon _ _ cnm cfs cTy) -> do
    -- mkFps = undefined

    -- mkTps = undefined
    --   -- DLetDec . DFunD 'fromPolySing $

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

traverseDVarPr
    :: Applicative f
    => Set Name
    -> (Name -> f Name)
    -> DPred -> f DPred
traverseDVarPr b f = go
  where
    go = \case
      DForallPr bndrs ctx x ->
        let (b', bndrs') = mapAccumL
              (\bb -> \case DKindedTV x t -> (S.insert x bb, DKindedTV x <$> traverseDVarT bb f t)
                            DPlainTV x    -> (S.insert x bb, pure $ DPlainTV x)
              ) b bndrs
        in  DForallPr <$> sequenceA bndrs'
                      <*> traverse (traverseDVarPr b' f) ctx
                      <*> traverseDVarPr  b' f x
      DAppPr x y -> DAppPr <$> go x <*> traverseDVarT b f y
      DSigPr x y -> DSigPr <$> go x <*> traverseDVarT b f y
      DVarPr x
        | x `S.member` b -> pure $ DVarPr x
        | otherwise      -> DVarPr <$> f x
      DConPr x   -> pure $ DConPr x
      DWildCardPr -> pure DWildCardPr

traverseDVarT :: Applicative f => Set Name -> (Name -> f Name) -> DType -> f DType
traverseDVarT b f = go
  where
    go = \case
      DForallT bndrs ctx x ->
        let (b', bndrs') = mapAccumL
              (\bb -> \case DKindedTV x t -> (S.insert x bb, DKindedTV x <$> traverseDVarT bb f t)
                            DPlainTV x    -> (S.insert x bb, pure $ DPlainTV x)
              ) b bndrs
        in  DForallT <$> sequenceA bndrs'
                     <*> traverse (traverseDVarPr b' f) ctx
                     <*> traverseDVarT  b' f x
      DAppT x y -> DAppT <$> go x <*> go y
      DSigT x y -> DSigT <$> go x <*> go y
      DVarT x
        | x `S.member` b -> pure $ DVarT x
        | otherwise      -> DVarT <$> f x
      DConT x   -> pure $ DConT x
      DArrowT   -> pure DArrowT
      DLitT x   -> pure $ DLitT x
      DWildCardT -> pure DWildCardT

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
             map (\(a,k) -> DVarT a `DSigT` k) bndrs
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

-- type instance PolySing (WrappedSing k b) = SingSing k b
-- type instance PolySing Bool = SBool
-- type instance PolySing (Maybe a) = SMaybe a

-- | Should convert:
--
-- PolySing k   => k
-- SBool        => Bool
-- SMaybe a     => Maybe a
-- SingSing k b => WrappedSing k b
--
-- The input is always expected to be (k -> Type).
deSingle :: DType -> Maybe DType
deSingle t = case unApply t of
    (DConT c, xs)
      | c == ''PolySing -> case xs of
          y:_ -> Just y
          _   -> Nothing
      | c == ''SingSing             -> Just $ applyDType (DConT ''WrappedSing) xs
      | Just c' <- isSingleConstr c -> Just $ applyDType (DConT c') xs
    -- TODO: handle case of 'f a b' ?
    _ -> Nothing

-- | Split a Type-kinded thing that is a singleton into the original type
-- and the value it is applied to.  Basically it is a de-AppT and 'deSingle'.
deSingleApplied :: DType -> Maybe (DType, DType)
deSingleApplied (f `DAppT` x) = (,x) <$> deSingle f
deSingleApplied _ = Nothing

-- | Will give a false positive for a type that is called "SXyyyy".
-- Returns the original constructor.
isSingleConstr :: Name -> Maybe Name
isSingleConstr (nameBase->cs) = case cs of
    'S':ds@(d:_) -> mkName ds <$ guard (isUpper d)
    _            -> Nothing

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

