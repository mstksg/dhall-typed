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
import           Control.Monad.Writer hiding          (lift)
import           Data.Bifunctor
import           Data.Char
import           Data.Containers.ListUtils
import           Data.Default
import           Data.Foldable
import           Data.List
import           Data.Map                             (Map)
import           Data.Maybe
import           Data.Sequence                        (Seq(..))
import           Data.Set                             (Set)
import           Data.Singletons.Decide               (Decision(..), (:~:)(..))
import           Data.Traversable
import           Debug.Trace
import           Dhall.Typed.Type.Singletons.Internal
import           Language.Haskell.TH
import           Language.Haskell.TH.Desugar
import           Language.Haskell.TH.Lift
import           Language.Haskell.TH.Syntax
import qualified Data.Map                             as M
import qualified Data.Sequence                        as Seq
import qualified Data.Set                             as S

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
        tell =<< polySingSingI cons
      when gpsoPSK $
        tell . (:[]) =<< polySingKind nm Nothing bndrs cons
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
         , DTySynInstD ''PolySing $
             DTySynEqn [fullHead] fullHead'
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


-- instance PolySingI 'IZ where
--     polySing = SIZ
-- instance PolySingI i => PolySingI ('IS i) where
--     polySing = SIS polySing

polySingSingI
    :: DsMonad q
    => [DCon]
    -> q [DDec]
polySingSingI cons = for cons $ \c@(DCon _ _ cnm _ _) -> do
    (_, vs) <- saturate c
    let cnm' = mapNameBase singleConstr cnm
        cctx = flip map vs $ \(aN, aT) ->
          let pr = case deSingleApplied aT of
                Just _  -> ''PolySingOfI
                Nothing -> ''PolySingI
          in  DConPr pr `DAppPr` DVarT aN
    pure $ DInstanceD Nothing cctx
      (DConT ''PolySingI `DAppT` applyDType (DConT cnm) (map (DVarT . fst) vs))
      [ DLetDec . DFunD 'polySing $
          [ DClause [] . applyDExp (DConE cnm') $
              DVarE 'polySing <$ vs
          ]
      ]

-- instance PolySingKind (Index as a) where
--     fromPolySing = \case
--       SIZ   -> IZ
--       SIS i -> IS (fromPolySing i)
--     toPolySing = \case
--       IZ   -> SomePS SIZ
--       IS i -> case toPolySing i of
--         SomePS j -> SomePS (SIS j)

-- instance PolySingKind PoolyBing where
--     fromPolySing = \case
--       SPB x -> PB (getWS (fromPolySing x))
--     toPolySing = \case
--       PB x -> case toPolySing (WS x) of
--         SomePS (SiSi y) -> SomePS (SPB (SiSi y))

-- toPolySingKind :: q [Dec] -> q [Dec]
-- toPolySingKind ds = do
--     -- DTyConI (DDataD _ ctx nm bndrs dk cons dervs) _ <- dsInfo <=< reifyWithLocals $ name
--     -- decsToTH <$> polySingDecs opts ctx nm bndrs dk cons dervs

      --   tell . (:[]) =<< polySingKind nm Nothing bndrs cons

-- TODO: redundant constraints
polySingKind
    :: forall q. DsMonad q
    => Name
    -> Maybe [DPred]
    -> [DTyVarBndr]
    -> [DCon]
    -> q DDec
polySingKind nm defctx bndrs cons = do
    -- qRunIO $ putStrLn $ "Generating PSK for " ++ show nm ++ "\n"
    fps <- traverse mkFps cons
    tps <- traverse mkTps cons
    eps <- traverse mkEps cons
    n   <- qNewName "x"
    let res = DInstanceD Nothing (fromMaybe cctx defctx)
          ( DConT ''PolySingKind `DAppT`
               applyDType (DConT nm) (dTyVarBndrToDType . mkPlain <$> bndrs)
          )
          [ DLetDec . DFunD 'fromPolySing $
              [ DClause [DVarPa n] $ DCaseE (DVarE n) fps
              ]
          , DLetDec . DFunD 'toPolySing $
              [ DClause [DVarPa n] $ DCaseE (DVarE n) tps
              ]
          -- , DLetDec . DFunD 'eqPS $
          --     [ DClause [DVarPa n] $ DCaseE (DVarE n) eps
          --     ]
          ]
    -- qRunIO . appendFile "scratch/eqPS.hs" . (++ "\n") . pprint . sweeten . (:[]) $
    --     DLetDec . DFunD 'eqPS $
    --       [ DClause [DVarPa n] $ DCaseE (DVarE n) eps
    --       ]
    -- qRunIO . print . length . pprint . sweeten $ [res]
    -- qRunIO . putStrLn . pprint $ sweeten cctx
    -- qRunIO . putStrLn . pprint . sweeten $
    --   [ DLetDec . DFunD 'fromPolySing $ [ DClause [DVarPa n] $ DCaseE (DVarE n) fps ]]
    -- qRunIO $ putStrLn "Done generating PSK."
    pure res
  where
    cctx :: [DPred]
    cctx = nubOrdOn show $ do
      DCon _ _ _ cfs cTy <- cons
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
      t' <- case unApply t of
        (DConT tct, targs)
          | tct == ''WrappedSing
          , t0:_ <- targs
          -> pure t0
          | otherwise -> empty
        _ -> pure t
      let (free, t'') = flip (traverseDVarT S.empty) t' $ \v ->
            case M.lookup v bndrMap of
              Just q  -> pure q
              Nothing -> v <$ tell [v]
      pure $ DForallPr (DPlainTV <$> nubOrd free) [] $
        DConPr ''PolySingKind `DAppPr` t''
--     fromPolySing = \case
--       SPB x -> PB (getWS (fromPolySing x))
    mkFps :: DCon -> q DMatch
    mkFps c@(DCon _ _ cnm _ _) = do
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
    mkTps c@(DCon _ _ cnm _ _) = do
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
    -- eqPS = \case
    --   SPB x -> \case
    --     SPB y -> case sameSingSing x y of
    --       Proved SiSiRefl -> Proved Refl
    --       Disproved v     -> Disproved $ \case Refl -> v SiSiRefl
    mkEps :: DCon -> q DMatch
    mkEps c@(DCon _ _ cnm _ _) = do
        (_, vs) <- saturate c
        n       <- qNewName "y"
        subEps  <- catMaybes <$> traverse (mkSubEps vs) cons
        pure . DMatch (DConPa cnm' (map (DVarPa . fst) vs)) $
            DLamE [n] $ DCaseE (DVarE n) subEps
      where
        cnm' = mapNameBase singleConstr cnm
        mkSubEps :: [(Name, DType)] -> DCon -> q (Maybe DMatch)
        mkSubEps vs c2@(DCon _ _ cnm2 _ _) = do
            (_, vs2) <- saturate c2
            if cnm == cnm2
              then Just .
                DMatch (DConPa cnm2' (map (DVarPa . fst) vs2)) <$>
                  foldrM (uncurry go)
                         (DConE 'Proved `DAppE` DConE 'Refl)
                         (zip vs vs2)
              else Just <$> do
                n <- qNewName "z"
                pure . DMatch (DConPa cnm2' (DWildPa <$ vs2)) $
                    DConE 'Disproved `DAppE`
                      DLamE [n] (DCaseE (DVarE n) [])
          where
            cnm2' = mapNameBase singleConstr cnm2
            go (oldN, t) (newN, _) finalRes = do
                n <- qNewName "z"
                m <- qNewName "q"
                pure $ DCaseE (applyDExp matcher [DVarE oldN, DVarE newN])
                  [ DMatch (DConPa 'Proved    [patner  ]) finalRes
                  , DMatch (DConPa 'Disproved [DVarPa n]) $
                      DAppE (DConE 'Disproved) $
                        DLamE [m] . DCaseE (DVarE m) $
                          [ DMatch (DConPa 'Refl []) $ DVarE n `DAppE` witner
                          ]
                  ]
              where
                (matcher, patner, witner) = case deSingleApplied t of
                  Just _  -> (DVarE 'sameSingSing, DConPa 'SiSiRefl [], DConE 'SiSiRefl)
                  Nothing -> (DVarE 'eqPS        , DConPa 'Refl     [], DConE 'Refl    )
              -- undefined
                    -- (DConE 'SomePS `DAppE` applyDExp (DConE cnm') (map reSiSi vs'))
    -- eqPS = \case
    --   SNil -> \case
    --     SNil -> Proved Refl
    --     _ :% _ -> Disproved $ \case {}
    --   x :% xs -> \case
    --     SNil -> Disproved $ \case {}
    --     y :% ys -> case eqPS x y of
    --       Proved Refl -> case eqPS xs ys of
    --         Proved Refl -> Proved Refl
    --         Disproved v -> Disproved $ \case Refl -> v Refl
    --       Disproved v -> Disproved $ \case Refl -> v Refl
        -- pure . DMatch (DConPa cnm' (map (DVarPa . fst) vs)) $
        --   applyDExp (DConE cnm) . flip map vs $ \(n, t) ->
        --     let arg = DVarE 'fromPolySing `DAppE` DVarE n
        --     in  case deSingleApplied t of
        --           Just _ -> DVarE 'getWS `DAppE` arg
        --           Nothing -> arg
      -- where
        -- cnm' = mapNameBase singleConstr cnm

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
              (\bb -> \case DKindedTV q t -> (S.insert q bb, DKindedTV q <$> traverseDVarT bb f t)
                            DPlainTV q    -> (S.insert q bb, pure $ DPlainTV q)
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
              (\bb -> \case DKindedTV q t -> (S.insert q bb, DKindedTV q <$> traverseDVarT bb f t)
                            DPlainTV q    -> (S.insert q bb, pure $ DPlainTV q)
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

mapNameBase :: (String -> String) -> Name -> Name
mapNameBase f = mkName . f . nameBase

