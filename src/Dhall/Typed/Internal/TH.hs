{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MultiWayIf          #-}
{-# LANGUAGE ParallelListComp    #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE ViewPatterns        #-}

module Dhall.Typed.Internal.TH (
  -- * General creation
    genPolySing
  , genPolySingWith
  , GenPolySingOpts(..), defaultGPSO
  , GenOpts(..)
  -- * Specific generation
  , genPolySingKind
  , genSingEq
  ) where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Writer hiding          (lift)
import           Data.Bifunctor
import           Data.Char
import           Data.Containers.ListUtils
import           Data.Default
import           Data.Foldable
import           Data.Function
import           Data.IntMap                          (IntMap)
import           Data.IntSet                          (IntSet)
import           Data.List
import           Data.Map                             (Map)
import           Data.Maybe
import           Data.Sequence                        (Seq(..))
import           Data.Set                             (Set)
import           Data.Singletons.Decide               (Decision(..))
import           Data.Traversable
import           Data.Type.Equality
import           Dhall.Typed.Type.Singletons.Internal
import           Language.Haskell.TH
import           Language.Haskell.TH.Desugar
import           Language.Haskell.TH.Syntax
import qualified Control.Monad.Trans                  as MT
import qualified Data.IntMap                          as IM
import qualified Data.IntSet                          as IS
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

data GenOpts = GOInfer
             | GOSkip
             | GOHead (Q [Dec])

data GenPolySingOpts = GPSO
    { gpsoSing   :: !Bool
    , gpsoSingI  :: !Bool
    , gpsoPSK    :: !GenOpts
    , gpsoSingEq :: !GenOpts
    }

instance Default GenPolySingOpts where
    def = defaultGPSO

defaultGPSO :: GenPolySingOpts
defaultGPSO = GPSO
    { gpsoSing   = True
    , gpsoSingI  = True
    , gpsoPSK    = GOInfer
    , gpsoSingEq = GOInfer
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

-- | Expects an instance head with constraints:
--
-- @
-- $(genPolySingKind [d|
--   instance PolySingKind a => PolySingKind (Maybe a) where
--
--   instance (PolySingKind a, PolySingKind b) => PolySingKind (Either a b) where
--   |])
-- @
--
-- The default constraint guessing mechanism can be pretty clunky, so this
-- allows you to help out the logic.
genPolySingKind
    :: forall q. DsMonad q
    => q [Dec]
    -> q [Dec]
genPolySingKind qdecs =
    fmap decsToTH . traverse (genPolySingKind_ Nothing) =<< dsDecs =<< qdecs

genPolySingKind_
    :: forall q. DsMonad q
    => Maybe Name             -- ^ restrict to a single name
    -> DDec
    -> q DDec
genPolySingKind_ targ = \case
    DInstanceD o ctx (DConT psk `DAppT` t) _
      | psk == ''PolySingKind
      , (DConT nm, ts) <- unApply t
      , maybe True (== nm) targ
      , Just ts' <- extractTs ts
      -> do
        DTyConI (DDataD _ _ _ _ _ cs _) _ <- dsInfo <=< reifyWithLocals $ nm
        polySingKind nm o (Just ctx) ts' cs
    _ -> errorWithoutStackTrace "Not a valid PolySingKind head."
  where
    extractTs = traverse $ \case
      DVarT n           -> Just $ DPlainTV n
      DVarT n `DSigT` q -> Just $ DKindedTV n q
      _                 -> Nothing

-- | Expects an instance head with constraints:
--
-- @
-- $(genSingEq [d|
--   instance SingEq a a => SingEq (Maybe a) (Maybe a)
--   |])
-- @
--
-- The default constraint guessing mechanism can be pretty clunky, so this
-- allows you to help out the logic.
genSingEq
    :: forall q. DsMonad q
    => q [Dec]
    -> q [Dec]
genSingEq qdecs =
    fmap decsToTH . traverse (genSingEq_ Nothing) =<< dsDecs =<< qdecs

genSingEq_
    :: forall q. DsMonad q
    => Maybe Name             -- ^ restrict to a single name
    -> DDec
    -> q DDec
genSingEq_ targ = \case
    DInstanceD o ctx ((DConT psk `DAppT` t1) `DAppT` t2) _
      | psk == ''SingEq
      , (DConT nm1, ts1) <- unApply t1
      , (DConT nm2, ts2) <- unApply t2
      , nm1 == nm2
      , maybe True (== nm1) targ
      , Just ts1' <- extractTs ts1
      , Just ts2' <- extractTs ts2
      -> do
        DTyConI (DDataD _ _ _ _ _ cs _) _ <- dsInfo <=< reifyWithLocals $ nm1
        polySingSingEq nm1 o (Just ctx) (Left (zip ts1' ts2')) cs
    _ -> errorWithoutStackTrace "Not a valid SingEq head."
  where
    extractTs = traverse $ \case
      DVarT n           -> Just $ DPlainTV n
      DVarT n `DSigT` q -> Just $ DKindedTV n q
      _                 -> Nothing

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
      case gpsoPSK of
        GOInfer  -> tell . (:[])
                =<< polySingKind nm Nothing Nothing bndrs cons
        GOSkip   -> pure ()
        GOHead q -> tell . (:[])
                =<< genPolySingKind_ (Just nm) . head
                =<< dsDecs
                =<< runQ q
      case gpsoSingEq of
        GOInfer  -> tell . (:[])
                =<< polySingSingEq nm Nothing Nothing (Right bndrs) cons
        GOSkip   -> pure ()
        GOHead q -> tell . (:[])
                =<< genSingEq_ (Just nm) . head
                =<< dsDecs
                =<< runQ q
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
        cctx = nubOrdOn show . flip map vs $ \(aN, aT) ->
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

-- TODO: redundant constraints
polySingKind
    :: forall q. DsMonad q
    => Name
    -> Maybe Overlap
    -> Maybe [DPred]
    -> [DTyVarBndr]
    -> [DCon]
    -> q DDec
polySingKind nm o defctx bndrs cons = do
    fps <- traverse mkFps cons
    tps <- traverse mkTps cons
    n   <- qNewName "x"
    let res = DInstanceD o (fromMaybe cctx defctx)
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
          , False       -- TODO: remove?
          -> pure t0
          | otherwise -> empty
        _ -> pure t
      let (free, t'') = flip (traverseDVarT S.empty) t' $ \v ->
            case M.lookup v bndrMap of
              Just q  -> pure q
              Nothing -> v <$ tell [v]
      pure $ mkForall (DPlainTV <$> nubOrd free) $
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

-- instance SingEq k k => SingEq (AggType k ls as) (AggType k ms bs) where
--     singEq = \case
--       SATZ -> \case
--         SATZ -> Proved HRefl
--         SATS _ _ _ -> Disproved $ \case {}
--       SATS x y z -> \case
--         SATZ -> Disproved $ \case {}
--         SATS x' y' z' -> case singEq x x' of
--           Proved HRefl -> case singEq y y' of
--             Proved HRefl -> case singEq z z' of
--               Proved HRefl -> Proved HRefl
--               Disproved v -> Disproved $ \case HRefl -> v HRefl

polySingSingEq
    :: forall q. DsMonad q
    => Name
    -> Maybe Overlap
    -> Maybe [DPred]
    -> Either [(DTyVarBndr, DTyVarBndr)] [DTyVarBndr]     -- ^ Left: defaults, Right: dummy
    -> [DCon]
    -> q DDec
polySingSingEq nm o defctx defbndrs cons = do
    (bndr1, bndr2) <- case defbndrs of
      Left bb -> pure $ unzip bb
      Right bb -> do
        bndr1 <- (traverse . traverseBndrName) (\_ -> qNewName "a") bb
        DTyConI _ (Just insts) <- dsInfo <=< reifyWithLocals $ ''SingEq

        let instMap = M.fromList $ mapMaybe singEqInstance insts
            fullyDet = findFullyDet instMap bb

        bndr2 <- for (zip [0..] bndr1) $ \(i, b) ->
          if i `IS.member` fullyDet
            then traverseBndrName (\_ -> qNewName "b") b
            else pure b
        pure (bndr1,bndr2)

    n     <- qNewName "x"
    eps   <- traverse mkEps cons

    let cctx = fromMaybe (mkCctx (zip bndr1 bndr2)) defctx
        res = DInstanceD o cctx
          ( applyDType (DConT ''SingEq)
              [ applyDType (DConT nm) (dTyVarBndrToDType . mkPlain <$> bndr1)
              , applyDType (DConT nm) (dTyVarBndrToDType . mkPlain <$> bndr2)
              ]
          )
    pure $ res
          [ DLetDec . DFunD 'singEq $
              [ DClause [DVarPa n] $ DCaseE (DVarE n) eps
              ]
          ]
  where
    findFullyDet :: Map String [Bool] -> [DTyVarBndr] -> IntSet
    findFullyDet insts bndrs =
        foldr IS.intersection (IS.fromList $ zipWith const [0..] bndrs)
                              (determines <$> cons)
      where
        determines :: DCon -> IntSet
        determines (DCon _ _ _ cfs cTy) = IM.keysSet
                                        . IM.filter S.null
                                        . fmap (`S.difference` found)
                                        $ needed'
          where
            needed :: IntMap (Set Name)
            needed = case unApply cTy of
              (DConT _, ts) -> IM.fromList . zip [0..] $
                  map (S.fromList . filter isVar . allNamesIn) ts
              _             -> error "polySingSingEq: Invalid return type on GADT constructor"
            needed' = snd
                    . IM.mapAccum (\seen news -> (seen `S.union` news, news `S.difference` seen)) S.empty
                    $ needed
            found :: Set Name
            found = S.fromList $ do
              t <- case cfs of
                DNormalC _ ts -> map snd ts
                DRecC ts      -> map (\(_,_,t) -> t) ts
              case t of
                (unApply->(DConT n, ts))
                  | n == nm -> foldMap (filter isVar . allNamesIn) ts
                (deSingleApplied->Just (unApply->(DConT n, ts), qs))
                  | Just constSame <- M.lookup (nameBase n) insts
                  -> filter isVar . concat $
                        zipWith (\case False -> allNamesIn; True -> const [])
                          (constSame ++ repeat False) (ts ++ [qs])
                (unApply->(tc, ts)) -> do
                  _ :|> l <- pure $ Seq.fromList (tc : ts)
                  filter isVar . allNamesIn $ l
            -- 1.  Shows up as the *last* argument in any input
            -- 2.  Shows up in any argument covered by a TestEq instance where "both
            --     sides" are different tyvars.
            -- 3.  Shows up in any recursive argument (this should be a sub-case of
            --     #2 that evens out when taking the intersection).
    mkCctx :: [(DTyVarBndr, DTyVarBndr)] -> [DPred]
    mkCctx b0 = nubOrdOn show $ do
      DCon _ _ _ cfs cTy <- cons
      let newBndrs :: [Maybe Name]
          newBndrs = case unApply cTy of
            (DConT _, ts) -> flip map ts $ \case
              DVarT n -> Just n
              DVarT n `DSigT` _ -> Just n
              _       -> Nothing
            _             -> error "polySingKind: Invalid return type on GADT constructor"
          bndrMap :: Map Name (Name, Name)
          bndrMap = M.fromList . catMaybes $
            [ (, (bndrName bO1, bndrName bO2)) <$> bN
            | bN <- newBndrs
            | (bO1, bO2) <- b0
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
      -- potentially bad because it duplicates 'free'
      let V2 (t1, free) (t2, _) = runWriterT . flip (traverseDVarT S.empty) t' $ \v ->
            case M.lookup v bndrMap of
              Just (q1, q2) -> MT.lift $ V2 q1 q2
              Nothing       -> v <$ tell (Endo (v:))
          free' = appEndo free []
      pure $ mkForall (DPlainTV <$> nubOrd free') $
        (DConPr ''SingEq `DAppPr` t1) `DAppPr` t2
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
                         (DConE 'Proved `DAppE` DConE 'HRefl)
                         (zip vs vs2)
              else Just <$> do
                n <- qNewName "z"
                pure . DMatch (DConPa cnm2' (DWildPa <$ vs2)) $
                    DConE 'Disproved `DAppE`
                      DLamE [n] (DCaseE (DVarE n) [])
          where
            cnm2' = mapNameBase singleConstr cnm2
            go (oldN, _) (newN, _) finalRes = do
                n <- qNewName "z"
                m <- qNewName "q"
                pure $ DCaseE (applyDExp (DVarE 'singEq) [DVarE oldN, DVarE newN])
                  [ DMatch (DConPa 'Proved    [DConPa 'HRefl []]) finalRes
                  , DMatch (DConPa 'Disproved [DVarPa n        ]) $
                      DAppE (DConE 'Disproved) $
                        DLamE [m] . DCaseE (DVarE m) $
                          [ DMatch (DConPa 'HRefl []) $ DVarE n `DAppE` DConE 'HRefl
                          ]
                  ]

-- okay. so this works. but how do we know what variables to fix, and what
-- to not?
--
-- It looks like we must, because there is one constructor ATZ
-- where k is not knowable.
--
-- But we *can* let ls, as vary.
--
-- ATZ determines ls, as, but leaves unknown k
-- ATS determins ls, as, k
--
-- So it's the net intersection of all the "knowable" types in each
-- constructor.
--
-- Looks like we can check out what is *knowable* by checking if all of the
-- variables show up as the "last" item in one of the inputs.  that's
-- because we are always checking "last" items.
--
-- So the return type:
--
-- > AggType k (l ': ls) (a ': as)
--
-- Has the variables k, l, ls, a, as.
--
-- * k shows up in (a :: k).  does this count? let's say no, for now.
--   Did some testing and yes, we should say no for now.  i don't think it
--   counts.
-- * l shows up as the last type in `SText l`
-- * ls shows up as a type in `AggType k ls as`.  Maybe we can special-case
--   recursive calls.  Yes.  All recursive calls will assume they can all
--   be determined, since if we get a false positive, this will be factored
--   out in the intersection of the constructors.
-- * a shows up as the last type in `WrappedSing k a
-- * as shows up as the last type in `AggType k ls as`.  We don't need to
--   special-case this, but we could.
--
-- So we count l, a, as from the last-var rule, and ls from the recursive
-- call rule.
--
-- Actually we should also have a TestEq instance rule.  If we have an
-- appropriate TestEq instance that covers the tyvar, we should be able to
-- count it.
--
-- So the rules to count it are:
--
-- 1.  Shows up as the *last* argument in any input
-- 2.  Shows up in any argument covered by a TestEq instance where "both
--     sides" are different tyvars.
-- 3.  Shows up in any recursive argument (this should be a sub-case of
--     #2 that evens out when taking the intersection).
--
-- Situations like vanilla types (Bool) will not run into this, because
-- their result types have no type variables.


-- | Returns the type constructor of the 'SingEq' instance, and also a list
-- of whether or not each field is constrained to be the same.
singEqInstance :: DDec -> Maybe (String, [Bool])
singEqInstance (DInstanceD _ _ t _)
    | (DConT se, [unApply->(DConT a, as), unApply->(DConT b, bs)]) <- unApply t
    , se == ''SingEq
    , a == b
    = Just (nameBase a, zipWith ((==) `on` show) as bs)
singEqInstance _ = Nothing

mkForall :: [DTyVarBndr] -> DPred -> DPred
mkForall xs
    | null xs   = id
    | otherwise = DForallPr (nubOrdOn show (kinds ++ xs)) []
  where
    kinds = [ DPlainTV o | DKindedTV _ k <- xs, o <- allNamesIn k, isVar o ]

bndrName :: DTyVarBndr -> Name
bndrName = getConst . traverseBndrName Const

mkPlain :: DTyVarBndr -> DTyVarBndr
mkPlain = DPlainTV . bndrName

traverseBndrName :: Functor f => (Name -> f Name) -> DTyVarBndr -> f DTyVarBndr
traverseBndrName f (DKindedTV x t) = (`DKindedTV` t) <$> f x
traverseBndrName f (DPlainTV x)    = DPlainTV <$> f x

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
-- SList a      => [a]
--
-- The input is always expected to be (k -> Type).
deSingle :: DType -> Maybe DType
deSingle t = case unApply t of
    -- hey we can do this by reifying the type family for instances
    (DConT c, xs)
      | c == ''PolySing -> case xs of
          y:_ -> Just y
          _   -> Nothing
      | c == ''SingSing             -> Just $ applyDType (DConT ''WrappedSing) xs
      | c == ''SList                -> Just $ applyDType (DConT ''[]) xs
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

isVar :: Name -> Bool
isVar = check . nameBase
  where
    check (c:_)
      | isSymbol c = c /= ':'
      | otherwise  = isLower c
    check _ = error "bad name"

data V2 a = V2 { v2x :: !a, v2y :: !a }
  deriving Functor

instance Applicative V2 where
    pure x = V2 x x
    V2 f g <*> V2 x y = V2 (f x) (g y)

instance Monad V2 where
    return = pure
    V2 x y >>= f = V2 (v2x (f x)) (v2y (f y))
