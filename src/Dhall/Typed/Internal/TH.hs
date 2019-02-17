{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}

module Dhall.Typed.Internal.TH (
    inspector
  , unApply
  , genPolySing
  ) where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.Trans.Writer
import           Data.Bifunctor
import           Data.Char
import           Data.Either
import           Data.List
import           Data.Traversable
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
    decsToTH <$> polySing nod ctx nm bndrs dk cons dervs

-- data DKind ts k where
-- type family SDKindOf ts k (x :: DKind ts k) = (y :: SDKind ts k x) | y -> x where
--     SDKindOf ts k          ('KVar i  ) = 'SKVar (SIndexOf ts k i)

-- type family SDSortOf (k :: DSort) = (s :: SDSort k) | s -> k where
--     SDSortOf 'Kind = 'SKind
--     SDSortOf (a ':*> b) = SDSortOf a ':%*> SDSortOf b

-- data Index :: [k] -> k -> Type where
--     IZ :: Index (a ': as) a
--     IS :: Index bs a -> Index (b ': bs) a
-- type family SIndexOf as a (i :: Index as a) = (s :: SIndex as a i) | s -> i where
--     SIndexOf (a ': as) a 'IZ     = 'SIZ
--     SIndexOf (a ': as) b ('IS i) = 'SIS (SIndexOf as b i)

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
    -> q [DDec]
polySing nod ctx nm bndrs dk cons _dervs = do
    bndr <- (`DKindedTV` bndrKind) <$> qNewName "x"
    dd   <- mkDataDec bndr
    ofa  <- ofFam bndr
    si   <- singI bndr
    -- runQ . reportError $ pprint (sweeten si)
    pure $ [dd, ofa] ++ si
  where
    -- TODO: fixity
    mkDataDec :: DTyVarBndr -> q DDec
    mkDataDec bndr = do
      cons' <- traverse singCons cons
      pure $ DDataD nod ctx nm' (bndrs ++ [bndr]) dk cons' []
    nm' :: Name
    nm' = mapNameBase singleConstr nm
    bndrKind :: DKind
    bndrKind = applyDType (DConT nm) (dTyVarBndrToDType <$> bndrs)
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
        go t = do
          (DConT fnm, targs) <- pure $ unApply t
          if isSingleConstr fnm
            then t <$ tell [ Left $ applyDType (DConT (mapName ofSingle fnm)) targs ]
            else do
              n <- qNewName "x"
              tell [Right $ DPlainTV n]     -- ???
              -- TODO: handle cases from different module?
              -- pure $ applyDType (DConT (mapName singleConstr fnm)) $
              pure $ applyDType (DConT (mapNameBase singleConstr fnm)) $
                targs ++ [DVarT n]
    ofFam :: DTyVarBndr -> q DDec
    ofFam bndr = do
        let newBndrs = bndrs ++ [bndr]
        y <- qNewName "y"
        let k'  = applyDType (DConT nm') (dTyVarBndrToDType <$> newBndrs)
            tfh = DTypeFamilyHead (mapNameBase ofSingle nm')
                    newBndrs
                    (DTyVarSig $ DKindedTV y k')
                    (Just (InjectivityAnn y [bndrName bndr]))
        eqns <- for cons $ \c@(DCon _ _ cnm _ cTy) -> do
          (sat, vs) <- saturate c
          let (_, newArgs) = unApply cTy
              res = applyDType (DConT (mapNameBase singleConstr cnm)) $
                      flip map vs $ \(anm, t) ->
                        let (DConT tC, tA) = unApply t
                            tC' = mapNameBase (ofSingle . singleConstr) tC
                        in  applyDType (DConT tC') $ tA ++ [DVarT anm]
          pure $ DTySynEqn (newArgs ++ [sat]) res
        pure $ DClosedTypeFamilyD tfh eqns
    singI :: DTyVarBndr -> q [DDec]
    singI bndr = do
        insts <- for cons $ \c@(DCon _ _ cnm cfs cTy) -> do
          (sat, vs) <- saturate c
          let (_, newArgs) = unApply cTy
          cctx <- for vs $ \(aN, aT) -> do
            (DConT atc, atarg) <- pure $ unApply aT
            pure . foldl' DAppPr (DConPr (mapNameBase iSingleConstr atc)) $
                    atarg ++ [DVarT aN]
          valArgs <- maybe (fail "Bad val arg") pure $ case cfs of
             DNormalC _ xs -> traverse (typeSingI . snd) xs
             DRecC xs      -> traverse (\(_,_,t) -> typeSingI t) xs
          pure $ DInstanceD Nothing cctx
            (applyDType (DConT clsNm) $ newArgs ++ [sat])
            [DLetDec . DFunD mthdNm $
               [ DClause [] . applyDExp (DConE (mapNameBase singleConstr cnm)) $
                   map DVarE valArgs
                  
               ]
            ]
        pure $ cls : insts
      where
        clsNm  = mapNameBase iSingleConstr nm
        mthdNm = mapNameBase iSingleValue nm
        cls = DClassD ctx clsNm
          (bndrs ++ [bndr])
          [FunDep [bndrName bndr] (bndrName <$> bndrs)]
          [DLetDec . DSigD mthdNm . applyDType (DConT nm')
             $ dTyVarBndrToDType <$> (bndrs ++ [bndr])
          ]

bndrName :: DTyVarBndr -> Name
bndrName (DKindedTV x _) = x
bndrName (DPlainTV x   ) = x

typeSingI :: DType -> Maybe Name
typeSingI t
  | (DConT c, _) <- unApply t = Just $ mapNameBase iSingleValue c
  | otherwise                 = Nothing


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

iSingleConstr :: String -> String
iSingleConstr (':':cs) = ":%" ++ cs ++ "?"
iSingleConstr cs = 'S' : cs ++ "I"

-- | Turn a type constructor into the "SingI" method name
iSingleValue :: String -> String
iSingleValue (':':cs) = '?':cs
iSingleValue cs       = 's':cs
  
