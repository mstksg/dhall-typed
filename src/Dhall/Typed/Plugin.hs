{-# LANGUAGE EmptyCase           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}

module Dhall.Typed.Plugin (
    plugin
  ) where

import           Control.Applicative
import           Control.Monad
import           Data.Maybe
import           DataCon
import           Dhall.Typed.Type.N
import           GHC.TcPluginM.Extra
import           Module
import           OccName
import           Plugins
import           TcEvidence
import           TcPluginM
import           TcRnTypes
import           TyCoRep             (Type (..))
import           TyCon
import           Type
import qualified Data.Kind           as K


plugin :: Plugin
plugin = defaultPlugin
    { tcPlugin = const $ Just subShiftEq
    , pluginRecompile = purePlugin
    }

subShiftEq :: TcPlugin
subShiftEq = tracePlugin "dhall-typed-plugin"
    TcPlugin { tcPluginInit  = lookupDTTC
             , tcPluginSolve = solveSubShift
             , tcPluginStop  = const (return ())
             }

solveSubShift
  :: DTTyCons
  -> [Ct]
  -> [Ct]
  -> [Ct]
  -> TcPluginM TcPluginResult
solveSubShift _dtty _givens _deriveds []      = return (TcPluginOk [] [])
solveSubShift dtty  _  _deriveds wanteds = do
    let wanteds'     = filter (isWanted . ctEvidence) wanteds
        unit_wanteds = mapMaybe (toSubShiftEquality dtty) wanteds'
    pure $ TcPluginOk unit_wanteds []

data DTTyCons = DTTC { dttcSub   :: TyCon       -- ^ 'Dhall.Typed.Core.Sub'
                     , dttcShift :: TyCon       -- ^ 'Dhall.Typed.Core.Shift'
                     , dttcDKind :: TyCon       -- ^ 'Dhall.Typed.Core.DKind'
                     , dttcDZ    :: TyCon       -- ^ lifted 'Dhall.Typed.Index.DZ'
                     , dttcDS    :: TyCon       -- ^ lifted 'Dhall.Typed.Index.DZ'
                     , dttcInsZ  :: TyCon       -- ^ lifted 'Dhall.Typed.Index.IndZ'
                     }

lookupDTTC :: TcPluginM DTTyCons
lookupDTTC = do
    core  <- lookupModule (mkModuleNameFS "Dhall.Typed.Core") "dhall-typed"
    index <- lookupModule (mkModuleNameFS "Dhall.Typed.Index") "dhall-typed"
    dttcSub   <- tcLookupTyCon   =<< lookupName core (mkTcOccFS "Sub")
    dttcShift <- tcLookupTyCon   =<< lookupName core (mkTcOccFS "Shift")
    dttcDKind <- tcLookupTyCon   =<< lookupName core (mkTcOccFS "DKind")    -- should we promote?
    dttcDZ    <- fmap promoteDataCon . tcLookupDataCon =<< lookupName index (mkDataOccFS "DZ")
    dttcDS    <- fmap promoteDataCon . tcLookupDataCon =<< lookupName index (mkDataOccFS "DS")
    dttcInsZ  <- fmap promoteDataCon . tcLookupDataCon =<< lookupName index (mkDataOccFS "InsZ")
    pure DTTC{..}


toSubShiftEquality :: DTTyCons -> Ct -> Maybe (EvTerm, Ct)
toSubShiftEquality dttc ct = (,ct) <$> case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2 -> go t1 t2 <|> go t2 t1
    _                  -> Nothing
  where
    go t1 t2 = do
      t3 <- subShiftTerm dttc t1
      guard $ t3 `eqType` t2
      pure $ evByFiat "sub-shift" t1 t2


-- Sub 0 X (Shift X)
--
-- Sob 0 - x
--       \ Shift x
--
-- Sub 0 X (Sub 1 (Shift X) (Shift (Shift X)))
--
-- Sub 0 - X
--       \ Sub 1 - Shift X
--               \ Shift (Shift X)
--
-- Sub 0 X (Sub 1 (Shift X) (Sub 2 (Shift (Shift X)) (Shift (Shift (Shift X)))
--
-- Sub 0 - X
--       \ Sub 1 - Shift X
--               \ Sub 2   - Shift (Shift X)
--                         \ Shift (Shift (Shift X))

data ShiftMatch :: N -> K.Type where
    ShiftMatch :: Type -> ShiftMatch n

data SubMatch :: N -> K.Type where
    SubMatch :: ShiftMatch n
             -> Either (ShiftMatch ('S n)) (SubMatch ('S n))
             -> SubMatch n

finalMatch
    :: SubMatch n
    -> Type
finalMatch (SubMatch _ y) = case y of
    Left (ShiftMatch x) -> x
    Right s             -> finalMatch s

parseShift
    :: DTTyCons
    -> Sing n
    -> Type
    -> Maybe (ShiftMatch n)
parseShift DTTC{..} = go
  where
    go :: Sing m -> Type -> Maybe (ShiftMatch m)
    go = \case
      SZ   -> pure . ShiftMatch
      SS m -> \t -> do
        shift `TyConApp` [ _ , _ , _ , _ , TyConApp ins _ , a ] <- Just t
        guard $ shift == dttcShift
             && ins   == dttcInsZ
        ShiftMatch b <- go m a
        pure $ ShiftMatch b

parseSub
    :: DTTyCons
    -> Sing n
    -> Type
    -> Maybe (SubMatch n)
parseSub tc@DTTC{..} = go
  where
    go :: Sing m -> Type -> Maybe (SubMatch m)
    go n t = do
      sub `TyConApp` [_, _, _, _, del, s, a] <- Just t
      guard $ sub == dttcSub
           && parseDel tc n del
      shift <- parseShift tc n s
      rest  <- (Left  <$> parseShift tc (SS n) a)
           <|> (Right <$> go (SS n) a           )
      pure $ SubMatch shift rest

parseDel
    :: forall (n :: N). ()
    => DTTyCons
    -> Sing n
    -> Type
    -> Bool
parseDel DTTC{..} = go
  where
    go :: forall (m :: N). Sing m -> Type -> Bool
    go = \case
      SZ -> \case
        dz `TyConApp` _ -> dz == dttcDZ
        _               -> False
      SS n -> \case
        ds `TyConApp` [_, _, _, _, _, d] -> ds == dttcDS && go n d
        _                                -> False

-- |
--
-- @
-- Sub '[j] '[] j k 'DZ b (Shift '[] '[j] j k 'InsZ a))
-- -- => a
-- @
--
-- @
-- Sub '[ l ] '[] l k 'DZ c
--   (Sub '[l, j] '[ l ] j k ('DS 'DZ) (Shift '[] '[ l ] l j 'InsZ b)
--       (Shift '[ j ] '[ l, j ] l k 'InsZ
--          (Shift '[] '[ j ] j k 'InsZ a)
--       )
--   )
-- -- => a
-- @
subShiftTerm
    :: DTTyCons
    -> Type
    -> Maybe Type
subShiftTerm d = fmap finalMatch . parseSub d SZ
