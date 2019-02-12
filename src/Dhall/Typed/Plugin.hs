{-# LANGUAGE EmptyCase         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE TypeFamilies      #-}

module Dhall.Typed.Plugin (
    plugin
  ) where

import           Control.Applicative
import           Control.Monad
import           Data.Maybe
import           DataCon
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
import           TysWiredIn


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

-- |
--
-- @
-- Sub '[j] '[] j k 'DZ b (Shift '[] '[j] j k 'InsZ a))
-- -- => a
-- @
--
--
-- TODO: double/triple Pi's? check.
subShiftTerm
    :: DTTyCons
    -> Type
    -> Maybe Type
subShiftTerm DTTC{..} t = do
    sub   `TyConApp` [ TyConApp c0 [ TyConApp dk0 []
                                   , TyConApp j0 []
                                   , TyConApp n0 [TyConApp dk1 []]
                                   ]
                     , TyConApp n1 [ TyConApp dk2 [] ]
                     , TyConApp j1 []
                     , TyConApp k0 []
                     , TyConApp d  [ TyConApp dk3 []
                                   , TyConApp j2 []
                                   , TyConApp n2 [TyConApp dk4 []]
                                   ]
                     , _
                     , r
                     ] <- Just t
    shift `TyConApp` [ TyConApp n3 [ TyConApp dk5 [] ]
                     , TyConApp c1 [ TyConApp dk6 []
                                   , TyConApp j3 []
                                   , TyConApp n4 [TyConApp dk7 []]
                                   ]
                     , TyConApp j4 []
                     , TyConApp k1 []
                     , TyConApp i  [ TyConApp dk8 []
                                   , TyConApp n5 [TyConApp dk9 []]
                                   , TyConApp j5  []
                                   ]
                     , a
                     ] <- Just r
    guard . and $
      [ j0 == j1 && j1 == j2 && j2 == j3 && j3 == j4 && j4 == j5
      , k0 == k1
      , all (== promotedNilDataCon ) [n0, n1, n2, n3, n4, n5]
      , all (== promotedConsDataCon) [c0, c1]
      , all (== dttcDKind)           [dk0, dk1, dk2, dk3, dk4, dk5, dk6, dk7, dk8, dk9]
      , sub   == dttcSub
      , shift == dttcShift
      , d     == dttcDZ
      , i     == dttcInsZ
      ]
    pure a
