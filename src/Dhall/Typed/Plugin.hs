{-# LANGUAGE EmptyCase       #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module Dhall.Typed.Plugin (
    plugin
  ) where

import           Control.Monad
import           Dhall.Typed.Core    ()
import           GHC.TcPluginM.Extra
import           Plugins
import           TcRnTypes
import           TyCoRep             (Type (..))
import           TyCon
import           Type


plugin :: Plugin
plugin = defaultPlugin
    { tcPlugin = const $ Just subShiftEq
    , pluginRecompile = purePlugin
    }

subShiftEq :: TcPlugin
subShiftEq = tracePlugin "dhall-typed-plugin"
    TcPlugin { tcPluginInit  = return ()
             , tcPluginSolve = const solveSubShift
             , tcPluginStop  = const (return ())
             }

solveSubShift
  :: [Ct]
  -> [Ct]
  -> [Ct]
  -> TcPluginM TcPluginResult
solveSubShift = undefined

-- Sub '[ 'Type] '[] 'Type 'Type 'Type 'DZ b (Shift '[] '[ 'Type] 'Type 'Type 'InsZ a)
--  ~ a

data DTTyCons = DTTC { dttcSub   :: TyCon       -- ^ 'Dhall.Typed.Core.Sub'
                     , dttcShift :: TyCon       -- ^ 'Dhall.Typed.Core.Shift'
                     , dttcDZ    :: TyCon       -- ^ lifted 'Dhall.Typed.Index.DZ'
                     , dttcInsZ  :: TyCon       -- ^ lifted 'Dhall.Typed.Index.IndZ'
                     , dttcNil   :: TyCon       -- ^ lifted '[]'
                     , dttcCons  :: TyCon       -- ^ lifted ':'
                     }

-- toSubShiftEquality :: DTTyCons -> Ct -> Maybe [(Type, Type)]
-- toSubShiftEquality DTTC{..} ct = case classifyPredType $ ctEvPred $ ctEvidence ct of
--     EqPred NomEq t1 t2 -> go t1 t2
--     _                  -> Nothing
--   where
--     go x y = undefined


-- |
--
-- @
-- Sub '[j] '[] j k j 'DZ b (Shift '[] '[j] j k 'InsZ a))
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
    sub   `TyConApp` [ TyConApp c0 [TyConApp j0 [], TyConApp n0 []]
                     , TyConApp n1 []
                     , TyConApp j1 []
                     , TyConApp k0 []
                     , TyConApp j2 []
                     , TyConApp d []
                     , _
                     , r
                     ] <- Just t
    shift `TyConApp` [ TyConApp n2 []
                     , TyConApp c1 [TyConApp j3 [], TyConApp n3 []]
                     , TyConApp j4 []
                     , TyConApp k1 []
                     , TyConApp i  []
                     , a
                     ] <- Just r
    guard . and $
      [ j0 == j1 && j1 == j2 && j2 == j3 && j3 == j4
      , k0 == k1
      , all (== dttcNil ) [n0, n1, n2, n3]
      , all (== dttcCons) [c0, c1]
      , sub   == dttcSub
      , shift == dttcShift
      , d     == dttcDZ
      , i     == dttcInsZ
      ]
    pure a

    -- go (TyConApp tc xs) (TyConApp tc' ys)
    --   | tc == tc'
    --   , null ([tc,tc'] `intersect` [typeNatAddTyCon,typeNatSubTyCon
    --                                ,typeNatMulTyCon,typeNatExpTyCon])
    --   = case filter (not . uncurry eqType) (zip xs ys) of
    --       [(x,y)]
    --         | isNatKind (typeKind x)
    --         , isNatKind (typeKind y)
    --         , let (x',k1) = runWriter (normaliseNat x)
    --         , let (y',k2) = runWriter (normaliseNat y)
    --         -> Just (Left (ct, x', y'),k1 ++ k2)
    --       _ -> Nothing
    --   | tc == typeNatLeqTyCon
    --   , [x,y] <- xs
    --   , let (x',k1) = runWriter (normaliseNat x)
    --   , let (y',k2) = runWriter (normaliseNat y)
    --   , let ks      = k1 ++ k2
    --   = case tc' of
    --      _ | tc' == promotedTrueDataCon
    --        -> Just (Right (ct, (x', y', True)), ks)
    --      _ | tc' == promotedFalseDataCon
    --        -> Just (Right (ct, (x', y', False)), ks)
    --      _ -> Nothing
    -- go x y
    --   | isNatKind (typeKind x)
    --   , isNatKind (typeKind y)
    --   , let (x',k1) = runWriter (normaliseNat x)
    --   , let (y',k2) = runWriter (normaliseNat y)
    --   = Just (Left (ct,x',y'),k1 ++ k2)
    --   | otherwise
    --   = Nothing
