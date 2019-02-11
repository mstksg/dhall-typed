{-# LANGUAGE EmptyCase       #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies    #-}

module Dhall.Typed.Plugin (
    plugin
  ) where

import           GHC.TcPluginM.Extra
import           Plugins
import           TyCon
import           Dhall.Typed.Core
import           TcRnTypes
import           TyCoRep             (Type (..))
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

-- toSubShiftEquality :: Ct -> Maybe [(Type, Type)]
-- toSubShiftEquality ct = do
--     EqPred NomEq t1 t2 <- Just . classifyPredType . ctEvPred . ctEvidence $ ct
--     Nothing



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

-- type family Foo

-- subTyCon :: TyCon
-- subTyCon = mkFamilyTyCon ''Foo

-- toNatEquality :: Ct -> Maybe (Either NatEquality NatInEquality,[(Type,Type)])
-- toNatEquality ct = case classifyPredType $ ctEvPred $ ctEvidence ct of

-- Sub '[ 'Type] '[] 'Type 'Type 'Type 'DZ b (Shift '[] '[ 'Type] 'Type 'Type 'InsZ a)
--  ~ a
--
--
--   SDType '[ 'Type] 'Type (Shift '[] '[ 'Type] 'Type 'Type 'InsZ a)
--     ~ SDType '[] 'Type a

-- sShift
--     :: SInsert as bs a ins
--     -> SDType as b x
--     -> SDType bs b (Shift as bs a b ins x)

-- sShift
--     :: SInsert as bs a ins
--     -> SDType as b x
--     -> SDType bs b (Shift as bs a b ins x)
