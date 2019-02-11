
module Dhall.Typed.Plugin (
    plugin
  ) where

import           GHC.TcPluginM.Extra
import           Plugins
import           TcRnTypes


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
