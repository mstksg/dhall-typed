{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE QuantifiedConstraints  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}

module Dhall.Typed.Type.Singletons (
    PolySing
  , PolySingI(..)
  , PolySingKind(..)
  , SomePolySing(..)
  , WrappedSing(..)
  , SingSing(..)
  , PolySingOfI
  ) where

import           Dhall.Typed.Type.Singletons.Internal
import           Dhall.Typed.Internal.TH
import           Control.Applicative


genPolySing ''Const
