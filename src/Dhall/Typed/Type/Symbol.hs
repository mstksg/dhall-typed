{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType     #-}

module Dhall.Typed.Type.Symbol (
    TLSSym(..)
    -- SSym(..)
  -- , Symbol_(..)
  -- , Sing (SSym_, getSSym_)
  ) where

import           GHC.TypeLits
import           Data.Singletons
import           Data.Kind

data TLSSym :: Symbol -> Type where
    TLSSym :: TLSSym s

-- data SSym :: Symbol -> Type where
--     SSym :: KnownSymbol s => SSym s

-- newtype Symbol_ = S_ { getS_ :: Symbol }

-- data instance Sing (x :: Symbol_) where
--     SSym_ :: { getSSym_ :: SSym x } -> Sing ('S_ x)

-- type family SSymOf (x :: Symbol) = (y :: SSym x) | y -> x where
--     SSymOf x = 'SSym
