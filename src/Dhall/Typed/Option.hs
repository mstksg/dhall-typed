{-# LANGUAGE GADTs          #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType     #-}

module Dhall.Typed.Option (
    Option(..)
  ) where

import           Data.Kind

data Option :: (k -> Type) -> Maybe k -> Type where
    Noth :: Option f 'Nothing
    Jus  :: f a -> Option f ('Just a)
