{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies   #-}
{-# LANGUAGE TypeInType     #-}
{-# LANGUAGE TypeOperators  #-}

module Dhall.Typed.Type.Bool (
    type (&&)
  ) where

type family (x :: Bool) && (y :: Bool) :: Bool where
    'False && x = 'False
    'True  && x = x
