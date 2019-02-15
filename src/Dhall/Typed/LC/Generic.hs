{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}


module Dhall.Typed.LC.Generic (
  ) where

import           Data.Kind
import           Dhall.Typed.Index
import           Dhall.Typed.Prod

-- data V k = V (k -> k -> k) ([k] -> k -> Type)

data Value k :: (k -> k -> k) -> ([k] -> k -> Type) -> k -> Maybe [k] -> k -> Type where
    P   :: prim as a -> Prod (Value k fun prim const vs) as -> Value k fun prim const vs a
    Var :: Index vs a
        -> Value k fun prim const ('Just vs) a
    Lam :: Sing v
        -> Value k fun prim const ('Just (v ': vs)) a
        -> Value k fun prim const ('Just vs) (fun v a)
    App :: Value k fun prim const ('Just vs) (fun a b)
        -> Value k fun prim const ('Just vs) a
        -> Value k fun prim const ('Just vs) b

    Fun :: Value k fun prim const vs const
        -> Value k fun prim const vs const
        -> Value k fun prim const vs const

    Pi  :: Sing v
        -> Value k fun prim const ('Just (v ': vs)) a
        -> Value k fun prim const ('Just vs       ) a

--     TPoly :: SDSort t
--           -> DType (t ': ts) (Map (KShiftSym ts t 'Kind) us) a
--           -> DType ts        us                              ('KPi (SDSortOf t) a)
--     TInst :: DType ts us ('KPi (SDSortOf t) b)
--           -> SDKind ts t a
--           -> DType ts us (KSub (t ': ts) ts t 'Kind 'DZ a b)
    -- (:->) :: DType ts us 'Type -> DType ts us 'Type -> DType ts us 'Type
    -- Pi    :: SDKind ts 'Kind u -> DType ts (u ': us) a -> DType ts us a
