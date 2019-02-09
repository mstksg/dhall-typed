{-# LANGUAGE EmptyCase             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE PartialTypeSignatures #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

module Dhall.Typed.Index (
  -- * Index
    Index(..), SIndex(..), sSameIx
  -- * Delete
  , Delete(..), delete, ISMaybe, Del, SDelete(..), sDelete, SDeleted(..)
  -- * Insert
  , Insert(..), insert, Ins, sInsert, SInsert(..)
  ) where

import           Data.Kind
import           Data.Type.Universe
import           Data.Type.Equality
import qualified GHC.TypeLits as TL

data SIndex as a :: Index as a -> Type where
    SIZ :: SIndex (a ': as) a 'IZ
    SIS :: SIndex as b i -> SIndex (a ': as) b ('IS i)

deriving instance Show (SIndex as a i)

sSameIx :: SIndex as a i -> SIndex as a j -> Maybe (i :~: j)
sSameIx = undefined

data Delete :: [k] -> [k] -> k -> Type where
    DZ :: Delete (a ': as) as a
    DS :: Delete as bs c -> Delete (a ': as) (a ': bs) c

data SDelete as bs a :: Delete as bs a -> Type where
    SDZ :: SDelete (a ': as) as a 'DZ
    SDS :: SDelete as bs c del -> SDelete (a ': as) (a ': bs) c ('DS del)

type family ISMaybe (i :: Maybe (Index as a)) :: Maybe (Index (b ': as) a) where
    ISMaybe 'Nothing = 'Nothing
    ISMaybe ('Just i) = 'Just ('IS i)
    ISMaybe i = TL.TypeError ('TL.Text "No ISMaybe: " 'TL.:<>: 'TL.ShowType i)

type family Del as bs a b (d :: Delete as bs a) (i :: Index as b) :: Maybe (Index bs b) where
    Del (a ': as) as        a a 'DZ     'IZ     = 'Nothing
    Del (a ': as) (a ': bs) b a ('DS d) 'IZ     = 'Just 'IZ
    Del (a ': as) as        a b 'DZ     ('IS i) = 'Just i
    Del (a ': as) (a ': bs) b c ('DS d) ('IS i) = ISMaybe (Del as bs b c d i)
    Del as bs a b d i = TL.TypeError ('TL.Text "No Del: " 'TL.:<>: 'TL.ShowType '(as, bs, a, b, d, i))

delete :: Delete as bs a -> Index as b -> Maybe (Index bs b)
delete = \case
    DZ -> \case
      IZ   -> Nothing
      IS i -> Just i
    DS d -> \case
      IZ   -> Just IZ
      IS i -> IS <$> delete d i

data SDeleted as bs a b :: Delete as bs a -> Index as b -> Maybe (Index bs b) -> Type where
    NoDelete  :: (Del as bs a b del i ~ 'Nothing) => SDeleted as bs a b del i 'Nothing
    YesDelete :: (Del as bs a b del i ~ 'Just j)  => SIndex bs b j -> SDeleted as bs a b del i ('Just j)

sDelete
    :: SDelete as bs a del
    -> SIndex as b i
    -> SDeleted as bs a b del i (Del as bs a b del i)
sDelete = \case
    SDZ -> \case
      SIZ   -> NoDelete
      SIS i -> YesDelete i
    SDS d -> \case
      SIZ   -> YesDelete SIZ
      SIS i -> case sDelete d i of
        NoDelete    -> NoDelete
        YesDelete j -> YesDelete (SIS j)

-- | This is just flipped delete, heh.
data Insert :: [k] -> [k] -> k -> Type where
    InsZ :: Insert as (a ': as) a
    InsS :: Insert as bs c -> Insert (a ': as) (a ': bs) c

data SInsert as bs a :: Insert as bs a -> Type where
    SInsZ :: SInsert as (a ': as) a 'InsZ
    SInsS :: SInsert as bs c ins -> SInsert (a ': as) (a ': bs) c ('InsS ins)

insert :: Insert as bs a -> Index as b -> Index bs b
insert = \case
    InsZ     -> IS
    InsS ins -> \case
      IZ   -> IZ
      IS i -> IS (insert ins i)

type family Ins as bs a b (ins :: Insert as bs a) (i :: Index as b) :: Index bs b where
    Ins as        (a ': as) a b 'InsZ       i       = 'IS i
    Ins (b ': as) (b ': bs) a b ('InsS ins) 'IZ     = 'IZ
    Ins (c ': as) (c ': bs) a b ('InsS ins) ('IS i) = 'IS (Ins as bs a b ins i)

sInsert
    :: forall as bs a b ins i. ()
    => SInsert as bs a ins
    -> SIndex as b i
    -> SIndex bs b (Ins as bs a b ins i)
sInsert = \case
    SInsZ     -> SIS
    SInsS ins -> \case
      SIZ   -> SIZ
      SIS i -> SIS (sInsert ins i)

