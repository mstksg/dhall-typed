{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PartialTypeSignatures  #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE StandaloneDeriving     #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# OPTIONS_GHC -fno-warn-orphans   #-}

module Dhall.Typed.Type.Index (
  -- * Index
    Index(..), SIndex(..), SIndexI(..), sSameIx, fromSIndex, SIndexOf
  -- * Delete
  , Delete(..), delete, ISMaybe, Del, SDelete(..), sDelete, GetDeleted(..)
  -- * Insert
  , Insert(..), insert, Ins, sInsert, SInsert(..)
  -- * Singletons
  , Sing(SIx, getSIx)
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Type.Equality
import           Data.Type.Universe
import           Dhall.Typed.Internal.TH
import qualified GHC.TypeLits            as TL

genPolySing ''Index

deriving instance Show (SIndex as a i)

class SIndexI as a (i :: Index as a) where
    sIndex :: SIndex as a i

instance SIndexI (a ': as) a 'IZ where
    sIndex = SIZ
instance SIndexI as b i => SIndexI (a ': as) b ('IS i) where
    sIndex = SIS sIndex

data instance Sing (i :: Index as a) where
    SIx  :: { getSIx  :: SIndex as a i } -> Sing i

instance SingKind (Index as a) where
    type Demote (Index as a) = Index as a

    fromSing (SIx i) = go i
      where
        go :: SIndex bs b i -> Index bs b
        go = \case
          SIZ   -> IZ
          SIS j -> IS (go j)

    toSing = \case
      IZ   -> SomeSing (SIx SIZ)
      IS i -> withSomeSing i (SomeSing . SIx . SIS . getSIx)

-- data SIndex as a :: Index as a -> Type where
--     SIZ :: SIndex (a ': as) a 'IZ
--     SIS :: SIndex as b i -> SIndex (a ': as) b ('IS i)

-- type family SIndexOf as a (i :: Index as a) = (s :: SIndex as a i) | s -> i where
--     SIndexOf (a ': as) a 'IZ     = 'SIZ
--     SIndexOf (a ': as) b ('IS i) = 'SIS (SIndexOf as b i)

sSameIx :: SIndex as a i -> SIndex as a j -> Maybe (i :~: j)
sSameIx = undefined

fromSIndex :: SIndex as a i -> Index as a
fromSIndex = \case
    SIZ   -> IZ
    SIS i -> IS (fromSIndex i)

data Delete :: [k] -> [k] -> k -> Type where
    DelZ :: Delete (a ': as) as a
    DelS :: Delete as bs c -> Delete (a ': as) (a ': bs) c

data SDelete as bs a :: Delete as bs a -> Type where
    SDelZ :: SDelete (a ': as) as a 'DelZ
    SDelS :: SDelete as bs c del -> SDelete (a ': as) (a ': bs) c ('DelS del)

type family ISMaybe (i :: Maybe (Index as a)) :: Maybe (Index (b ': as) a) where
    ISMaybe 'Nothing = 'Nothing
    ISMaybe ('Just i) = 'Just ('IS i)
    ISMaybe i = TL.TypeError ('TL.Text "No ISMaybe: " 'TL.:<>: 'TL.ShowType i)

type family Del as bs a b (d :: Delete as bs a) (i :: Index as b) :: Maybe (Index bs b) where
    Del (a ': as) as        a a 'DelZ     'IZ     = 'Nothing
    Del (a ': as) (a ': bs) b a ('DelS d) 'IZ     = 'Just 'IZ
    Del (a ': as) as        a b 'DelZ     ('IS i) = 'Just i
    Del (a ': as) (a ': bs) b c ('DelS d) ('IS i) = ISMaybe (Del as bs b c d i)
    Del as bs a b d i = TL.TypeError ('TL.Text "No Del: " 'TL.:<>: 'TL.ShowType '(as, bs, a, b, d, i))

delete :: Delete as bs a -> Index as b -> Maybe (Index bs b)
delete = \case
    DelZ -> \case
      IZ   -> Nothing
      IS i -> Just i
    DelS d -> \case
      IZ   -> Just IZ
      IS i -> IS <$> delete d i

data GetDeleted as bs a b :: Delete as bs a -> Index as b -> Type where
    GotDeleted :: (Del as bs a b del i ~ 'Nothing) => a :~: b -> GetDeleted as bs a b del i
    ThatsToxic :: (Del as bs a b del i ~ 'Just j ) => SIndex bs b j -> GetDeleted as bs a b del i

sDelete
    :: SDelete as bs a del
    -> SIndex as b i
    -> GetDeleted as bs a b del i
sDelete = \case
    SDelZ -> \case
      SIZ   -> GotDeleted Refl
      SIS i -> ThatsToxic i
    SDelS d -> \case
      SIZ   -> ThatsToxic SIZ
      SIS i -> case sDelete d i of
        GotDeleted Refl -> GotDeleted Refl
        ThatsToxic j    -> ThatsToxic (SIS j)


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

