{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PartialTypeSignatures  #-}
{-# LANGUAGE QuantifiedConstraints  #-}
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
    Index(..), SIndex(..), sSameIx, fromSIndex -- , SIndexOf
  , SSIndex(..)
  -- * Delete
  , Delete(..), del, ISMaybe, Del, SDelete(..), sDel, GetDeleted(..)
  -- * Insert
  , Insert(..), insert, Ins, sIns, SInsert(..)
  -- * Singletons
  , Sing(SIx, getSIx)
  ) where

import           Data.Kind
import           Data.Singletons
import           Data.Type.Equality
import           Data.Type.Universe
import           Dhall.Typed.Internal.TH
import           Dhall.Typed.Type.Singletons
import qualified GHC.TypeLits                as TL

genPolySing ''Index

genPolySing ''SIndex

-- data SIndex as a :: Index as a -> Type where
--     SIZ :: SIndex (a ': as) a 'IZ
--     SIS :: SIndex as b i -> SIndex (a ': as) b ('IS i)

deriving instance Show (SIndex as a i)

-- type instance PolySing (Index as a) = SIndex as a

-- type instance PolySingOf (SIndex (a ': as) a) 'IZ     = 'SIZ
-- type instance PolySingOf (SIndex (a ': as) b) ('IS i) = 'SIS (PolySingOf (SIndex as b) i)

-- type SIndexOf as a (i :: Index as a) = (PolySingOf i :: SIndex as a i)

-- type instance PolySing (SIndex as a i) = SingSing (Index as a) i

-- instance PolySingI (SIndex (a ': as) a) 'IZ where
--     type PolySingOf 'IZ = 'SIZ
--     polySing = SIZ

-- instance PolySingI (SIndex as b) i => PolySingI (SIndex (a ': as) b) ('IS i) where
--     type PolySingOf ('IS i) = 'SIS (PolySingOf i)
--     polySing = SIS polySing

-- newtype SSIndex as a i :: SIndex as as i -> Type where
-- newtype SingSing k x :: PolySing k x -> Type where
--     SingSing :: forall k (x :: k) (s :: PolySing k x). PolySing k x -> SingSing k x s

-- instance PolySingKind (Index as a) where
--     fromPolySing = \case
--       SIZ   -> IZ
--       SIS i -> IS (fromPolySing i)
--     toPolySing = \case
--       IZ   -> SomePS SIZ
--       IS i -> case toPolySing i of
--         SomePS j -> SomePS (SIS j)

newtype instance Sing (i :: Index as a) where
    SIx  :: { getSIx  :: SIndex as a i } -> Sing i

instance SingKind (Index as a) where
    type Demote (Index as a) = Index as a

    fromSing (SIx i) = case i of
      SIZ   -> IZ
      SIS j -> IS (fromSing (SIx j))

    toSing = \case
      IZ   -> SomeSing (SIx SIZ)
      IS i -> case toSing i of
        SomeSing (SIx j) -> SomeSing (SIx (SIS j))

-- class SIndexI as a (i :: Index as a) | i -> as a where
--     sIndex :: SIndex as a i

-- instance SIndexI (a ': as) a 'IZ where
--     sIndex = SIZ

-- instance SIndexI as b i => SIndexI (a ': as) b ('IS i) where
--     sIndex = SIS sIndex

-- type instance SIndexOf 
-- type family PolySingOf k (x :: k) = (y :: PolySing k x) | y -> x
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

genPolySing ''Delete

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

del :: Delete as bs a -> Index as b -> Maybe (Index bs b)
del = \case
    DelZ -> \case
      IZ   -> Nothing
      IS i -> Just i
    DelS d -> \case
      IZ   -> Just IZ
      IS i -> IS <$> del d i

data GetDeleted as bs a b :: Delete as bs a -> Index as b -> Type where
    GotDeleted :: (Del as bs a b del i ~ 'Nothing) => a :~: b -> GetDeleted as bs a b del i
    ThatsToxic :: (Del as bs a b del i ~ 'Just j ) => SIndex bs b j -> GetDeleted as bs a b del i

sDel
    :: SDelete as bs a del
    -> SIndex as b i
    -> GetDeleted as bs a b del i
sDel = \case
    SDelZ -> \case
      SIZ   -> GotDeleted Refl
      SIS i -> ThatsToxic i
    SDelS d -> \case
      SIZ   -> ThatsToxic SIZ
      SIS i -> case sDel d i of
        GotDeleted Refl -> GotDeleted Refl
        ThatsToxic j    -> ThatsToxic (SIS j)


-- | This is just flipped delete, heh.
data Insert :: [k] -> [k] -> k -> Type where
    InsZ :: Insert as (a ': as) a
    InsS :: Insert as bs c -> Insert (a ': as) (a ': bs) c

genPolySing ''Insert

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

sIns
    :: forall as bs a b ins i. ()
    => SInsert as bs a ins
    -> SIndex as b i
    -> SIndex bs b (Ins as bs a b ins i)
sIns = \case
    SInsZ     -> SIS
    SInsS ins -> \case
      SIZ   -> SIZ
      SIS i -> SIS (sIns ins i)

