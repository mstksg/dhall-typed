{-# LANGUAGE EmptyCase            #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Dhall.Typed.Index (
  -- * Delete
    Delete(..), delete, ISMaybe, Del
  -- * Insert
  , Insert(..), insert, Ins, sInsert
  -- * Singletons
  , Sing (SIZ, SIS, SInsZ, SInsS)
  ) where

import           Data.Kind
import           Data.Type.Universe
import qualified GHC.TypeLits as TL

data instance Sing (i :: Index as a) where
    SIZ :: Sing 'IZ
    SIS :: Sing i -> Sing ('IS i)


data Delete :: [k] -> [k] -> k -> Type where
    DZ :: Delete (a ': as) as a
    DS :: Delete as bs c -> Delete (a ': as) (a ': bs) c

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

-- | This is just flipped delete, heh.
data Insert :: [k] -> [k] -> k -> Type where
    InsZ :: Insert as (a ': as) a
    InsS :: Insert as bs c -> Insert (a ': as) (a ': bs) c

data instance Sing (i :: Insert as bs a) where
    SInsZ :: Sing 'InsZ
    SInsS :: Sing i -> Sing ('InsS i)

insert :: Insert as bs a -> Index as b -> Index bs b
insert = \case
    InsZ     -> IS
    InsS ins -> \case
      IZ   -> IZ
      IS i -> IS (insert ins i)

type family Ins as bs a b (ins :: Insert as bs a) (i :: Index as b) :: Index bs b where
    Ins as        (a ': as) a b 'InsZ       i       = 'IS i
    Ins (b ': as) (b ': bs) a b ('InsS ins) 'IZ     = 'IZ
    Ins (a ': as) (a ': bs) a b ('InsS ins) ('IS i) = 'IS (Ins as bs a b ins i)

sInsert
    :: forall k (as :: [k]) (bs :: [k]) (a :: k) (b :: k) (ins :: Insert as bs a) (i :: Index as b). ()
    => Sing ins
    -> Sing i
    -> Sing (Ins as bs a b ins i)
sInsert = undefined
-- sInsert = \case
--     SInsZ     -> SIS
--     SInsS ins -> \case
--       SIZ   -> SIZ
--       SIS i -> SIS (sInsert ins i)
--     InsS ins -> \case
--       IZ   -> IZ
--       IS i -> IS (insert ins i)


-- data Weaken :: [k] -> [k] -> k -> Type where
--     WZ :: Weaken '[] '[b] b
--     WS :: Weaken as bs b -> Weaken (a ': as) (a ': bs) b

-- type family Weak as bs a b (w :: Weaken as bs a) (i :: Index as b) :: Index bs b where
--     Weak (a ': as) (a ': bs) b a ('WS w) 'IZ     = 'IZ
--     Weak (a ': as) (a ': bs) b a ('WS w) ('IS i) = 'IS (Weak as bs b a w i)

-- weak :: Weaken as bs a -> Index as b -> Index bs b
-- weak = \case
--     WZ -> \case {}
--     WS w -> \case
--       IZ   -> IZ
--       IS i -> IS (weak w i)

