{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Dhall.Typed.Context (
    Context(..)
  , ContextItem(..)
  , lookupCtx
  , ShiftSortSym
  ) where

import           Data.Functor
import           Data.Kind
import           Data.Singletons
import           Data.Text              (Text)
import           Dhall.Typed.Core
import           Dhall.Typed.Type.Index

data ShiftSortSym ts ps us a (ins :: Insert ts ps a)
                  :: DType ts us 'Type
                  ~> DType ps (Map (KShiftSym ts ps a 'Kind ins) us) 'Type

data Context ts us :: [DType ts us 'Type] -> Type where
    CtxNil    :: Context '[] '[] '[]
    ConsSort  :: Text
              -> SDSort t
              -> Context ts        us vs
              -> Context (t ': ts) (Map (KShiftSym ts (t ': ts) t 'Kind 'InsZ) us)
                                   (Map (ShiftSortSym ts (t ': ts) us t 'InsZ) vs)
    ConsKind  :: Text
              -> NDKind ts 'Kind u
              -> Context ts us vs
              -> Context ts (u ': us) (Map (ShiftSym ts us (u ': us) u 'Type 'InsZ) vs)
    ConsType  :: Text
              -> NDType ts us 'Type v
              -> Context ts us vs
              -> Context ts us (v ': vs)

data ContextItem ts us :: [DType ts us 'Type] -> Type where
    TCISort :: Index ts t -> SDSort t             -> ContextItem ts us vs
    TCIKind :: Index us u -> NDKind ts 'Kind u    -> ContextItem ts us vs
    TCIType :: Index vs v -> NDType ts us 'Type v -> ContextItem ts us vs

lookupCtx
    :: forall ts us vs. ()
    => Text
    -> Integer
    -> Context ts us vs
    -> Maybe (ContextItem ts us vs)
lookupCtx v = go
  where
    go :: forall ps qs rs. Integer -> Context ps qs rs -> Maybe (ContextItem ps qs rs)
    go i = \case
      CtxNil       -> Nothing
      ConsSort t (s :: SDSort p) (vs :: Context ps' qs' rs') ->
        let descend :: Integer
                    -> Maybe (ContextItem (p ': ps')
                                          (Map (KShiftSym ps' (p ': ps') p 'Kind 'InsZ) qs')
                                          (Map (ShiftSortSym ps' (p ': ps') qs' p 'InsZ) rs')
                             )
            descend j = go j vs <&> \case
              TCISort l e -> TCISort (IS l) e
              -- TCIKind l a -> TCIKind _ _
        in  case (v == t, i <= 0) of
              (False, _    ) -> descend i
              (True , False) -> descend (i - 1)
              (True , True ) -> Just (TCISort IZ s)
      ConsKind t (k :: NDKind ps 'Kind q) (vs :: Context ps qs' rs') ->
        let descend :: Integer
                    -> Maybe (ContextItem ps (q ': qs')
                                (Map (ShiftSym ps qs' (q ': qs') q 'Type 'InsZ) rs')
                             )
            descend j = go j vs <&> \case
              TCISort l e       -> TCISort l e
              TCIKind l a       -> TCIKind (IS l)           a
              TCIType (l :: Index rs' r) (NDT a :: NDType ps qs' 'Type r) ->
                TCIType (shiftIndex k a l) (NDT (sShift1 a))
        in  case (v == t, i <= 0) of
              (False, _    ) -> descend i
              (True , False) -> descend (i - 1)
              (True , True ) -> Just (TCIKind IZ k)
      ConsType t x vs ->
        let descend j = go j vs <&> \case
              TCISort l a -> TCISort l      a
              TCIKind l a -> TCIKind l      a
              TCIType l a -> TCIType (IS l) a
        in  case (v == t, i <= 0) of
              (False, _    ) -> descend i
              (True , False) -> descend (i - 1)
              (True , True ) -> Just (TCIType IZ x)

shiftIndex
    :: NDKind ps 'Kind q
    -> SDType ps qs' 'Type x
    -> Index rs' (TNormalize ps qs' 'Type x)
    -> Index (Map (ShiftSym ps qs' (q ': qs') q 'Type 'InsZ) rs')
             (TNormalize ps (q ': qs') 'Type (Shift ps qs' (q ': qs') q 'Type 'InsZ x))
shiftIndex _ _ = undefined

