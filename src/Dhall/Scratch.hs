{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE PolyKinds            #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- module Dhall.Scratch where

module Dhall.Scratch (
  ) where

-- import           Data.Kind
-- import           Data.Singletons
-- import           Data.Singletons.TH
-- import           Data.Singletons.TypeLits
-- import           Data.Type.Universe
-- import           Numeric.Natural

-- data DKind = KType
--            | DKind :~~> DKind
--            | KSort          -- embed sorts

-- genSingletons [''DKind]

-- -- data DKind :: DKind -> Type where

-- -- type family Map f as where
-- --   Map 

-- -- type family LambdaAll as where
-- --     LambdaAll '[] = '[]
-- --     LambdaAll (a ': as) = 'DTLambda a ': LambdaAll as

-- data DType :: k -> DKind -> Type where
--     EKind    :: DKind -> DType sym 'KSort
--     DNatural :: DType sym 'KType
--     DBool    :: DType sym 'KType
--     (:-->)   :: DType sym 'KType -> DType sym 'KType -> DType sym 'KType
--     (:~->)   :: DKind -> DType sym 'KType -> DType sym 'KType

-- data SomeDType :: k -> Type where
--     SDT :: Sing s -> DType k s -> SomeDType k


-- data DTerm :: [DType Symbol 'KType] -> DType Symbol 'KType -> Type where
--     -- DTermType   :: DType Symbol k   -> DTerm vs k
--     DVar        :: Index vs t           -> DTerm vs t
--     DNaturalLit :: Natural              -> DTerm vs 'DNatural
--     DBoolLit    :: Bool                 -> DTerm vs 'DBool
--     DIsEven     :: DTerm vs ('DNatural ':--> 'DBool)
--     DLambda     :: DTerm (v ': vs) t    -> DTerm vs (v ':--> t)
--     -- DPi         :: DTerm (vs :: [DType Symbol (u ': us) 'KType]) t      -- should vs change?
--     --             -> DTerm (LambdaAll vs) (u ':~-> t)
--     DApp        :: DTerm vs (a ':--> b) -> DTerm vs a -> DTerm vs b
--     -- DTApp       :: DTerm (vs :: [DType Symbol us 'KType]) (k ':~-> t)   -- need a way to make a term of this type
--     --             -> DType Symbol us k
--     --             -> DTerm vs t


-- -- genSingletons [''DType]

-- -- data DType :: 

-- --   rulePairs :: ExprTypeType -> ExprTypeType -> Maybe ExprTypeType
-- --   rulePairs a b = case b of
-- --     Type -> Just Type
-- --     Kind -> case a of
-- --       Type -> Nothing
-- --       Kind -> Just Kind
-- --       Sort -> Just Sort
-- --     Sort -> case a of
-- --       Type -> Nothing
-- --       Kind -> Nothing
-- --       Sort -> Just Sort
