{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DerivingVia   #-}
{-# LANGUAGE TupleSections #-}

module Dhall.Typed.Type.Either (
    EitherFail(..)
  , runEitherFail
  , label
  , (<?>)
  , liftEF
  -- * With function
  , label'
  , runEitherFail'
  ) where


import           Control.Monad.Except
import           Control.Monad.Fail
import           Control.Monad.State
import           Data.Functor.Identity

newtype EitherFail e a = EF { unEF :: (String -> e) -> Either e (a, String -> e) }
  deriving Functor
  deriving (Applicative, Monad, MonadError e) via StateT (String -> e) (Either e)

instance MonadFail (EitherFail e) where
    fail s = EF $ \f -> Left (f s)

label' :: (String -> e) -> EitherFail e a -> EitherFail e a
label' l x = do
    res <- x
    EF $ \_ -> Right (res, l)

label :: e -> EitherFail e a -> EitherFail e a
label = label' . const

(<?>) :: EitherFail e a -> e -> EitherFail e a
(<?>) = flip label

runEitherFail' :: (String -> e) -> EitherFail e a -> Either e a
runEitherFail' f = fmap fst . ($ f) . unEF

runEitherFail :: e -> EitherFail e a -> Either e a
runEitherFail = runEitherFail' . const

liftEF :: Either e a -> EitherFail e a
liftEF e = EF $ \f -> (,f) <$> e
