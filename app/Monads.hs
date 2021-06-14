{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-|
Module          : Monads
Description     : Provides monad type for conversion and type checking
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Monads where

import           Control.Monad.Except
import           Control.Monad.State

-- | a composite monad which contains a state monad and an exception monad
newtype G e s a = G {mkg :: ExceptT e (State s) a}
  deriving (Monad, Applicative, Functor, MonadError e, MonadState s)

-- | run the monad and get the result
runG :: G e s a -> s -> Either e a
runG g = evalState (runExceptT (mkg g))
