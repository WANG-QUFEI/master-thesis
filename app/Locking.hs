{-|
Module          : Locking
Description     : Provides locking/unlocking strategies for constants
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Locking where

import           Classes
import           Lang

-- | A simple locking/unlocking strategy for constants
-- 1. when 'lockType' is True: 'varlist' represents a list of variables that are locked.
-- 2. when 'lockType' is False: 'varlist' represents a list of variables taht are unlocked.
data LockStyle
  = ExplicitLock
      { lockType :: Bool,
        varlist  :: [String]
      }
  | NoLock
  | AllLock
  deriving (Show)

instance EnvStrategy LockStyle where
  getEnv l c        =
    case c of
      CNil -> ENil
      CConsVar c' _ _ -> getEnv l c'
      CConsDef c' x a e ->
        let r = getEnv l c'
        in case l of
          AllLock -> r
          NoLock -> EConsDef r x a e
          ExplicitLock lt vars ->
            if (lt && elem x vars) || (not lt && notElem x vars)
            then r
            else EConsDef r x a e
