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
-- LockAll  : lock all constants
-- LockNone : lock none constants
-- LockList <varlist> : lock on the list of constants
data LockStyle = LockAll
               | LockNone
               | LockList [String]
               deriving (Show)

instance EnvStrategy LockStyle where
  getEnv LockAll _ = ENil
  getEnv LockNone c =
    case c of
      CNil -> ENil
      CConsVar c' _ _ -> getEnv LockNone c'
      CConsDef c' x a e ->
        let r = getEnv LockNone c'
        in EConsDef r x a e
  getEnv ls@(LockList vars) c =
    case c of
      CNil -> ENil
      CConsVar c' _ _ -> getEnv ls c'
      CConsDef c' x a e ->
        let r = getEnv ls c'
        in if x `elem` vars
           then r
           else EConsDef r x a e
