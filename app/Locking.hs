{-|
Module          : Locking
Description     : Provides locking/unlocking strategies for constants
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Locking where

import           Classes
import           Lang

data NoLocking = NoLocking

instance EnvStrategy NoLocking where
  getEnv NoLocking cont = case cont of
    CNil             -> ENil
    CConsVar c _ _   -> getEnv NoLocking c
    CConsDef c x a e ->
      let r = getEnv NoLocking c
      in EConsDef r x a e

-- | Representation of annotated locking
-- 1. when 'lockType' is True: 'varlist' represents a list of variables that are locked.
-- 2. when 'lockType' is False: 'varlist' represents a list of variables taht are unlocked.
data AnnotatedLocking = AnnotatedLocking {
  lockType :: Bool,
  varlist  :: [String]}

instance EnvStrategy AnnotatedLocking where
  getEnv al@(AnnotatedLocking lt vl) cont =
    case cont of
      CNil             -> ENil
      CConsVar c _ _   -> getEnv al cont
      CConsDef c x a e ->
        let r = getEnv al c
        in if (lt && elem x vl) || (not lt && notElem x vl)
           then r
           else EConsDef r x a e
