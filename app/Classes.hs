module Classes where

import           Lang (Cont, Env, Name)

class InformativeError e where
  explain :: e -> [Name]

class LockStrategy s where
  -- ^ get environment from a type checking context
  getEnv           :: s -> Cont -> Env
  -- ^ add a list of names to be locked
  addLock          :: s -> [Name] -> s
  -- ^ remove a list of names to be locked
  removeLock       :: s -> [Name] -> s
  -- ^ get the names locked from the context
  getNamesLocked   :: s -> Cont -> [Name]
  -- ^ get the names unlocked from the context
  getNamesUnLocked :: s -> Cont -> [Name]
