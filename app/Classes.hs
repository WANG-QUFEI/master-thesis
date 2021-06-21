module Classes where

import           Lang (Cont, Env)

class InformativeError e where
  explain :: e -> [String]

class LockStrategy s where
  getEnv            :: s -> Cont -> Env
  addLock           :: s -> [String] -> s
  removeLock        :: s -> [String] -> s
  getConstsLocked   :: s -> Cont -> [String]
  getConstsUnLocked :: s -> Cont -> [String]
