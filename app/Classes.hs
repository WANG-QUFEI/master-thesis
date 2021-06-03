module Classes where

import           Lang (Cont, Env)

class InformativeError e where
  explain :: e -> [String]

class EnvStrategy s where
  getEnv :: s -> Cont -> Env
