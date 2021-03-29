module Repl where

import TypeChecker

-- | get the environment related with a context by giving a list of unlocked definitions
envContLock :: [String] -> Cont -> Env
envContLock _ CNil = ENil
envContLock xs (CConsVar c _ _) = envContLock xs c
envContLock xs (CConsDef c x a e) =
  let r = envContLock xs c in
    if x `elem` xs
    then EConsDef r x a e
    else r

defCont :: String -> Cont -> Exp
defCont x CNil = Var x
defCont x (CConsVar c x' a)
  | x == x'   = Var x
  | otherwise = defCont x c
defCont x (CConsDef c x' a e)
  | x == x'   = e
  | otherwise = defCont x c

headRed :: Cont -> Exp -> Val
headRed c (Var x) = eval (defCont x c) ENil
headRed c (App e1 e2) = appVal (headRed c e1) (eval e2 ENil)
headRed c e = eval e ENil

readBack :: [String] -> Val -> Exp
readBack _ U = U
readBack _ (Var x) = Var x
readBack ns (App v1 v2) = App (readBack ns v1) (readBack ns v2)
readBack ns (Clos (Abs x a e) r) =
  let z  = freshVar x ns
      a' = readBack ns (eval a r)
      e' = readBack (z : ns) (eval e (EConsVar r x (Var z)))
  in Abs z a' e'

eval2 :: Cont -> Exp -> Exp
eval2 c e = readBack (map fst (typeCont c)) (headRed c e)
