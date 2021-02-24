module Main where

import Prelude hiding ((*))

import Core.Abs
import Core.ErrM
import Core.Print
import Core.Par

-- value of this language in weak head normal form
data Value = VNt Neutral
           | VSet
           | VArrow Value Closure
           | VLam Closure
           | VPostu Id Value
           deriving Show

-- neutral value
data Neutral = NGen Int Id
             | NApp Neutral Value
             deriving Show

-- pattern used in closure to represent binding variables in a lambda expression
data Pattern = PUnit
             | PVar Id Value
             deriving Show

-- get a pattern from a special kind of expression (EPostu)
mkPattern :: Rho -> Exp -> Pattern
mkPattern rho (EPostu id e) = PVar id (eval e rho)
mkPattern _ _ = PUnit

ideq :: Id -> Id -> Bool
ideq (Id (_, id1)) (Id (_, id2)) = id1 == id2

-- whether an identifer is in a pattern
inPat :: Id -> Pattern -> Bool
inPat x PUnit = False
inPat x (PVar x' _) = ideq x x'

-- function closures
data Closure = Closure Pattern Exp Rho deriving Show

-- instantiation of a closure by a value
(*) :: Closure -> Value -> Value
(Closure p e r) * v = eval e (UpVar r p v)

mkClosure :: Pattern -> Exp -> Rho -> Closure
mkClosure p e rho = Closure p e rho

-- environment
data Rho = RNil | UpVar Rho Pattern Value | UpDec Rho Decl deriving Show

-- get variable from environment
getRho :: Rho -> Id -> Value
getRho (UpVar r p v) x
  | x `inPat` p = v
  | otherwise   = getRho r x
getRho r0@(UpDec r (Def id _ e)) x
  | x `ideq` id = eval e r0
  | otherwise   = getRho r x
getRho RNil (Id (pos, id)) = error ("unbound variable " ++ id ++ ", at " ++ show pos)

-- length of environment
envSize :: Rho -> Int
envSize RNil = 0
envSize (UpVar rho _ _) = envSize rho + 1
envSize (UpDec rho _)   = envSize rho

-- Operaions on Values
app :: Value -> Value -> Value
app (VLam c) v = c * v
app (VNt k)  v = VNt (NApp k v)
app v1 v2 = error ("app " ++ show v1 ++ ", " ++ show v2)

-- semantics fo this language, an expression evaluates to a value in a certain environment
eval :: Exp -> Rho -> Value
eval e0 rho = case e0 of
  EPostu id e      -> VPostu id (eval e rho)
  EVar id          -> getRho rho id
  ESet             -> VSet
  EAPP e1  e2      -> app (eval e1 rho) (eval e2 rho)
  EArrow e1 e2     -> VArrow (eval e1 rho) (mkClosure PUnit e2 rho)
  EAbs   e1 e2     -> VLam (mkClosure (mkPattern rho e1) e2 rho)
  EDec d   e       -> eval e (UpDec rho d)




















-------------------------------------------------------------------------------------------
main :: IO ()
main = do
  error "<Not Yet Implemented!>"
