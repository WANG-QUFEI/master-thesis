module Main where

import Prelude hiding ((*))

import Core.Abs
import Core.ErrM
import Core.Print
import Core.Par

-- value of this language in weak head normal form
data Value = VNt Neut
           | VSet
           | VLam Value Closure
           deriving Show

-- neutral value
data Neut = NGen Int
          | NApp Neut Value
          deriving Show

-- binding variable used in lambda expression
data Binding = BUnit
             | BVar Id
             deriving (Eq, Show)

-- environment
data Rho = RNil | UpVar Rho Binding Value | UpDec Rho Decl deriving Show

-- function closure
data Closure = Closure Binding Exp Rho deriving Show

-- instantiation of a closure by a value
(*) :: Closure -> Value -> Value
(Closure b e r) * v = eval e (UpVar r b v)

-- whether a variable is binded
inBinding :: Id -> Binding -> Bool
inBinding x BUnit     = False
inBinding x (BVar x') = x == x'

-- get variable from environment
getRho :: Rho -> Id -> Value
getRho (UpVar r b v) x
  | x `inBinding` b = v
  | otherwise       = getRho r x
getRho r0@(UpDec r (Def id _ e)) x
  | x == id   = eval e r0
  | otherwise = getRho r x
getRho RNil (Id id) = error ("unbound variable: " ++ id)

-- length of environment
lRho :: Rho -> Int
lRho RNil            = 0
lRho (UpVar rho _ _) = lRho rho + 1
lRho (UpDec rho _  ) = lRho rho

-- Operaions on Values
app :: Value -> Value -> Value
app (VLam _ f) v = f * v
app (VNt k)    v = VNt (NApp k v)
app v1 v2        = error ("app " ++ show v1 ++ ", " ++ show v2)

-- semantics fo this language, an expression evaluates to a value in a certain environment
eval :: Exp -> Rho -> Value
eval e0 rho = case e0 of
  EVar id         -> getRho rho id
  ESet            -> VSet
  EAPP  e1 e2     -> app (eval e1 rho) (eval e2 rho)
  EImpl e1 e2     -> VLam (eval e1 rho) $ Closure BUnit e2 rho
  ELam  e1 e2     -> case e1 of
                       EPostu id e' -> VLam (eval e' rho) $ Closure (BVar id) e2 rho
                       _            -> error "invalid lambda"
  EDec  d  e      -> eval e (UpDec rho d)
  _               -> error "Can not evaluate postulates"

-----------------------------------------------------------------------------------------
-- normal expression
data NExp = NNt NNeut
          | NSet
          | NLam NExp Int NExp
          deriving (Eq, Show)

data NNeut = NNGen Int
           | NNApp NNeut NExp
           deriving (Eq, Show)

data NRho = NRNil
          | NUpVar NRho Binding NExp
          | NUpDec NRho Decl
          deriving (Eq, Show)

-- readback functions
rbV :: Int -> Value -> NExp
rbV k v = case v of
  VNt n -> NNt (rbN k n)
  VSet  -> NSet
  VLam t g -> NLam (rbV k t) k (rbV (k + 1) (g * genV k))

rbN :: Int -> Neut -> NNeut
rbN i (NGen j) = NNGen j
rbN i (NApp n v) = NNApp (rbN i n) (rbV i v)

genV :: Int -> Value
genV k = VNt (NGen k)

rbRho :: Int -> Rho -> NRho
rbRho _ RNil = NRNil
rbRho i (UpVar r b v) = NUpVar (rbRho i r) b (rbV i v)
rbRho i (UpDec r dec) = NUpDec (rbRho i r) dec

------------------------------------------------
-- Error monad and type environment
------------------------------------------------
data G a = Success a | Fail String

instance Functor G where
  fmap f (Success a) = Success (f a)
  fmap _ (Fail s)    = Fail s

instance Applicative G where
  pure = return
  (Fail s) <*> _              = Fail s
  _ <*> (Fail s)              = Fail s
  (Success f) <*> (Success a) = Success (f a)

instance Monad G where
  (Success x) >>= k = k x
  Fail s      >>= k = Fail s
  return            = Success

instance MonadFail G where
  fail s = Fail s
















-------------------------------------------------------------------------------------------
main :: IO ()
main = do
  error "<Not Yet Implemented!>"
