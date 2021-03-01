module TypeChecker (runTypeCheck) where

import Prelude hiding ((*))
import Control.Monad.State
import Data.Maybe

import Core.Abs
import Core.ErrM
import Core.Print
import Core.Par

-- value of this language in weak head normal form
data Val = VNt Neut
         | VSet
         | VLam Val Closure
         deriving Show

-- neutral value
data Neut = NGen Int
          | NApp Neut Val
          deriving Show

-- binding variable used in lambda expression
data Binding = BUnit
             | BVar Id
             deriving (Eq, Show)

-- environment
data Rho = RNil | UpVar Rho Binding Val | UpDec Rho Decl deriving Show

-- function closure
data Closure = Closure Binding Exp Rho deriving Show

-- instantiation of a closure by a value
(*) :: Closure -> Val -> Val
(Closure b e r) * v = eval e (UpVar r b v)

-- whether a variable is binded
inBinding :: Id -> Binding -> Bool
inBinding x BUnit     = False
inBinding x (BVar x') = x == x'

-- get variable from environment
getRho :: Rho -> Id -> Val
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

-- Operaions on Vals
app :: Val -> Val -> Val
app (VLam _ f) v = f * v
app (VNt k)    v = VNt (NApp k v)
app v1 v2        = error ("app " ++ show v1 ++ ", " ++ show v2)

-- semantics fo this language, an expression evaluates to a value in a certain environment
eval :: Exp -> Rho -> Val
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
rbV :: Int -> Val -> NExp
rbV k v = case v of
  VNt n -> NNt (rbN k n)
  VSet  -> NSet
  VLam t g -> NLam (rbV k t) k (rbV (k + 1) (g * genV k))

rbN :: Int -> Neut -> NNeut
rbN i (NGen j) = NNGen j
rbN i (NApp n v) = NNApp (rbN i n) (rbV i v)

genV :: Int -> Val
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

getResultG :: G a -> Either a String
getResultG (Success a) = Left a
getResultG (Fail s)    = Right s

-- type environment
type Gamma = [(Id, Val)]

lookupG :: (Show a, Eq a) => a -> [(a, b)] -> G b
lookupG s [] = fail ("lookupG " ++ show s)
lookupG s ((s1, u) : us) | s == s1   = return u
                         | otherwise = lookupG s us

-- update type environment: Gamma |- x : t => Gamma'
upG :: Gamma -> Binding -> Val -> G Gamma
upG gma BUnit _ = return gma
upG gma (BVar x) t = return ((x, t) : gma)

-------------------------------------------------
-- Type checking rules
-------------------------------------------------
checkT :: Int -> Rho -> Gamma -> Exp  -> G ()
check  :: Int -> Rho -> Gamma -> Exp  -> Val -> G (Rho, Gamma)
checkI :: Int -> Rho -> Gamma -> Exp  -> G Val
checkD :: Int -> Rho -> Gamma -> Decl -> G (Rho, Gamma)

-- check that an expression e0 is a type
checkT i rho gam e0 = case e0 of
  EImpl e1 e2 -> do checkT i rho gam e1
                    checkT i rho gam e2
  ELam  (EPostu id e1) e2 -> do
    checkT i rho gam e1
    gam' <- upG gam (BVar id) (eval e1 rho)
    checkT (i + 1) (UpVar rho (BVar id) (genV i)) gam' e2
  ESet       -> return ()
  EPostu _ _ -> fail $ "Postulate can not be a type: " ++ show e0
  _          -> do
    check i rho gam e0 VSet
    return ()

-- check that an expression e0 has type t0
check i rho gam e0 t0 = case (e0, t0) of
  (ELam (EPostu id e1) e2, VLam val clo) -> do
    eqNf i (eval e1 rho) val
    let vi = genV i
    gam' <- upG gam (BVar id) val
    check (i + 1) (UpVar rho (BVar id) vi) gam' e2 (clo * vi)
    return (rho, gam)
  (ELam (EPostu id e1) e2, VSet)         -> do
    check i rho gam e1 VSet
    gam' <- upG gam (BVar id) (eval e1 rho)
    let vi = genV i
    check (i + 1) (UpVar rho (BVar id) vi) gam' e2 VSet
    return (rho, gam)
  ((EImpl e1 e2), VSet)                  -> do
    check i rho gam e1 VSet
    check i rho gam e2 VSet
    return (rho, gam)
  ((EDec dec e'), t)                     -> do
    (rho', gam') <- checkD i rho gam dec
    check i rho' gam' e' t
    case e' of
      EPostu id e1 ->
        return (rho', (id, t) : gam')
      _            ->
        return (rho', gam')
  (e, t)                                 -> do
    v <- checkI i rho gam e
    eqNf i v t
    return (rho, gam)
-- infer the type of an expression e0
checkI i rho gam e0 = case e0 of
  EVar id    -> lookupG id gam
  EAPP e1 e2 -> do
    v1     <- checkI i rho gam e1
    (t, g) <- extLam v1
    check i rho gam e2 t
    return $ g * (eval e2 rho)
  ESet       -> return VSet
  EPostu id e -> return $ eval e rho
  _          -> fail $ "checkI: " ++ show e0

checkD i rho gam dec@(Def id et ev) = do
  checkT i rho gam et
  let t  = eval et rho
      vi = genV i
  gam' <- upG gam (BVar id) t
  check (i + 1) (UpVar rho (BVar id) vi) gam' ev t
  return (UpDec rho dec, gam')

-- test equality of values by applying read back function  
eqNf :: Int -> Val -> Val -> G ()
eqNf i v1 v2
  | n1 == n2  = return ()
  | otherwise = fail $ "Values not equal: " ++ show v1 ++ " =/= " ++ show v2
  where n1 = rbV i v1
        n2 = rbV i v2

extLam :: Val -> G (Val, Closure)
extLam v = case v of
  VLam t g -> return (t, g)
  _        -> fail $ "invalid lambda value: " ++ show v

----------------------------------------------------------------------------
--------------- type checking monad for the entire program -----------------
----------------------------------------------------------------------------
type TypeCheckProg a = State (Bool, Rho, Gamma) a

progTypeCheck :: Program -> TypeCheckProg [String]
progTypeCheck (Prog explist) = do
  msx <- mapM checkExp explist
  return $ catMaybes msx
  where checkExp :: Exp -> TypeCheckProg (Maybe String)
        checkExp e = do
          (continue, rho, gam) <- get
          case continue of
            False -> return Nothing
            _     -> case e of
              EPostu id e0 -> case getResultG (checkT 0 rho gam e0) of
                Left _      -> do -- e0 is a valid type
                  let t    = eval e0 rho
                      gam' = (id, t) : gam
                  put (True, rho, gam')
                  return Nothing
                Right err -> do -- e0 is not a type
                  put (False, rho, gam)
                  return (Just err)
              EVar id      -> case getResultG (checkI 0 rho gam e) of
                Left _      -> return Nothing -- id is a bounded variable
                Right err -> do
                  put (False, rho, gam)
                  return (Just err)
              ESet -> return Nothing
              EAPP _ _     -> case getResultG (checkI 0 rho gam e) of
                Left _      -> return Nothing -- valid application
                Right err -> do
                  put (False, rho, gam)
                  return (Just err)
              EDec _ _     -> case getResultG (check 0 rho gam e VSet) of -- a list of declarations must be followed by a expression whose type is VSet, like ESet
                Left (rho', gam') -> do -- valid application
                  put (True, rho', gam')
                  return Nothing 
                Right err -> do
                  put (False, rho, gam)
                  return (Just err)
              _             -> return $ Just ("invalid single expression: " ++ show e)

runTypeCheck :: Program -> [String]
runTypeCheck p = evalState (progTypeCheck p) (True, RNil, [])
