{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TypeChecker (
    runTypeCheck
  , errorText
  , TypeCheckError
  , ErrorText
  ) where

import Data.Maybe
import Data.List
import Debug.Trace
import Control.Monad.State
import Control.Monad.Except

import Core.Abs
import Core.Print  ( printTree )
----------------------------------------------------------
-- Data types
----------------------------------------------------------

-- |Abstract syntax for expressions, using the same syntax for lambda and dependent product
data AbsExp = U
            | Ref   Int
            | App   AbsExp AbsExp
            | Lam   AbsExp AbsExp
            | Post  AbsExp
            | Where AbsDef
            deriving (Eq, Show)

-- | abstract syntax for definition
data AbsDef = AbsDef AbsExp AbsExp deriving (Eq, Show)

-- | program in abstract syntax
type AbsProgram = [AbsExp]

-- | value for an abstract expression
data Val = VU
         | Var Int
         | VApp Val Val
         | VLam Val Clos
         deriving (Eq, Show)

type Env   = [Val] -- ^ value enviroment for type checking
type Gamma = [Val] -- ^ type environment for type checking

-- | closure as value for expressions in lambda and pi form
data Clos = Clos AbsExp Env deriving (Eq, Show)

-- | expression in normal form, used for convertibility checking
data NExp = NU
          | NInt Int
          | NApp NExp NExp
          | NLam Int NExp NExp
          deriving (Eq, Show)

type ErrorStack = [(AbsExp, String)]

data TypeCheckError = DupDecl           Id
                    | ValNotEqual       ErrorStack
                    | VarNotbound       Id
                    | TypeNotMatch      AbsExp Val
                    | InvalidApp        ErrorStack
                    | InferErr          ErrorStack
                    | CanNotEvaluate    AbsExp
                    | ExtendWithContext TypeCheckError String
                    deriving (Show)

type ErrorText = String

errorText :: TypeCheckError -> [ErrorText]
errorText err = case err of
  DupDecl (Id (pos, id))     -> ["Duplicated declaration of variable " ++ id ++ ", at " ++ show pos]
  ValNotEqual s              -> "Unequal terms" : map (\(e, f) -> "  " ++ f ++  show e) (reverse s)
  VarNotbound (Id (pos, id)) -> ["Unbound variable " ++ id ++ ", at " ++ show pos]
  TypeNotMatch e t           -> ["Type unmatch, the expression does not have the value as its type", "\10070 expression: " ++ show e, "\10070 value: " ++ show t]
  InvalidApp s               -> "Invalid application: " : map (\(e, f) -> "  " ++ f ++  show e) (reverse s)
  InferErr s                 -> "Type can not be inferred: " : map (\(e, f) -> "  " ++ f ++ show e) (reverse s)
  CanNotEvaluate e           -> ["Expression can not be evaluated", "\10070 " ++ show e]
  ExtendWithContext pre tail -> (errorText pre) ++ [tail]

-- | monad used for type checking
newtype G e s a = G {mkg :: ExceptT e (State s) a}
  deriving (Monad, Applicative, Functor, MonadError e, MonadState s)

type TypeCheckM a = G TypeCheckError (Env, Gamma) a

type ConvertM a = G TypeCheckError [String] a

runG :: G e s a -> s -> Either e a
runG g s = evalState (runExceptT (mkg g)) s

-- | string part of an id
idAsString :: Id -> String
idAsString (Id (_, id)) = id

-- | create a closure for an abstract expression from the enclosing environment
mkClos :: AbsExp -> Env -> Clos
mkClos ae env = Clos ae env
----------------------------------------------------------
-- type checking methods
----------------------------------------------------------
-- | check the duplication of declaration
checkDuplicateDecl :: Program -> Either TypeCheckError Bool
checkDuplicateDecl (Prog es) =
  let xs = evalState (mapM check es) []
  in  foldl (>>) (Right True) xs
  where
    check :: Exp -> State [String] (Either TypeCheckError Bool)
    check e = case getExpId e of
      Just id -> do
        idlist <- get
        case (idAsString id) `elem` idlist of
          True -> return . Left $ DupDecl id
          _    -> put ((idAsString id) : idlist) >> return (Right True)
      _       -> return (Right True)
    getExpId :: Exp -> Maybe Id
    getExpId e = case e of
      EPost id _ -> Just id
      EDec  id _ -> Just id
      _          -> Nothing

-- | get the abstract syntax of a program
absProg :: Program -> TypeCheckM AbsProgram
absProg p@(Prog es) = case checkDuplicateDecl p of
  Left error -> throwError error
  _          -> case runG (mapM g es) [] of
    Left error -> throwError error
    Right as   -> return as
  where g :: Exp -> ConvertM AbsExp
        g e = case e of
          EU                    -> return U
          EVar id               -> do
            idlist <- get
            case (idAsString id) `elemIndex` idlist of
              Just idx -> return $ Ref idx
              Nothing  -> throwError $ VarNotbound id
          EApp e1 e2            -> do
            e1' <- g e1
            e2' <- g e2
            return $ App e1' e2'
          EArr e1 e2            -> do
            e1' <- g e1
            modify (\s -> "" : s)
            e2' <- g e2
            modify (\s -> tail s)
            return $ Lam e1' e2'
          EPi id e1 e2 -> do
            e1' <- g e1
            modify (\s -> idAsString id : s)
            e2' <- g e2
            modify (\s -> tail s)
            return $ Lam e1' e2'
          EPost id e            -> do
            e' <-  g e
            l  <-  gets length
            modify (\s -> idAsString id : s)
            return $ Post e'
          EDec id (Def e1 e2)   -> do
            e1' <- g e1
            e2' <- g e2
            l   <- gets length
            modify (\s -> idAsString id : s)
            return $ Where (AbsDef e1' e2')

-- | semantics of the language, evaluation of the abstract expressions
eval :: AbsExp -> Env -> TypeCheckM Val
eval e env = case e of
  U         -> return VU
  Ref idx   -> return (env !! idx)
  App e1 e2 -> app e1 e2 env
  Lam e1 e2 -> do
    v1 <- eval e1 env
    return $ VLam v1 (mkClos e2 env)
  _         -> throwError $ CanNotEvaluate e

-- | instantiation of a closure by a value
inst :: Clos -> Val -> TypeCheckM Val
inst (Clos e env) v = eval e (v : env)

-- | application of values
app :: AbsExp -> AbsExp -> Env -> TypeCheckM Val
app e1 e2 env = do
  v1 <- eval e1 env
  v2 <- eval e2 env
  case v1 of
    (VLam _ clos) -> inst clos v2
    Var _         -> return $ VApp v1 v2
    VApp _ _      -> return $ VApp v1 v2
    _             -> trace (show v1 ++ "\n" ++ show v2) throwError (InvalidApp [(e1, "app: ")])
-- | readback function, converting a value to its normal form
rbV :: Int -> Val -> TypeCheckM NExp
rbV i v = case v of
  VU           -> return NU
  Var k        -> return $ NInt k
  VApp v1 v2   -> do
    n1 <- rbV i v1
    n2 <- rbV i v2
    return $ NApp n1 n2
  VLam v  clos -> do
    n1 <- rbV i v
    v' <- inst clos (Var i)
    n2 <- rbV (i + 1) v'
    return $ NLam i n1 n2

updateContext :: Val -> Val -> TypeCheckM ()
updateContext v1 v2 = do
  (env, gamma) <- get
  put (v1 : env, v2 : gamma)

-- | check the equality of two values by first reducing them to the normal form
eqNe :: Int -> Val -> Val -> TypeCheckM ()
eqNe i v1 v2 = do
  n1 <- rbV i v1
  n2 <- rbV i v2
  if n1 == n2
    then return ()
    else throwError $ ValNotEqual []

handleErrStack :: AbsExp -> String -> TypeCheckError -> TypeCheckM a
handleErrStack e fs err = case err of
  InvalidApp  s -> throwError $ InvalidApp  ((e, fs) : s)
  InferErr    s -> throwError $ InferErr    ((e, fs) : s)
  ValNotEqual s -> throwError $ ValNotEqual ((e, fs) : s)

checkT :: AbsExp ->        TypeCheckM ()   -- ^ check an expression is a type
check  :: AbsExp -> Val -> TypeCheckM ()   -- ^ check an expression has a value as its type
checkI :: AbsExp ->        TypeCheckM Val  -- ^ infer the type of an expression
checkD :: AbsDef ->        TypeCheckM ()   -- ^ check an definition is valid

checkT e = do {
  case e of
    U -> return ()
    Lam e1 e2 -> do
      checkT e1
      init_ctx@(env, gamma) <- get
      let v1 = Var (length env)
      v2 <- eval e1 env
      updateContext v1 v2
      checkT e2
      put init_ctx
    Post e -> do
      checkT e
      env <- gets fst
      t   <- eval e env
      updateContext (Var (length env)) t
    _ -> check e VU } `catchError` handleErrStack e "checkT: "

check e t = do {
  case (e, t) of
    (Lam e1 e2, VLam t g) -> do
      init_ctx@(env, gamma) <- get
      let s = length env
      t' <- eval e1 env
      eqNe s t' t
      updateContext (Var s) t
      tt <- inst g (Var s)
      check e2 tt
      put init_ctx
    (Lam e1 e2, VU) -> do
      check e1 VU
      init_ctx@(env, gamma) <- get
      let v1 = Var (length env)
      v2 <- eval e1 env
      updateContext v1 v2
      check e2 VU
      put init_ctx
    (Lam _ _, _) -> throwError (TypeNotMatch e t)
    _ -> do
      t'  <- checkI e
      env <- gets fst
      eqNe (length env) t t' } `catchError` handleErrStack e "check: "

checkI e = do {
  case e of
    U -> return VU
    Ref idx -> do
      gamma <- gets snd
      return (gamma !! idx)
    App e1 e2 -> do
      v1 <- checkI e1
      case v1 of
        VLam t g -> do
          check e2 t
          env <- gets fst
          v2 <- eval e2 env
          inst g v2
        _ -> throwError (InvalidApp [(e1, "checkI: ")])  
    _ -> throwError (InferErr []) } `catchError` handleErrStack e "checkI: "

checkD d@(AbsDef e1 e2) = do { do
  checkT e1
  env <- gets fst
  t <- eval e1 env
  check e2 t
  v <- eval e2 env
  updateContext v t } `catchError` handleErrStack (Where d) "checkD: "

-- | type check a program
runTypeCheck :: Program -> Either TypeCheckError ()
runTypeCheck p@(Prog es) = runG pCheck ([], [])
  where pCheck :: TypeCheckM ()
        pCheck = do
          p' <- absProg p
          mapM_ f (zip p' [0..])
        f :: (AbsExp, Int) -> TypeCheckM ()
        f (e, n) = do
          case e of
            U                 -> return ()
            Ref _             -> (checkI e >> return ()) `catchError` (h n)
            App _ _           -> (checkI e >> return ()) `catchError` (h n)
            Lam _ _           -> (checkT e)              `catchError` (h n)
            Post _            -> (checkT e)              `catchError` (h n)
            Where dec         -> (checkD dec)            `catchError` (h n)
        h :: Int -> TypeCheckError -> TypeCheckM ()
        h n error = let e_origin    = es !! n
                        msg_context = "When checking source \9944 " ++ printTree e_origin
                    in  throwError $ ExtendWithContext error msg_context
