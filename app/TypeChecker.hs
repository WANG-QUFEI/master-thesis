{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TypeChecker (
    TypeCheckError
  , Exp(..)
  , Val
  , Env(..)
  , Cont(..)
  , G
  , runTypeCheckCtx
  , errorText
  , runG
  , eval
  , appVal
  ) where

import Data.Maybe
import Data.List
import Debug.Trace
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as Map

import Core.Abs
import Core.Print  ( printTree )
----------------------------------------------------------
-- Data types
----------------------------------------------------------
-- | abstract syntax for expressions, extended with closure as values
data Exp = U
         | Var    String
         | App    Exp Exp
         | Abs    String Exp Exp
         | Where  String Exp Exp Exp
         | Clos   Exp Env
         deriving (Show)

-- | the syntax for 'Exp' is also used as value in this language
type Val = Exp

-- | abstract syntax for declarations
data Decl = Dec String Exp
          | Def String Exp Exp
          deriving (Show)

-- | abstract context after the conversion of the concrete context
type AbsCtx = [Decl]

-- | environment
data Env = ENil
         | EConsVar Env String Val
         | EConsDef Env String Exp Exp
         deriving (Show)

-- | A type-checking context related with an environment
data Cont = CNil
          | CConsVar Cont String Exp
          | CConsDef Cont String Exp Exp
          deriving (Show)

type ErrorStack = [(Exp, String)]

type ErrorText = String

data TypeCheckError = InvalidApp     Exp
                    | DupDecl        Id Id
                    | VarNotbound    Id
                    | TypeInferErr   Exp
                    | NotConvertible Val Val
                    | ExtendedErr    TypeCheckError [ErrorText]
                    deriving (Show)
  
-- | a composite monad which contains a state monad and an exception monad
newtype G e s a = G {mkg :: ExceptT e (State s) a}
  deriving (Monad, Applicative, Functor, MonadError e, MonadState s)

-- | monad for converting 
type ConvertM a = G TypeCheckError (Map.Map String Id) a

-- | monad for type-checking
type TypeCheckM a = G TypeCheckError Cont a

-- | run the monad and get the result
runG :: G e s a -> s -> Either e a
runG g s = evalState (runExceptT (mkg g)) s

-- | string of an id
idStr :: Id -> String
idStr (Id (_, id)) = id

-- | position of an id
idPos :: Id -> (Int, Int)
idPos (Id (pos, _)) = pos

-- | turn a TypeCheckError to a list of string for display
errorText :: TypeCheckError -> [ErrorText]
errorText err = case err of
  InvalidApp e                -> ["Invalid application on: " ++ show e]
  DupDecl    id1 id2          -> ["Duplicated declaration of variable: already declared '" ++ idStr id1 ++ "' at " ++ show (idPos id1) ++
                                  ". Find duplication at " ++ show (idPos id2)]
  VarNotbound (Id (pos, id))  -> ["Unbound variable " ++ id ++ ", at " ++ show pos]
  TypeInferErr e              -> ["Can not infer type for: " ++ show e]
  NotConvertible v v'         -> ["Values not convertible", "v1: " ++ show v, "v2: " ++ show v']
  ExtendedErr err ss          -> (errorText err) ++ ss

-- | turn a concrete context into an abstract context, check proper declaration and reference of variables at the same time
absCtx :: Context -> ConvertM AbsCtx
absCtx (Ctx xs) = mapM absDecl xs
  where
    absDecl :: CDecl -> ConvertM Decl
    absDecl (CDec id e) = do
      r <- gets (Map.lookup (idStr id))
      case r of
        Just id' -> throwError $ DupDecl id' id
        _        -> do
          e' <- absExp e
          modify (\s -> Map.insert (idStr id) id s)
          return $ Dec (idStr id) e'
    absDecl (CDef id e1 e2) = do
      r <- gets (Map.lookup (idStr id))
      case r of
        Just id' -> throwError $ DupDecl id' id
        _        -> do
          e1' <- absExp e1
          e2' <- absExp e2
          modify (\s -> Map.insert (idStr id) id s)
          return $ Def (idStr id) e1' e2'
    absExp :: CExp -> ConvertM Exp
    absExp e = case e of
      CU -> return U
      CVar id -> do
        r <- gets (Map.lookup (idStr id))
        case r of
          Just _ -> return $ Var (idStr id)
          _      -> throwError $ VarNotbound id
      CApp e1 e2 -> do
        e1' <- absExp e1
        e2' <- absExp e2
        return $ App e1' e2'
      CArr e1 e2 -> do
        e1' <- absExp e1
        e2' <- absExp e2
        return $ Abs "" e1' e2'
      CPi id e1 e2 -> do
        m <- get
        case Map.lookup (idStr id) m of
          Just id' -> throwError $ DupDecl id' id
          _        -> do
            e1' <- absExp e1
            put (Map.insert (idStr id) id m)
            e2' <- absExp e2
            put m
            return $ Abs (idStr id) e1' e2'
      CWhere id e1 e2 e3 -> do
        m <- get
        case Map.lookup (idStr id) m of
          Just id' -> throwError $ DupDecl id' id
          _        -> do
            e1' <- absExp e1
            put (Map.insert (idStr id) id m)
            e2' <- absExp e2
            e3' <- absExp e3
            put m
            return $ Where (idStr id) e1' e2' e3'


-- | extend an environment with a variable and its value
consEVar :: Env -> String -> Val -> Env
consEVar r "" v = r
consEVar r x v = EConsVar r x v

-- | extend a type-checking context with a variable and its type
consCVar :: Cont -> String -> Exp -> Cont
consCVar c "" _ = c
consCVar c x a = CConsVar c x a

-- | semantics about how an expression should be evaluated
eval :: Exp -> Env -> Val
eval e r = case e of
  U               -> U
  Var x           -> getVal x r
  App e1 e2       -> appVal (eval e1 r) (eval e2 r)
  Abs _ _ _       -> Clos e r
  Where x a e e'  -> eval e' (EConsDef r x a e)
  Clos _ _        -> e

-- | application operation on values
appVal :: Val -> Val -> Val
appVal v1 v2 = case v1 of
  Clos (Abs x a e) r -> eval e (consEVar r x v2)
  _ -> App v1 v2

-- | get variable value
getVal :: String -> Env -> Val
getVal x ENil = Var x
getVal x (EConsVar r x' v)
  | x == x' = v
  | otherwise = getVal x r
getVal x (EConsDef r x' a e)
  | x == x' = eval e r
  | otherwise = getVal x r

-- | get the environment related with a type-checking context
envCont :: Cont -> Env
envCont CNil = ENil
envCont (CConsVar c x a) = envCont c
envCont (CConsDef c x a e) = EConsDef (envCont c) x a e

-- | get the type of variables within a context
typeCont :: Cont -> [(String, Val)]
typeCont CNil = []
typeCont (CConsVar c x a)   = (x, eval a (envCont c)) : (typeCont c)
typeCont (CConsDef c x a e) = (x, eval a (envCont c)) : (typeCont c)

-- | generate a fresh name based on a list of names
freshVar :: String -> [String] -> String
freshVar x xs = if x `elem` xs
                then freshVar (x ++ "'") xs
                else x

-- | get the type of a variable
getType :: [(String, Val)] -> String -> Maybe Val
getType [] x = Nothing
getType ((x', v) : t) x
  | x' == x = Just v
  | otherwise = getType t x
  
-- | given a type-checking context, infer the type of an expression
checkInfer   :: Cont -> Exp -> TypeCheckM Val
-- | given a type-checking context, check that an expression has given type
checkT       :: Cont -> Exp -> Val -> TypeCheckM ()
-- | check the convertibility of two values
checkConvert :: [(String, Val)] -> Val -> Val -> TypeCheckM ()
-- | given a type-checking context, check that a definition is valid
checkDef     :: Cont -> String -> Exp -> Exp -> TypeCheckM Cont
-- | given a type-checking context, check taht a declaration is valid
checkDec     :: Cont -> String -> Exp -> TypeCheckM Cont

checkInfer c U = return U
checkInfer c (Var x) = case getType (typeCont c) x of
  Just v -> return v
  _      -> error $ "should not happen, id: " ++ x
checkInfer c (App e1 e2) = do
  v <- checkInfer c e1
  case v of
    Clos (Abs x a b) r -> do
      checkT c e2 (eval a r)
      let v' = eval e2 (envCont c)
      return $ eval b (consEVar r x v')
    _ -> throwError $ InvalidApp e1
checkInfer _ e = throwError $ TypeInferErr e

checkT c U U = return ()
checkT c (Var x) v = do
  let tc = typeCont c
  case getType tc x of
    Just v' -> checkConvert tc v' v
    _       -> error $ "should not happen, can not get type of variable: " ++ x
checkT c (App e1 e2) v = do
  v1 <- checkInfer c e1
  case v1 of
    Clos (Abs x a b) r -> do
      checkT c e2 (eval a r)
      let v2 = eval e2 (envCont c)
          v' = eval b (consEVar r x v2)
      checkConvert (typeCont c) v v'
    _ -> throwError $ InvalidApp e1
checkT c (Abs x a b) U = do
  checkT c a U
  checkT (consCVar c x a) b U
checkT c (Abs x a e) (Clos (Abs x' a' e') r) = do
  checkT c a U
  let v  = eval a (envCont c)
      v' = eval a' r
  checkConvert (typeCont c) v v'
  checkT (consCVar c x a) e (eval e' (consEVar r x' (Var x)))
checkT c (Where x a e1 e) v = do
  c' <- checkDef c x a e1
  checkT c' e v

checkConvert xs U U = return ()
checkConvert _ (Var x) (Var x') =
  if x == x'
  then return ()
  else throwError $ NotConvertible (Var x) (Var x')
checkConvert xs (App e1 e2) (App e1' e2') = do
  checkConvert xs e1 e1'
  checkConvert xs e2 e2'
checkConvert xs (Clos (Abs x a e) r) (Clos (Abs x' a' e') r') = do
  let v  = eval a r
      v' = eval a' r'
  checkConvert xs v v'
  let y  = freshVar x (map fst xs)
      vy = Var y
  checkConvert ((y, v) : xs) (eval e (consEVar r x vy)) (eval e' (consEVar r' x' vy))
checkConvert _ v v' = throwError $ NotConvertible v v'

checkDef c x a e = do
  checkT c a U
  checkT c e (eval a (envCont c))
  return $ CConsDef c x a e

checkDec c x a = do
  checkT c a U
  return $ consCVar c x a

runTypeCheckCtx :: Context -> Either TypeCheckError Cont
runTypeCheckCtx ctx@(Ctx cs) = 
  case runG (absCtx ctx) Map.empty of
    Left err -> Left err
    Right ds -> runG (typeCheckCtx (zip ds [0, 1 ..])) CNil
  where
    typeCheckCtx :: [(Decl, Int)] -> TypeCheckM Cont
    typeCheckCtx ds = do
      mapM_ checkDecl ds
      get
    checkDecl :: (Decl, Int) -> TypeCheckM ()
    checkDecl (d@(Dec x a), n) = do { 
      c  <- get ;
      c' <- checkDec c x a ;
      put c' } `catchError` (errhandler d n)
    checkDecl (d@(Def x a e), n) = do {
      c  <- get ;
      c' <- checkDef c x a e ;
      put c' } `catchError` (errhandler d n)
    errhandler :: Decl -> Int -> TypeCheckError -> TypeCheckM ()
    errhandler d n err = do
      let ss = ["when checking: " ++ (printTree (cs !! n)), "         decl: " ++ show d]
      throwError $ ExtendedErr err ss



