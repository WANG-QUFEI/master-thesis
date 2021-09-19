{-|
Module          : TypeChecker
Description     : providing functions that type check the abstract syntax
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module TypeChecker where

import           Control.Monad
import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.Map             as Map
import           Debug.Trace

import           Classes
import           Convertor
import           Core.Abs
import           Core.Layout          (resolveLayout)
import           Core.Par
import           Lang
import           Message
import           Monads


-- | monad for type-checking
type TypeCheckM a = G TypeCheckError Cont a

-- | a datatype used as exception in an ExceptT monad
data TypeCheckError
  = CannotInferType Exp
  | NotFunctionClos Exp
  | NoTypeBoundVar String
  | TypeNotMatch Exp QExp
  | NotConvertible QExp QExp
  | ExtendedWithPos TypeCheckError Decl
  | ExtendedWithCtx TypeCheckError [String]
  deriving (Show)

instance InformativeError TypeCheckError where
  explain (CannotInferType e)       = ["Cannot infer type for expression: " ++ show e]
  explain (NotFunctionClos v)       = ["Value supposed to be a function closure, but it isn't", show v]
  explain (NotConvertible v1 v2)    = ["Values not convertible", "v1: " ++ show v1, "v2: " ++ show v2]
  explain (NoTypeBoundVar var)      = ["Variable without a bound type (this exception normally should not happen)",
                                       "variable name: " ++ var]
  explain (TypeNotMatch e v)        = ["Expression does not have the given type", "exp: " ++ show e, "type: " ++ show v]
  explain (ExtendedWithPos terr d)  = "Found type check error at: " : show d : explain terr
  explain (ExtendedWithCtx terr ss) = ss ++ explain terr

-- | check that a declaration/definition is valid
checkD :: LockStrategy s => s -> Cont -> Decl -> TypeCheckM Cont
checkD s c (Dec x a) = do
  checkT s c a U
  return $ consCVar c x a
checkD s c (Def x a e) = do
  checkT s c a U
  let va = eval a (getEnv s c)
  checkT s c e va
  return $ CConsDef c x a e

-- | check an expression is well typed given a certain type
checkT :: LockStrategy s => s -> Cont -> Exp -> QExp -> TypeCheckM ()
checkT _ _ U U = return ()
checkT s c (Var x) v = do
  case getType c x of
    Just t -> do
      let v' = eval t (getEnv s c)
      void (checkCI s c v' v)
    Nothing -> throwError $ NoTypeBoundVar x
checkT s c e@App {} v = do
  v' <- checkI s c e
  void (checkCI s c v' v)
checkT s c (Abs (Dec x a) b) U = do
  checkT s c a U
  let c' = consCVar c x a
  checkT s c' b U
checkT s c (Abs (Dec x a) e) (Clos (Abs (Dec x' a') e') r) = do
  checkT s c a U
  let env = getEnv s c
      va  = eval a env
      va' = eval a' r
  void $ checkCI s c va va'
  let r' = consEVar r x' (Var x)
      ve' = eval e' r'
      c' = consCVar c x a
  checkT s c' e ve'
checkT s c (Abs d@Def {} e) v = do
  c' <- checkD s c d
  checkT s c' e v
checkT _ _ e v = throwError $ TypeNotMatch e v

-- | check an expression is well typed and infer its type
checkI :: LockStrategy s => s -> Cont -> Exp -> TypeCheckM QExp
checkI _ _ U = return U -- U has itself as its element
checkI s c (Var x) = do
  case getType c x of
    Just t -> let env = getEnv s c
              in return $ eval t env
    Nothing -> throwError $ NoTypeBoundVar x
checkI s c (App m n) = do
  tm <- checkI s c m
  case tm of
    Clos (Abs (Dec x a) b) r -> do
      let va = eval a r
      checkT s c n va
      let env = getEnv s c
          vn = eval n env
          r' = consEVar r x vn
      return (eval b r')
    _ -> throwError (NotFunctionClos tm)
checkI s c (Abs d@Def {} e) = do
  c' <- checkD s c d
  checkI s c' e
checkI _ _ e = throwError $ CannotInferType e

-- | check that two values are equal and infer their type
checkCI :: LockStrategy s => s -> Cont -> QExp -> QExp -> TypeCheckM QExp
checkCI _ _ U U = return U
checkCI s c (Var x) (Var x') =
  if x == x'
  then case getType c x of
         Just t -> do
           let env = getEnv s c
           return $ eval t env
         Nothing -> throwError $ NoTypeBoundVar x
  else throwError $ NotConvertible (Var x) (Var x')
checkCI s c (App m1 n1) (App m2 n2) = do
  v <- checkCI s c m1 m2
  case v of
    Clos (Abs (Dec x a) b) r -> do
      let va = eval a r
      checkCT s c n1 n2 va
      let r' = consEVar r x n1
      return $ eval b r'
    _ -> throwError $ NotFunctionClos v
checkCI s c v1@Clos {} v2@Clos {} = do
  checkCT s c v1 v2 U
  return U
checkCI _ _ v v' = throwError $ NotConvertible v v'

-- | check that two values are equal under a given type
checkCT  :: LockStrategy s => s -> Cont -> QExp -> QExp -> QExp -> TypeCheckM ()
checkCT s c v1 v2 (Clos (Abs (Dec x a) b) r) = do
  let va = eval a r
      y  = freshVar x (namesCont c)
      vy = Var y
      c' = consCVar c y va
      r0 = getEnv s c
      m = eval (App v1 vy) r0
      n = eval (App v2 vy) r0
      r' = consEVar r x vy
      vb = eval b r'
  checkCT s c' m n vb
checkCT s c (Clos (Abs (Dec x1 a1) b1) r1) (Clos (Abs (Dec x2 a2) b2) r2) U = do
  let va1 = eval a1 r1
      va2 = eval a2 r2
  checkCT s c va1 va2 U
  let x' = freshVar x1 (namesCont c)
      var = Var x'
      vb1 = eval b1 (consEVar r1 x1 var)
      vb2 = eval b2 (consEVar r2 x2 var)
      c' = consCVar c x' va1
  checkCT s c' vb1 vb2 U
checkCT s c v1 v2 t = do
  t' <- checkCI s c v1 v2
  void $ checkCI s c t t'

-- | parse and type check a file
parseCheckFile :: LockStrategy s => s -> String -> Either String (Context, Cont)
parseCheckFile s text = case pContext (resolveLayout True  $ myLexer text) of
  Left parseError -> Left (unlines (map errorMsg ["failed to parse the file", parseError]))
  Right cx ->
    case runTypeCheckCtx s cx of
      Left ss  -> Left (unlines (map errorMsg ss))
      Right ax -> Right (cx, ax)

-- | type check an expression under given context and locking strategy
convertCheckExpr :: LockStrategy s => s -> Context -> Cont -> CExp -> Either String Exp
convertCheckExpr s cc ac ce =
  let m = toMap cc in
  case runG (absExp ce) m of
    Left err -> Left $ unlines . map errorMsg $ explain err
    Right e  -> case runG (checkI s ac e) CNil of
                  Left err -> Left $ unlines . map errorMsg $ explain err
                  Right _  -> Right e

-- | type check an declaration/definition under given context and locking strategy
convertCheckDecl :: LockStrategy s => s -> Context -> Cont -> CDecl -> Either String Decl
convertCheckDecl s cc ac cd =
  let m = toMap cc in
  case runG (absDecl cd) m of
    Left err -> Left $ unlines . map errorMsg $ explain err
    Right d  -> case runG (checkD s ac d) CNil of
                  Left err -> Left $ unlines . map errorMsg $ explain err
                  _        -> Right d

toMap :: Context -> Map.Map String Id
toMap (Ctx ds) = Map.unions (map toMapD ds)

toMapD :: CDecl -> Map.Map String Id
toMapD (CDec x _)   = Map.singleton (idStr x) x
toMapD (CDef x _ _) = Map.singleton (idStr x) x

runTypeCheckCtx :: LockStrategy s => s -> Context -> Either [String] Cont
runTypeCheckCtx s ctx@(Ctx _) =
  case runG (absCtx ctx) Map.empty of
    Left err -> Left $ explain err
    Right ds ->
      case runG (typeCheckCtx ds) CNil of
        Left err -> Left $ explain err
        Right c  -> Right c
  where
    typeCheckCtx :: [Decl] -> TypeCheckM Cont
    typeCheckCtx ds = do
      mapM_ checkAndUpdateDecl ds
      get

    checkAndUpdateDecl :: Decl -> TypeCheckM ()
    checkAndUpdateDecl d = do
      c <- get
      c' <- checkD s c d
      put c'
      `catchError` (\e -> throwError $ ExtendedWithPos e d)

readBack :: [String] -> QExp -> Exp
readBack _ U = U
readBack _ (Var x) = Var x
readBack ns (App v1 v2) = App (readBack ns v1) (readBack ns v2)
readBack ns (Clos (Abs (Dec "" a) e) r) =
  let a' = readBack ns (eval a r)
      e' = readBack ns (eval e r)
  in Abs (Dec "" a') e'
readBack ns (Clos (Abs (Dec x a) e) r) =
  let z  = freshVar x ns
      qa = eval a r
      a' = readBack ns qa
      r' = consEVar r x (Var z)
      qe = eval e r'
      e' = readBack (z : ns) qe
  in Abs (Dec z a') e'
readBack _ v = error ("readBack: " ++ show v)
