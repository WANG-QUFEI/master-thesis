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

import           Classes
import           Convertor
import           Core.Abs
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
  | TypeNotMatch Exp Val
  | NotConvertible Val Val
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

-- | check an expression is well typed and infer its type
checkInferT :: LockStrategy s => s -> Cont -> Exp -> TypeCheckM Val
checkInferT _ _ U = return U -- U has itself as its element
checkInferT s c (Var x) = do
  case getType c x of
    Just t -> let env = getEnv s c
              in return $ eval t env
    Nothing -> throwError $ NoTypeBoundVar x
checkInferT s c (App m n) = do
  tm <- checkInferT s c m
  case tm of
    Clos (Abs (Dec x a) b) r -> do
      let va = eval a r
      checkWithT s c n va
      let env = getEnv s c
          vn = eval n env
          r' = consEVar r x vn
      return (eval b r')
    _ -> throwError (NotFunctionClos tm)
checkInferT s c (Abs d@Def {} e) = do
  c' <- checkDecl s c d
  checkInferT s c' e
checkInferT _ _ e = throwError $ CannotInferType e

-- | check an expression is well typed given a certain type
checkWithT :: LockStrategy s => s -> Cont -> Exp -> Val -> TypeCheckM ()
checkWithT _ _ U U = return ()
checkWithT s c (Var x) v = do
  case getType c x of
    Just t -> do
      let env = getEnv s c
          vt  = eval t env
      void (checkEqualInferT s c vt v)
    Nothing -> throwError $ NoTypeBoundVar x
checkWithT s c e@App {} v = do
  v' <- checkInferT s c e
  void (checkEqualInferT s c v v')
checkWithT s c (Abs (Dec x a) b) U = do
  checkWithT s c a U
  let c' = consCVar c x a
  checkWithT s c' b U
checkWithT s c (Abs (Dec x a) e) (Clos (Abs (Dec x' a') e') r) = do
  checkWithT s c a U
  let env = getEnv s c
      va  = eval a env
      va' = eval a' r
  void $ checkEqualInferT s c va va'
  let r' = consEVar r x' (Var x)
      ve' = eval e' r'
      c' = consCVar c x a
  checkWithT s c' e ve'
checkWithT s c (Abs d@Def {}  e) v = do
  c' <- checkDecl s c d
  checkWithT s c' e v
checkWithT _ _ e v = throwError $ TypeNotMatch e v

-- | check that two values are equal and infer their type
checkEqualInferT :: LockStrategy s => s -> Cont -> Val -> Val -> TypeCheckM Val
checkEqualInferT _ _ U U = return U
checkEqualInferT s c (Var x) (Var x') =
  if x == x'
  then case getType c x of
         Just t -> do
           let env = getEnv s c
           return $ eval t env
         Nothing -> throwError $ NoTypeBoundVar x
  else throwError $ NotConvertible (Var x) (Var x')
checkEqualInferT s c (App m1 n1) (App m2 n2) = do
  v <- checkEqualInferT s c m1 m2
  case v of
    Clos (Abs (Dec x a) b) r -> do
      let va = eval a r
      checkEqualWithT s c n1 n2 va
      let nv = eval n1 (getEnv s c)
          r' = consEVar r x nv
      return $ eval b r'
    _ -> throwError $ NotFunctionClos v
checkEqualInferT s c v1@Clos {} v2@Clos {} = do
  checkEqualWithT s c v1 v2 U
  return U
checkEqualInferT _ _ v v' = throwError $ NotConvertible v v'

-- | check that two values are equal under a given type
checkEqualWithT  :: LockStrategy s => s -> Cont -> Val -> Val -> Val -> TypeCheckM ()
checkEqualWithT s c v1 v2 (Clos (Abs (Dec x a) b) r) = do
  let va = eval a r
      x' = freshVar x (varsCont c)
      var = Var x'
      c' = consCVar c x' va
      r' = consEVar r x var
      vb = eval b r'
      rc = getEnv s c
      m = eval (App v1 var) rc
      n = eval (App v2 var) rc
  checkEqualWithT s c' m n vb
checkEqualWithT s c (Clos (Abs (Dec x1 a1) b1) r1) (Clos (Abs (Dec x2 a2) b2) r2) U = do
  let va1 = eval a1 r1
      va2 = eval a2 r2
  void $ checkEqualInferT s c va1 va2
  let x' = freshVar x1 (varsCont c)
      var = Var x'
      c' = consCVar c x' va1
      v1 = eval b1 (consEVar r1 x1 var)
      v2 = eval b2 (consEVar r2 x2 var)
  void $ checkEqualInferT s c' v1 v2
checkEqualWithT s c v1 v2 _ = do
  void $ checkEqualInferT s c v1 v2

-- | check that a declaration/definition is valid
checkDecl :: LockStrategy s => s -> Cont -> Decl -> TypeCheckM Cont
checkDecl s c (Dec x a) = do
  checkWithT s c a U
  return $ consCVar c x a

checkDecl s c (Def x a e) = do
  checkWithT s c a U
  let va = eval a (getEnv s c)
  checkWithT s c e va
  return $ CConsDef c x a e

-- | parse and type check a file
parseCheckFile :: LockStrategy s => s -> String -> Either String (Context, Cont)
parseCheckFile s text = case pContext (myLexer text) of
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
    Right e  -> case runG (checkInferT s ac e) CNil of
                  Left err -> Left $ unlines . map errorMsg $ explain err
                  Right _  -> Right e

-- | type check an declaration/definition under given context and locking strategy
convertCheckDecl :: LockStrategy s => s -> Context -> Cont -> CDecl -> Either String Decl
convertCheckDecl s cc ac cd =
  let m = toMap cc in
  case runG (absDecl cd) m of
    Left err -> Left $ unlines . map errorMsg $ explain err
    Right d  -> case runG (checkDecl s ac d) CNil of
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
      c' <- checkDecl s c d
      put c'
      `catchError` (\e -> throwError $ ExtendedWithPos e d)
