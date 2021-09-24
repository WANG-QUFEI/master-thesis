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
--import           Debug.Trace

import           Convertor
import           Core.Abs
import           Core.Layout          (resolveLayout)
import           Core.Par
import           Data.Maybe
import           Lang
import           Util


-- | monad for type-checking
type TypeCheckM a = G TypeCheckError (Cont, ConvertCheck) a

-- | a datatype used as exception in an ExceptT monad
data TypeCheckError
  = CannotInferType Exp
  | NotFunctionClos Exp
  | TypeNotMatch Exp QExp
  | NotConvertible QExp QExp
  | ExtendedWithPos TypeCheckError Decl
  | ExtendedWithCtx TypeCheckError [String]
  deriving (Show)

instance InformativeError TypeCheckError where
  explain (CannotInferType e)       = ["Cannot infer type for expression: " ++ show e]
  explain (NotFunctionClos v)       = ["Value supposed to be a function closure, but it isn't", show v]
  explain (NotConvertible v1 v2)    = ["Values not convertible", "v1: " ++ show v1, "v2: " ++ show v2]
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
  let q = getTypeQ s c x
  cc <- gets snd
  checkConvert s cc c q v
checkT s c e@App {} v = do
  q <- checkI s c e
  cc <- gets snd
  checkConvert s cc c q v
checkT s c (Abs (Dec x a) b) U = do
  checkT s c a U
  let c' = consCVar c x a
  checkT s c' b U
checkT s c (Abs (Dec x a) m) (Clos (Abs (Dec x' a') t) r) = do
  checkT s c a U
  let r0 = getEnv s c
      va  = eval a r0
      va' = eval a' r
  cc <- gets snd
  checkConvert s cc c va va'
  let r' = consEVar r x' (Var x)
      q = eval t r'
      c' = consCVar c x a
  checkT s c' m q
checkT s c (Abs d@Def {} e) q = do
  c' <- checkD s c d
  checkT s c' e q
checkT _ _ e v = throwError $ TypeNotMatch e v

-- | check an expression is well typed and infer its type
checkI :: LockStrategy s => s -> Cont -> Exp -> TypeCheckM QExp
checkI s c (Var x) = do
  let q = getTypeQ s c x
  return q
checkI s c (App m n) = do
  t <- checkI s c m
  case t of
    Clos (Abs (Dec x a) b) r -> do
      let va = eval a r
      checkT s c n va
      let r0 = getEnv s c
          vn = eval n r0
          r' = consEVar r x vn
      return (eval b r')
    _ -> throwError (NotFunctionClos t)
checkI _ _ e = throwError $ CannotInferType e

checkConvert :: LockStrategy s => s -> ConvertCheck -> Cont -> QExp -> QExp -> TypeCheckM ()
checkConvert _ Beta c q1 q2 = convertBeta (namesCont c) q1 q2
checkConvert s Eta  c q1 q2 = void (convertEta s c q1 q2)

convertBeta :: [String] -> QExp -> QExp -> TypeCheckM ()
convertBeta _ U U = return ()
convertBeta _ (Var x) (Var x') =
  if x == x' then return () else throwError $ NotConvertible (Var x) (Var x')
convertBeta ns (App k1 v1) (App k2 v2) = do
  convertBeta ns k1 k2
  convertBeta ns v1 v2
convertBeta ns (Clos (Abs (Dec x a) m) r) (Clos (Abs (Dec x' a') m') r') = do
  let va  = eval a r
      va' = eval a' r'
  convertBeta ns va va'
  let y = freshVar x' ns
      r1 = consEVar r x (Var y)
      q1 = eval m r1
      r1' = consEVar r' x' (Var y)
      q1' = eval m' r1'
  convertBeta (y : ns) q1 q1'
convertBeta _ q1 q2 = throwError $ NotConvertible q1 q2

convertEta :: LockStrategy s => s -> Cont -> QExp -> QExp -> TypeCheckM QExp
convertEta _ _ U U = return U
convertEta s c (Var x) (Var x') =
  if x == x'
  then return (getTypeQ s c x)
  else throwError $ NotConvertible (Var x) (Var x')
convertEta s c (App m1 n1) (App m2 n2) = do
  v <- convertEta s c m1 m2
  case v of
    Clos (Abs (Dec x a) b) r -> do
      let va = eval a r
      convertEtaT s c n1 n2 va
      let r' = consEVar r x n1
      return $ eval b r'
    _ -> throwError $ NotFunctionClos v
convertEta s c v1@Clos {} v2@Clos {} = do
  convertEtaT s c v1 v2 U
  return U
convertEta _ _ v v' = throwError $ NotConvertible v v'

convertEtaT  :: LockStrategy s => s -> Cont -> QExp -> QExp -> QExp -> TypeCheckM ()
convertEtaT s c v1 v2 (Clos (Abs (Dec x a) b) r) = do
  let va = eval a r
      y  = freshVar x (namesCont c)
      c' = consCVar c y va
      r0 = getEnv s c
      m = eval (App v1 (Var y)) r0
      n = eval (App v2 (Var y)) r0
      r' = consEVar r x (Var y)
      vb = eval b r'
  convertEtaT s c' m n vb
convertEtaT s c (Clos (Abs (Dec x1 a1) b1) r1) (Clos (Abs (Dec x2 a2) b2) r2) U = do
  let va1 = eval a1 r1
      va2 = eval a2 r2
  convertEtaT s c va1 va2 U
  let x' = freshVar x1 (namesCont c)
      var = Var x'
      vb1 = eval b1 (consEVar r1 x1 var)
      vb2 = eval b2 (consEVar r2 x2 var)
      c' = consCVar c x' va1
  convertEtaT s c' vb1 vb2 U
convertEtaT s c v1 v2 t = do
  t' <- convertEta s c v1 v2
  void $ convertEta s c t t'

-- | parse and type check a file
parseCheckFile :: LockStrategy s => s -> ConvertCheck -> String -> Either String (Context, Cont)
parseCheckFile s c text = case pContext (resolveLayout True  $ myLexer text) of
  Left parseError -> Left (unlines (map errorMsg ["failed to parse the file", parseError]))
  Right cx ->
    case runTypeCheckCtx s c cx of
      Left ss  -> Left (unlines (map errorMsg ss))
      Right ax -> Right (cx, ax)

-- | type check an expression under given context and locking strategy
convertCheckExpr :: LockStrategy s => s -> ConvertCheck -> Context -> Cont -> CExp -> Either String Exp
convertCheckExpr s ctc cc ac ce =
  let m = toMap cc in
  case runG (absExp ce) m of
    Left err -> Left $ unlines . map errorMsg $ explain err
    Right e  -> checkExpr ac e
  where
    checkExpr :: Cont -> Exp -> Either String Exp
    checkExpr _ U = Right U
    checkExpr ctx e@(Abs d m) =
      case runG (checkD s ctx d) (CNil, ctc) of
        Left err   -> Left $ unlines . map errorMsg $ explain err
        Right ctx' -> case checkExpr ctx' m of
                         Left err -> Left err
                         Right _  -> Right e
    checkExpr ctx e =
      case runG (checkI s ctx e) (CNil, ctc) of
        Left err -> Left $ unlines . map errorMsg $ explain err
        Right _  -> Right e

-- | type check an declaration/definition under given context and locking strategy
convertCheckDecl :: LockStrategy s => s -> ConvertCheck -> Context -> Cont -> CDecl -> Either String Decl
convertCheckDecl s ctc cc ac cd =
  let m = toMap cc in
  case runG (absDecl cd) m of
    Left err -> Left $ unlines . map errorMsg $ explain err
    Right d  -> case runG (checkD s ac d) (CNil, ctc) of
                  Left err -> Left $ unlines . map errorMsg $ explain err
                  _        -> Right d

toMap :: Context -> Map.Map String Id
toMap (Ctx ds) = Map.unions (map toMapD ds)

toMapD :: CDecl -> Map.Map String Id
toMapD (CDec x _)   = Map.singleton (idStr x) x
toMapD (CDef x _ _) = Map.singleton (idStr x) x

runTypeCheckCtx :: LockStrategy s => s -> ConvertCheck -> Context -> Either [String] Cont
runTypeCheckCtx s cc ctx@(Ctx _) =
  case runG (absCtx ctx) Map.empty of
    Left err -> Left $ explain err
    Right ds ->
      case runG (typeCheckCtx ds) (CNil, cc) of
        Left err -> Left $ explain err
        Right c  -> Right c
  where
    typeCheckCtx :: [Decl] -> TypeCheckM Cont
    typeCheckCtx ds = do
      mapM_ checkAndUpdateDecl ds
      gets fst

    checkAndUpdateDecl :: Decl -> TypeCheckM ()
    checkAndUpdateDecl d = do
      (c, cc') <- get
      c' <- checkD s c d
      put (c', cc')
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

getTypeQ :: LockStrategy s => s -> Cont -> String -> QExp
getTypeQ s c x =
  let t = fromJust (getType c x)
      e = getEnv s c
  in eval t e
