{-|
Module          : TypeChecker
Description     : providing functions that type check the abstract syntax
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
{-# OPTIONS_GHC -Wno-unused-do-bind #-}
module TypeChecker where

import           Control.Monad
import           Control.Monad.Except
-- import           Debug.Trace
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
  | NoTypeBoundVar String
  | TypeNotMatch Exp Val
  | NotConvertible Val Val
  | ExtendedWithPos TypeCheckError Decl
  deriving (Show)

instance InformativeError TypeCheckError where
  explain (CannotInferType e)       = ["Cannot infer type of expression: " ++ show e]
  explain (NotConvertible v1 v2)    = ["Values not convertible", "v1: " ++ show v1, "v2: " ++ show v2]
  explain (NoTypeBoundVar var)      = ["Variable without a bound type (this exception normally should not happen)",
                                       "variable name: " ++ var]
  explain (TypeNotMatch e v)        = ["Expression does not have the given type", "exp: " ++ show e, "type given: " ++ show v]
  explain (ExtendedWithPos terr d)  = ("Type check error found at " ++ show d) : explain terr

-- | check an expression is well typed and infer its type
checkI    :: EnvStrategy s => s -> Cont -> Exp -> TypeCheckM Val
-- | check an expression is well typed given a certain type
checkT    :: EnvStrategy s => s -> Cont -> Exp -> Val -> TypeCheckM ()
-- | check that two values are equal and infer their type
checkCI   :: EnvStrategy s => s -> Cont -> Val -> Val -> TypeCheckM Val
-- | check that two values are equal under a given type
checkCT   :: EnvStrategy s => s -> Cont -> Val -> Val -> Val -> TypeCheckM ()
-- | check that a declaration/definition is valid
checkDecl :: EnvStrategy s => s -> Cont -> Decl -> TypeCheckM Cont

checkI _ _ U = return U -- U has itself as its element
checkI s c (Var x) = do
  case getType c x of
    Just t -> let env = getEnv s c
              in return $ eval t env
    Nothing -> throwError $ NoTypeBoundVar x
checkI s c eapp@(App m n) = do
  tm <- checkI s c m
  case tm of
    Clos (Abs (Dec x a) b) r -> do
      let va = eval a r
      checkT s c n va
      let env = getEnv s c
          vn = eval n env
          r' = consEVar r x vn
      return (eval b r')
    _ -> throwError $ CannotInferType eapp
checkI s c (Abs d@Def {} e) = do
  c' <- checkDecl s c d
  checkI s c' e
checkI s c e@Abs {} = do
  checkT s c e U
  return U
checkI _ _ e = throwError $ CannotInferType e

checkT _ _ U U = return ()
checkT s c (Var x) v = do
  case getType c x of
    Just t -> do
      let env = getEnv s c
          vt  = eval t env
      void (checkCI s c vt v)
    Nothing -> throwError $ NoTypeBoundVar x
checkT s c e@App {} v = do
  v' <- checkI s c e
  void (checkCI s c v v')
checkT s c (Abs (Dec x a) b) U = do
  checkT s c a U
  let c' = consCVar c x a
  checkT s c' b U
checkT s c (Abs (Dec x a) e) (Clos (Abs (Dec x' a') e') r) = do
  checkT s c a U
  let env = getEnv s c
      va  = eval a env
      va' = eval a' r
  checkCI s c va va'
  let r' = consEVar r x' (Var x)
      ve' = eval e' r'
      c' = consCVar c x a
  checkT s c' e ve'
checkT s c (Abs d@Def {}  e) v = do
  c' <- checkDecl s c d
  checkT s c' e v
checkT _ _ e t = throwError $ TypeNotMatch e t

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
          env = getEnv s c
          nv  = eval n1 env
      checkCT s c n1 n2 va
      let r' = consEVar r x nv
      return $ eval b r'
    _ -> throwError $ NotConvertible (App m1 n1) (App m2 n2)
checkCI s c v1@Clos {} v2@Clos {} = do
  checkCT s c v1 v2 U
  return U
checkCI _ _ v v' = throwError $ NotConvertible v v'

checkCT s c v1 v2 (Clos (Abs (Dec z a) b) r) = do
  let va = eval a r
      fz = freshVar z (varsCont c)
      vfz = Var fz
      r1 = consEVar r z vfz
      vb = eval b r1
      env = getEnv s c
      v1' = eval (App v1 vfz) env
      v2' = eval (App v2 vfz) env
      c1 = consCVar c fz va
  checkCT s c1 v1' v2' vb
checkCT s c (Clos (Abs (Dec x1 a1) b1) r1) (Clos (Abs (Dec x2 a2) b2) r2) U = do
  let va1 = eval a1 r1
      va2 = eval a2 r2
  checkCI s c va1 va2
  let fx = freshVar x1 (varsCont c)
      vfx = Var fx
      c' = consCVar c fx va1
      v1 = eval b1 (consEVar r1 x1 vfx)
      v2 = eval b2 (consEVar r2 x2 vfx)
  void $ checkCI s c' v1 v2
checkCT s c v1 v2 _ = do
  void $ checkCI s c v1 v2

checkDecl s c (Dec x a) = do
  checkT s c a U
  return $ consCVar c x a

checkDecl s c (Def x a e) = do
  checkT s c a U
  let va = eval a (getEnv s c)
  checkT s c e va
  return $ CConsDef c x a e

-- | parse and type check a file
parseCheckFile :: EnvStrategy s => s -> String -> Either String (Context, Cont)
parseCheckFile s text = case pContext (myLexer text) of
  Left parseError -> Left (unlines (map errorMsg ["failed to parse the file", parseError]))
  Right cx ->
    case runTypeCheckCtx s cx of
      Left ss  -> Left (unlines (map errorMsg ss))
      Right ax -> Right (cx, ax)

-- | type check an expression under given context and locking strategy
convertCheckExpr :: EnvStrategy s => s -> Context -> Cont -> CExp -> Either String Exp
convertCheckExpr s cc ac ce =
  let m = toMap cc in
  case runG (absExp ce) m of
    Left err -> Left $ unlines . map errorMsg $ explain err
    Right e  -> case runG (checkI s ac e) CNil of
                  Left err -> Left $ unlines . map errorMsg $ explain err
                  Right _  -> Right e

-- | type check an declaration/definition under given context and locking strategy
convertCheckDecl :: EnvStrategy s => s -> Context -> Cont -> CDecl -> Either String Decl
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

runTypeCheckCtx :: EnvStrategy s => s -> Context -> Either [String] Cont
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
