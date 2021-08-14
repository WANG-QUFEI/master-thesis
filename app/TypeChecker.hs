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
import qualified Data.HashMap.Strict.InsOrd as OrdM

import qualified Convertor                  as Con
import qualified Core.Abs                   as Abs
import           Core.Layout                (resolveLayout)
import           Core.Par
import           Lang
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
  explain (NoTypeBoundVar x)        = ["Variable without a bound type (this exception normally should not happen)",
                                       "variable name: " ++ x]
  explain (TypeNotMatch e v)        = ["Expression does not have the given type", "exp: " ++ show e, "type: " ++ show v]
  explain (ExtendedWithPos terr d)  = "Found type check error at: " : show d : explain terr
  explain (ExtendedWithCtx terr ss) = ss ++ explain terr

-- |Check that a declaration is valid
checkD :: LockStrategy s => s -> Cont -> Decl -> TypeCheckM Cont
checkD s c (Dec x a) = do
  checkT s c a U
  return $ bindConT c x a
checkD s c (Def x a b) = do
  checkT s c a U
  let qa = eval (getEnv s c) a
  checkT s c b qa
  return $ bindConD c x a b
checkD s c (DSeg x sg) =
  case sg of
    SRef sn ->
      let c' = getSegByPath c [sn]
          cn = Cs (mapCont c')
      in return $ bindConS c x cn
    SNest sg' sn ->
      let rpath = sn : revSegPath sg'
          c' = getSegByPath c rpath
          cn = Cs (mapCont c')
      in return $ bindConS c x cn
    SInst sg' ips -> do
      let rpath = revSegPath sg'
          c' = getSegByPath c rpath
      c'' <- checkSegInst s c c' ips
      let cn = Cs (mapCont c'')
      return $ bindConS c x cn
    SDef ds ->
      let ns = cns c ++ [x]
      in do
        c' <- foldM (checkD s) (emptyCont ns) ds
        return $ bindConS c x (Cs (mapCont c'))

-- |Check that an expression has a q-expression as type
checkT :: LockStrategy s => s -> Cont -> Exp -> QExp -> TypeCheckM ()
checkT _ _ U U = return ()
checkT s c (Var x) q = do
  let t  = getType c x
      qt = eval (getEnv s c) t
  void (checkConvertI s c qt q)
checkT s c (SegVar sg x) q = do
  let (sg', ips) = breakSeg sg
      rpath = revSegPath sg'
      c' = getSegByPath c rpath
  c'' <- checkSegInst s c c' ips
  let t  = getType c'' x
      qt = eval (getEnv s c'') t
  void (checkConvertI s c'' qt q)
checkT s c e@App {} q = do
  q' <- checkI s c e
  void (checkConvertI s c q q')
checkT s c (Abs x a b) U = do
  checkT s c a U
  let c' = bindConT c x a
  checkT s c' b U
checkT s c (Abs x a b) (Clos (Abs x' a' b') r') = do
  checkT s c a U
  let r  = getEnv s c
      qa = eval r a
      qa' = eval r' a'
  void $ checkConvertI s c qa qa'
  let y   = qualifiedName (cns c) x
      r'' = bindEnvQ r' x' (Var y)
      qb' = eval r'' b'
      c'  = bindConT c x a
  checkT s c' b qb'
checkT s c (Let x a b e) q = do
  c' <- checkD s c (Def x a b)
  checkT s c' e q
checkT _ _ e v = throwError $ TypeNotMatch e v

-- |Check that an expression is well typed and infer its type
checkI :: LockStrategy s => s -> Cont -> Exp -> TypeCheckM QExp
checkI _ _ U = return U
checkI s c (Var x) = do
  let t = getType c x
      r = getEnv s c
  return $ eval r t
checkI s c (SegVar sg x) = do
  let (sg', ips) = breakSeg sg
      rpath = revSegPath sg'
      c' = getSegByPath c rpath
  c'' <- checkSegInst s c c' ips
  let t   = getType c'' x
      r'' = getEnv s c''
  return $ eval r'' t
checkI s c (App m n) = do
  qm <- checkI s c m
  case qm of
    Clos (Abs x a b) r -> do
      let qa = eval r a
      checkT s c n qa
      let r0 = getEnv s c
          ns = cns c
          qn = eval r0 n
          r' = bindEnvQ r (qualifiedName ns x) qn
      return $ eval r' b
    _ -> throwError (NotFunctionClos qm)
checkI s c (Let x a b e) = do
  c' <- checkD s c (Def x a b)
  checkI s c' e
checkI _ _ e = throwError $ CannotInferType e

-- |Check that two q-exps are convertible and infer their type
checkConvertI :: LockStrategy s => s -> Cont -> QExp -> QExp -> TypeCheckM QExp
checkConvertI _ _ U U = return U
checkConvertI s c (Var x) (Var y)
  | x == y = let t  = getType c x
                 r  = getEnv s c
                 qt = eval r t
             in return qt
  | otherwise = throwError $ NotConvertible (Var x) (Var y)
checkConvertI s c (App m1 n1) (App m2 n2) = do
  q <- checkConvertI s c m1 m2
  case q of
    Clos (Abs x a b) r' -> do
      let qa = eval r' a
      checkConvertT s c n1 n2 qa
      let r  = getEnv s c
          qn = eval r n1
          r1 = bindEnvQ r' x qn
      return $ eval r1 b
    _ -> throwError $ NotFunctionClos q
checkConvertI s c q1@Clos {} q2@Clos {} = do
  checkConvertT s c q1 q2 U
  return U
checkConvertI _ _ q1 q2 = throwError $ NotConvertible q1 q2

-- |Check that two q-expressions are convertible under a given type
checkConvertT :: LockStrategy s => s -> Cont -> QExp -> QExp -> QExp -> TypeCheckM ()
checkConvertT s c q1 q2 (Clos (Abs x a b) r') = do
  let names = namesCont c
      y     = freshVar x names
      qa    = eval r' a
      c'    = bindConT c y qa
      r     = getEnv s c
      qm    = eval r (App q1 (Var y))
      qn    = eval r (App q2 (Var y))
      r''   = bindEnvQ r' x (Var y)
      qb    = eval r'' b
  checkConvertT s c' qm qn qb
checkConvertT s c (Clos (Abs x1 a1 b1) r1) (Clos (Abs x2 a2 b2) r2) U = do
  let qa1 = eval r1 a1
      qa2 = eval r2 a2
  checkConvertT s c qa1 qa2 U
  let names = namesCont c
      y     = freshVar x1 names
      c'    = bindConT c y qa1
      r1'   = bindEnvQ r1 x1 (Var y)
      r2'   = bindEnvQ r2 x2 (Var y)
      qb1   = eval r1' b1
      qb2   = eval r2' b2
  checkConvertT s c' qb1 qb2 U
checkConvertT s c q1 q2 t = do
  t' <- checkConvertI s c q1 q2
  void $ checkConvertI s c t t'

-- |Check that the instantiation of a segment is type checked, namely the expressions provided
-- match the type of the constant
checkSegInst :: LockStrategy s => s
             -> Cont -- ^ the context where the instantiation occurs
             -> Cont -- ^ the segment to which the instantiation applies
             -> [InstPair] -- ^ a list of expressions and the corresponding names to be instantiated
             -> TypeCheckM Cont -- ^ the segment after the instantiation
checkSegInst _ _  ct []  = return ct
checkSegInst s cp cc ips = foldM g cc ips
  where g :: Cont -> InstPair -> TypeCheckM Cont
        g c (e, x) = do
          let Just (Ct t) = OrdM.lookup x (mapCont c) -- get the type of 'x' in segment 'c'
              rc = getEnv s c
              qt = eval rc t
          checkT s cp e qt      -- in context 'cp', check that the expression 'e' matches the type of 't'
          let rp = getEnv s cp
              qe = eval rp e    -- evaluate 'e' in the environment got from 'cp'
              c' = bindConD c x t qe -- bind the q-expression of 'e' to variable 'x' in the context 'c'
          return c'

-- |Parse and type check a file
parseAndCheck :: LockStrategy s => s -> String -> Either [String] (Abs.Context, Cont)
parseAndCheck s str = case pContext (resolveLayout True  $ myLexer str) of
  Left err -> Left (map errorMsg ["failed to parse the file", err])
  Right cxt -> case runG (Con.absCtx cxt) Con.initTree of
    Left err -> Left $ explain err
    Right axt -> case runG (typeCheck axt) (emptyCont []) of
      Left err -> Left $ explain err
      Right c  -> Right (cxt, c)
  where
    typeCheck :: AbsContext -> TypeCheckM Cont
    typeCheck axt = do
      mapM_ checkUpdate axt
      get

    checkUpdate :: Decl -> TypeCheckM ()
    checkUpdate d = do
      c <- get
      c' <- checkD s c d
      put c'
      `catchError` (\e -> throwError $ ExtendedWithPos e d)

-- |Type check an expression under given context and locking strategy
checkExpr :: LockStrategy s => s -> Abs.Context -> Cont -> Abs.Exp -> Either String Exp
checkExpr s cc cont ce =
  let Right tree = runG (Con.ctxTree cc) Con.initTree
  in case runG (Con.absExp (cns cont) ce) tree of
    Left err -> Left $ unlines . map errorMsg $ explain err
    Right e  -> case runG (soundExpr cont e) (emptyCont (cns cont)) of
                  Left err -> Left $ unlines . map errorMsg $ explain err
                  Right _  -> Right e
  where
    soundExpr :: Cont -> Exp -> TypeCheckM ()
    soundExpr c (Abs x a b) = do
      checkT s c a U
      let c' = bindConT c x a
      void $ checkI s c' b
    soundExpr c e = void $ checkI s c e

-- |Type check an declaration/definition under given context and locking strategy
checkDecl :: LockStrategy s => s -> Abs.Context -> Cont -> Abs.Decl -> Either String Cont
checkDecl s cc cont cd =
  let Right tree = runG (Con.ctxTree cc) Con.initTree
  in case runG (Con.absDecl (cns cont) cd) tree of
       Left err -> Left $ unlines . map errorMsg $ explain err
       Right d  -> case runG (checkD s cont d) (emptyCont (cns cont)) of
                  Left err    -> Left $ unlines . map errorMsg $ explain err
                  Right cont' -> Right cont'
