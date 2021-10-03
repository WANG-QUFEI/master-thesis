{-# LANGUAGE BlockArguments #-}
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

import qualified Convertor            as Con
import           Core.Layout          (resolveLayout)
import           Core.Par
import           Lang
import           Text.Printf          (printf)
import           Util


-- | monad for type-checking
type TypeCheckM a = G TypeCheckError (Cont, ConvertCheck) a

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
  explain (CannotInferType e)       = ["cannot infer type!", printf "exp: %s" (show e)]
  explain (NotFunctionClos v)       = ["not a function closure!", show v]
  explain (NotConvertible q1 q2)    = ["values not convertible!", "q1: " ++ show q1, "q2: " ++ show q2]
  explain (NoTypeBoundVar x)        = ["no bound type!", "var: " ++ x]
  explain (TypeNotMatch e q)        = ["type mismatch", "exp: " ++ show e, "type: " ++ show q]
  explain (ExtendedWithPos err d)   = "detect type check error at: " : show d : explain err
  explain (ExtendedWithCtx err ss)  = ss ++ explain err

-- |Check that a declaration is valid
checkD :: LockStrategy s => s -> Cont -> Decl -> TypeCheckM Cont
checkD s c d = do
  doCheck d
  `catchError` (\e -> throwError $ ExtendedWithPos e d)
  where
    doCheck :: Decl -> TypeCheckM Cont
    doCheck (Dec x a) = do
      checkT s c a U
      return $ bindConT c x a
    doCheck (Def x a b) = do
      checkT s c a U
      let qa = eval (getEnv s c) a
      checkT s c b qa
      return $ bindConD c x a b
    doCheck (Seg x ds) =
      let ns = cns c ++ [x]
      in do
        c' <- foldM (checkD s) (emptyCont ns) ds
        return $ bindConS c x (Cs (mapCont c'))
    doCheck (SegInst x ref eps) = do
      let c' = findSeg c (refnsp ref)
      c'' <- checkSegInst s c c' eps
      let cn = Cs (mapCont c'')
      return $ bindConS c x cn

-- |Check that an expression has a q-expression as type
checkT :: LockStrategy s => s -> Cont -> Exp -> QExp -> TypeCheckM ()
checkT _ _ U U = return ()
checkT s c (Var x) q = do
  let q' = getTypeQ s c x
  ct <- gets snd
  checkConvert s ct c q' q
checkT s c (SVar ref eps) q = do
  let pr = reverse (rns ref)
      c' = findSeg c pr
      x  = rid ref
  c'' <- checkSegInst s c c' eps
  let q' = getTypeQ s c'' x
  ct <- gets snd
  checkConvert s ct c'' q' q
checkT s c e@App {} q = do
  q' <- checkI s c e
  ct <- gets snd
  checkConvert s ct c q q'
checkT s c (Abs x a b) U = do
  checkT s c a U
  let c' = bindConT c x a
  checkT s c' b U
checkT s c (Abs x a b) (Clos (Abs x' a' b') r') = do
  checkT s c a U
  let r  = getEnv s c
      qa = eval r a
      qa' = eval r' a'
  ct <- gets snd
  checkConvert s ct c qa qa'
  let y   = qualifiedName' (cns c) x
      r'' = bindEnvQ r' x' (Var y)
      qb' = eval r'' b'
      c'  = bindConT c x a
  checkT s c' b qb'
checkT s c (Let x a b e) q = do
  c' <- checkD s c (Def x a b)
  checkT s c' e q
checkT _ _ e q = throwError $ TypeNotMatch e q

-- |Check that an expression is well typed and infer its type
checkI :: LockStrategy s => s -> Cont -> Exp -> TypeCheckM QExp
checkI s c (Var x) = do
  let q = getTypeQ s c x
  return q
checkI s c (SVar ref eps) = do
  let pr = reverse (rns ref)
      c' = findSeg c pr
      x  = rid ref
  c'' <- checkSegInst s c c' eps
  let q = getTypeQ s c'' x
  return q
checkI s c (App m n) = do
  qm <- checkI s c m
  case qm of
    Clos (Abs x a b) r -> do
      let qa = eval r a
      checkT s c n qa
      let r0 = getEnv s c
          qn = eval r0 n
          r' = bindEnvQ r x qn
      return $ eval r' b
    _ -> throwError (NotFunctionClos qm)
checkI _ _ e = throwError $ CannotInferType e

checkConvert :: LockStrategy s => s -> ConvertCheck -> Cont -> QExp -> QExp -> TypeCheckM ()
checkConvert _ Beta c q1 q2 = convertBeta (cns c) (namesCtx c) q1 q2
checkConvert s Eta  c q1 q2 = void (convertEta s c q1 q2)

convertBeta :: Namespace -> [String] -> QExp -> QExp -> TypeCheckM ()
convertBeta _ _ U U = return ()
convertBeta _ _ (Var x) (Var x') =
  if x == x' then return () else throwError $ NotConvertible (Var x) (Var x')
convertBeta nsp ns (App k1 v1) (App k2 v2) = do
  convertBeta nsp ns k1 k2
  convertBeta nsp ns v1 v2
convertBeta nsp ns (Clos (Abs x a m) r) (Clos (Abs x' a' m') r') = do
  let va  = eval r a
      va' = eval r' a'
  convertBeta nsp ns va va'
  let y = freshVar x ns
      y' = qualifiedName' nsp y
      r1 = bindEnvQ r x (Var y')
      q1 = eval r1 m
      r1' = bindEnvQ r' x' (Var y')
      q1' = eval r1' m'
  convertBeta nsp (y : ns) q1 q1'
convertBeta _ _ q1 q2 = throwError $ NotConvertible q1 q2

-- |Check that two q-exps are convertible and infer their type
convertEta :: LockStrategy s => s -> Cont -> QExp -> QExp -> TypeCheckM QExp
convertEta _ _ U U = return U
convertEta s c (Var x) (Var y)
  | x == y = return (getTypeQ s c x)
  | otherwise = throwError $ NotConvertible (Var x) (Var y)
convertEta s c (App m1 n1) (App m2 n2) = do
  q <- convertEta s c m1 m2
  case q of
    Clos (Abs x a b) r' -> do
      let qa = eval r' a
      convertEtaT s c n1 n2 qa
      let r1 = bindEnvQ r' x n1
      return $ eval r1 b
    _ -> throwError $ NotFunctionClos q
convertEta s c q1@Clos {} q2@Clos {} = do
  convertEtaT s c q1 q2 U
  return U
convertEta _ _ q1 q2 = throwError $ NotConvertible q1 q2

-- |Check that two q-expressions are convertible under a given type
convertEtaT :: LockStrategy s => s -> Cont -> QExp -> QExp -> QExp -> TypeCheckM ()
convertEtaT s c q1 q2 (Clos (Abs x a b) r') = do
  let names = namesCtx c
      y     = freshVar x names
      r     = getEnv s c
      qm    = eval r (App q1 (Var y))
      qn    = eval r (App q2 (Var y))
      y'    = qualifiedName' (cns c) y
      r''   = bindEnvQ r' x (Var y')
      qa    = eval r' a
      c'    = bindConT c y qa
      qb    = eval r'' b
  convertEtaT s c' qm qn qb
convertEtaT s c (Clos (Abs x1 a1 b1) r1) (Clos (Abs x2 a2 b2) r2) U = do
  let qa1 = eval r1 a1
      qa2 = eval r2 a2
  convertEtaT s c qa1 qa2 U
  let names = namesCtx c
      y     = freshVar x1 names
      y'    = qualifiedName' (cns c) y
      r1'   = bindEnvQ r1 x1 (Var y')
      r2'   = bindEnvQ r2 x2 (Var y')
      qb1   = eval r1' b1
      qb2   = eval r2' b2
      c'    = bindConT c y qa1
  convertEtaT s c' qb1 qb2 U
convertEtaT s c q1 q2 t = do
  t' <- convertEta s c q1 q2
  void $ convertEta s c t t'

-- |Check that the instantiation of a segment is type checked, namely the expressions provided
-- match the type of the constant
checkSegInst :: LockStrategy s => s
             -> Cont -- ^ the context where the instantiation occurs
             -> Cont -- ^ the segment to which the instantiation applies
             -> [ExPos] -- ^ a list of expressions and the corresponding names to be instantiated
             -> TypeCheckM Cont -- ^ the segment after the instantiation
checkSegInst _ _  cc []  = return cc
checkSegInst s cp cc eps = foldM g cc eps
  where g :: Cont -> ExPos -> TypeCheckM Cont
        g c (e, x) = do
          let (c', t) = getType c x -- get the type of 'x' in segment 'c'
              r = getEnv s c'
              q = eval r t
          checkT s cp e q      -- in context 'cp', check that the expression 'e' matches the type of 't'
          let rp = getEnv s cp
              qe = eval rp e    -- evaluate 'e' in the environment got from 'cp'
              cr = bindConD c x t qe -- bind the q-expression of 'e' to variable 'x' in the context 'c'
          return cr

-- |Parse and type check a file
parseAndCheck :: LockStrategy s => s -> ConvertCheck -> String -> Either [String] Cont
parseAndCheck s ctc str = case pContext (resolveLayout True  $ myLexer str) of
  Left err -> Left (map errorMsg ["failed to parse the file", err])
  Right cxt -> case runG (Con.absCtx cxt) Con.initTree of
    Left err -> Left $ explain err
    Right axt -> case runG (typeCheckProg s axt) (emptyCont [], ctc) of
      Left err -> Left $ explain err
      Right c  -> Right c

typeCheckProg :: LockStrategy s => s -> [Decl] -> TypeCheckM Cont
typeCheckProg s axt = do
  mapM_ (checkUpdate s) axt
  gets fst

checkUpdate :: LockStrategy s => s -> Decl -> TypeCheckM ()
checkUpdate s d = do
  (c, ctc')  <- get
  c' <- checkD s c d
  put (c', ctc')

-- |Read a quasi-expression back into an expression of the normal form
readBack :: [String] -> QExp -> Exp
readBack _  U = U
readBack _  (Var x) = Var x
readBack ss (App a b) = App (readBack ss a) (readBack ss b)
readBack ss (Clos (Abs "" a b) r) =
  let a' = readBack ss (eval r a)
      b' = readBack ss (eval r b)
  in Abs "" a' b'
readBack ss (Clos (Abs x a b) r) =
  let y  = freshVar x ss
      a' = readBack ss (eval r a)
      r' = bindEnvQ r x (Var y)
      b' = readBack (y:ss) (eval r' b)
  in Abs y a' b'
readBack _ _ = error "error: readBack"

getTypeQ :: LockStrategy s => s -> Cont -> String -> QExp
getTypeQ s c x =
  let (c', t) = getType c x
      r = getEnv s c'
  in eval r t
