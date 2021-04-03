{-|
Module          : TypeChecker
Description     : providing functions that type check a transformed context
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module TypeChecker where


import           Data.List
import qualified Data.Map as Map
import           Data.Maybe
import           Control.Monad.Except
import           Control.Monad.State
import           Debug.Trace

import           Base
import           Core.Abs
import           Core.Print ( printTree )
import           TransUtil

-- | monad for type-checking
type TypeCheckM a = G TypeCheckError Cont a

-- | given a type-checking context, infer the type of an expression
checkInfer   :: Cont -> Exp -> TypeCheckM Val
-- | given a type-checking context, check that an expression has given type
checkT       :: Cont -> Exp -> Val -> TypeCheckM ()
-- | check the convertibility of two values
checkConvert :: Cont -> Val -> Val -> TypeCheckM ()
-- | given a type-checking context, check that a definition is valid
checkDef     :: Cont -> String -> Exp -> Exp -> TypeCheckM Cont
-- | given a type-checking context, check taht a declaration is valid
checkDec     :: Cont -> String -> Exp -> TypeCheckM Cont

checkInfer c U = return U
checkInfer c (Var x) = case getType c x of
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
checkInfer c (Where x a e1 e) = do
  c' <- checkDef c x a e1
  checkInfer c' e
checkInfer c e@(Abs _ _ _) = do
  checkT c e U
  return U
checkInfer _ e = throwError $ TypeInferErr e

checkT c U U = return ()
checkT c (Var x) v = case getType c x of
  Just v' -> checkConvert c v' v
  _       -> error $ "should not happen, can not get type of variable: " ++ x
checkT c (App e1 e2) v = do
  v1 <- checkInfer c e1
  case v1 of
    Clos (Abs x a b) r -> do
      checkT c e2 (eval a r)
      let v2 = eval e2 (envCont c)
          v' = eval b (consEVar r x v2)
      checkConvert c v v'
    _ -> throwError $ InvalidApp e1
checkT c (Abs x a b) U = do
  checkT c a U
  checkT (consCVar c x a) b U
checkT c (Abs x a e) (Clos (Abs x' a' e') r) = do
  checkT c a U
  let v  = eval a (envCont c)
      v' = eval a' r
  checkConvert c v v'
  checkT (consCVar c x a) e (eval e' (consEVar r x' (Var x)))
checkT c (Where x a e1 e) v = do
  c' <- checkDef c x a e1
  checkT c' e v

checkConvert _ U U = return ()
checkConvert _ (Var x) (Var x') =
  if x == x'
  then return ()
  else throwError $ NotConvertible (Var x) (Var x')
checkConvert c (App e1 e2) (App e1' e2') = do
  checkConvert c e1 e1'
  checkConvert c e2 e2'
checkConvert c (Clos (Abs x a e) r) (Clos (Abs x' a' e') r') = do
  let v  = eval a r
      v' = eval a' r'
  checkConvert c v v'
  let y  = freshVar x (varsCont c)
      vy = Var y
  checkConvert (consCVar c y v) (eval e (consEVar r x vy)) (eval e' (consEVar r' x' vy))
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


checkExpValidity :: Context -> Cont -> CExp -> Either TypeCheckError Exp
checkExpValidity cc ac ce = let m = toMap cc in
  case runG (absExp ce) m of
    Left err -> Left err
    Right e  -> case runG (checkInfer ac e) CNil of
      Left err -> Left err
      Right _  -> Right e
  where
    toMap :: Context -> Map.Map String Id
    toMap (Ctx ds) = Map.unions (map toMapD ds)
    toMapD :: CDecl -> Map.Map String Id
    toMapD (CDec id _) = Map.singleton (idStr id) id
    toMapD (CDef id _ _) = Map.singleton (idStr id) id
