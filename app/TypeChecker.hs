{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TypeChecker where
import Data.Maybe
import Data.List
import Debug.Trace
import Control.Monad.State
import Control.Monad.Except
import qualified Data.Map as Map

import Core.Abs
import Core.Print  ( printTpree )
----------------------------------------------------------
-- Data types
----------------------------------------------------------

data Exp = Var String
         | App Exp Exp
         | Abs String Exp Exp
         | Def String Exp Exp Exp
         | U
         | Clos Exp Env

type Val = Exp

convert :: CExp -> Exp
convert ce = case ce of
  CU -> U
  CVar id -> Var (idStr id)
  CApp e1 e2 -> App (convert e1) (convert e2)
  CArr e1 e2 -> Abs "" (convert e1) (convert e2)
  CPi  (CDec id e1) e2 -> Abs (idStr id) (convert e1) (convert e2)
  CWhere (CDef id e1 e2) e -> Def (idStr id) (convert e1) (convert e2) (convert e) 


-- | environment that maps variables to its values
data Env = Nil
         | ConsVar Env String Val
         | ConsDef Env String Exp Exp
         deriving (Show)

data Cont = Nil
          | ConsVar Cont String Exp
          | ConsDef Cont String Exp Exp


type ErrorStack = [(Exp, String)]

-- data TypeCheckError = DupDecl           Id
--                     | ValNotEqual       ErrorStack
--                     | VarNotbound       Id
--                     | TypeNotMatch      AbsExp Val
--                     | InvalidApp        ErrorStack
--                     | InferErr          ErrorStack
--                     | CanNotEvaluate    AbsExp
--                     | ExtendWithContext TypeCheckError String
--                     deriving (Show)

data TypeCheckError = IllegalExp         Exp
                    | DupDecl            Id Id
                    | VarNotbound        Id
                    deriving (Show)

type ErrorText = String

errorText :: TypeCheckError -> [ErrorText]
errorText err = case err of
  IllegalExp e                -> ["Illegal expression: " ++ show e]
  DupDecl    id1 id2          -> ["Duplicated declaration of variable at the same scope: already declared '" ++ idStr id1 ++ "' at " ++ show (idPos id1) ++
                                  ";find duplication at " ++ show (idPos id2)]
  VarNotbound (Id (pos, id))  -> ["Unbound variable " ++ id ++ ", at " ++ show pos]

-- errorText err = case err of
--   DupDecl (Id (pos, id))     -> ["Duplicated declaration of variable " ++ id ++ ", at " ++ show pos]
--   ValNotEqual s              -> "Unequal terms" : map (\(e, f) -> "  " ++ f ++  show e) (reverse s)
--   VarNotbound (Id (pos, id)) -> ["Unbound variable " ++ id ++ ", at " ++ show pos]
--   TypeNotMatch e t           -> ["Type unmatch, the expression does not have the value as its type", "\10070 expression: " ++ show e, "\10070 value: " ++ show t]
--   InvalidApp s               -> "Invalid application: " : map (\(e, f) -> "  " ++ f ++  show e) (reverse s)
--   InferErr s                 -> "Type can not be inferred: " : map (\(e, f) -> "  " ++ f ++ show e) (reverse s)
--   CanNotEvaluate e           -> ["Expression can not be evaluated", "\10070 " ++ show e]
--   ExtendWithContext pre tail -> (errorText pre) ++ [tail]

dummyId :: Id
dummyId = Id ((-1, -1), "")

-- | desugaring, change arrow expressions ("->") into "pi" expression ([x:A] M)
desugarCtx :: Context -> Context
desugarCtx (Ctx ds) = Ctx (map f ds)
  where f :: Decl -> Decl
        f (Dec id e)     = Dec id (g e)
        f (Def id e1 e2) = Def id (g e1) (g e2)
        g :: Exp -> Exp
        g e = case e of
          App e1 e2 -> App (g e1) (g e2)
          Arr e1 e2 -> Pi (Dec dummyId (g e1)) (g e2)
          Pi  d  e  -> let e' = g e
                       in case d of
                            Dec id e1    -> Pi (Dec id (g e1)) e'
                            Def id e1 e2 -> Pi (Def id (g e1) (g e2)) e'
          Where e d -> let e' = g e
                       in case d of
                            Dec id e1    -> Where e' (Dec id (g e1))
                            Def id e1 e2 -> Where e' (Def id (g e1) (g e2))
          _         -> e

-- | monad used for type checking
newtype G e s a = G {mkg :: ExceptT e (State s) a}
  deriving (Monad, Applicative, Functor, MonadError e, MonadState s)

type TypeCheckM a = G TypeCheckError Cont a

type ConvertM a = G TypeCheckError [Map.Map String Id] a

runG :: G e s a -> s -> Either e a
runG g s = evalState (runExceptT (mkg g)) s

typeCont :: Cont -> [(String, Val)]
typeCont Nil = []
typeCont (ConsVar c id a)   = (id, eval a (envCont c)) : (typeCont c)
typeCont (ConsDef c id a e) = (id, eval a (envCont c)) : (typeCont c)

nameCont :: Cont -> [String]
nameCont c = map fst (typeCont c)

freshVar :: String -> [String] -> String
freshVar x xs = if x `not in` xs
                then x
                else freshVar (x ++ "'") xs

checkInferT :: Cont -> Exp -> TypeCheckM Val
checkT      :: Cont -> Exp -> Val -> TypeCheckM ()
convert1    :: [(String, Val)] -> Val -> Val -> TypeCheckM ()
checkDef    :: Cont -> String -> Exp -> Exp -> TypeCheckM ()

convert1 xs U U = return ()
convert1 xs (App e1 e2) (App e1' e2') = do
  convert1 xs e1 e1'
  convert1 xs e2 e2'
convert1 xs (Clos (Abs id1 a1 e1) r1) (Clos (Abs id2 a2 e2) r2) = do
  let v1 = eval a1 r1
  convert1 xs v1 (eval a2 r2)
  let id = freshVar id1 (map fst xs)
      v  = Var id
  convert1 ((id1, v):xs) (eval e1 (ConsVar r1 id1 v)) (eval e2 (ConsVar r2 id2 v))

  
checkInferT c U = return U
checkInferT c (Var id) = return $ lookup id (typeCont c)
checkInferT c (App e1 e2) = do
  tv1 <- checkInferT c e1
  case tv1 of
    Clos (Abs id a b) r -> do
      checkT c e2 (eval a r)
      return $ eval b (ConsVar r id (eval e2 (envCont c)))
    _ -> throwError $ TypeError
checkInferT _ _ = throwError $ TypeError


checkT c U U = return ()
checkT c (Var x) v = do
  let tc = typeCont c
  convert1 tc (lookup x tc) v
checkT c (App e1 e2) v = do
  v1 <- checkInferT c e1
  case v1 of
    Clos (Abs id a b) r -> do
      checkT c e2 (eval a r)
      convert1 (typeCont c) v (eval b (ConsVar r id (eval (envCont c) e2)))
    _ -> throwError $ TypeError
checkT c (Abs "" a b) U = do
  checkT c a U
  checkT c b U
checkT c (Abs id a b) U = do
  checkT c a U
  if List.member id (nameCont c)
    then throwError $ DupDecl
    else checkT (ConsVar c id a) b U
checkT c (Abs id a e) (Clos (Abs id1 a1 b1) r) = do
  checkT c a U
  let va = eval a (envCont c)
      va1 = eval a1 r
  convert1 (typeCont c) va va1
  if List.member id (nameCont c)
    then throwError $ DupDecl
    else checkT (ConsVar c id a) e (eval b1 (ConsVar r id1 (Var id)))
checkT c (Def id a e1 e) v = do
  c' <- checkDef c id a e1
  checkT c' e v

checkDef    :: Cont -> String -> Exp -> Exp -> TypeCheckM Cont
checkDef c id a e = do
  if List.member id (nameCont c)
    then throwError $ DupDecl
    else do
      checkT c a U
      checkT c e (eval a (envCont))
      return $ ConsDef c id a e


idStr :: Id -> String
idStr (Id (_, id)) = id

idPos :: Id -> (Int, Int)
idPos (Id (pos, _)) = pos

-- | check proper declaration and reference of variables
checkVar :: Context -> ConvertM ()
checkVar (Ctx ds) = mapM f ds
  where f :: Decl -> ConvertM ()
        f (Dec id e) = do
          c <- gets head
          case Map.lookup (idStr id) c of
            Just id' -> throwError $ DupDecl id' id
            _        -> do
              g e
              modify (extendCtx id)
        f (Def id e1 e2) = do
          c <- gets head
          case Map.lookup (idStr id) c of
            Just id' -> throwError $ DupDecl id' id
            _        -> do
              g e1
              g e2
              modify (extendCtx id)
        g :: Exp -> ConvertM ()
        g e = case e of
          U            -> return ()
          Var id       -> do
            b <- gets (findVar (idStr id))
            case b of
              True -> return ()
              _    -> throwError $ VarNotbound id
          App e1 e2    -> (g e1) >> (g e2)
          Arr e1 e2    -> error "should not happen"
          Pi  d  e     -> do
            modify pushNew -- ^ introduce new syntactic level
            case d of
              Dec id e' -> do
                g e'
                modify (extendCtx id)
              Def id e1 e2 -> do
                g e1
                g e2
                modify (extendCtx id)
            case e of
              Pi d' e' -> case d' of
                Dec id e1 -> do
                  c <- gets head
                  case Map.lookup (idStr id) c of
                    Just id' -> throwError $ DupDecl id' id
                    _        -> do
                      g e1
                      modify (extendCtx id)
                Def id e1 e2 -> do
                  c <- gets head
                  case Map.lookup (idStr id) c of
                    Just id' -> throwError $ DupDecl id' id
                    _        -> do
                      g e1
                      g e2
                      modify (extendCtx id)
              _ -> g e
          Where e d    ->  do
            undefined



eval2 

              
eval :: Exp -> Env -> Val
eval e r = case e of
  U          -> U
  Var id     -> getVal id e
  App e1 e2  -> appVal (eval e1 r) (eval e2 r)
  Pi _ _     -> Clos e r
  Def id e1 e2 e3 -> eval e3 (ConsDef r id e1 e2)
  Clos e' r   -> e

  
appVal :: Val -> Val -> Val
app v1 v2 = case v1 of
  Clos (Abs id e1 e2) r -> eval e2 (ConsVar r id v2)
  _ -> App v1 v2

getVal :: String -> Env -> Val
getVal id Nil = Var id
getVal id (ConsVar r id' v)
  | id == id' = v
  | otherwise = getVal id r
getVal id (ConsDef r id' a e)
  | id == id' = eval e r
  | otherwise = getVal id r

envCont :: Cont -> Env
envCont Nil = Nil
envCont (ConsVar c id e) = envCont c
envCont (ConsDef c id e1 e2) = ConsDef (envCont c) id e1 e2




-- -- | get the abstract syntax of a program
-- absProg :: Program -> TypeCheckM AbsProgram
-- absProg p@(Prog es) = case checkDuplicateDecl p of
--   Left error -> throwError error
--   _          -> case runG (mapM g es) [] of
--     Left error -> throwError error
--     Right as   -> return as
--   where g :: Exp -> ConvertM AbsExp
--         g e = case e of
--           EU                    -> return U
--           EVar id               -> do
--             idlist <- get
--             case (idAsString id) `elemIndex` idlist of
--               Just idx -> return $ Ref idx
--               Nothing  -> throwError $ VarNotbound id
--           EApp e1 e2            -> do
--             e1' <- g e1
--             e2' <- g e2
--             return $ App e1' e2'
--           EArr e1 e2            -> do
--             e1' <- g e1
--             modify (\s -> "" : s)
--             e2' <- g e2
--             modify (\s -> tail s)
--             return $ Lam e1' e2'
--           EPi id e1 e2 -> do
--             e1' <- g e1
--             modify (\s -> idAsString id : s)
--             e2' <- g e2
--             modify (\s -> tail s)
--             return $ Lam e1' e2'
--           EPost id e            -> do
--             e' <-  g e
--             l  <-  gets length
--             modify (\s -> idAsString id : s)
--             return $ Post e'
--           EDec id (Def e1 e2)   -> do
--             e1' <- g e1
--             e2' <- g e2
--             l   <- gets length
--             modify (\s -> idAsString id : s)
--             return $ Where (AbsDef e1' e2')

-- -- | semantics of the language, evaluation of the abstract expressions
-- eval :: AbsExp -> Env -> TypeCheckM Val
-- eval e env = case e of
--   U         -> return VU
--   Ref idx   -> return (env !! idx)
--   App e1 e2 -> app e1 e2 env
--   Lam e1 e2 -> do
--     v1 <- eval e1 env
--     return $ VLam v1 (mkClos e2 env)
--   _         -> throwError $ CanNotEvaluate e

-- -- | instantiation of a closure by a value
-- inst :: Clos -> Val -> TypeCheckM Val
-- inst (Clos e env) v = eval e (v : env)

-- -- | application of values
-- app :: AbsExp -> AbsExp -> Env -> TypeCheckM Val
-- app e1 e2 env = do
--   v1 <- eval e1 env
--   v2 <- eval e2 env
--   case v1 of
--     (VLam _ clos) -> inst clos v2
--     Var _         -> return $ VApp v1 v2
--     VApp _ _      -> return $ VApp v1 v2
--     _             -> trace (show v1 ++ "\n" ++ show v2) throwError (InvalidApp [(e1, "app: ")])
-- -- | readback function, converting a value to its normal form
-- rbV :: Int -> Val -> TypeCheckM NExp
-- rbV i v = case v of
--   VU           -> return NU
--   Var k        -> return $ NInt k
--   VApp v1 v2   -> do
--     n1 <- rbV i v1
--     n2 <- rbV i v2
--     return $ NApp n1 n2
--   VLam v  clos -> do
--     n1 <- rbV i v
--     v' <- inst clos (Var i)
--     n2 <- rbV (i + 1) v'
--     return $ NLam i n1 n2

-- updateContext :: Val -> Val -> TypeCheckM ()
-- updateContext v1 v2 = do
--   (env, gamma) <- get
--   put (v1 : env, v2 : gamma)

-- -- | check the equality of two values by first reducing them to the normal form
-- eqNe :: Int -> Val -> Val -> TypeCheckM ()
-- eqNe i v1 v2 = do
--   n1 <- rbV i v1
--   n2 <- rbV i v2
--   if n1 == n2
--     then return ()
--     else throwError $ ValNotEqual []

-- handleErrStack :: AbsExp -> String -> TypeCheckError -> TypeCheckM a
-- handleErrStack e fs err = case err of
--   InvalidApp  s -> throwError $ InvalidApp  ((e, fs) : s)
--   InferErr    s -> throwError $ InferErr    ((e, fs) : s)
--   ValNotEqual s -> throwError $ ValNotEqual ((e, fs) : s)

-- checkT :: AbsExp ->        TypeCheckM ()   -- ^ check an expression is a type
-- check  :: AbsExp -> Val -> TypeCheckM ()   -- ^ check an expression has a value as its type
-- checkI :: AbsExp ->        TypeCheckM Val  -- ^ infer the type of an expression
-- checkD :: AbsDef ->        TypeCheckM ()   -- ^ check an definition is valid

-- checkT e = do {
--   case e of
--     U -> return ()
--     Lam e1 e2 -> do
--       checkT e1
--       init_ctx@(env, gamma) <- get
--       let v1 = Var (length env)
--       v2 <- eval e1 env
--       updateContext v1 v2
--       checkT e2
--       put init_ctx
--     Post e -> do
--       checkT e
--       env <- gets fst
--       t   <- eval e env
--       updateContext (Var (length env)) t
--     _ -> check e VU } `catchError` handleErrStack e "checkT: "

-- check e t = do {
--   case (e, t) of
--     (Lam e1 e2, VLam t g) -> do
--       init_ctx@(env, gamma) <- get
--       let s = length env
--       t' <- eval e1 env
--       eqNe s t' t
--       updateContext (Var s) t
--       tt <- inst g (Var s)
--       check e2 tt
--       put init_ctx
--     (Lam e1 e2, VU) -> do
--       check e1 VU
--       init_ctx@(env, gamma) <- get
--       let v1 = Var (length env)
--       v2 <- eval e1 env
--       updateContext v1 v2
--       check e2 VU
--       put init_ctx
--     (Lam _ _, _) -> throwError (TypeNotMatch e t)
--     _ -> do
--       t'  <- checkI e
--       env <- gets fst
--       eqNe (length env) t t' } `catchError` handleErrStack e "check: "

-- checkI e = do {
--   case e of
--     U -> return VU
--     Ref idx -> do
--       gamma <- gets snd
--       return (gamma !! idx)
--     App e1 e2 -> do
--       v1 <- checkI e1
--       case v1 of
--         VLam t g -> do
--           check e2 t
--           env <- gets fst
--           v2 <- eval e2 env
--           inst g v2
--         _ -> throwError (InvalidApp [(e1, "checkI: ")])  
--     _ -> throwError (InferErr []) } `catchError` handleErrStack e "checkI: "

-- checkD d@(AbsDef e1 e2) = do { do
--   checkT e1
--   env <- gets fst
--   t <- eval e1 env
--   check e2 t
--   v <- eval e2 env
--   updateContext v t } `catchError` handleErrStack (Where d) "checkD: "

-- -- | type check a program
-- runTypeCheck :: Program -> Either TypeCheckError ()
-- runTypeCheck p@(Prog es) = runG pCheck ([], [])
--   where pCheck :: TypeCheckM ()
--         pCheck = do
--           p' <- absProg p
--           mapM_ f (zip p' [0..])
--         f :: (AbsExp, Int) -> TypeCheckM ()
--         f (e, n) = do
--           case e of
--             U                 -> return ()
--             Ref _             -> (checkI e >> return ()) `catchError` (h n)
--             App _ _           -> (checkI e >> return ()) `catchError` (h n)
--             Lam _ _           -> (checkT e)              `catchError` (h n)
--             Post _            -> (checkT e)              `catchError` (h n)
--             Where dec         -> (checkD dec)            `catchError` (h n)
--         h :: Int -> TypeCheckError -> TypeCheckM ()
--         h n error = let e_origin    = es !! n
--                         msg_context = "When checking source \9944 " ++ printTree e_origin
--                     in  throwError $ ExtendWithContext error msg_context

