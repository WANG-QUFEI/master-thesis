{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module TypeChecker where
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

-- | abstract syntax for expressions
data AbsExp = U
            | Var String
            | App AbsExp AbsExp
            | Pi  AbsDecl AbsExp
            | Where AbsExp AbsDecl
            deriving (Eq, Show)

-- | abstract syntax for declarations
data AbsDecl = AbsDec String AbsExp
             | AbsDef String AbsExp AbsExp
             deriving (Eq, Show)

-- | abstract syntax for a context
type AbsContext = [AbsDecl]

-- | environment that maps variables to its values
data Rho = Nil
         | ConsVar Rho (String, Value)
         | ConsDef Rho AbsDecl
         deriving (Show)

-- | value of the expression
data Value = VU
           | VVar String
           | VApp Value Value
           | VClos AbsExp Rho
           deriving (Show)
                     
type ErrorStack = [(AbsExp, String)]

-- data TypeCheckError = DupDecl           Id
--                     | ValNotEqual       ErrorStack
--                     | VarNotbound       Id
--                     | TypeNotMatch      AbsExp Val
--                     | InvalidApp        ErrorStack
--                     | InferErr          ErrorStack
--                     | CanNotEvaluate    AbsExp
--                     | ExtendWithContext TypeCheckError String
--                     deriving (Show)

data TypeCheckError = IllegalExp         AbsExp
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

-- | desugaring, change "->" arrow expression into "Pi" expression
desugarCtx :: Context -> Context
desugarCtx (Ctx []) = Ctx []
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

type TypeCheckM a = G TypeCheckError (Rho, Gamma) a

type ConvertM a = G TypeCheckError [Map.Map String Id] a

runG :: G e s a -> s -> Either e a
runG g s = evalState (runExceptT (mkg g)) s

idStr :: Id -> String
idStr (Id (_, id)) = id

idPos :: Id -> (Int, Int)
idPos (Id (pos, _)) = pos

-- | check proper declaration and reference of variables
convertCtx :: Context -> ConvertM AbsContext
convertCtx (Ctx ds) = mapM f ds
  where f :: Decl -> ConvertM AbsDecl
        f (Dec id e) = do
          c <- gets head
          case Map.lookup (idStr id) c of
            Just id' -> throwError $ DupDecl id' id
            _        -> do
              e' <- g e
              modify (extendCtx id)
              return $ AbsDec (idStr id) e'
        f (Def id e1 e2) = do
          c <- gets head
          case Map.lookup (idStr id) c of
            Just id' -> throwError $ DupDecl id' id
            _        -> do
              e1' <- g e1
              e2' <- g e2
              modify (extendCtx id)
              return $ AbsDef (idStr id) e1' e2'
        g :: Exp -> ConvertM AbsExp
        g e = case e of
          U            -> return U
          Var id       -> do
            b <- gets (findVar (idStr id))
            case b of
              True -> return $ Var (idStr id)
              _    -> throwError $ VarNotbound id
          App e1 e2    -> do
            e1' <- g e1
            e2' <- g e2
            return $ App e1' e2'
          Arr e1 e2    -> undefined -- ^ TODO: continue

eval :: AbsExp -> Rho -> TypeCheckM Value
eval e r = case e of
  U          -> return VU
  Var id     -> return $ getVal id r
  App e1 e2  -> app (eval e1 r) (eval e2 r)
  Pi _ _     -> return $ VClos e r
  Where e1 d -> eval e1 (ConsDef r d)

app :: Value -> Value -> TypeCheckM Value
app v1 v2 = case v1 of
  VClos e r ->
    case e of
      Pi d e1 ->
        case d of
          AbsDec id _ ->
            eval e1 (ConsVar r (id, v2))
          _ ->
            throwError $ IllegalExp e
      _ ->
        error "should not happen"
  _ -> return $ VApp v1 v2

getVal :: String -> Rho -> TypeCheckM Value
getVal id Nil = VVar id
getVal id (ConsVar r (id', v))
  | id == id' = return v
  | otherwise = getVal id r
getVal id (ConsDef r d) = case d of
  AbsDec _ _ -> getVal id r
  AbsDef id' _ e2 -> do
    v <- eval e2 r
    getVal id (ConsVar r (id', v))            


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

