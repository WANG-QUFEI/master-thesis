{-|
Module          : Commands
Description     : a module that provides command line functions
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Commands
  ( Cmd(..)
  , ShowItem(..)
  , CheckItem(..)
  , LockOption(..)
  , getCommand
  , hReduct
  -- , unfold
  -- , typeOf
  -- , minimumConsts
  -- , checkConstant
   ) where

import           Classes
import qualified Core.Abs as Abs
import qualified Core.Par as Par
import           Lang
import qualified Locking as L
import           Message
import           Monads
import           TypeChecker

import           Control.Monad
import           Control.Monad.Except
import           Data.List.Split
import           Data.Maybe
import           Debug.Trace

-- |Data type for the commands
data Cmd = Help
         | Quit
         | Load FilePath
         | Show ShowItem
         | Lock LockOption
         | Bind String Abs.Exp
         | Check CheckItem
         | Unfold (Either String Abs.Exp)
         | TypeOf (Either String Abs.Exp)
         | HeadReduct
         | FindMinimumConsts String
         deriving (Show)

data ShowItem = SFilePath         -- show file path
              | SFileContent      -- show file content
              | SConsants         -- show all constants from the currently loaded file
              | SLocked           -- show locked constants
              | SUnlocked         -- show unlocked constants
              | SContext          -- show the type-checking context
              | SName String      -- show the expression bound to a name
              deriving (Show)

data CheckItem = CExp  Abs.Exp    -- check an expression
               | CDecl Abs.Decl   -- check a declaration/definition
               | Const String     -- check a constant
               deriving (Show)

data LockOption = LockAll
                | LockNone
                | LockAdd [String]
                | LockRemove [String]
                deriving (Show)

-- | Parse a string into a command, return an error message if no command
--   could be found
getCommand :: String -> Either String Cmd
getCommand str =
  let ws  = words str
      tws = tail ws
  in case head ws of
    ":?"      -> return Help
    ":help"   -> return Help
    ":q"      -> return Quit
    ":load"   -> parseLoad tws
    ":show"   -> parseShow tws
    ":lock"   -> parseLock tws
    ":bind"   -> parseBind tws
    ":check"  -> parseCheck tws
    ":unfold" -> parseUnfold tws
    ":typeOf" -> parseTypeof tws
    ":hred"   -> return HeadReduct
    ":fmc"    -> parseMiniConsts tws
    _         -> Left "invalid command, type ':?' for a detailed description of the command"
  where
    parseLoad :: [String] -> Either String Cmd
    parseLoad tws = case tws of
      [fp] -> return $ Load fp
      _ -> Left "invalid command, type ':?' for a detailed description of the command"

    parseShow :: [String] -> Either String Cmd
    parseShow tws = case tws of
      ["filePath"]       -> return (Show SFilePath)
      ["fp"]             -> return (Show SFilePath)
      ["fileContent"]    -> return (Show SFileContent)
      ["fc"]             -> return (Show SFileContent)
      ["const_all"]      -> return (Show SConsants)
      ["ca"]             -> return (Show SConsants)
      ["const_locked"]   -> return (Show SLocked)
      ["cl"]             -> return (Show SLocked)
      ["const_unlocked"] -> return (Show SUnlocked)
      ["cu"]             -> return (Show SUnlocked)
      ["context"]        -> return (Show SContext)
      ["ctx"]            -> return (Show SContext)
      ["-name", n]       -> return (Show (SName n))
      _                  -> Left "invalid command, type ':?' for a detailed description of the command"

    parseLock :: [String] -> Either String Cmd
    parseLock tws = case tws of
      ["-all"]             -> return $ Lock LockAll
      ["-none"]            -> return $ Lock LockNone
      ["-add", varlist]    -> do
        ss <- parseList varlist
        return $ Lock (LockAdd ss)
      ["-remove", varlist] -> do
        ss <- parseList varlist
        return $ Lock (LockRemove ss)
      _ -> Left "invalid command, type ':?' for a detailed description of the command"

    parseBind :: [String] -> Either String Cmd
    parseBind tws = case tws of
      v : "=" : ws' -> do
        e <- parseExpr (unwords ws')
        return $ Bind v e
      _ -> Left "invalid command, type ':?' for a detailed description of the command"

    parseCheck :: [String] -> Either String Cmd
    parseCheck tws = case tws of
      "-expr" : ws'  -> do
        e <- parseExpr (unwords ws')
        return $ Check (CExp e)
      "-decl" : ws'  -> do
        d <- parseDecl (unwords ws')
        return $ Check (CDecl d)
      ["-const", var] -> return $ Check (Const var)
      _ ->  Left "invalid command, type ':?' for a detailed description of the command"

    parseUnfold :: [String] -> Either String Cmd
    parseUnfold tws = case tws of
      ["-name", v] -> return $ Unfold (Left v)
      "-expr" : ws' -> do
        e <- parseExpr (unwords ws')
        return $ Unfold (Right e)
      _ ->  Left "invalid command, type ':?' for a detailed description of the command"

    parseTypeof :: [String] -> Either String Cmd
    parseTypeof tws = case tws of
      ["-name", v] -> return $ TypeOf (Left v)
      "-expr" : ws' -> do
        e <- parseExpr (unwords ws')
        return $ TypeOf (Right e)
      _ ->  Left "invalid command, type ':?' for a detailed description of the command"

    parseList :: String -> Either String [String]
    parseList s =
      if head s == '[' && last s == ']'
      then let s' = init . tail $ s
           in Right (endBy "," s')
      else Left "invalid command, type ':?' for a detailed description of the command"

    parseExpr :: String -> Either String Abs.Exp
    parseExpr "" = Left "invalid command, type ':?' for a detailed description of the command"
    parseExpr s  = Par.pExp (Par.myLexer s)

    parseDecl :: String -> Either String Abs.Decl
    parseDecl "" = Left "invalid command, type ':?' for a detailed description of the command"
    parseDecl s  = Par.pDecl (Par.myLexer s)

    parseMiniConsts :: [String] -> Either String Cmd
    parseMiniConsts [var] = return $ FindMinimumConsts var
    parseMiniConsts _     = Left "invalid command, type ':?' for a detailed description of the command"

-- |Apply head reduction on an expression
hReduct :: Cont -> Exp -> Exp
hReduct _ U = U
hReduct c (Abs x a b) =
  let ns = cns c
      qa = eval (emptyEnv ns) a
      c' = bindConT c x qa
      b' = hReduct c' b
      a' = hReduct c a
  in Abs x a' b'
hReduct c (Let x a b e) =
  let c' = bindConD c x a b
      e' = hReduct c' e
  in Let x a b e'
hReduct c e = readBack (namesCont c) (incrEval c e)

-- |Evaluate an expression in 'one small step'
incrEval :: Cont -> Exp -> QExp
incrEval c (Var x) =
  let ns = cns c
      dx = getDef c x
  in eval (emptyEnv ns) dx
incrEval c (App e1 e2) =
  let q1 = incrEval c e1
      ns = cns c
      q2 = eval (emptyEnv ns) e2
  in appVal q1 q2
incrEval _ _ = error "error: incrEval"

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



-- typeOf :: Cont -> Exp -> Exp
-- typeOf c (Abs d@(Def x a b) e) =
--   let c' = CConsDef c x a b
--       e' = typeOf c' e
--   in Abs d e'
-- typeOf c e = readBack (varsCont c) (typeOfV c e)

-- typeOfV :: Cont -> Exp -> Val
-- typeOfV c (Var x)     =
--   let Just a = getType c x
--   in eval a (getEnv L.LockNone c)
-- typeOfV _ U           = U
-- typeOfV c (App e1 e2) = appVal (typeOfV c e1) (eval e2 ENil)
-- typeOfV _ e           = error ("not typeable expression: " ++ show e)

-- unfold :: LockStrategy s => s -> Cont -> Exp -> Exp
-- unfold s c e =
--   let ve = eval e (getEnv s c)
--   in readBack (varsCont c) ve

-- checkConstant :: LockStrategy l => l -> Cont -> String -> Either String ()
-- checkConstant ls c s =
--   case locate c s of
--     Nothing -> Left . errorMsg $ "No constant with name '" ++ s ++ "' exists in the current context"
--     Just (_, d) ->
--       case runG (checkDecl ls c d) CNil of
--         Left err ->
--           let errmsg = explain err
--           in Left (unlines (map errorMsg errmsg))
--         Right _ -> return ()

-- minimumConsts :: Cont -> String -> Either String [String]
-- minimumConsts c s =
--   case locate c s of
--     Nothing -> Left . errorMsg $ "No constant with name '" ++ s ++ "' exists in the current context"
--     Just (c', d) ->
--       case runG (trialAndUnfold [] L.LockAll c' d) CNil of
--         Left err ->
--           let errmsg = explain err
--           in Left (unlines (map errorMsg errmsg))
--         Right ss -> Right ss

-- locate :: Cont -> String -> Maybe (Cont, Decl)
-- locate c s = case c of
--   CNil -> Nothing
--   CConsVar c' x a ->
--     if x == s
--     then Just (c', Dec s a)
--     else locate c' s
--   CConsDef c' x a e ->
--     if x == s
--     then Just (c', Def x a e)
--     else locate c' s

-- trialAndUnfold :: LockStrategy s => [String] -> s -> Cont -> Decl -> TypeCheckM [String]
-- trialAndUnfold ss ls c d = do
--   void $ checkDecl ls c d
--   return $ getConstsUnLocked ls c
--   `catchError` h
--   where
--     h :: TypeCheckError -> TypeCheckM [String]
--     h err = case err of
--               TypeNotMatch _ v     -> tryNextConst err (v, U)
--               CannotInferType e    -> tryNextConst err (e, U)
--               NotFunctionClos v    -> tryNextConst err (v, U)
--               NotConvertible v1 v2 -> tryNextConst err (v1, v2)
--               _ -> throwError $ ExtendedWithCtx err ["Unexpected exception in trialAndUnfold"]

--     tryNextConst :: TypeCheckError -> (Exp, Exp) -> TypeCheckM [String]
--     tryNextConst err (e1, e2) =
--       let mx1 = constExp e1
--           mx2 = constExp e2
--           xs  = catMaybes [mx1, mx2]
--           xs' = filter (`notElem` ss) xs
--       in case xs' of
--            [] -> throwError $ ExtendedWithCtx err ["No further unfoldable constants could be found"]
--            x:_ -> let ls' = removeLock ls [x]
--                       ss' = x : ss
--                   in trialAndUnfold ss' ls' c d

--     constExp :: Exp -> Maybe String
--     constExp (Var x) = Just x
--     constExp (App e1 e2) =
--       case constExp e1 of
--         Just x  -> Just x
--         Nothing -> constExp e2
--     constExp _ = Nothing
