{-|
Module          : Commands
Description     : a module that provides command line functions
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
module Commands
  ( Cmd(..)
  , getCommand
  , parseAndTypeCheck
  -- , checkExpValidity
  -- , headRed
  -- , unfold
  -- , fullEval
  -- , typeOf
  -- , typeCheckErrMsg
  -- , okayMsg
  -- , errorMsg
  -- , infoMsg
  ) where

import           Classes
import           Core.Abs
import           Core.Par
import           Lang
import           Locking
import           Message
import           TypeChecker

import           Data.List.Split


-- | data type for the commands
data Cmd = Help
         | Quit
         | Load LockStyle FilePath
         | Show ShowItem
         | Check CheckItem
         | HeadReduct
         deriving (Show)

data ShowItem = SFilePath         -- show file path
              | SFileContent      -- show file content
              | SConsants         -- show all constants from the currently loaded file
              | SLocked           -- show locked constants
              | SUnlocked         -- show unlocked constants from the currently loaded file
              | SExp              -- show the latest type-checked expression
              | SAbsContext       -- show the abstract context (type-checking context)
              deriving (Show)

data CheckItem = CExp CExp        -- check an expression
               | CDecl CDecl      -- check a declaration/definition
               deriving (Show)

-- | Parse a string into a command, return an error message if no command
--   could be found
getCommand :: String -> Either String Cmd
getCommand str =
  let ws = words str
  in case head ws of
    ":?"     -> return Help
    ":q"     -> return Quit
    ":load"  -> parseLoad (tail ws)
    ":show"  -> parseShow (tail ws)
    ":check" -> parseCheck (tail ws)
    ":hred"  -> return HeadReduct
    _        -> Left "invalid command, type ':?' for a detailed description of the command"
  where
    parseLoad :: [String] -> Either String Cmd
    parseLoad tws = case tws of
      ["-lock", consts, fp] -> do
        ss <- parseConsts consts
        return $ Load (ExplicitLock True ss) fp
      ["-unlock", consts, fp] -> do
        ss <- parseConsts consts
        return $ Load (ExplicitLock False ss) fp
      ["-no_lock", fp]  -> return $ Load NoLock fp
      ["-all_lock", fp] -> return $ Load AllLock fp
      _ -> Left "invalid command, type ':?' for a detailed description of the command"

    parseShow :: [String] -> Either String Cmd
    parseShow tws = case tws of
      ["filePath"]       -> return (Show SFilePath)
      ["fileContent"]    -> return (Show SFileContent)
      ["const_all"]      -> return (Show SConsants)
      ["const_locked"]   -> return (Show SLocked)
      ["const_unlocked"] -> return (Show SUnlocked)
      ["expr"]           -> return (Show SExp)
      ["absCtx"]         -> return (Show SAbsContext)
      _                  -> Left "invalid command, type ':?' for a detailed description of the command"

    parseCheck :: [String] -> Either String Cmd
    parseCheck tws = case tws of
      "-expr" : ws'  -> do
        e <- parseExpr (unwords ws')
        return $ Check (CExp e)
      "-decl" : ws'  -> do
        d <- parseDecl (unwords ws')
        return $ Check (CDecl d)
      _              ->  Left "invalid command, type ':?' for a detailed description of the command"

    parseConsts :: String -> Either String [String]
    parseConsts s =
      if head s == '[' && last s == ']'
      then let s' = init . tail $ s
           in Right (endBy "," s')
      else Left "invalid command, type ':?' for a detailed description of the command"

    parseExpr :: String -> Either String CExp
    parseExpr "" = Left "invalid command, type ':?' for a detailed description of the command"
    parseExpr s  = pCExp (myLexer s)

    parseDecl :: String -> Either String CDecl
    parseDecl "" = Left "invalid command, type ':?' for a detailed description of the command"
    parseDecl s  = pCDecl (myLexer s)

-- | parse and type check the content of a file
parseAndTypeCheck :: EnvStrategy s => s -> String -> Either String (Context, Cont)
parseAndTypeCheck s text = case pContext (myLexer text) of
  Left parseError   -> Left (unlines (map errorMsg ["failed to parse the file", parseError]))
  Right concreteCtx ->
    case runTypeCheckCtx s concreteCtx of
      Left ss           -> Left (unlines (map errorMsg ss))
      Right abstractCtx -> Right (concreteCtx, abstractCtx)


-- getCommand :: String -> Either String Cmd
-- getCommand s =
--   if isEmptyString s
--     then Right None
--     else
--       let ws = words s
--        in case head ws of
--             ":?"      -> Right Help
--             ":q"      -> Right Quit
--             ":sf"     -> Right ShowFile
--             ":lf"     -> getLoad ws
--             ":ce"     -> getCheckExp ws
--             ":cd"     -> getCheckDecl ws
--             ":hred"   -> Right HeadReduct
--             ":eval"   -> Right FullEvalExp
--             ":unfold" -> Right (Unfold (tail ws))
--             ":type"   -> getExpType ws
--             _         -> Left $ errorMsg "Invalid command"
--   where
--     isEmptyString :: String -> Bool
--     isEmptyString s = all isSpace s

--     getLoad :: [String] -> Either String Cmd
--     getLoad ws = case tail ws of
--       []     -> Left $ errorMsg "Lack of file path"
--       fp : _ -> Right (LoadFile fp)

--     getCheckExp :: [String] -> Either String Cmd
--     getCheckExp ws = case tail ws of
--       []  -> Left $ errorMsg "Lack of expression"
--       ws' -> case pCExp (myLexer (unwords ws')) of
--         Left _   -> Left $ errorMsg "Syntax error: bad expression"
--         Right ce -> Right (CheckE ce)

--     getCheckDecl :: [String] -> Either String Cmd
--     getCheckDecl ws = case tail ws of
--       [] -> Left $ errorMsg "Lack of declaration/definition"
--       ws' -> case pCDecl (myLexer (unwords ws')) of
--         Left _   -> Left $ errorMsg "Syntax error: bad declaration/definition"
--         Right cd -> Right (CheckD cd)

--     getExpType :: [String] -> Either String Cmd
--     getExpType ws = case tail ws of
--       [] -> Left $ errorMsg "Lack of expression"
--       ws' -> case pCExp (myLexer (unwords ws')) of
--         Left _   -> Left (errorMsg "Syntax error: bad expression")
--         Right ce -> Right (GetType ce)


-- -- | evaluate an expression with all variables available
-- fullEval :: Cont -> Exp -> Val
-- fullEval c e = eval e (getEnv NoLocking c)

-- -- | given a type checking context, head evaluation on an expression
-- headRed :: Cont -> Exp -> Exp
-- headRed c (Abs d e) =
--   case d of
--     Dec x a ->
--       let va = eval a (getEnv NoLocking c)
--           a' = headRed c a
--           e' = headRed (consCVar c x va) e
--       in Abs (Dec x a') e'
--     Def x a b ->
--       let e' = headRed (CConsDef c x a b) e
--       in Abs d e'
-- headRed c e = readBack (varsCont c) (headRedV c e)

-- -- | turn a value into an expression, remove the closure of a value
-- readBack :: [String] -> Val -> Exp
-- readBack _ U = U
-- readBack _ (Var x) = Var x
-- readBack ns (App v1 v2) = App (readBack ns v1) (readBack ns v2)
-- readBack ns (Clos (Abs (Dec "" a) e) r) = Abs (Dec "" (readBack ns (eval a r))) (readBack ns (eval e r))
-- readBack ns (Clos (Abs (Dec x a) e) r) =
--   let z  = freshVar x ns
--       a' = readBack ns (eval a r)
--       e' = readBack (z : ns) (eval e (consEVar r x (Var z)))
--   in Abs (Dec z a') e'
-- readBack _ _ = error "operation not supported"

-- headRedV :: Cont -> Exp -> Val
-- headRedV c (Var x)     = eval (defCont x c) ENil
-- headRedV c (App e1 e2) = appVal (headRedV c e1) (eval e2 ENil)
-- headRedV c e           = eval e ENil

-- -- | given a type checking context, get the definition of a variable
-- defCont :: String -> Cont -> Exp
-- defCont x CNil = Var x
-- defCont x (CConsVar c x' _)
--   | x == x'   = Var x
--   | otherwise = defCont x c
-- defCont x (CConsDef c x' a e)
--   | x == x'   = e
--   | otherwise = defCont x c

-- -- | given a type checking context, evaluate an expression with a list of constants unlocked
-- unfold :: Cont -> [String] -> Exp -> Exp
-- unfold c ss e =
--   let envStra = AnnotatedLocking False ss
--   in readBack (varsCont c) (eval e $ getEnv envStra c)

-- typeOf :: Cont -> Exp -> Exp
-- typeOf c (Abs d e) =
--   case d of
--     Dec x a ->
--       let a' = typeOf c a
--           v  = eval a (getEnv NoLocking c)
--           c' = consCVar c x v
--           e' = typeOf c' e
--       in Abs (Dec x a') e'
--     Def x a b ->
--       let e' = typeOf (CConsDef c x a b) e
--       in Abs d e'
-- typeOf c e = readBack (varsCont c) (typeOfV c e)

-- typeOfV :: Cont -> Exp -> Val
-- typeOfV c (Var x)     = let Just v = getType c x in v
-- typeOfV c U           = U
-- typeOfV c (App e1 e2) = appVal (typeOfV c e1) (eval e2 ENil)
-- typeOfV _ e           = error ("typeOf " ++ show e)
