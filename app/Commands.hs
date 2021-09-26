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
  , headRed
  , unfold
  , typeOf
  , checkConstant
   ) where

import           Core.Abs
import           Core.Par
import           Lang
import           TypeChecker
import           Util

import           Data.List.Split

-- | data type for the commands
data Cmd = Help
         | Quit
         | Load FilePath
         | Show ShowItem
         | Lock LockOption
         | Bind String CExp
         | Check CheckItem
         | Unfold (Either String CExp)
         | TypeOf (Either String CExp)
         | HeadReduct
         | SetConvert ConvertCheck
         deriving (Show)

data ShowItem = SFilePath         -- show file path
              | SFileContent      -- show file content
              | SConsants         -- show all constants from the currently loaded file
              | SLocked           -- show locked constants
              | SUnlocked         -- show unlocked constants
              | SContext          -- show the type-checking context
              | SName String      -- show the expression bound to a name
              deriving (Show)

data CheckItem = CExp CExp        -- check an expression
               | CDecl CDecl      -- check a declaration/definition
               | Const String     -- check a constant
               deriving (Show)

data LockOption = OptLockAll
                | OptLockNone
                | OptLockAdd [String]
                | OptLockRemove [String]
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
    ":set"    -> parseSet tws
    ":lock"   -> parseLock tws
    ":bind"   -> parseBind tws
    ":check"  -> parseCheck tws
    ":unfold" -> parseUnfold tws
    ":typeOf" -> parseTypeof tws
    ":hred"   -> return HeadReduct
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

    parseSet :: [String] -> Either String Cmd
    parseSet tws = case tws of
      ["convert", "beta"] -> return (SetConvert Beta)
      ["convert", "eta"]  -> return (SetConvert Eta)
      _                   -> Left "invalid command, type ':?' for a detailed description of the command"

    parseLock :: [String] -> Either String Cmd
    parseLock tws = case tws of
      ["-all"]             -> return $ Lock OptLockAll
      ["-none"]            -> return $ Lock OptLockNone
      ["-add", varlist]    -> do
        ss <- parseList varlist
        return $ Lock (OptLockAdd ss)
      ["-remove", varlist] -> do
        ss <- parseList varlist
        return $ Lock (OptLockRemove ss)
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

    parseExpr :: String -> Either String CExp
    parseExpr "" = Left "invalid command, type ':?' for a detailed description of the command"
    parseExpr s  = pCExp (myLexer s)

    parseDecl :: String -> Either String CDecl
    parseDecl "" = Left "invalid command, type ':?' for a detailed description of the command"
    parseDecl s  = pCDecl (myLexer s)

headRed :: Cont -> Exp -> Exp
headRed c (Abs x a e) =
  let c' = CConsVar c x a
      e' = headRed c' e
  in Abs x a e'
headRed c (Let x a b e) =
  let e' = headRed (CConsDef c x a b) e
  in Let x a b e'
headRed c e = readBack (namesCtx c) (headRedV c e)

headRedV :: Cont -> Exp -> QExp
headRedV c (Var x)     = eval (defVar x c) ENil
headRedV c (App e1 e2) = appVal (headRedV c e1) (eval e2 ENil)
headRedV _ e           = eval e ENil

defVar :: String -> Cont -> Exp
defVar x CNil = Var x
defVar x (CConsVar c x' _)
  | x == x'   = Var x
  | otherwise = defVar x c
defVar x (CConsDef c x' _ e)
  | x == x'   = e
  | otherwise = defVar x c

typeOf :: Cont -> Exp -> Exp
typeOf c (Let x a b e) =
  let c' = CConsDef c x a b
      e' = typeOf c' e
  in Let x a b e'
typeOf c (Abs x a e) =
  let c' = consCVar c x a
      e' = typeOf c' e
  in Abs x a e'
typeOf c e = readBack (namesCtx c) (typeOfV c e)

typeOfV :: Cont -> Exp -> QExp
typeOfV c (Var x) =
  let (c', a) = getType c x
  in eval a (getEnv Util.LockNone c')
typeOfV _ U           = U
typeOfV c (App e1 e2) = appVal (typeOfV c e1) (eval e2 ENil)
typeOfV _ e           = error ("typeOfV: " ++ show e)

unfold :: LockStrategy s => s -> Cont -> Exp -> Exp
unfold s c e =
  let ve = eval e (getEnv s c)
  in readBack (namesCtx c) ve

checkConstant :: LockStrategy s => s -> ConvertCheck -> Cont -> String -> Either String ()
checkConstant ls cc c s =
  case locate c s of
    Nothing -> Left . errorMsg $ "No constant with name '" ++ s ++ "' exists in the current context"
    Just (_, d) ->
      case runG (checkD ls c d) (CNil, cc) of
        Left err ->
          let errmsg = explain err
          in Left (unlines (map errorMsg errmsg))
        Right _ -> return ()

locate :: Cont -> String -> Maybe (Cont, Decl)
locate c s = case c of
  CNil -> Nothing
  CConsVar c' x a ->
    if x == s
    then Just (c', Dec s a)
    else locate c' s
  CConsDef c' x a e ->
    if x == s
    then Just (c', Def x a e)
    else locate c' s

