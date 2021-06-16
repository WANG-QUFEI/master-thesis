{-|
Module          : Commands
Description     : a module that provides command line functions
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
module Commands
  ( Cmd(..)
  , ShowItem(..)
  , CheckItem(..)
  , getCommand
  , headRed
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

import           Data.List.Split

-- | data type for the commands
data Cmd = Help
         | Quit
         | Load LockStyle FilePath
         | Show ShowItem
         | Check CheckItem
         | ChangeLock LockStyle
         | AddToLock [String]
         | RemoveFromLock [String]
         | HeadReduct
         | UnfoldExpr
         deriving (Show)

data ShowItem = SFilePath         -- show file path
              | SFileContent      -- show file content
              | SConsants         -- show all constants from the currently loaded file
              | SLocked           -- show locked constants
              | SUnlocked         -- show unlocked constants from the currently loaded file
              | SExp              -- show the latest type-checked expression
              | SContext       -- show the abstract context (type-checking context)
              deriving (Show)

data CheckItem = CExp CExp        -- check an expression
               | CDecl CDecl      -- check a declaration/definition
               deriving (Show)

-- | Parse a string into a command, return an error message if no command
--   could be found
getCommand :: String -> Either String Cmd
getCommand str =
  let ws  = words str
      tws = tail ws
  in case head ws of
    ":?"      -> return Help
    ":q"      -> return Quit
    ":load"   -> parseLoad tws
    ":show"   -> parseShow tws
    ":check"  -> parseCheck tws
    ":change" -> parseChangeLock tws
    ":add"    -> parseAddRemove True tws
    ":remove" -> parseAddRemove False tws
    ":hred"   -> return HeadReduct
    ":unfold" -> return UnfoldExpr
    _         -> Left "invalid command, type ':?' for a detailed description of the command"
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
      ["context"]        -> return (Show SContext)
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

    parseChangeLock :: [String] -> Either String Cmd
    parseChangeLock tws = case tws of
      ["-lock", consts] -> do
        ss <- parseConsts consts
        return $ ChangeLock (ExplicitLock True ss)
      ["-unlock", consts] -> do
        ss <- parseConsts consts
        return $ ChangeLock (ExplicitLock False ss)
      ["-no_lock"] -> return $ ChangeLock NoLock
      ["-all_lock"] -> return $ ChangeLock AllLock
      _ -> Left "invalid command, type ':?' for a detailed description of the command"

    parseAddRemove :: Bool -> [String] -> Either String Cmd
    parseAddRemove b tws = case tws of
      [consts] -> do
        ss <- parseConsts consts
        if b
          then return $ AddToLock ss
          else return $ RemoveFromLock ss
      _ -> Left "invalid command, type ':?' for a detailed description of the command"

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

readBack :: [String] -> Val -> Exp
readBack _ U = U
readBack _ (Var x) = Var x
readBack ns (App v1 v2) = App (readBack ns v1) (readBack ns v2)
readBack ns (Clos (Abs (Dec "" a) e) r) =
  let a' = readBack ns (eval a r)
      e' = readBack ns (eval e r)
  in Abs (Dec "" a') e'
readBack ns (Clos (Abs (Dec x a) e) r) =
  let z  = freshVar x ns
      a' = readBack ns (eval a r)
      e' = readBack (z : ns) (eval e (consEVar r x (Var z)))
  in Abs (Dec z a') e'
readBack _ v = error ("cannot readback value: " ++ show v)

headRed :: Cont -> Exp -> Exp
headRed c (Abs (Dec x a) e) =
  let va = eval a ENil
      a' = headRed c a
      e' = headRed (consCVar c x va) e
  in Abs (Dec x a') e'
headRed c (Abs d@(Def x a b) e) =
  let e' = headRed (CConsDef c x a b) e
  in Abs d e'
headRed c e = readBack (varsCont c) (headRedV c e)

headRedV :: Cont -> Exp -> Val
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
typeOf c (Abs (Dec x a) e) =
  let a' = typeOf c a
      va = eval a (getEnv NoLock c)
      c' = consCVar c x va
      e' = typeOf c' e
  in Abs (Dec x a') e'
typeOf c (Abs d@(Def x a b) e) =
  let c' = CConsDef c x a b
      e' = typeOf c' e
  in Abs d e'
typeOf c e = readBack (varsCont c) (typeOfV c e)

typeOfV :: Cont -> Exp -> Val
typeOfV c (Var x)     =
  let Just a = getType c x
  in eval a (getEnv NoLock c)
typeOfV _ U           = U
typeOfV c (App e1 e2) = appVal (typeOfV c e1) (eval e2 ENil)
typeOfV _ e           = error ("not typeable expression: " ++ show e)

-- | unfold an expression under given context and locking strategy
unfoldExpr :: EnvStrategy s => Cont -> s -> Exp -> Exp
unfoldExpr c s e =
  let ve = eval e (getEnv s c)
  in readBack (varsCont c) ve
