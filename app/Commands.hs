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
   ) where

import           Classes
import           Core.Abs
import           Core.Par
import           Lang
import qualified Locking         as L

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
    _         -> Left "invalid command, type ':?' for a detailed description of the command"
  where
    parseLoad :: [String] -> Either String Cmd
    parseLoad tws = case tws of
      [fp] -> return $ Load fp
      _ -> Left "invalid command, type ':?' for a detailed description of the command"

    parseShow :: [String] -> Either String Cmd
    parseShow tws = case tws of
      ["filePath"]       -> return (Show SFilePath)
      ["fileContent"]    -> return (Show SFileContent)
      ["const_all"]      -> return (Show SConsants)
      ["const_locked"]   -> return (Show SLocked)
      ["const_unlocked"] -> return (Show SUnlocked)
      ["context"]        -> return (Show SContext)
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
  let c' = consCVar c x a
      e' = typeOf c' e
  in if hasVar x e'
     then Abs (Dec x a) e'
     else Abs (Dec "" a) e'
typeOf c (Abs d@(Def x a b) e) =
  let c' = CConsDef c x a b
      e' = typeOf c' e
  in Abs d e'
typeOf c e = readBack (varsCont c) (typeOfV c e)

typeOfV :: Cont -> Exp -> Val
typeOfV c (Var x)     =
  let Just a = getType c x
  in eval a (getEnv L.LockNone c)
typeOfV _ U           = U
typeOfV c (App e1 e2) = appVal (typeOfV c e1) (eval e2 ENil)
typeOfV _ e           = error ("not typeable expression: " ++ show e)

unfold :: EnvStrategy s => s -> Cont -> Exp -> Exp
unfold s c e =
  let ve = eval e (getEnv s c)
  in readBack (varsCont c) ve

hasVar :: String -> Exp -> Bool
hasVar _ U = False
hasVar x (Var x') = x == x'
hasVar x (App e1 e2) =
  hasVar x e1 || hasVar x e2
hasVar x (Abs (Dec _ a) e) =
  hasVar x a || hasVar x e
hasVar x (Abs (Def _ a b) e) =
  hasVar x a || hasVar x b || hasVar x e
hasVar _ _ = error "not applicable: hasVar"
