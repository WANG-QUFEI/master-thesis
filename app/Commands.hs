{-|
Module          : Commands
Description     : provides simple command line functions
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Commands
  ( Cmd(..)
  , parseToCommand
  , parseCheckFile
  , checkExpValidity
  , headRed
  , unfold
  , fullEval
  , typeOf
  , typeCheckErrMsg
  , okayMsg
  , errorMsg
  , infoMsg
  ) where

import           Data.Char
import           Data.List.Split
import           System.Directory (doesFileExist)

import           Classes
import           Core.Abs
import           Core.Par         (myLexer, pCDecl, pCExp, pContext)
import           Lang
import           Locking
import           MessageHelper
import           TypeChecker

-- | data type for the commands
data Cmd = Quit
         | None
         | Help
         | ShowFile
         | LoadFile FilePath
         | CheckE CExp
         | CheckD CDecl
         | HeadReduct
         | FullEvalExp
         | Unfold [String]
         | GetType CExp
         deriving (Show)

-- | Parse a string into a command, return an error message if no command
--   could be found
parseToCommand :: String -> Either String Cmd
parseToCommand s =
  if blankStr s
    then Right None
    else
      let ws = words s
       in case head ws of
            ":?"      -> Right Help
            ":h"      -> Right Help
            ":help"   -> Right Help
            ":q"      -> Right Quit
            ":quit"   -> Right Quit
            ":sf"     -> Right ShowFile
            ":lf"     -> getLoad ws
            ":ce"     -> getCheckExp ws
            ":cd"     -> getCheckDecl ws
            ":hred"   -> Right HeadReduct
            ":eval"   -> Right FullEvalExp
            ":unfold" -> Right (Unfold (tail ws))
            ":type"   -> getExpType ws
            _         -> Left $ errorMsg "Invalid command"
  where
    blankStr :: String -> Bool
    blankStr s = all isSpace s

    getLoad :: [String] -> Either String Cmd
    getLoad ws = case tail ws of
      []     -> Left $ errorMsg "Lack of file path"
      fp : _ -> Right (LoadFile fp)

    getCheckExp :: [String] -> Either String Cmd
    getCheckExp ws = case tail ws of
      []  -> Left $ errorMsg "Lack of expression"
      ws' -> case pCExp (myLexer (unwords ws')) of
        Left _   -> Left $ errorMsg "Syntax error: bad expression"
        Right ce -> Right (CheckE ce)

    getCheckDecl :: [String] -> Either String Cmd
    getCheckDecl ws = case tail ws of
      [] -> Left $ errorMsg "Lack of declaration/definition"
      ws' -> case pCDecl (myLexer (unwords ws')) of
        Left _   -> Left $ errorMsg "Syntax error: bad declaration/definition"
        Right cd -> Right (CheckD cd)

    getExpType :: [String] -> Either String Cmd
    getExpType ws = case tail ws of
      [] -> Left $ errorMsg "Lack of expression"
      ws' -> case pCExp (myLexer (unwords ws')) of
        Left _   -> Left (errorMsg "Syntax error: bad expression")
        Right ce -> Right (GetType ce)

-- | parse and type check the content of a file
parseCheckFile :: EnvStrategy s => s -> String -> Either String (Context, Cont)
parseCheckFile s text = case pContext (myLexer text) of
  Left parseError   -> Left (unlines (map errorMsg ["Failed to parse the file", parseError]))
  Right concreteCtx -> case runTypeCheckCtx s concreteCtx of
                 Left ss           -> Left (typeCheckErrMsg $ ss)
                 Right abstractCtx -> Right (concreteCtx, abstractCtx)

-- | evaluate an expression with all variables available
fullEval :: Cont -> Exp -> Val
fullEval c e = eval e (getEnv NoLocking c)

-- | given a type checking context, head evaluation on an expression
headRed :: Cont -> Exp -> Exp
headRed c (Abs d e) =
  case d of
    Dec x a ->
      let va = eval a (getEnv NoLocking c)
          a' = headRed c a
          e' = headRed (consCVar c x va) e
      in Abs (Dec x a') e'
    Def x a b ->
      let e' = headRed (CConsDef c x a b) e
      in Abs d e'
headRed c e = readBack (varsCont c) (headRedV c e)

-- | turn a value into an expression, remove the closure of a value
readBack :: [String] -> Val -> Exp
readBack _ U = U
readBack _ (Var x) = Var x
readBack ns (App v1 v2) = App (readBack ns v1) (readBack ns v2)
readBack ns (Clos (Abs (Dec "" a) e) r) = Abs (Dec "" (readBack ns (eval a r))) (readBack ns (eval e r))
readBack ns (Clos (Abs (Dec x a) e) r) =
  let z  = freshVar x ns
      a' = readBack ns (eval a r)
      e' = readBack (z : ns) (eval e (consEVar r x (Var z)))
  in Abs (Dec z a') e'
readBack _ _ = error "operation not supported"

headRedV :: Cont -> Exp -> Val
headRedV c (Var x)     = eval (defCont x c) ENil
headRedV c (App e1 e2) = appVal (headRedV c e1) (eval e2 ENil)
headRedV c e           = eval e ENil

-- | given a type checking context, get the definition of a variable
defCont :: String -> Cont -> Exp
defCont x CNil = Var x
defCont x (CConsVar c x' _)
  | x == x'   = Var x
  | otherwise = defCont x c
defCont x (CConsDef c x' a e)
  | x == x'   = e
  | otherwise = defCont x c

-- | given a type checking context, evaluate an expression with a list of constants unlocked
unfold :: Cont -> [String] -> Exp -> Exp
unfold c ss e =
  let envStra = AnnotatedLocking False ss
  in readBack (varsCont c) (eval e $ getEnv envStra c)

typeOf :: Cont -> Exp -> Exp
typeOf c (Abs d e) =
  case d of
    Dec x a ->
      let a' = typeOf c a
          v  = eval a (getEnv NoLocking c)
          c' = consCVar c x v
          e' = typeOf c' e
      in Abs (Dec x a') e'
    Def x a b ->
      let e' = typeOf (CConsDef c x a b) e
      in Abs d e'
typeOf c e = readBack (varsCont c) (typeOfV c e)

typeOfV :: Cont -> Exp -> Val
typeOfV c (Var x)     = let Just v = getType c x in v
typeOfV c U           = U
typeOfV c (App e1 e2) = appVal (typeOfV c e1) (eval e2 ENil)
typeOfV _ e           = error ("typeOf " ++ show e)
