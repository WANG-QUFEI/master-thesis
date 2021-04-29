{-|
Module          : CmdUtil
Description     : provides simple command line functions
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module CmdUtil
  ( Cmd(..)
  , getCmd
  , parseCheckFile
  , checkExpValidity
  , headRed
  , unfold
  , totalEval
  , typeOf
  , typeCheckErrMsg
  , okayMsg
  , errorMsg
  , infoMsg
  ) where

import           Data.Char
import           Data.List.Split
import           System.Directory (doesFileExist)

import           Base
import           Core.Abs
import           Core.Par         (myLexer, pCExp, pContext)
import           MessageHelper
import           TypeChecker


-- | data type for the commands
data Cmd = Quit
         | None
         | Help
         | ShowFile
         | Load FilePath
         | Check CExp
         | HeadRed
         | ExpEval
         | Unfold [String]
         | GetType CExp
         deriving (Show)

-- | given an input string, return a valid command or an error message if the input is not valid
getCmd :: String -> Either String Cmd
getCmd s = case blankStr s of
  True -> Right None
  _    -> let ws = words s in
    case head ws of
      ":?"      -> Right Help
      ":h"      -> Right Help
      ":help"   -> Right Help
      ":q"      -> Right Quit
      ":quit"   -> Right Quit
      ":s"      -> Right ShowFile
      ":show"   -> Right ShowFile
      ":l"      -> getLoad ws
      ":load"   -> getLoad ws
      ":c"      -> getCheck ws
      ":check"  -> getCheck ws
      ":hred"   -> Right HeadRed
      ":eval"   -> Right ExpEval
      ":u"      -> Right (Unfold (tail ws))
      ":unfold" -> Right (Unfold (tail ws))
      ":t"      -> getExpType ws
      _         -> Left $ errorMsg "unknown command"
  where
    blankStr :: String -> Bool
    blankStr s = all isSpace s

    getLoad :: [String] -> Either String Cmd
    getLoad ws = case tail ws of
                   []  -> Left $ errorMsg "missing file path"
                   f:_ -> Right (Load f)

    getCheck :: [String] -> Either String Cmd
    getCheck ws = case tail ws of
                   []  -> Left $ errorMsg "missing expression"
                   ws' -> case pCExp (myLexer (unwords ws')) of
                            Left _   -> Left $ errorMsg "syntax error, bad expression"
                            Right ce -> Right (Check ce)

    getExpType :: [String] -> Either String Cmd
    getExpType ws = case tail ws of
                      [] -> Left $ errorMsg "missing expression"
                      ws' -> case pCExp (myLexer (unwords ws')) of
                               Left _ -> Left (errorMsg "syntax error, bad expression")
                               Right ce -> Right (GetType ce)


-- | parse and type check the content of a file
parseCheckFile :: String -> Either String (Context, Cont)
parseCheckFile text = case pContext (myLexer text) of
  Left err  -> Left (unlines (map errorMsg ["parse failed!", err]))
  Right ctx -> case runTypeCheckCtx ctx of
                 Left tce -> Left (typeCheckErrMsg tce)
                 Right ac -> Right (ctx, ac)

-- | evaluate an expression with all variables available
totalEval :: Cont -> Exp -> Val
totalEval c e = eval e (envCont c)

-- | given a type checking context, head evaluation on an expression
headRed :: Cont -> Exp -> Exp
headRed c (Abs d e) =
  case d of
    Dec x a ->
      let v = eval a (envCont c)
          a' = headRed c a
          e' = headRed (consCVar c x v) e
      in Abs (Dec x a') e'
    Def x a b ->
      let e' = headRed (CConsDef c x a b) e
      in Abs d e'
headRed c e = readBack (varsCont c) (headRedV c e)

headRedV :: Cont -> Exp -> Val
headRedV c (Var x)     = eval (defCont x c) ENil
headRedV c (App e1 e2) = appVal (headRedV c e1) (eval e2 ENil)
headRedV c e           = eval e ENil

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

-- | get the environment related with a context by giving a list of unlocked definitions
envContLock :: [String] -> Cont -> Env
envContLock _ CNil = ENil
envContLock xs (CConsVar c _ _) = envContLock xs c
envContLock xs (CConsDef c x a e) =
  let r = envContLock xs c
  in if x `elem` xs
     then EConsDef r x a e
     else r

-- | given a type checking context, evaluate an expression with a list of constants unlocked
unfold :: Cont -> [String] -> Exp -> Exp
unfold c [] e = readBack (varsCont c) (eval e ENil)
unfold c ss e = readBack (varsCont c) (eval e (envContLock ss c))

-- | given a type checking context, get the definition of a variable
defCont :: String -> Cont -> Exp
defCont x CNil = Var x
defCont x (CConsVar c x' _)
  | x == x'   = Var x
  | otherwise = defCont x c
defCont x (CConsDef c x' a e)
  | x == x'   = e
  | otherwise = defCont x c

typeOf :: Cont -> Exp -> Exp
typeOf c (Abs d e) =
  case d of
    Dec x a ->
      let a' = typeOf c a
          v  = eval a (envCont c)
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
