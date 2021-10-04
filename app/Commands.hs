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
  , SetItem(..)
  , LockOption(..)
  , getCommand
  , headRed
  , typeOf
  , unfold
  , checkExpr
  , checkProg
  , isConvertible
  ) where

import qualified Convertor       as Con
import qualified Core.Abs        as Abs
import qualified Core.Par        as Par
import           Lang
import           TypeChecker
import           Util

import           Core.Layout
import           Data.Char
import           Data.List.Split
import           Data.Map        (Map, (!))
import qualified Data.Map        as M
--import           Debug.Trace
import           Text.Printf     (printf)

-- |Data type for the commands
data Cmd = Help
         | Quit
         | Check CheckItem
         | Load FilePath
         | CLet String Abs.Exp
         | CType Abs.Exp
         | HRed (Maybe Abs.Exp)
         | Show ShowItem
         | Lock LockOption
         | CheckC Abs.Exp Abs.Exp
         | SetOpt SetItem
         deriving (Show)


data ShowItem = SLock         -- show lock strategy
              | SContext      -- show the type-checking context
              deriving (Show)

data CheckItem = CProg Abs.Context
               | CExp  Abs.Exp
               deriving Show

newtype SetItem = SConvert ConvertCheck deriving Show

data LockOption = OptAllLock
                | OptNoneLock
                | OptAddLock [String]
                | OptRemoveLock [String]
                deriving (Show)

data CmdSelector = CmdSel { funs    :: Map String ([String] -> Either String Cmd)
                          , prompts :: Map String String}

-- | Parse a string into a command, return an error message if no command
-- could be found parsePorgExp str
getCommand :: String -> Either String Cmd
getCommand str =
  if head str /= ':'
  then if isLetClause str
       then let ss = tail . words $ str in parseLet ss
       else parsePorgExp str
  else
    let ws = words str
    in case selectCmd (head ws) (CmdSel fm pm) of
      Nothing -> Left (printf "unknown command: %s" str)
      Just f  -> f (tail ws)
  where
    fm = M.fromList [(":?",      \_ -> Right Help),
                     (":help",   \_ -> Right Help),
                     (":quit",   \_ -> Right Quit),
                     (":load",   parseLoad),
                     (":type",   parseType),
                     (":hRed",   parseHred),
                     (":show",   parseShow),
                     (":lock",   parseLock),
                     (":set",    parseSet),
                     (":check_convert", parseCheckC)]
    pm = M.fromList [(":?", "show the usage message"),
                     (":help", "show the usage message"),
                     (":quit", "stop the program"),
                     (":load", "<file_path>"),
                     (":type", "<expression>"),
                     (":hRed", "<expression>"),
                     (":show", "{-lock | -context}"),
                     (":lock", "{-all | -none | -add <[variable]> | -remove <[variable]>}"),
                     (":set",   "{-conversion [beta | eta]}"),
                     (":check_convert", "<exp1> ~ <exp2>")]

parsePorgExp :: String -> Either String Cmd
parsePorgExp str =
  let tokens = resolveLayout True $ Par.myLexer str
  in case Par.pContext tokens of
       Right ctx -> return $ Check (CProg ctx)
       Left  _   -> let tokens' = Par.myLexer str in
         case Par.pExp tokens' of
           Right e -> return $ Check (CExp e)
           Left  _ -> Left $ "unknown command: " ++ str

parseExpr :: String -> Either String Abs.Exp
parseExpr s  = Par.pExp (Par.myLexer s)

parseLoad :: [String] -> Either String Cmd
parseLoad ss = case ss of
  []  -> Left ":load <file>"
  x:_ -> return $ Load x

isLetClause :: String -> Bool
isLetClause str =
  let ss = words str
  in case ss of
    "let" : _ : "=" : _ -> True
    _                   -> False

parseLet :: [String] -> Either String Cmd
parseLet ss = case ss of
  n : "=" : exps -> do
    e <- parseExpr (unwords exps)
    return $ CLet n e
  _   -> Left ":let <name> = <expression>"

parseCheckC :: [String] -> Either String Cmd
parseCheckC [] = Left "no expressions specified"
parseCheckC ss = do
  let (s1, s2) = span (/= '~') (unwords ss)
  e1 <- parseExpr s1
  e2 <- parseExpr (tail s2)
  return $ CheckC e1 e2

parseType :: [String] -> Either String Cmd
parseType ss = do
  e <- parseExpr (unwords ss)
  return $ CType e

parseHred :: [String] -> Either String Cmd
parseHred [] = return $ HRed Nothing
parseHred ss = do
  e <- parseExpr (unwords ss)
  return $ HRed (Just e)

parseShow :: [String] -> Either String Cmd
parseShow ss = case ss of
  ["-lock"]    -> return $ Show SLock
  ["-context"] -> return $ Show SContext
  _            -> Left ":show {-lock | -context}"

parseLock :: [String] -> Either String Cmd
parseLock ss = case ss of
  ["-all"]             -> return $ Lock OptAllLock
  ["-none"]            -> return $ Lock OptNoneLock
  "-add" : xs ->
    let xs' = filter (not . isSpace) . unwords $ xs
    in do
      vs <- parseList xs'
      return $ Lock (OptAddLock vs)
  "-remove" : xs ->
    let xs' = filter (not . isSpace) . unwords $ xs
    in do
      vs <- parseList xs'
      return $ Lock (OptRemoveLock vs)
  _ -> Left ":lock {-all | -none | -add <[variable]>| -remove <[variable]>}"

selectCmd :: String -> CmdSelector -> Maybe ([String] -> Either String Cmd)
selectCmd str sel =
  let fm = funs sel
      pm = prompts sel
      xs = M.keys fm
  in case matchCmd str xs of
    []  -> Nothing
    [x] -> M.lookup x fm
    cms ->
      let msg = "ambiguous input, possible commands:" : map (\x -> printf "  %s     %s" x (pm ! x)) cms
          f'  = \_ -> Left $ unlines msg
      in Just f'

matchCmd :: String -> [String] -> [String]
matchCmd s xs = foldl matchChar xs (zip s [0,1..])

matchChar :: [String] -> (Char, Int) -> [String]
matchChar xs (c, i) = filter (\x -> length x > i && x !! i == c) xs

parseSet :: [String] -> Either String Cmd
parseSet tws = case tws of
  "-conversion" : ["beta"] -> return $ SetOpt (SConvert Beta)
  "-conversion" : ["eta"]  -> return $ SetOpt (SConvert Eta)
  _                        -> Left ":set -conversion [beta | eta]"

parseList :: String -> Either String [String]
parseList s =
  if head s == '[' && last s == ']'
  then let s' = init . tail $ s
       in Right (endBy "," s')
  else Left "<variables> must be in the form '[v1,v2,...,vn]'"

-- |Instantiate a segment with expressions
segCont :: Cont -> Namespace -> [ExPos] -> Cont
segCont c pr eps =
  let r   = getEnv LockNone c
      qps = map (mfst $ eval r) eps
      c'  = findSeg c pr
  in foldr g c' qps
  where g :: (QExp, Name) -> Cont -> Cont
        g (q, x) cont =
          let (_, t) = getType cont x
          in bindConD cont x t q

-- |Apply head reduction on an expression
headRed :: Cont -> Exp -> Exp
headRed c (Abs x a b) =
  let c' = bindConT c x a
      b' = headRed c' b
  in Abs x a b'
headRed c (Let x a b e) =
  let c' = bindConD c x a b
      e' = headRed c' e
  in Let x a b e'
headRed c e = readBack (namesCtx c) (headRedV c e)

-- |Evaluate an expression in 'one small step'
headRedV :: Cont -> Exp -> QExp
headRedV c (Var x) =
  let (dx,c') = getDef c x
      r  = getEnv LockAll c'
  in eval r dx
headRedV c (App e1 e2) =
  let r  = getEnv LockAll c
      q1 = headRedV c e1
      q2 = eval r e2
  in appVal q1 q2
headRedV c (SVar ref eps) =
  let pr = reverse (rns ref)
      r  = getEnv LockNone c
      r' = segEnv r pr eps
      x  = rid ref
      dx = getDef' r' x
      c' = findSeg c pr
      re = getEnv LockAll c'
  in eval re dx
headRedV c e = eval (getEnv LockAll c) e

typeOf :: Cont -> Exp -> Exp
typeOf c (Let x a b e) =
  let c' = bindConD c x a b
      e' = typeOf c' e
  in Let x a b e'
typeOf c (Abs x a b) =
  let c' = bindConT c x a
      b' = typeOf c' b
  in Abs x a b'
typeOf c e = readBack (namesCtx c) (typeOfV c e)

typeOfV :: Cont -> Exp -> QExp
typeOfV _ U = U
typeOfV c (Var x) =
  let (_, t) = getType c x
  in eval (getEnv LockAll c) t
typeOfV c (SVar ref eps) =
  let pr = reverse (rns ref)
      x  = rid ref
      c' = segCont c pr eps
      (_, t)  = getType c' x
  in eval (getEnv LockAll c') t
typeOfV c (App e1 e2) =
  let t1 = typeOfV c e1
      q2 = eval (emptyEnv (cns c)) e2
  in appVal t1 q2
typeOfV _ _ = error "error: typeOfV"

unfold :: LockStrategy s => s -> Cont -> Exp -> Exp
unfold s c e =
  let q = eval (getEnv s c) e
  in readBack (namesCtx c) q

-- |Type check an expression under given context and locking strategy
checkExpr :: LockStrategy s => s -> ConvertCheck -> Cont -> Abs.Exp -> Either String (Exp, Exp)
checkExpr s ctc ac cexp =
  case runG (Con.convertExp cexp) ac of
    Left err   -> Left $ unlines . map errorMsg $ explain err
    Right aexp -> case soundExpr ac aexp of
                  Left err -> Left err
                  Right e  -> let t = typeOf ac e in Right (e, t)
  where
    soundExpr :: Cont -> Exp -> Either String Exp
    soundExpr _ U = Right U
    soundExpr ctx e@(Abs x a m) =
      case runG (checkD s ctx (Dec x a)) (emptyCont (cns ctx), ctc) of
        Left err   -> Left $ unlines . map errorMsg $ explain err
        Right ctx' -> case soundExpr ctx' m of
                        Left err -> Left err
                        Right _  -> Right e
    soundExpr ctx e@(Let x a b m) =
      case runG (checkD s ctx (Def x a b)) (emptyCont (cns ctx), ctc) of
        Left err   -> Left $ unlines . map errorMsg $ explain err
        Right ctx' -> case soundExpr ctx' m of
                        Left err -> Left err
                        Right _  -> Right e
    soundExpr ctx e =
      case runG (checkI s ctx e) (emptyCont (cns ctx), ctc) of
        Left err -> Left $ unlines . map errorMsg $ explain err
        Right _  -> Right e

-- |Type check an declaration/definition under given context and locking strategy
checkProg :: LockStrategy s => s -> ConvertCheck -> Cont -> Abs.Context -> Either String Cont
checkProg s ctc ac cc =
  case runG (Con.convertCtx cc) ac of
    Left err -> Left $ unlines . map errorMsg $ explain err
    Right ds -> case runG (typeCheckProg s ds) (ac, ctc) of
                  Left err -> Left $ unlines . map errorMsg $ explain err
                  Right c  -> Right c

isConvertible ::LockStrategy s => s -> ConvertCheck -> Cont -> Exp -> Exp -> Either String Bool
isConvertible s ctc ac e1 e2 = do
  let env = getEnv s ac
      q1 = eval env e1
      q2 = eval env e2
  case runG (checkConvert s ctc ac q1 q2) (ac, ctc) of
    Left err -> Left $ unlines . map errorMsg $ ("Not convertible" : explain err)
    Right _  -> Right True
