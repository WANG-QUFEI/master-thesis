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
  , checkConstant
   ) where

import qualified Core.Abs                   as Abs
import qualified Core.Par                   as Par
import           Lang
import           TypeChecker
import           Util

import qualified Data.HashMap.Strict.InsOrd as OrdM
import           Data.List.Split
import           Data.Map                   (Map, (!))
import qualified Data.Map                   as M
import           Text.Printf                (printf)

-- |Data type for the commands
data Cmd = Help
         | Quit
         | Load FilePath
         | Show ShowItem
         | Lock LockOption
         | Bind String Abs.Exp
         | Check CheckItem
         | SetOpt SetItem
         | Unfold (Either String Abs.Exp)
         | TypeOf (Either String Abs.Exp)
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

data CheckItem = CExp  Abs.Exp    -- check an expression
               | CDecl Abs.Decl   -- check a declaration/definition
               | Const String     -- check a constant
               deriving Show

newtype SetItem = SConvert ConvertCheck deriving Show

data LockOption = OptAllLock
                | OptNoneLock
                | OptAddLock [String]
                | OptRemoveLock [String]
                deriving (Show)

data CmdSelector = CmdSel { funs    :: Map String ([String] -> Either String Cmd)
                          , prompts :: Map String String}

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
  where
    matchCmd :: String -> [String] -> [String]
    matchCmd s xs = foldl matchChar xs (zip s [0,1..])

    matchChar :: [String] -> (Char, Int) -> [String]
    matchChar xs (c, i) = filter (\x -> length x > i && x !! i == c) xs

-- | Parse a string into a command, return an error message if no command
-- could be found
getCommand :: String -> Either String Cmd
getCommand str =
  let ws  = words str
      tws = tail ws
  in case selectCmd (head ws) (CmdSel fm pm) of
    Nothing -> Left "invalid command, type ':?' for a detailed description of the command"
    Just f -> f tws
  where
    fm = M.fromList [(":?",      \_ -> Right Help),
                     (":help",   \_ -> Right Help),
                     (":quit",   \_ -> Right Quit),
                     (":load",   parseLoad),
                     (":show",   parseShow),
                     (":lock",   parseLock),
                     (":bind",   parseBind),
                     (":check",  parseCheck),
                     (":set",    parseSet),
                     (":unfold", parseUnfold),
                     (":typeOf", parseTypeof),
                     (":hred",   \_ -> Right HeadReduct)]
    pm = M.fromList [("?", "show the usage message"),
                     (":help", "show the usage message"),
                     (":quit", "stop the program"),
                     (":load", "<filename>"),
                     (":show", "{filePath | fileContent | const_all | const_locked | const_unlocked | expr | context | -name <name>}"),
                     (":lock", "{-all | -none | -add | -remove} [<varlist>]"),
                     (":bind", "<name> = <expr>, bind a name <name> to expression <expr>"),
                     (":check", "{-expr | -decl | -const}  { <expr> | <decl> | <constant>}"),
                     (":set",   "{-conversion [beta | eta]}"),
                     (":unfold", "{-name | -expr} { <name> | <expr> }"),
                     (":typeOf", "{-name | -expr} { <name> | <expr> }"),
                     (":hred", "apply head reduction on the expression bound to name 'it'")]

    parseLoad :: [String] -> Either String Cmd
    parseLoad tws = case tws of
      []  -> Left ":load <file>"
      x:_ -> return $ Load x

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
      _                  -> Left ":show {filePath | fileContent | const_all | const_locked | const_unlocked | expr | context | -name <name>}"

    parseLock :: [String] -> Either String Cmd
    parseLock tws = case tws of
      ["-all"]             -> return $ Lock OptAllLock
      ["-none"]            -> return $ Lock OptNoneLock
      ["-add", varlist]    -> do
        ss <- parseList varlist
        return $ Lock (OptAddLock ss)
      ["-remove", varlist] -> do
        ss <- parseList varlist
        return $ Lock (OptRemoveLock ss)
      _ -> Left ":lock {-all | -none | -add | -remove} [<varlist>]"

    parseBind :: [String] -> Either String Cmd
    parseBind tws = case tws of
      v : "=" : ws' -> do
        e <- parseExpr (unwords ws')
        return $ Bind v e
      _ -> Left ":bind <name> = <expr>"

    parseCheck :: [String] -> Either String Cmd
    parseCheck tws = case tws of
      "-expr" : ws'  -> do
        e <- parseExpr (unwords ws')
        return $ Check (CExp e)
      "-decl" : ws'  -> do
        d <- parseDecl (unwords ws')
        return $ Check (CDecl d)
      ["-const", var] -> return $ Check (Const var)
      _ ->  Left ":check {-expr | -decl | -const}  {<expr> | <decl> | <constant>}"

    parseSet :: [String] -> Either String Cmd
    parseSet tws = case tws of
      "-conversion" : ["beta"] -> return $ SetOpt (SConvert Beta)
      "-conversion" : ["eta"]  -> return $ SetOpt (SConvert Eta)
      _                        -> Left ":set -conversion [beta | eta]"

    parseUnfold :: [String] -> Either String Cmd
    parseUnfold tws = case tws of
      ["-name", v] -> return $ Unfold (Left v)
      "-expr" : ws' -> do
        e <- parseExpr (unwords ws')
        return $ Unfold (Right e)
      _ ->  Left ":unfold {-name | -expr} {<name> | <expr>}"

    parseTypeof :: [String] -> Either String Cmd
    parseTypeof tws = case tws of
      ["-name", v] -> return $ TypeOf (Left v)
      "-expr" : ws' -> do
        e <- parseExpr (unwords ws')
        return $ TypeOf (Right e)
      _ ->  Left ":typeOf {-name | -expr} {<name> | <expr>}"

    parseList :: String -> Either String [String]
    parseList s =
      if head s == '[' && last s == ']'
      then let s' = init . tail $ s
           in Right (endBy "," s')
      else Left "<varlist> must be in the form '[v1,v2,...,vn]' with no whitespace interspersed"

    parseExpr :: String -> Either String Abs.Exp
    parseExpr "" = Left "lack of expression"
    parseExpr s  = Par.pExp (Par.myLexer s)

    parseDecl :: String -> Either String Abs.Decl
    parseDecl "" = Left "lack of declaration"
    parseDecl s  = Par.pDecl (Par.myLexer s)

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
headRed c e = readBack (namesCont c) (headRedV c e)

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
headRedV c (SegVar ref eps) =
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
typeOf c e = readBack (namesCont c) (typeOfV c e)

typeOfV :: Cont -> Exp -> QExp
typeOfV _ U = U
typeOfV c (Var x) =
  let (_, t) = getType c x
  in eval (getEnv LockAll c) t
typeOfV c (SegVar ref eps) =
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
  in readBack (namesCont c) q

checkConstant :: LockStrategy s => s -> ConvertCheck -> Cont -> Name -> Either String ()
checkConstant s ct c x =
  case locate x of
    Nothing -> Left . errorMsg $ "No constant with name '" ++ x ++ "' exists in the current context"
    Just (c', d) ->
      case runG (checkD s c' d) (emptyCont (cns c), ct) of
        Left err ->
          let errmsg = explain err
          in Left (unlines (map errorMsg errmsg))
        Right _ -> return ()
  where
    locate :: Name -> Maybe (Cont, Decl)
    locate n = case OrdM.lookup n (mapCont c) of
      Just (Ct a) ->
        let c' = splitCont n c
        in Just (c', Dec n a)
      Just (Cd a b) ->
        let c' = splitCont n c
        in Just (c', Def n a b)
      _ -> Nothing
