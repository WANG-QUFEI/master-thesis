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
  , typeOf
  , unfold
  , checkConstant
  -- , minimumConsts
   ) where

import qualified Core.Abs                   as Abs
import qualified Core.Par                   as Par
import           Lang
import           Lock
import           Monads
import           TypeChecker

import qualified Data.HashMap.Strict.InsOrd as OrdM
import           Data.List.Split
import           Data.Map                   (Map, (!))
import qualified Data.Map                   as M
-- import           Debug.Trace
import           Text.Printf                (printf)

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

data LockOption = AllLock
                | NoneLock
                | AddLock [String]
                | RemoveLock [String]
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
    fm = M.fromList [(":?", \_ -> Right Help),
                     (":help", \_ -> Right Help),
                     (":quit", \_ -> Right Quit),
                     (":load", parseLoad),
                     (":show", parseShow),
                     (":lock", parseLock),
                     (":bind", parseBind),
                     (":check", parseCheck),
                     (":unfold", parseUnfold),
                     (":typeOf", parseTypeof),
                     (":hred", \_ -> Right HeadReduct),
                     (":fmc", parseMiniConsts)]
    pm = M.fromList [("?", "show the usage message"),
                     (":help", "show the usage message"),
                     (":quit", "stop the program"),
                     (":load", "<filename>"),
                     (":show", "{filePath | fileContent | const_all | const_locked | const_unlocked | expr | context | -name <name>}"),
                     (":lock", "{-all | -none | -add | -remove} [<varlist>]"),
                     (":bind", "<name> = <expr>, bind a name <name> to expression <expr>"),
                     (":check", "{-expr | -decl | -const}  { <expr> | <decl> | <constant>}"),
                     (":unfold", "{-name | -expr} { <name> | <expr> }"),
                     (":typeOf", "{-name | -expr} { <name> | <expr> }"),
                     (":hred", "apply head reduction on the expression bound to name 'it'"),
                     (":fmc", "<constant>, find the minimum set of constants that need to be unfolded")]

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
      ["-all"]             -> return $ Lock AllLock
      ["-none"]            -> return $ Lock NoneLock
      ["-add", varlist]    -> do
        ss <- parseList varlist
        return $ Lock (AddLock ss)
      ["-remove", varlist] -> do
        ss <- parseList varlist
        return $ Lock (RemoveLock ss)
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

    parseMiniConsts :: [String] -> Either String Cmd
    parseMiniConsts []    = Left "lack of constant"
    parseMiniConsts (x:_) = return $ FindMinimumConsts x

-- |Instantiate a segment with expressions
segCont :: Cont -> Namespace -> [ExPos] -> Cont
segCont c pr eps =
  let r   = getEnv LockNone c
      qps = map (mfst $ eval r) eps
      c'  = findSeg c pr
  in foldr g c' qps
  where g :: (QExp, Name) -> Cont -> Cont
        g (q, x) cont =
          let t = getType cont x
          in bindConD cont x t q

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

-- |Apply head reduction on an expression
hReduct :: Cont -> Exp -> Exp
hReduct _ U = U
hReduct c (Abs x a b) =
  let r  = getEnv LockAll c
      qa = eval r a
      a' = hReduct c a
      c' = bindConT c x qa
      b' = hReduct c' b
  in Abs x a' b'
hReduct c (Let x a b e) =
  let c' = bindConD c x a b
      e' = hReduct c' e
  in Let x a b e'
hReduct c e = readBack (namesCont c) (incrEval c e)

-- |Evaluate an expression in 'one small step'
incrEval :: Cont -> Exp -> QExp
incrEval c (Var x) =
  let (dx,c') = getDef c x
      r  = getEnv LockAll c'
  in eval r dx
incrEval c (App e1 e2) =
  let r  = getEnv LockAll c
      q1 = incrEval c e1
      q2 = eval r e2
  in appVal q1 q2
incrEval c (SegVar ref eps) =
  let pr = reverse (rns ref)
      x  = rid ref
      r  = getEnv LockNone c
      r' = segEnv r pr eps
      dx = getDef' r' x
      c' = findSeg c pr
      re = getEnv LockAll c'
  in eval re dx
incrEval _ _ = error "error: incrEval"

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
  let t = getType c x
  in eval (getEnv LockAll c) t
typeOfV c (SegVar ref eps) =
  let pr = reverse (rns ref)
      x  = rid ref
      c' = segCont c pr eps
      t  = getType c' x
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

checkConstant :: LockStrategy s => s -> Cont -> Name -> Either String ()
checkConstant s c x =
  case locate x of
    Nothing -> Left . errorMsg $ "No constant with name '" ++ x ++ "' exists in the current context"
    Just (_, d) ->
      case runG (checkD s c d) (emptyCont (cns c)) of
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
