{-|
Module          : Main
Description     : Entry point of the program
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Main (main) where

import           Commands
import qualified Core.Abs                 as Abs
import           Lang
import           Lock
import           TypeChecker

import           Control.Monad.State
import           Data.Char
import qualified Data.Map                 as Map
import qualified Data.Text                as T
import qualified Data.Text.IO             as TI
import           System.Console.Haskeline
import           System.Directory
import qualified Text.Show.Unicode        as U

-- | the context/state of the REPL operation
data ReplState = ReplState
  { filePath     :: FilePath,            -- path of the loaded file
    fileContent  :: T.Text,              -- content of the loaded file
    concretCtx   :: Abs.Context,         -- concret context of the loaded file
    context      :: Cont,                -- abstract context of the loaded file
    lockStrategy :: SimpleLock,          -- locking/unlocking variables
    bindMap      :: Map.Map String Exp,  -- a map binds well-typed expressions to names
    continue     :: Bool                 -- whether to continue execution
  }

initState :: ReplState
initState = ReplState "" T.empty (Abs.Ctx []) (emptyCont []) LockNone (Map.fromList [("it", U)]) True

main :: IO ()
main = do
  putStrLn "siminitt, version 1.0. ':?' for help, ':q' to quit"
  let sio = runInputT defaultSettings repl
  evalStateT sio initState

repl :: InputT (StateT ReplState IO) ()
repl = do
  ms <- getInputLine "\960.\955> "
  forM_ ms handleInput
  ct <- lift $ gets continue
  when ct repl

handleInput :: String -> InputT (StateT ReplState IO) ()
handleInput str =
  if isEmptyString str
  then return ()
  else let str' = trimString str
       in case getCommand str' of
            Left err                    -> outputStr' (errorMsg err)
            Right Quit                  -> stop
            Right Help                  -> usage
            Right (Load fp)             -> handleLoad fp
            Right (Show s)              -> handleShow s
            Right (Lock l)              -> handleLock l
            Right (Bind x cexp)         -> handleBind x cexp
            Right (Check c)             -> handleCheck c
            Right (Unfold uf)           -> handleUnfold uf
            Right (TypeOf tf)           -> handleTypeOf tf
            Right HeadReduct            -> handleHeadRed
            Right (FindMinimumConsts v) -> handleFindMiniConsts v

stop :: InputT (StateT ReplState IO) ()
stop = lift $ modify (\s -> s {continue = False})

-- |Print a string to the terminal with newline character ensured
outputStr' :: MonadIO m => String -> InputT m ()
outputStr' "" = return ()
outputStr' s  =
  let c = last s
  in if c == '\n'
     then outputStr s
     else outputStrLn s

isEmptyString :: String -> Bool
isEmptyString = all isSpace

trimString :: String -> String
trimString = t . t
  where t = reverse . dropWhile isSpace

handleLoad :: FilePath -> InputT (StateT ReplState IO) ()
handleLoad fp = do
  b <- liftIO . doesFileExist $ fp
  if not b
    then outputStr' . errorMsg $ "error: file does not exist"
    else do
    ls <- lift . gets $ lockStrategy
    t  <- liftIO (TI.readFile fp)
    let ts = T.unpack t
    case parseAndCheck ls ts of
      Left err -> outputStr' (unlines err)
      Right (cx, ac) -> do
        outputStrLn $ okayMsg "file loaded!"
        lift $ modify (\s -> s {filePath    = fp,
                                fileContent = t,
                                concretCtx  = cx,
                                context     = ac})

handleShow :: ShowItem -> InputT (StateT ReplState IO) ()
handleShow SFilePath = do
  fp <- lift $ gets filePath
  if fp == ""
    then outputStrLn . errorMsg $ "no file loaded"
    else outputStrLn fp
handleShow SFileContent = do
  fc <- lift $ gets fileContent
  outputStrLn (T.unpack fc)
handleShow SConsants = do
  ac <- lift $ gets context
  outputStrLn $ U.ushow (allNames ac)
handleShow SLocked = do
  ls <- lift $ gets lockStrategy
  ac <- lift $ gets context
  let sl = lockedNames ls ac
  outputStrLn . U.ushow $ sl
  outputStrLn $ "Lock strategy: " ++ U.ushow ls
handleShow SUnlocked = do
  ls <- lift $ gets lockStrategy
  ac <- lift $ gets context
  let su = unlockedNames ls ac
  outputStrLn . U.ushow $ su
  outputStrLn $ "Lock strategy: " ++ U.ushow ls
handleShow SContext = do
  ac <- lift $ gets context
  outputStr' $ U.ushow ac
handleShow (SName name) = do
  m <- lift . gets $ bindMap
  case Map.lookup name m of
    Nothing -> outputStrLn . errorMsg $ "error: name not bound"
    Just e  -> outputStr' (U.ushow e)

handleLock :: LockOption -> InputT (StateT ReplState IO) ()
handleLock AllLock = do
  let ls = LockAll
  showChangeOfLock ls
  lift . modify $ \s -> s {lockStrategy = ls}

handleLock NoneLock = do
  let ls = LockNone
  showChangeOfLock ls
  lift . modify $ \s -> s {lockStrategy = ls}
handleLock (AddLock ss) = do
  ls <- lift . gets $ lockStrategy
  let ls' = addLock ls ss
  showChangeOfLock ls'
  lift . modify $ \s -> s {lockStrategy = ls'}
handleLock (RemoveLock ss) = do
  ls <- lift . gets $ lockStrategy
  let ls' = removeLock ls ss
  showChangeOfLock ls'
  lift . modify $ \s -> s {lockStrategy = ls'}

handleBind :: String -> Abs.Exp -> InputT (StateT ReplState IO) ()
handleBind x cexp = do
  ls <- lift . gets $ lockStrategy
  cx <- lift . gets $ concretCtx
  ac <- lift . gets $ context
  m  <- lift . gets $ bindMap
  case checkExpr ls cx ac cexp of
    Left err -> outputStr' err
    Right e  ->
      let m' = Map.insert x e m
      in lift . modify $ \s -> s {bindMap = m'}

handleCheck :: CheckItem -> InputT (StateT ReplState IO) ()
handleCheck (CExp cexp) = do
  ls <- lift $ gets lockStrategy
  cx <- lift $ gets concretCtx
  ac <- lift $ gets context
  case checkExpr ls cx ac cexp of
    Left err -> do
      outputStrLn (errorMsg "error: invalid expression!")
      outputStr' err
    Right e  -> do
      outputStrLn (okayMsg "okay~")
      m <- lift . gets $ bindMap
      let m' = Map.insert "it" e m
      lift $ modify (\s -> s {bindMap = m'})
handleCheck (CDecl cdecl) = do
  ls <- lift $ gets lockStrategy
  cx <- lift $ gets concretCtx
  ac <- lift $ gets context
  case checkDecl ls cx ac cdecl of
    Left err -> do
      outputStrLn (errorMsg "error: invalid declaration/definition!")
      outputStr' err
    Right ac'  -> do
      outputStrLn (okayMsg "okay~")
      lift $ modify (\s -> s {concretCtx = addDecl cx cdecl,
                              context = ac'})
  where
    addDecl :: Abs.Context -> Abs.Decl -> Abs.Context
    addDecl (Abs.Ctx ds) d = Abs.Ctx (ds ++ [d])

handleCheck (Const var) = do
  ls <- lift . gets $ lockStrategy
  ac <- lift . gets $ context
  case checkConstant ls ac var of
    Left errmsg -> outputStr' errmsg
    Right _     -> outputStrLn "okay~"

handleTypeOf :: Either String Abs.Exp -> InputT (StateT ReplState IO) ()
handleTypeOf (Left name) = do
  ac <- lift . gets $ context
  m <- lift . gets $ bindMap
  case Map.lookup name m of
    Just e ->
      let te = typeOf ac e
      in outputStr' (U.ushow te)
    Nothing -> outputStrLn . errorMsg $ "name: '" ++ name ++ "' is not bound"
handleTypeOf (Right cexp) = do
  ls <- lift . gets $ lockStrategy
  cx <- lift . gets $ concretCtx
  ac <- lift . gets $ context
  case checkExpr ls cx ac cexp of
    Left err -> outputStr' err
    Right e  ->
      let te = typeOf ac e
      in outputStr' (U.ushow te)

handleHeadRed :: InputT (StateT ReplState IO) ()
handleHeadRed = do
  ac <- lift . gets $ context
  m  <- lift . gets $ bindMap
  let Just e = Map.lookup "it" m
      e' = hReduct ac e
  outputStr' . U.ushow $ e'
  let m' = Map.insert "it" e' m
  lift . modify $ \s -> s {bindMap = m'}

handleUnfold :: Either String Abs.Exp -> InputT (StateT ReplState IO) ()
handleUnfold (Left name) = do
  ls <- lift . gets $ lockStrategy
  ac <- lift . gets $ context
  m <- lift . gets $ bindMap
  case Map.lookup name m of
    Just e ->
      let e' = unfold ls ac e
      in outputStr' (U.ushow e')
    Nothing -> outputStr' . errorMsg $ "name: '" ++ name ++ "' is not bound"
handleUnfold (Right cexp) = do
  ls <- lift . gets $ lockStrategy
  cx <- lift . gets $ concretCtx
  ac <- lift . gets $ context
  case checkExpr ls cx ac cexp of
    Left err -> outputStr' err
    Right e  ->
      let e' = unfold ls ac e
      in outputStr' (U.ushow e')

showChangeOfLock :: SimpleLock -> InputT (StateT ReplState IO) ()
showChangeOfLock lockNew = do
  lockNow <- lift . gets $ lockStrategy
  outputStrLn "Change lock strategy"
  outputStrLn $ "  from: " ++ U.ushow lockNow
  outputStrLn $ "  to: " ++ U.ushow lockNew

handleFindMiniConsts :: String -> InputT (StateT ReplState IO) ()
handleFindMiniConsts _ = outputStr' "not supported yet"
  -- ac <- lift . gets $ context
  -- case minimumConsts ac x of
  --   Left err -> outputStrLn err
  --   Right ss -> outputStrLn (U.ushow ss)

usage :: InputT (StateT ReplState IO) ()
usage = let msg = [ " Commands available:"
                  , "   :?, :help                     show this usage message"
                  , "   :q                            quit"
                  , "   :load <file>                  load <file> with the current locking strategy, default strategy is '-none'"
                  , "   :show {filePath | fileContent | const_all | const_locked | const_unlocked | expr | context | -name <name>}"
                  , "      filePath, fp               show the path of the currently loaded file"
                  , "      fileContent, fc            show the content of the currently loaded file"
                  , "      const_all, ca              show the name of all of the constants of the currently loaded file"
                  , "      const_locked, cl           show the name of all of the locked constants specified by the user"
                  , "      const_unlocked, cu         show the name of all of the unlocked constants of the currently loaded file"
                  , "      context, ctx               show the type checking context"
                  , "      -name <name>               show the expression bound to the name <name>"
                  , "   :lock {-all | -none | -add | -remove} [<varlist>]"
                  , "                                 change lock strategy:"
                  , "                                 -all: lock all constants; -none: lock none constants;"
                  , "                                 -add <varlist>: add a list of constants to the locking strategy"
                  , "                                 -remove <varlist>: remove a list of constants from the locking strategy"
                  , "                                 <varlist> must be in the form '[v1,v2,...,vn]' with no whitespace interspersed"
                  , "   :bind <name> = <expr>         bind a name <name> to expression <expr>, if <expr> is well typed under the current"
                  , "                                 locking strategy."
                  , "   :check {-expr | -decl | -const}  {<expr> | <decl> | <constant>}"
                  , "      -expr   <expr>             parse and type check an expression in the current context with the current locking strategy."
                  , "                                 a type checked expression will be bound to the name 'it'"
                  , "      -decl   <decl>             parse and type check a declaration/definition in the current context with the current locking strategy."
                  , "                                 a type checked declaration/definition will be added to the context"
                  , "      -const  <constant>         type check a constant (identifier of a declaration/definition) in the current context with the current"
                  , "                                 locking strategy."
                  , "                                 the constant must come from the current context. This command is used to experiment with the locking/un-"
                  , "                                 locking mechanism."
                  , "   :unfold {-name | -expr} {<name> | <expr>}"
                  , "                                 unfold an expression bound to a name <name> or a given expression <expr> under the"
                  , "                                 current locking strategy."
                  , "                                 a given expression will firstly be type-checked before its being unfolded"
                  , "   :typeOf {-name | -expr} {<name> | <expr>}"
                  , "                                 calculate the type of an expression bound to a name <name> or a given expression <expr>."
                  , "                                 a given expression will firstly be type-checked before being calculated the type"
                  , "   :hred                         apply head reduction on the expression bound to name 'it', making the result be bound to"
                  , "                                 'it' instead"
                  , "   :fmc <constant>               find the minimum set of constants that need to be unfolded, such that the declaration/definition"
                  ,"                                  referred by <constant> in the current context is type valid"
                   ]
        in outputStr (unlines msg)
