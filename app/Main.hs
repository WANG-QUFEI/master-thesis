{-|
Module          : Main
Description     : Entry point of the program
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Main (main) where

import           Commands
import           Core.Abs
import           Lang
import qualified Locking                  as L
import           Message
import           TypeChecker

import           Control.Monad.State
import           Data.Char
import qualified Data.Map                 as Map
import qualified Data.Set                 as Set
import qualified Data.Text                as T
import qualified Data.Text.IO             as TI
import           System.Console.Haskeline
import           System.Directory
import qualified Text.Show.Unicode        as U

-- | the context/state of the REPL operation
data ReplState = ReplState
  { filePath    :: FilePath,            -- path of the loaded file
    fileContent :: T.Text,              -- content of the loaded file
    concretCtx  :: Context,             -- concret context of the loaded file
    context     :: Cont,                -- abstract context of the loaded file
    lockStyle   :: L.LockStyle,           -- locking/unlocking variables
    bindMap     :: Map.Map String Exp,  -- a map binds well-typed expressions to names
    continue    :: Bool                 -- whether to continue execution
  }

initState :: ReplState
initState = ReplState "" T.empty (Ctx []) CNil L.LockNone (Map.fromList [("it", U)]) True

main :: IO ()
main = do
  putStrLn "siminitt, version 0.1. ':?' for help, ':q' to quit"
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
            Left err            -> outputStrLn (errorMsg err)
            Right Quit          -> stop
            Right Help          -> usage
            Right (Load fp)     -> handleLoad fp
            Right (Show s)      -> handleShow s
            Right (Lock l)      -> handleLock l
            Right (Bind x cexp) -> handleBind x cexp
            Right (Check c)     -> handleCheck c
            Right (Unfold uf)   -> handleUnfold uf
            Right (TypeOf tf)   -> handleTypeOf tf
            Right HeadReduct    -> handleHeadRed

handleHeadRed :: InputT (StateT ReplState IO) ()
handleHeadRed = do
  ax <- lift . gets $ context
  m  <- lift . gets $ bindMap
  let Just e = Map.lookup "it" m
      e' = headRed ax e
  outputStrLn . U.ushow $ e'
  let m' = Map.insert "it" e' m
  lift . modify $ \s -> s {bindMap = m'}

stop :: InputT (StateT ReplState IO) ()
stop = lift $ modify (\s -> s {continue = False})

isEmptyString :: String -> Bool
isEmptyString = all isSpace

trimString :: String -> String
trimString = t . t
  where t = reverse . dropWhile isSpace

handleLoad :: FilePath -> InputT (StateT ReplState IO) ()
handleLoad fp = do
  b <- liftIO . doesFileExist $ fp
  if not b
    then outputStrLn . errorMsg $ "error: file does not exist"
    else do
    ls <- lift . gets $ lockStyle
    t  <- liftIO (TI.readFile fp)
    let ts = T.unpack t
    case parseCheckFile ls ts of
      Left err -> outputStrLn err
      Right (cx, ax) -> do
        outputStrLn $ okayMsg "file loaded!"
        lift $ modify (\s -> s {filePath    = fp,
                                fileContent = t,
                                concretCtx  = cx,
                                context     = ax})

handleShow :: ShowItem -> InputT (StateT ReplState IO) ()
handleShow SFilePath = do
  fp <- lift $ gets filePath
  if fp == ""
    then outputStrLn . errorMsg $ "there's no file that has been loaded"
    else outputStrLn fp
handleShow SFileContent = do
  fc <- lift $ gets fileContent
  if fc == T.empty
    then outputStrLn . errorMsg $ "there's no file that has been loaded"
    else outputStrLn (T.unpack fc)
handleShow SConsants = do
  ac <- lift $ gets context
  if ac == CNil
    then outputStrLn . errorMsg $ "there's no file that has been loaded"
    else outputStrLn $ U.ushow (varsCont ac)
handleShow SLocked = do
  ls <- lift $ gets lockStyle
  ac <- lift $ gets context
  let varsAll = varsCont ac
  case ls of
    L.LockNone    -> outputStrLn "[]"
    L.LockAll     -> outputStrLn $ U.ushow varsAll
    L.LockList ss -> do
      let set1 = Set.fromList varsAll
          set2 = Set.fromList ss
          ss'  = Set.toList (Set.intersection set1 set2)
      outputStrLn . U.ushow $ ss'
handleShow SUnlocked = do
  ls <- lift $ gets lockStyle
  ac <- lift $ gets context
  let varsAll = varsCont ac
  case ls of
    L.LockAll     -> outputStrLn "[]"
    L.LockNone    -> outputStrLn $ U.ushow varsAll
    L.LockList ss -> do
      let set1 = Set.fromList varsAll
          set2 = Set.fromList ss
          ss'  = Set.toList (Set.difference set1 set2)
      outputStrLn . U.ushow $ ss'
handleShow SContext = do
  ac <- lift $ gets context
  outputStrLn $ U.ushow ac
handleShow (SName name) = do
  m <- lift . gets $ bindMap
  case Map.lookup name m of
    Nothing -> outputStrLn . errorMsg $ "error: name not bound"
    Just e  -> outputStrLn (U.ushow e)

handleLock :: LockOption -> InputT (StateT ReplState IO) ()
handleLock LockAll =
  let ls = L.LockAll
  in lift . modify $ \s -> s {lockStyle = ls}
handleLock LockNone =
  let ls = L.LockNone
  in lift . modify $ \s -> s {lockStyle = ls}
handleLock (LockAdd ss) = do
  ls <- lift . gets $ lockStyle
  case ls of
    L.LockAll -> return ()
    L.LockNone ->
      let ls' = L.LockList ss
      in lift . modify $ \s -> s {lockStyle = ls'}
    L.LockList ss' ->
      let set1 = Set.fromList ss'
          set2 = Set.fromList ss
          us   = Set.toList (Set.union set1 set2)
      in lift . modify $ \s -> s {lockStyle = L.LockList us}
handleLock (LockRemove ss) = do
  ls <- lift . gets $ lockStyle
  ax <- lift . gets $ context
  case ls of
    L.LockNone -> return ()
    L.LockAll -> do
      let allVars = varsCont ax
          set1 = Set.fromList allVars
          set2 = Set.fromList ss
          ss'  = Set.toList (Set.difference set1 set2)
      lift . modify $ \s -> s {lockStyle = L.LockList ss'}
    L.LockList ss' ->
      let set1 = Set.fromList ss'
          set2 = Set.fromList ss
          us   = Set.toList (Set.difference set1 set2)
      in lift . modify $ \s -> s {lockStyle = L.LockList us}

handleBind :: String -> CExp -> InputT (StateT ReplState IO) ()
handleBind x cexp = do
  ls <- lift . gets $ lockStyle
  cx <- lift . gets $ concretCtx
  ax <- lift . gets $ context
  m  <- lift . gets $ bindMap
  case convertCheckExpr ls cx ax cexp of
    Left err -> outputStr err
    Right e  ->
      let m' = Map.insert x e m
      in lift . modify $ \s -> s {bindMap = m'}

handleCheck :: CheckItem -> InputT (StateT ReplState IO) ()
handleCheck (CExp cexp) = do
  ls <- lift $ gets lockStyle
  cx <- lift $ gets concretCtx
  ax <- lift $ gets context
  case convertCheckExpr ls cx ax cexp of
    Left err -> do
      outputStrLn (errorMsg "error: invalid expression!")
      outputStr err
    Right e  -> do
      outputStrLn (okayMsg "okay~")
      m <- lift . gets $ bindMap
      let m' = Map.insert "it" e m
      lift $ modify (\s -> s {bindMap = m'})
handleCheck (CDecl cdecl) = do
  ls <- lift $ gets lockStyle
  cx <- lift $ gets concretCtx
  ax <- lift $ gets context
  case convertCheckDecl ls cx ax cdecl of
    Left err -> do
      outputStrLn (errorMsg "error: invalid declaration/definition!")
      outputStrLn err
    Right d  -> do
      outputStrLn (okayMsg "okay~")
      let (cx', ax') = expandContext (cx, ax) (cdecl, d)
      lift $ modify (\s -> s {concretCtx = cx',
                              context = ax'})
  where
    expandContext :: (Context, Cont) -> (CDecl, Decl) -> (Context, Cont)
    expandContext (Ctx ds, ax) (cd, d) =
      let cx = Ctx (ds ++ [cd])
          ax' = case d of
            Dec x a   -> CConsVar ax x a
            Def x a b -> CConsDef ax x a b
      in (cx, ax')

handleTypeOf :: Either String CExp -> InputT (StateT ReplState IO) ()
handleTypeOf (Left name) = do
  ax <- lift . gets $ context
  m <- lift . gets $ bindMap
  case Map.lookup name m of
    Just e ->
      let te = typeOf ax e
      in outputStrLn (U.ushow te)
    Nothing -> outputStrLn . errorMsg $ "name: '" ++ name ++ "' is not bound"
handleTypeOf (Right cexp) = do
  ls <- lift . gets $ lockStyle
  cx <- lift . gets $ concretCtx
  ax <- lift . gets $ context
  case convertCheckExpr ls cx ax cexp of
    Left err -> outputStrLn err
    Right e  ->
      let te = typeOf ax e
      in outputStrLn (U.ushow te)

handleUnfold :: Either String CExp -> InputT (StateT ReplState IO) ()
handleUnfold (Left name) = do
  ls <- lift . gets $ lockStyle
  ax <- lift . gets $ context
  m <- lift . gets $ bindMap
  case Map.lookup name m of
    Just e ->
      let e' = unfold ls ax e
      in outputStrLn (U.ushow e')
    Nothing -> outputStrLn . errorMsg $ "name: '" ++ name ++ "' is not bound"
handleUnfold (Right cexp) = do
  ls <- lift . gets $ lockStyle
  cx <- lift . gets $ concretCtx
  ax <- lift . gets $ context
  case convertCheckExpr ls cx ax cexp of
    Left err -> outputStrLn err
    Right e  ->
      let e' = unfold ls ax e
      in outputStrLn (U.ushow e')

usage :: InputT (StateT ReplState IO) ()
usage = let msg = [ " Commands available:"
                  , "   :?, :help                     show this usage message"
                  , "   :q                            quit"
                  , "   :load <file>                  load <file> with the current locking strategy, default strategy is '-none'"
                  , "   :show {filePath | fileContent | const_all | const_locked | const_unlocked | expr | context | -name <name> }"
                  , "      - filePath                 show the path of the currently loaded file"
                  , "      - fileContent              show the content of the currently loaded file"
                  , "      - const_all                show the name of all of the constants of the currently loaded file"
                  , "      - const_locked             show the name of all of the locked constants specified by the user"
                  , "      - const_unlocked           show the name of all of the unlocked constants of the currently loaded file"
                  , "      - context                  show the type checking context"
                  , "      - -name <name>             show the expression bound to the name <name>"
                  , "   :lock {-all | -none | -add | -remove} [<varlist>]"
                  , "                                 change lock strategy:"
                  , "                                 -all: lock all constants; -none: lock none constants;"
                  , "                                 -add <varlist>: add a list of constants to the locking strategy"
                  , "                                 -remove <varlist>: remove a list of constants from the locking strategy"
                  , "                                 <varlist> must be in the form '[v1,v2,...,vn]' with no whitespace interspersed"
                  , "   :bind <name> = <expr>         bind a name <name> to expression <expr>, if <expr> is well typed under the current"
                  , "                                 locking strategy."
                  , "   :check {-expr | -decl}  { <expr> | <decl> }"
                  , "                                 parse and type check an expression or declaration/definition with the current locking"
                  , "                                 strategy. A successfully type checked expression will be bound to the name 'it',"
                  , "                                 whereas a successfully type checked declaration/definition will be added to the"
                  , "                                 underlying type-checking context"
                  , "   :unfold {-name | -expr} { <name> | <expr> }"
                  , "                                 unfold an expression bound to a name <name> or a given expression <expr> under the"
                  , "                                 current locking strategy."
                  , "                                 A given expression will firstly be type-checked before it being unfolded"
                  , "   :typeOf {-name | -expr} { <name> | <expr> }"
                  , "                                 calculate the type of an expression bound to a name <name> or a given expression <expr>."
                  , "                                 A given expression will firstly be type-checked before being calculated the type"
                  , "   :hred                         apply head reduction on the expression bound to name 'it', making the result be bound to"
                  , "                                 'it' instead"
                   ]
        in outputStr (unlines msg)
