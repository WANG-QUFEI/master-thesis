{-|
Module          : Main
Description     : Entry point of the program
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Main (main) where

import           Commands
import qualified Core.Abs                   as Abs
import           Lang
import           TypeChecker
import           Util

import           Control.Monad.State
import           Data.Char
import qualified Data.HashMap.Strict.InsOrd as OrdM
import qualified Data.Text                  as T
import qualified Data.Text.IO               as TI
--import           Debug.Trace
import           System.Console.Haskeline
import           System.Directory
import qualified Text.Show.Unicode          as U

-- | the context/state of the REPL operation
data ReplState = ReplState {
  buff         :: (Bool, T.Text),      -- structure for multi-line user input
  context      :: Cont,                -- abstract context of the loaded file
  bindCtx      :: Cont,                -- a map binds well-typed expressions to names
  lockStrategy :: SimpleLock,          -- locking/unlocking variables
  conversion   :: ConvertCheck,        -- convertibility support, beta conversion or eta conversion
  continue     :: Bool                 -- whether to continue execution
  }

initState :: ReplState
initState = ReplState (False, T.empty) (emptyCont []) initDynamicContext LockNone Beta True

initDynamicContext :: Cont
initDynamicContext = Cont [] (OrdM.singleton "_it" (Cd U U))

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
  else do
    (b, t) <- lift $ gets buff
    let str' = trimString str
    if b
      then case str' of
             ":}" -> do
               lift $ modify (\s -> s {buff = (False, T.empty)})
               let text = T.unpack t
               unless (isEmptyString text) (parseExec text)
             _    -> do
               lift $ modify (\s -> s {buff = (True, T.append t (T.pack (str ++ "\n")))})
      else case str' of
             ":{" -> do
               lift $ modify (\s -> s {buff = (True, T.empty)})
             _    ->
               parseExec str'

promptExec :: String -> InputT (StateT ReplState IO) a -> InputT (StateT ReplState IO) ()
promptExec question action = do
  ms <- getInputLine question
  case ms of
    Nothing  -> return ()
    Just ans -> when (isAffirmative (trimString ans)) (void action)
  where
    isAffirmative :: String -> Bool
    isAffirmative s = head s == 'y' || head s == 'Y'

parseExec :: String -> InputT (StateT ReplState IO) ()
parseExec str =
  case getCommand str of
    Left err        -> outputStr' (errorMsg err)
    Right Help      -> usage
    Right Quit      -> lift $ modify (\s -> s {continue = False})
    Right (Check c) -> handleCheck c
    Right (Load fp) -> do
      dc <- lift . gets $ bindCtx
      if OrdM.size (mapCont dc) < 2
        then handleLoad fp
        else promptExec "load/reload a file will erase all the bindings, continue? [Y/N] " (handleLoad fp)
    Right (CLet x ce)      -> handleLet x ce
    Right (CType ce)       -> handleGetType ce
    Right (HRed me)        -> handleHred me
    Right (Show si)        -> handleShow si
    Right (Lock lopt)      -> handleLock lopt
    Right (SetOpt sopt)    -> handleSet sopt
    Right (CheckC ce1 ce2) -> handleCheckC ce1 ce2

usage :: InputT (StateT ReplState IO) ()
usage = let msg = [ " Commands available:"
                  , "   <statement>                             A statement could be an expression or a declaration"
                  , "                                           For an expression, it will be type checked and evaluated and the"
                  , "   let <name> = <expression>               Bind an expression to a name if the expression is valid"
                  , "                                           If the expression is valid, its type will be inferred and a definition"
                  , "                                           consisting of the name, the type and the expression will be bound to the"
                  , "                                           name “_it” in the dynamic context"
                  , "                                           For an declaration, it will be type checked and added to the static context"
                  , "   :load <file>                            Load <file> with the current locking strategy"
                  , "                                           Once successfully loaded, the context of the file will become the new static context and"
                  , "                                           the dynamic context will be reset to its initial state"
                  , "                                           be added to the dynamic context"
                  , "   :type <expression>                      Infer the type of an expression after it is type checked"
                  , "   :hRed <expression>                      Apply head reduction on an expression after it is type checked"
                  , "   :show {-lock | -context}                Show information about the current state"
                  , "      -lock                                show the current lock strategy"
                  , "      -context                             show the type checking context"
                  , "   :lock {-all | -none | -add | -remove}   Change lock strategy"
                  , "      -all                                 lock all constants"
                  , "      -none                                unlock all constants"
                  , "      -add    <[variable]>                 add a list of names to be locked"
                  , "      -remove <[variable]>                 remove a list of names to be locked"
                  , "   :set {-conversion}"
                  , "      -conversion  <beta | eta>            set the convertibility checking support, beta conversion or eta conversion"
                  , "   :check_convert <exp1> ~ <exp2>          Check the convertibility of two expressions if they are both valid"
                  , "   :quit                                   stop the program"
                  , "   :?, :help                               show this usage message"
                   ]
        in outputStr (unlines msg)

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
    c  <- lift . gets $ conversion
    t  <- liftIO (TI.readFile fp)
    let ts = T.unpack t
    case parseAndCheck ls c ts of
      Left err -> outputStr' (unlines err)
      Right ctx -> do
        outputStr' $ okayMsg "file loaded!"
        lift $ modify (\s -> s {context = ctx, bindCtx = initDynamicContext})

handleCheckC :: Abs.Exp -> Abs.Exp -> InputT (StateT ReplState IO) ()
handleCheckC ce1 ce2 = do
  s  <- lift $ gets lockStrategy
  ct <- lift $ gets conversion
  sc <- lift $ gets context
  dc <- lift $ gets bindCtx
  let ctx = combineCtx sc dc
  case checkExpr s ct ctx ce1 of
    Left err -> do
      outputStr' (errorMsg "the first expression is not valid")
      outputStr' err
    Right (e1, _) ->
      case checkExpr s ct ctx ce2 of
        Left err -> do
          outputStr' (errorMsg "the second expression is not valid")
          outputStr' err
        Right (e2, t) ->
          case isConvertible s ct ctx e1 e2 t of
            Left err -> outputStr' err
            Right _  -> outputStr' (okayMsg "checked convertible")

handleCheck :: CheckItem -> InputT (StateT ReplState IO) ()
handleCheck (CExp cexp) = do
  s  <- lift $ gets lockStrategy
  ct <- lift $ gets conversion
  sc <- lift $ gets context
  dc <- lift $ gets bindCtx
  let ctx = combineCtx sc dc
  case checkExpr s ct ctx cexp of
    Left err -> outputStr' err
    Right (e, t)  -> do
      let e' = unfold s ctx e
      outputStr' (U.ushow e')
      let m' = OrdM.insert "_it" (Cd t e') (mapCont dc)
          dc' = dc {mapCont = m'}
      lift . modify $ \stat -> stat {bindCtx = dc'}
handleCheck (CProg cx) = do
  s  <- lift $ gets lockStrategy
  ct <- lift $ gets conversion
  sc <- lift $ gets context
  case checkProg s ct sc cx of
    Left err -> outputStr' err
    Right c' ->
      lift . modify $ \stat -> stat {context = combineCtx sc c'}

handleLet :: String -> Abs.Exp -> InputT (StateT ReplState IO) ()
handleLet x cexp = do
  s  <- lift . gets $ lockStrategy
  ct <- lift . gets $ conversion
  sc <- lift . gets $ context
  dc <- lift . gets $ bindCtx
  case checkExpr s ct (combineCtx sc dc) cexp of
    Left err -> outputStr' err
    Right (e, t) ->
      let dc' = bindConD dc x t e
      in lift . modify $ \stat -> stat {bindCtx = dc'}

handleGetType :: Abs.Exp -> InputT (StateT ReplState IO) ()
handleGetType cexp = do
  s  <- lift . gets $ lockStrategy
  ct <- lift . gets $ conversion
  sc <- lift . gets $ context
  dc <- lift . gets $ bindCtx
  case checkExpr s ct (combineCtx sc dc) cexp of
    Left err     -> outputStr' err
    Right (_, t) -> outputStr' (U.ushow t)

handleHred :: Maybe Abs.Exp -> InputT (StateT ReplState IO) ()
handleHred Nothing = do
  sc <- lift . gets $ context
  dc <- lift . gets $ bindCtx
  let ctx = combineCtx sc dc
      Just (Cd t e) = OrdM.lookup "_it" (mapCont dc)
      e' = headRed ctx e
  outputStr' . U.ushow $ e'
  let m' = OrdM.insert "_it" (Cd t e') (mapCont dc)
      dc' = dc {mapCont = m'}
  lift . modify $ \s -> s {bindCtx = dc'}
handleHred (Just cexp) = do
  s  <- lift . gets $ lockStrategy
  ct <- lift . gets $ conversion
  sc <- lift . gets $ context
  dc <- lift . gets $ bindCtx
  let ctx = combineCtx sc dc
  case checkExpr s ct ctx cexp of
    Left err     -> outputStr' err
    Right (e, t) -> do
      let e' = headRed ctx e
      outputStr' . U.ushow $ e'
      let m' = OrdM.insert "_it" (Cd t e') (mapCont dc)
          dc' = dc {mapCont = m'}
      lift . modify $ \stat -> stat {bindCtx = dc'}

combineCtx :: Cont -> Cont -> Cont
combineCtx sc dc =
  let cmap = OrdM.union (mapCont sc) (mapCont dc)
  in Cont (cns sc) cmap

handleShow :: ShowItem -> InputT (StateT ReplState IO) ()
handleShow SContext = do
  sc <- lift $ gets context
  dc <- lift $ gets bindCtx
  outputStr' "--- static context ----"
  outputStr' $ U.ushow sc
  outputStr' "--- dynamic context ----"
  outputStr' $ U.ushow dc
handleShow SLock = do
  lock <- lift . gets $ lockStrategy
  outputStr' ("current lock strategy is: " ++ U.ushow lock)

showLockChange :: SimpleLock -> InputT (StateT ReplState IO) ()
showLockChange lockNew = do
  lockNow <- lift . gets $ lockStrategy
  outputStrLn "Change lock strategy"
  outputStrLn $ "  from: " ++ U.ushow lockNow
  outputStrLn $ "  to: " ++ U.ushow lockNew

handleLock :: LockOption -> InputT (StateT ReplState IO) ()
handleLock OptAllLock = do
  let ls = LockAll
  showLockChange ls
  lift . modify $ \s -> s {lockStrategy = ls}
handleLock OptNoneLock = do
  let ls = LockNone
  showLockChange ls
  lift . modify $ \s -> s {lockStrategy = ls}
handleLock (OptAddLock ss) = do
  ls <- lift . gets $ lockStrategy
  let ls' = addLock ls ss
  showLockChange ls'
  lift . modify $ \s -> s {lockStrategy = ls'}
handleLock (OptRemoveLock ss) = do
  ls <- lift . gets $ lockStrategy
  let ls' = removeLock ls ss
  showLockChange ls'
  lift . modify $ \s -> s {lockStrategy = ls'}

handleSet :: SetItem -> InputT (StateT ReplState IO) ()
handleSet (SConvert Beta) = do
  lift . modify $ \s -> s {conversion = Beta}
  outputStr' (okayMsg "set to beta-conversion")
handleSet (SConvert Eta) = do
  lift . modify $ \s -> s {conversion = Eta}
  outputStr' (okayMsg "set to eta-conversion")
