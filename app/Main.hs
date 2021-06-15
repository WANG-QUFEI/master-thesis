{-|
Module          : Main
Description     : Entry point of the program
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Main (main) where

import           Commands
import           Core.Abs                 (Context (..))
import           Lang
import           Locking
import           Message
import           TypeChecker

import           Control.Monad.State
import           Data.Char
import qualified Data.Set                 as Set
import qualified Data.Text                as T
import qualified Data.Text.IO             as TI
import           System.Console.Haskeline
import           System.Directory

-- | the context/state of the REPL operation
data ReplState = ReplState
  { filePath    :: FilePath,      -- path of the loaded file
    fileContent :: T.Text,        -- content of the loaded file
    concretCtx  :: Context,       -- concret context of the loaded file
    context     :: Cont,          -- abstract context of the loaded file
    lockStyle   :: LockStyle,     -- locking/unlocking variables
    expr        :: Exp,           -- abstract form of the last successfully evaluated expression
    continue    :: Bool           -- continue execution ?
  }

initState :: ReplState
initState = ReplState "" T.empty (Ctx []) CNil NoLock U True

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
            Left err           -> outputStrLn (errorMsg err)
            Right Quit         -> stop
            Right Help         -> usage
            Right (Load ls fp) -> do
              b <- liftIO (doesFileExist fp)
              if b
                then tryLoadFile ls fp
                else outputStrLn (errorMsg "error: file does not exist")
            Right (Show si)    -> showItem si
            Right (Check ci)   -> checkItem ci
            _                  -> return ()

stop :: InputT (StateT ReplState IO) ()
stop = lift $ modify (\s -> s {continue = False})

isEmptyString :: String -> Bool
isEmptyString = all isSpace

trimString :: String -> String
trimString = t . t
  where t = reverse . dropWhile isSpace

tryLoadFile :: LockStyle -> FilePath -> InputT (StateT ReplState IO) ()
tryLoadFile ls fp = do
  t <- liftIO (TI.readFile fp)
  let scontent = T.unpack t
  case parseCheckFile ls scontent of
    Left err -> outputStrLn err
    Right (cx, ax) -> do
      outputStrLn $ okayMsg "file loaded!"
      lift $ modify (\s -> s {filePath    = fp,
                              fileContent = t,
                              concretCtx  = cx,
                              context     = ax,
                              lockStyle   = ls})

showItem :: ShowItem -> InputT (StateT ReplState IO) ()
showItem SFilePath = do
  fp <- lift $ gets filePath
  if fp == ""
    then outputStrLn "no file been loaded"
    else outputStrLn fp
showItem SFileContent = do
  fc <- lift $ gets fileContent
  if fc == T.empty
    then outputStrLn "no file been loaded"
    else outputStrLn (T.unpack fc)
showItem SConsants = do
  ac <- lift $ gets context
  if ac == CNil
    then outputStrLn "no file been loaded"
    else outputStrLn $ show (varsCont ac)
showItem SLocked = do
  ls <- lift $ gets lockStyle
  ac <- lift $ gets context
  case ls of
    NoLock   -> outputStrLn "[]"
    AllLock  -> outputStrLn $ show (varsCont ac)
    ExplicitLock True ss -> outputStrLn $ show ss
    ExplicitLock False ss -> do
      let set1 = Set.fromList (varsCont ac)
          set2 = Set.fromList ss
          setd = Set.difference set1 set2
      outputStrLn $ show setd
showItem SUnlocked = do
  ls <- lift $ gets lockStyle
  ac <- lift $ gets context
  case ls of
    AllLock   -> outputStrLn "[]"
    NoLock    -> outputStrLn $ show (varsCont ac)
    ExplicitLock False ss -> outputStrLn $ show ss
    ExplicitLock True ss -> do
      let set1 = Set.fromList (varsCont ac)
          set2 = Set.fromList ss
          setd = Set.difference set1 set2
      outputStrLn $ show setd
showItem SExp = do
  ae <- lift $ gets expr
  outputStrLn $ show ae
showItem SContext = do
  ac <- lift $ gets context
  outputStrLn $ show ac

checkItem :: CheckItem -> InputT (StateT ReplState IO) ()
checkItem (CExp cexp) = do
  ls <- lift $ gets lockStyle
  cx <- lift $ gets concretCtx
  ax <- lift $ gets context
  case convertCheckExpr ls cx ax cexp of
    Left err -> do
      outputStrLn (errorMsg "invalid expression!")
      outputStrLn err
    Right e  -> do
      outputStrLn (okayMsg "valid expression!")
      lift $ modify (\s -> s {expr = e})
checkItem (CDecl _decl) = undefined

usage :: InputT (StateT ReplState IO) ()
usage = let msg = [ " Commands available:"
                  , "   :?                            show this usage message"
                  , "   :q                            quit"
                  , "   :show {'filePath' | 'fileContent' | 'const_all' | 'const_locked' | 'const_unlocked' | 'expr' | 'context'}"
                  , "      - :show filePath           show the path of the currently loaded file"
                  , "      - :show fileContent        show the content of the currently loaded file"
                  , "      - :show const_all          show the name of all of the constants of the currently loaded file"
                  , "      - :show const_locked       show the name of all of the locked constants specified by the user"
                  , "      - :show const_unlocked     show the name of all of the unlocked constants of the currently loaded file"
                  , "      - :show expr               show the latest well-typed expression"
                  , "      - :show absCtx             show the current type checking context (a list of constants declaration/definition)"
                  , "   :load {'-lock' | '-unlock' | '-no_lock' | '-all_lock'} [<varlist>] <file>"
                  , "                                 load <file> with certain locking/unlocking strategy"
                  , "                                 when used with option '-lock' or '-unlock', <varlist>, a list of names of variables, must be given"
                  , "                                 when used with option '-no_lock' or '-all_lock', <varlist> must not be given"
                  , "                                 <varlist> must be in the form '[var1,var2,...,varn]' with no whitespace interspersed"
                  , "                                 "
                  , "   :check {'-expr' | '-decl'}  <exp>|<decl>"
                  , "                                 parse and type check an expression or declaration/definition with the current setting"
                  , "                                 of locking/unlocking variables,"
                  , "                                 A successfully type-checked declaration/definition will be added automatically to the"
                  , "                                 current type-checking context"
                  , "   :hred                         apply head reduction on the latest type-checked expression, making"
                  , "                                 the result be the new expression of the context"
                  , "   :unfold <varlist>             evaluate the current expression of the context with a list of variables (constants)"
                  , "                                 unlocked, making the reuslt be the new expression of the context"
                  ]
        in outputStr (unlines msg)


-- -----------------------------------------------------
-- repl :: InputT IO ()
-- repl = do
--   outputStrLn "welcome, type ':?' for the usage of this program, ':q' to quit"
--   loop (Ctx []) CNil U

-- loop :: Context -> Cont -> Exp -> InputT IO ()
-- loop cc ac e = do
--   ms <- getInputLine "\955> "
--   case ms of
--     Nothing -> loop cc ac e
--     Just s  -> case getCommand s of
--       Left err  -> do
--         outputStrLn err
--         loop cc ac e
--       Right Quit -> return ()
--       Right None -> loop cc ac e
--       Right Help -> do
--         usage
--         loop cc ac e
--       Right ShowFile -> case cc of
--         Ctx [] -> do
--           outputStrLn $ infoMsg "empty context, no file loaded"
--           loop cc ac e
--         _      -> do
--           outputStrLn (printTree cc)
--           loop cc ac e
--       Right (Load fp) -> do
--         fb <- liftIO (doesFileExist fp)
--         if fb then (do
--           r <- liftIO (loadFile fp)
--           case r of
--             Left err -> do
--               outputStr err
--               loop cc ac e
--             Right (cc', ac') -> do
--               outputStrLn $ okayMsg "file loaded!"
--               loop cc' ac' e) else (do
--           outputStrLn $ errorMsg "file does not exist"
--           loop cc ac e)
--       Right (Check ce) -> case checkExpValidity cc ac ce of
--         Left tce -> do
--           outputStr (typeCheckErrMsg tce)
--           loop cc ac e
--         Right e' -> do
--           outputStrLn (okayMsg "expression type checked!")
--           loop cc ac e'
--       Right (CheckD cd) ->
--       Right (GetType ce) -> case checkExpValidity cc ac ce of
--         Left tce -> do
--           outputStr (typeCheckErrMsg tce)
--           loop cc ac e
--         Right e' -> do
--           let e1 = typeOf ac e'
--           outputStrLn $ infoMsg (show e1)
--           loop cc ac e
--       Right HeadRed -> do
--         let e' = headRed ac e
--         outputStrLn $ infoMsg (show e')
--         loop cc ac e'
--       Right ExpEval -> do
--         let v = totalEval ac e
--         outputStrLn $ infoMsg (show v)
--       Right (Unfold xs) -> do
--         let e' = unfold ac xs e
--         outputStrLn $ infoMsg ("evaluate the current expression with the following definitions unlocked: " ++ show xs)
--         outputStrLn $ infoMsg (show e')
--         loop cc ac e'


-- loadFile :: FilePath -> IO (Either String (Context, Cont))
-- loadFile fp = do
--   text <- readFile fp
--   return $ parseCheckFile text
