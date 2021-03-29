module Main (main) where

import System.Environment ( getArgs, getProgName )
import System.Exit        ( exitFailure, exitSuccess )
import System.Directory   ( doesFileExist )
import System.IO          ( stdout, hFlush )
import Control.Monad      ( when )
import Text.Regex.TDFA
import Data.Char          ( isSpace )
  
import Core.Lex    ( Token )
import Core.Par    ( pContext, pCmd, myLexer )
import Core.Print  ( Print, printTree )
import Core.Abs
import TypeChecker

type Err = Either String

type ParseFun a = [Token] -> Err a

type Verbosity = Int

type REPL_State = Int

main :: IO ()
main = do
  putStrLn "\n*** Command Line Interface (CLI) for Loading a File and Producing a Computing Context for the Language SiminiTT ***\n"
  args <- getArgs
  case args of
    []           -> usage
    "--help":_   -> usage
    ["-v"]       -> usage
    "-v":file:_  -> do
      fileExist <- doesFileExist file
      if fileExist
        then loadFile 2 pContext file >>= repl 0
        else putStrLn "error: file does not exist" >> exitFailure
    file:_       -> do
      fileExist <- doesFileExist file
      if fileExist
        then loadFile 0 pContext file >>= repl 0
        else putStrLn "error: file does not exist" >> exitFailure

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: siminitt [Option] FilePath"
    , ""
    , "Options: "
    , "  --help          display this help message"
    , "  -v              display verbose information"
    , ""
    , "FilePath:         path of the file to be loaded"]
  exitFailure

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

loadFile :: (Print a, Show a) => Verbosity -> ParseFun a -> FilePath -> IO Cont
loadFile v p f = readFile f >>= load v p

load :: (Print a, Show a) => Verbosity -> ParseFun a -> String -> IO Cont
load v p s = case p ts of
    Left s -> do
      putStrLn "\n\9889\9889\9889 PARSE FAILED \9889\9889\9889\n"
      putStrV v "Tokens:"
      putStrV v $ show ts
      putStrLn s
      exitFailure
    Right src -> do
      printSuccess "PARSING SUCCESS"
      printSource v src
      let Right p = pContext ts
      case runTypeCheckCtx p of
        Left err -> printError err >> exitFailure
        Right c  -> printSuccess "TYPE CHECK SUCCESS" >> return c
  where
  ts = myLexer s

printSource :: (Show a, Print a) => Int -> a -> IO ()
printSource v src = do
  let ls  = lines $ printTree src
      k   = maximum . (fmap length) $ ls
      cut = take k (repeat '-')    
      ls' = ("" : cut : ls) ++ [cut, ""]
  mapM_ (putStrV v) ls'

printSyntax :: (Show a, Print a) => Int -> a -> IO ()
printSyntax v tree = (putStrV v $ show tree) >> putStrV v ""

printError :: TypeCheckError -> IO ()
printError err = do
  putStrLn "\9889\9889\9889 TYPE CHECK FAILED \9889\9889\9889"
  let ts  = errorText err
  case ts of
    [] -> return ()
    (h : tail) -> do
      let ts' = fmap (\x -> " \10008 " ++ x) ts
      mapM_ putStrLn ts'

printSuccess :: String -> IO ()
printSuccess s = putStrLn ("\n\9972 " ++ s ++ " \9972\n")

repl :: REPL_State -> Cont -> IO ()
repl 0 c = do
  putStrLn "File loaded, entering the REPL mode, type ':?' for help, ':q' to quit"
  repl 1 c
repl 1 c = do
  s <- prompt "\955> "
  handle c s
  repl 1 c

blankStr :: String -> Bool
blankStr s = all isSpace s

prompt :: String -> IO String
prompt s = do
  putStr s
  hFlush stdout
  getLine

handle :: Cont -> String -> IO ()
handle c s =
  if blankStr s
  then return ()
  else case pCmd (myLexer s) of
    Left err  -> putStrLn $ "invalid command: " ++ err
    Right cmd -> case cmd of
      Help -> cmdUsage
      Exit -> putStrLn "Bye~" >> exitSuccess
      ShowCtx -> let vs = reverse (varsCont c) in
        case vs of
          []  -> putStrLn "current context is empty"
          [x] -> putStrLn ("names declared in the context:\n" ++ x)
          _   -> do
            let vs' = (map (\v -> v ++ ", ") (init vs)) ++ [last vs]
            putStrLn "names declared in the context: "
            mapM_ putStr vs'
            putStr "\n"
      _    -> undefined -- ^ TODO: continue
  

cmdUsage :: IO ()
cmdUsage = putStrLn (unlines msg)
  where msg = ["Commands available from the prompt:",
               "  :help, :?               display this list of commands",
               "  :quit, :q               exit REPL",
               "  :show context           show the current type-checking context resulted from loading the file",
               "  :rb <val>               apply readback function on a value",
               "  :hRed <exp>             aplly head-reduction on a well-typed expression",
               "  :incrEval <exp>         shortcut for firstly applying head-reduction on the expression, then ",
               "                          readback function on the result of the first operation"]
