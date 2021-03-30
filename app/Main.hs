module Main (main) where

import System.Environment ( getArgs, getProgName )
import System.Exit        ( exitFailure, exitSuccess )
import System.Directory   ( doesFileExist )
import System.IO          ( stdout, hFlush )
import Control.Monad      ( when )
import Text.Regex.TDFA
import Data.Char          ( isSpace )
import Debug.Trace
  
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

loadFile :: (Print a, Show a) => Verbosity -> ParseFun a -> FilePath -> IO (Cont, Context)
loadFile v p f = readFile f >>= load v p

load :: (Print a, Show a) => Verbosity -> ParseFun a -> String -> IO (Cont, Context)
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
      let Right ctx = pContext ts
      case runTypeCheckCtx ctx of
        Left err   -> printError err >> exitFailure
        Right c  -> printSuccess "TYPE CHECK SUCCESS" >> return (c, ctx)
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

repl :: REPL_State -> (Cont, Context) -> IO ()
repl 0 (ac, cc) = do
  putStrLn "File loaded, entering the REPL mode, type ':?' for help, ':q' to quit"
  repl 1 (ac, cc)
repl 1 (ac, cc) = do
  s <- prompt "\955> "
  handle (ac, cc) s
  repl 1 (ac, cc)

blankStr :: String -> Bool
blankStr s = all isSpace s

prompt :: String -> IO String
prompt s = do
  putStr s
  hFlush stdout
  getLine

handle :: (Cont, Context) -> String -> IO ()
handle (ac, cc) s =
  if blankStr s
  then return ()
  else case pCmd (myLexer s) of
    Left _ -> putStrLn "invalid command"
    Right cmd -> case cmd of
      Help -> cmdUsage
      Exit -> exitSuccess
      ShowCtx -> putStrLn (printTree cc)
      Eval e  -> checkAndEval id e >> return ()
      Iter n e
        | n <= 0 -> putStrLn "nothing to do"
        | n == 1 -> checkAndEval id e >> return ()
        | otherwise -> do
            me <- checkAndEval (\x -> "1: " ++ x) e
            case me of
              Nothing -> return ()
              Just ae -> iterEval 2 (n - 1) ae
  where
    checkAndEval :: ShowS -> CExp -> IO (Maybe Exp)
    checkAndEval ss e = case headEvalCExp cc ac e of
      Left err -> printError err >> return Nothing
      Right e' -> putStrLn (ss (show e')) >> return (Just e')
    iterEval :: Integer -> Integer -> Exp -> IO ()
    iterEval nt nc e
      | nc == 0 = return ()
      | otherwise = do
          let e' = headEval ac e
          if e' == e
            then putStrLn "== stop: evaluation converged =="
            else putStrLn (show nt ++ ": " ++ show e') >> iterEval (nt + 1) (nc - 1) e'


cmdUsage :: IO ()
cmdUsage = putStrLn (unlines msg)
  where msg = ["Commands available from the prompt:",
               "  :help, :?               display this list of commands",
               "  :quit, :q               exit REPL",
               "  :s                      show the current type-checking context resulted from loading the file",
               "  :e <exp>                shortcut for firstly applying head-reduction on the expression, then ",
               "                          readback function on the result of the first operation",
               "  :it <num> <exp>         apply 'e' operation on the expression and its result iteratively for <num> times"]
