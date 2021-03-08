module Main (main) where

import System.Environment ( getArgs, getProgName )
import System.Exit        ( exitFailure, exitSuccess )
import Control.Monad      ( when )
import Debug.Trace

import Core.Lex    ( Token )
import Core.Par    ( pProgram, myLexer )
import Core.Print  ( Print, printTree )
import Core.Abs
import Core.Layout ( resolveLayout )
import TypeChecker

type Err = Either String
type ParseFun a = [Token] -> Err a

myLLexer = resolveLayout True . myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: (Print a, Show a) => Verbosity -> ParseFun a -> FilePath -> IO ()
runFile v p f = readFile f >>= run v p

run :: (Print a, Show a) => Verbosity -> ParseFun a -> String -> IO ()
run v p s = case p ts of
    Left s -> do
      putStrLn "\nParse              Failed...\n"
      putStrV v "Tokens:"
      putStrV v $ show ts
      putStrLn s
      exitFailure
    Right src -> do
      printSuccess "PARSING SUCCESS"
      printSource v src
      let Right p = pProgram ts
      case runTypeCheck p of
        Left err -> printError err
        Right _  -> printSuccess "TYPE CHECK SUCCESS" >> exitSuccess
  where
  ts = myLLexer s

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
       exitFailure

printSuccess :: String -> IO ()
printSuccess s = putStrLn ("\9972 " ++ s ++ " \9972")

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: siminitt [Option] File"
    , "Options: "
    , "  --help          Display this help message"
    , "  -p              print parsing result"
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    [] -> putStrLn "invalid argument!" >> usage
    "--help":_   -> usage
    "-p":file:_  -> runFile 2 pProgram file
    file:_       -> runFile 0 pProgram file
  
