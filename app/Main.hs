module Main (main) where

import System.Environment ( getArgs, getProgName )
import System.Exit        ( exitFailure, exitSuccess )
import Control.Monad      ( when )
import Control.Monad.State

import Core.Lex    ( Token )
import Core.Par    ( pProgram, myLexer )
import Core.Skel   ()
import Core.Print  ( Print, printTree )
import Core.Abs    (Program)
import Core.Layout ( resolveLayout )
import TypeChecker

type Err = Either String
type ParseFun a = [Token] -> Err a

myLLexer = resolveLayout True . myLexer

type Verbosity = Int

putStrV :: Verbosity -> String -> IO ()
putStrV v s = when (v > 1) $ putStrLn s

runFile :: (Print a, Show a) => Verbosity -> ParseFun a -> FilePath -> IO ()
runFile v p f = putStrLn f >> readFile f >>= run v p

run :: (Print a, Show a) => Verbosity -> ParseFun a -> String -> IO ()
run v p s = case p ts of
    Left s -> do
      putStrLn "\nParse              Failed...\n"
      putStrV v "Tokens:"
      putStrV v $ show ts
      putStrLn s
      exitFailure
    Right prog -> do
      putStrLn "\nParse Successful!"
      showTree v prog
      case typeCheckProgram ts of
        []       -> putStrLn "\nType-checking Successful!" >> exitSuccess
        (err:_)  -> putStrLn ("\nType check error: " ++ err) >> exitFailure
  where
  ts = myLLexer s
  typeCheckProgram :: [Token] -> [String]
  typeCheckProgram ts = let (Right p) = pProgram ts in runTypeCheck p
    
showTree :: (Show a, Print a) => Int -> a -> IO ()
showTree v tree
 = do
      putStrV v $ "\n[Abstract Syntax]\n\n" ++ show tree
      putStrV v $ "\n[Linearized tree]\n\n" ++ printTree tree

usage :: IO ()
usage = do
  putStrLn $ unlines
    [ "usage: Call with one of the following argument combinations:"
    , "  --help          Display this help message."
    , "  (no arguments)  Parse stdin verbosely."
    , "  (files)         Parse content of files verbosely."
    , "  -s (files)      Silent mode. Parse content of files silently."
    ]
  exitFailure

main :: IO ()
main = do
  args <- getArgs
  case args of
    ["--help"] -> usage
    [] -> getContents >>= run 2 pProgram
    "-s":fs -> mapM_ (runFile 0 pProgram) fs
    fs -> mapM_ (runFile 2 pProgram) fs

