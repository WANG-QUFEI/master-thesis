{-|
Module          : Main
Description     : Entry point of the program
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Main (main) where

import           Control.Monad.IO.Class   (MonadIO (liftIO))
import           System.Console.Haskeline (InputT, defaultSettings,
                                           getInputLine, outputStr, outputStrLn,
                                           runInputT)
import           System.Directory         (doesFileExist)

import           Lang                     (Cont (CNil), Exp (U))
import           CmdUtil                  (Cmd (Check, ExpEval, GetType, HeadRed, Help, Load, None, Quit, ShowFile, Unfold),
                                           checkExpValidity, errorMsg, getCmd,
                                           headRed, infoMsg, okayMsg,
                                           parseCheckFile, totalEval,
                                           typeCheckErrMsg, typeOf, unfold)
import           Core.Abs                 (Context (..))
import           Core.Print               (printTree)

main :: IO ()
main = runInputT defaultSettings repl

-----------------------------------------------------
repl :: InputT IO ()
repl = do
  outputStrLn "~ welcome, type ':?' for the usage of this program, ':q' to quit"
  loop (Ctx []) CNil U

loop :: Context -> Cont -> Exp -> InputT IO ()
loop cc ac e = do
  ms <- getInputLine "~ "
  case ms of
    Nothing -> loop cc ac e
    Just s  -> case getCmd s of
      Left err  -> do
        outputStrLn err
        loop cc ac e
      Right Quit -> return ()
      Right None -> loop cc ac e
      Right Help -> do
        usage
        loop cc ac e
      Right ShowFile -> case cc of
        Ctx [] -> do
          outputStrLn $ infoMsg "empty context, no file loaded"
          loop cc ac e
        _      -> do
          outputStrLn (printTree cc)
          loop cc ac e
      Right (Load fp) -> do
        fb <- liftIO (doesFileExist fp)
        if fb then (do
          r <- liftIO (loadFile fp)
          case r of
            Left err -> do
              outputStr err
              loop cc ac e
            Right (cc', ac') -> do
              outputStrLn $ okayMsg "file loaded!"
              loop cc' ac' e) else (do
          outputStrLn $ errorMsg "file does not exist"
          loop cc ac e)
      Right (Check ce) -> case checkExpValidity cc ac ce of
        Left tce -> do
          outputStr (typeCheckErrMsg tce)
          loop cc ac e
        Right e' -> do
          outputStrLn (okayMsg "expression type checked!")
          loop cc ac e'
      Right (CheckD cd) -> 
      Right (GetType ce) -> case checkExpValidity cc ac ce of
        Left tce -> do
          outputStr (typeCheckErrMsg tce)
          loop cc ac e
        Right e' -> do
          let e1 = typeOf ac e'
          outputStrLn $ infoMsg (show e1)
          loop cc ac e
      Right HeadRed -> do
        let e' = headRed ac e
        outputStrLn $ infoMsg (show e')
        loop cc ac e'
      Right ExpEval -> do
        let v = totalEval ac e
        outputStrLn $ infoMsg (show v)
      Right (Unfold xs) -> do
        let e' = unfold ac xs e
        outputStrLn $ infoMsg ("evaluate the current expression with the following definitions unlocked: " ++ show xs)
        outputStrLn $ infoMsg (show e')
        loop cc ac e'

usage :: InputT IO ()
usage = let msg = [ " Commands available from the prompt:"
                  , "   :h(elp), :?               show this usage message"
                  , "   :q(uit)                   exit"
                  , "   :s(how)                   show the content of the loaded file of the REPL context"
                  , "   :l(oad)  <file>           parse, type check and load a file, make it be the type checking"
                  , "                               context of the REPL context when successful"
                  , "   :c(heck) <exp>            type check an expression, let it be the new expression of the"
                  , "                               REPL context when successful"
                  , "   :hred                     apply head reduction on the expression of the REPL context, make"
                  , "                               the result to be the new expression in of the REPL context"
                  , "   :eval                     evaluate the current expression with all constants available"
                  , "   :u(nfold) [<variable>]    evaluate the expression in the context with the list of variables("
                  , "                               definitions) unlocked, make the reuslt be the new expression of the"
                  , "                               REPL context"
                  , "   :t <exp>                  get the type of an expression"
                  ]
        in outputStr (unlines msg)

loadFile :: FilePath -> IO (Either String (Context, Cont))
loadFile fp = do
  text <- readFile fp
  return $ parseCheckFile text
