{-|
Module          : REPL
Description     : A REPL command line tool for the use of this simple dependently typed language
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module REPL
  ( module Control.Monad.State
  , ReplState
  , defaultReplState
  , repl
  , ) where

import Control.Monad.State
import System.IO
import System.Console.ANSI

import Core.Abs
import Base

type StateIO s a = StateT s IO a

data ReplState = Rs { buffer   :: [Char]         -- ^ buffer and react to the user's input
                    , history  :: [String]       -- ^ user's command history
                    , cctx     :: Context        -- ^ concrete context related with the current loaded file
                    , actx     :: Cont           -- ^ abstract context realted with the current loaded file
                    , e        :: Exp            -- ^ abstract expression used to operate on
                    } deriving (Show)

maxBufferSize = 10240

defaultReplState = Rs {buffer = [], history = [], cctx = Ctx [], actx = CNil, e = U}
  
repl :: StateIO ReplState ()
repl = do
  liftIO (putStrLn "~~~ Welcome, type ':?' for help, ':q' to quit ~~~")
  liftIO (hSetBuffering stdin NoBuffering >> hSetBuffering stdout NoBuffering)
  s <- get
  c <- liftIO (prompt s)
  return ()

prompt :: ReplState -> IO (String, ReplState)
prompt s = do
  putStr "\955> "
  hFlush stdout
  hInput s

hInput :: ReplState -> IO (String, ReplState)
hInput s = do
  ch <- getChar
  undefined
