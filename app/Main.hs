{-|
Module          : Main
Description     : Entry point of the program
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Main (main) where

import REPL

main :: IO ()
main = evalStateT repl defaultReplState
