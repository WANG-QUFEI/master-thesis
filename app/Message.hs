{-|
Module          : MessageHelper
Description     : provides functions for the prettier display of messages
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Message
  ( errorMsg
  , okayMsg
  , infoMsg
  ) where

errorMsg :: String -> String
errorMsg s = "\10006 " ++ s

okayMsg :: String -> String
okayMsg s = "\10004 " ++ s

infoMsg :: String -> String
infoMsg = id
