{-|
Module          : MessageHelper
Description     : provides functions for the prettier display of messages
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module MessageHelper
  ( errorMsg
  , okayMsg
  , infoMsg
  , typeCheckErrMsg
  ) where

import           Base

errorMsg :: String -> String
errorMsg s = "\10006 " ++ s

okayMsg :: String -> String
okayMsg s = "\10004 " ++ s

typeCheckErrMsg :: TypeCheckError -> String
typeCheckErrMsg tce = let ss = "type check failed!" : (errorText tce)
                      in unlines (map errorMsg ss)

infoMsg :: String -> String
infoMsg = id
