{-# LANGUAGE CPP #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-- | Pretty-printer for Core.
--   Generated by the BNF converter.

module Core.Print where

import qualified Core.Abs
import Data.Char

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 (map ($ "") $ d []) "" where
  rend i ss = case ss of
    "["      :ts -> showChar '[' . rend i ts
    "("      :ts -> showChar '(' . rend i ts
    "{"      :ts -> showChar '{' . new (i+1) . rend (i+1) ts
    "}" : ";":ts -> new (i-1) . space "}" . showChar ';' . new (i-1) . rend (i-1) ts
    "}"      :ts -> new (i-1) . showChar '}' . new (i-1) . rend (i-1) ts
    [";"]        -> showChar ';'
    ";"      :ts -> showChar ';' . new i . rend i ts
    t  : ts@(p:_) | closingOrPunctuation p -> showString t . rend i ts
    t        :ts -> space t . rend i ts
    _            -> id
  new i     = showChar '\n' . replicateS (2*i) (showChar ' ') . dropWhile isSpace
  space t s =
    case (all isSpace t', null spc, null rest) of
      (True , _   , True ) -> []              -- remove trailing space
      (False, _   , True ) -> t'              -- remove trailing space
      (False, True, False) -> t' ++ ' ' : s   -- add space if none
      _                    -> t' ++ s
    where
      t'          = showString t []
      (spc, rest) = span isSpace s

  closingOrPunctuation :: String -> Bool
  closingOrPunctuation [c] = c `elem` closerOrPunct
  closingOrPunctuation _   = False

  closerOrPunct :: String
  closerOrPunct = ")],;"

parenth :: Doc -> Doc
parenth ss = doc (showChar '(') . ss . doc (showChar ')')

concatS :: [ShowS] -> ShowS
concatS = foldr (.) id

concatD :: [Doc] -> Doc
concatD = foldr (.) id

replicateS :: Int -> ShowS -> ShowS
replicateS n f = concatS (replicate n f)

-- | The printer class does the job.

class Print a where
  prt :: Int -> a -> Doc
  prtList :: Int -> [a] -> Doc
  prtList i = concatD . map (prt i)

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt = prtList

instance Print Char where
  prt _ s = doc (showChar '\'' . mkEsc '\'' s . showChar '\'')
  prtList _ s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q s = case s of
  _ | s == q -> showChar '\\' . showChar s
  '\\'-> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  _ -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print Core.Abs.Id where
  prt _ (Core.Abs.Id (_,i)) = doc $ showString $ i

instance Print Core.Abs.Context where
  prt i e = case e of
    Core.Abs.Ctx cdecls -> prPrec i 0 (concatD [prt 0 cdecls])

instance Print Core.Abs.CExp where
  prt i e = case e of
    Core.Abs.CU -> prPrec i 2 (concatD [doc (showString "*")])
    Core.Abs.CVar id -> prPrec i 2 (concatD [prt 0 id])
    Core.Abs.CApp cexp1 cexp2 -> prPrec i 1 (concatD [prt 1 cexp1, prt 2 cexp2])
    Core.Abs.CArr cexp1 cexp2 -> prPrec i 0 (concatD [prt 1 cexp1, doc (showString "->"), prt 0 cexp2])
    Core.Abs.CPi id cexp1 cexp2 -> prPrec i 0 (concatD [doc (showString "["), prt 0 id, doc (showString ":"), prt 0 cexp1, doc (showString "]"), prt 0 cexp2])
    Core.Abs.CWhere id cexp1 cexp2 cexp3 -> prPrec i 0 (concatD [doc (showString "["), prt 0 id, doc (showString ":"), prt 0 cexp1, doc (showString "="), prt 0 cexp2, doc (showString "]"), prt 0 cexp3])

instance Print Core.Abs.CDecl where
  prt i e = case e of
    Core.Abs.CDec id cexp -> prPrec i 0 (concatD [prt 0 id, doc (showString ":"), prt 0 cexp])
    Core.Abs.CDef id cexp1 cexp2 -> prPrec i 0 (concatD [prt 0 id, doc (showString ":"), prt 0 cexp1, doc (showString "="), prt 0 cexp2])
  prtList _ [] = concatD []
  prtList _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print [Core.Abs.CDecl] where
  prt = prtList

