{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
#if __GLASGOW_HASKELL__ <= 708
{-# LANGUAGE OverlappingInstances #-}
#endif

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

-- | Pretty-printer for Core.
--   Generated by the BNF converter.

module Core.Print where

import Prelude
  ( ($), (.)
  , Bool(..), (==), (<)
  , Int, Integer, Double, (+), (-), (*)
  , String, (++)
  , ShowS, showChar, showString
  , all, elem, foldr, id, map, null, replicate, shows, span
  )
import Data.Char ( Char, isSpace )
import qualified Core.Abs

-- | The top-level printing method.

printTree :: Print a => a -> String
printTree = render . prt 0

type Doc = [ShowS] -> [ShowS]

doc :: ShowS -> Doc
doc = (:)

render :: Doc -> String
render d = rend 0 False (map ($ "") $ d []) ""
  where
  rend
    :: Int        -- ^ Indentation level.
    -> Bool       -- ^ Pending indentation to be output before next character?
    -> [String]
    -> ShowS
  rend i p = \case
      "["      :ts -> char '[' . rend i False ts
      "("      :ts -> char '(' . rend i False ts
      "{"      :ts -> onNewLine i     p . showChar   '{'  . new (i+1) ts
      "}" : ";":ts -> onNewLine (i-1) p . showString "};" . new (i-1) ts
      "}"      :ts -> onNewLine (i-1) p . showChar   '}'  . new (i-1) ts
      [";"]        -> char ';'
      ";"      :ts -> char ';' . new i ts
      t  : ts@(s:_) | closingOrPunctuation s
                   -> pending . showString t . rend i False ts
      t        :ts -> pending . space t      . rend i False ts
      []           -> id
    where
    -- Output character after pending indentation.
    char :: Char -> ShowS
    char c = pending . showChar c

    -- Output pending indentation.
    pending :: ShowS
    pending = if p then indent i else id

  -- Indentation (spaces) for given indentation level.
  indent :: Int -> ShowS
  indent i = replicateS (2*i) (showChar ' ')

  -- Continue rendering in new line with new indentation.
  new :: Int -> [String] -> ShowS
  new j ts = showChar '\n' . rend j True ts

  -- Make sure we are on a fresh line.
  onNewLine :: Int -> Bool -> ShowS
  onNewLine i p = (if p then id else showChar '\n') . indent i

  -- Separate given string from following text by a space (if needed).
  space :: String -> ShowS
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

instance {-# OVERLAPPABLE #-} Print a => Print [a] where
  prt i = concatD . map (prt i)

instance Print Char where
  prt _ c = doc (showChar '\'' . mkEsc '\'' c . showChar '\'')

instance Print String where
  prt _ = printString

printString :: String -> Doc
printString s = doc (showChar '"' . concatS (map (mkEsc '"') s) . showChar '"')

mkEsc :: Char -> Char -> ShowS
mkEsc q = \case
  s | s == q -> showChar '\\' . showChar s
  '\\' -> showString "\\\\"
  '\n' -> showString "\\n"
  '\t' -> showString "\\t"
  s -> showChar s

prPrec :: Int -> Int -> Doc -> Doc
prPrec i j = if j < i then parenth else id

instance Print Integer where
  prt _ x = doc (shows x)

instance Print Double where
  prt _ x = doc (shows x)

instance Print Core.Abs.Id where
  prt _ (Core.Abs.Id (_,i)) = doc $ showString i
instance Print Core.Abs.Context where
  prt i = \case
    Core.Abs.Ctx cdecls -> prPrec i 0 (concatD [prt 0 cdecls])

instance Print Core.Abs.CExp where
  prt i = \case
    Core.Abs.CU -> prPrec i 2 (concatD [doc (showString "*")])
    Core.Abs.CVar id_ -> prPrec i 2 (concatD [prt 0 id_])
    Core.Abs.CESeg cseg id_ -> prPrec i 2 (concatD [doc (showString "("), prt 0 cseg, doc (showString ")"), doc (showString "."), prt 0 id_])
    Core.Abs.CApp cexp1 cexp2 -> prPrec i 1 (concatD [prt 1 cexp1, prt 2 cexp2])
    Core.Abs.CArr cexp1 cexp2 -> prPrec i 0 (concatD [prt 1 cexp1, doc (showString "->"), prt 0 cexp2])
    Core.Abs.CPi id_ cexp1 cexp2 -> prPrec i 0 (concatD [doc (showString "["), prt 0 id_, doc (showString ":"), prt 0 cexp1, doc (showString "]"), prt 0 cexp2])
    Core.Abs.CWhere id_ cexp1 cexp2 cexp3 -> prPrec i 0 (concatD [doc (showString "["), prt 0 id_, doc (showString ":"), prt 0 cexp1, doc (showString "="), prt 0 cexp2, doc (showString "]"), prt 0 cexp3])

instance Print Core.Abs.CDecl where
  prt i = \case
    Core.Abs.CDec id_ cexp -> prPrec i 0 (concatD [prt 0 id_, doc (showString ":"), prt 0 cexp])
    Core.Abs.CDef id_ cexp1 cexp2 -> prPrec i 0 (concatD [prt 0 id_, doc (showString ":"), prt 0 cexp1, doc (showString "="), prt 0 cexp2])
    Core.Abs.CDSeg id_ cseg -> prPrec i 0 (concatD [prt 0 id_, doc (showString "="), prt 0 cseg])

instance Print Core.Abs.CSeg where
  prt i = \case
    Core.Abs.CSegDecl cdecls -> prPrec i 0 (concatD [doc (showString "seg"), doc (showString "{"), prt 0 cdecls, doc (showString "}")])
    Core.Abs.CSegInsti id_ cexps -> prPrec i 0 (concatD [prt 0 id_, doc (showString "["), prt 0 cexps, doc (showString "]")])
    Core.Abs.CSegInstc cseg cexps -> prPrec i 0 (concatD [prt 0 cseg, doc (showString "["), prt 0 cexps, doc (showString "]")])
    Core.Abs.CSegSub cseg id_ -> prPrec i 0 (concatD [prt 0 cseg, doc (showString "."), prt 0 id_])

instance Print [Core.Abs.CDecl] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ";"), prt 0 xs]

instance Print [Core.Abs.CExp] where
  prt _ [] = concatD []
  prt _ [x] = concatD [prt 0 x]
  prt _ (x:xs) = concatD [prt 0 x, doc (showString ","), prt 0 xs]
