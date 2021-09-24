{-|
Module          : Lang
Description     : Provides the syntax and semantics of the simple dependent typed language
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Lang where

import           Core.Abs

-- | abstract syntax for expressions, extended with closure as values
data Exp = U
         | Var String
         | App Exp Exp
         | Abs Decl Exp
         | Clos Exp Env
         deriving (Eq)

-- | the syntax for 'Exp' is also used as value in this language
type QExp = Exp

-- | abstract syntax for declarations
data Decl = Dec String Exp | Def String Exp Exp deriving (Eq)

-- | environment that relates a variable to a value
data Env = ENil
         | EConsVar Env String QExp
         | EConsDef Env String Exp Exp
         deriving (Eq, Show)

-- | context that relates a variable to a type
data Cont = CNil
          | CConsVar Cont String Exp
          | CConsDef Cont String Exp Exp
          deriving (Eq)

-- | an abstract context for a loaded source file
type AbsContext = [Decl]

-- | constants used to control the 'show' behaviour
pBar, pLow, pHigh :: Int
pBar  = 1
pLow  = pBar - 1
pHigh = pBar + 1

instance Show Cont where
  showsPrec _ CNil = showString ""
  showsPrec p (CConsVar CNil x a) = showString x . showString " : " . showsPrec p a
  showsPrec p (CConsDef CNil x a b) = showString x . showString " : " . showsPrec p a . showString " = " . showsPrec p b
  showsPrec p (CConsVar c x a) = showsPrec p c . showString "\n" . showString x . showString " : " . showsPrec p a
  showsPrec p (CConsDef c x a b) = showsPrec p c . showString "\n" . showString x . showString " : " . showsPrec p a . showString " = " . showsPrec p b

instance Show Exp where
  showsPrec p e = showParen (p > pBar) se
    where
      se :: ShowS
      se = case e of
        U -> showString "*"
        Var x -> showString x
        App e1 e2 ->
          let p1 = case e1 of
                     U       -> pLow
                     Var _   -> pLow
                     App _ _ -> pLow
                     _       -> pHigh
              p2 = case e2 of
                     U     -> pLow
                     Var _ -> pLow
                     _     -> pHigh
          in showsPrec p1 e1 . showString " " . showsPrec p2 e2
        Abs (Dec "" a) e' -> case a of
                              Abs _ _ -> showsPrec pHigh a . showString " -> " . showsPrec pLow e'
                              _       -> showsPrec pLow a . showString " -> " . showsPrec pLow e'
        Abs d@(Dec _ _) e'  -> showString "[ " . showsPrec pBar d . showString " ] " . showsPrec pLow e'
        Abs d@Def {} e' -> showString "[ " . showsPrec pBar d . showString " ] " . showsPrec pLow e'
        Clos e' _ -> showParen True (showsPrec pLow e') . showString "(..)"

instance Show Decl where
  showsPrec _ d = case d of
    Dec "" a  -> showsPrec pBar a
    Dec x a   -> showString (x ++ " : ") . showsPrec pBar a
    Def x a e -> showString (x ++ " : ") . showsPrec pBar a . showString " = " . showsPrec pBar e

-- | string of an id
idStr :: Id -> String
idStr (Id (_, s)) = s

-- | position of an id
idPos :: Id -> (Int, Int)
idPos (Id (pos, _)) = pos

-- | evaluate an expression in a given environment
eval :: Exp -> Env -> QExp
eval e r = case e of
  U                  -> U
  Var x              -> getVal r x
  App e1 e2          -> appVal (eval e1 r) (eval e2 r)
  Abs Dec {} _       -> Clos e r
  Abs (Def x a b) e' -> eval e' (EConsDef r x a b)
  Clos _ _           -> e

-- | get the value of a variable from an environment
getVal :: Env -> String -> QExp
getVal ENil x = Var x
getVal (EConsVar r x' v) x
  | x == x'   = v
  | otherwise = getVal r x
getVal (EConsDef r x' _ e) x
  | x == x'   = eval e r
  | otherwise = getVal r x

-- | application operation on values
appVal :: QExp -> QExp -> QExp
appVal v1 v2 = case v1 of
  Clos (Abs (Dec x _) e) r -> eval e (consEVar r x v2)
  _                        -> App v1 v2

-- | get the type of a variable in a given context
getType :: Cont -> String -> Maybe Exp
getType CNil _ = Nothing
getType (CConsVar c x' t) x
  | x' == x = Just t
  | otherwise = getType c x
getType (CConsDef c x' t _) x
  | x' == x = Just t
  | otherwise = getType c x

-- | extend an environment with a variable and its value
consEVar :: Env -> String -> QExp -> Env
consEVar r "" _ = r
consEVar r x v  = EConsVar r x v

-- | extend a type-checking context with a variable and its type
consCVar :: Cont -> String -> Exp -> Cont
consCVar c "" _ = c
consCVar c x t  = CConsVar c x t

-- | get all variables of a context
namesCont :: Cont -> [String]
namesCont CNil               = []
namesCont (CConsVar c x _)   = reverse (x : namesCont c)
namesCont (CConsDef c x _ _) = reverse (x : namesCont c)

-- | generate a fresh name based on a list of names
freshVar :: String -> [String] -> String
freshVar x xs
  | x `elem` xs = freshVar (x ++ "'") xs
  | x == "" = freshVar "var" xs
  | otherwise = x
