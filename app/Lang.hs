{-|
Module          : Lang
Description     : Provides the syntax and semantics of the simple dependent typed language
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Lang where

-- | type alias of 'String', referring to the names of variables and constants of the language
type Name = String

-- | syntax for expressions and quasi-expressions
data Exp = U                              -- ^ universe of small types
         | Var Name                       -- ^ variables or constants
         | SegVar Seg Name                -- ^ variables or constants in a segment
         | App Exp Exp                    -- ^ function application
         | Abs Name Exp Exp               -- ^ function abstraction or dependent pi type
         | Let Name Exp Exp Exp           -- ^ a let clause, e.g. let x = a in b
         | Closure Exp Env                -- ^ function closure

-- | quasi-expressions
type QExp = Exp

-- | syntax for declarations
data Decl = Dec Name Exp                  -- ^ a declaration of a variable with its type
          | Def Name Exp Exp              -- ^ a definition of a constant
          | DSeg Name Seg                 -- ^ a declaration of a segment

-- | syntax for segments
data Seg = SDef [Decl]                     -- ^ a segment is defined as a list of declarations
         | SRef Name                       -- ^ a segment could be referenced by a name
         | SInst Seg [Exp]                 -- ^ a segment could be instantiated by a list of expressions
         | SNest Seg Name                  -- ^ a segment could be declared into another segment

-- | syntax for environment
data Env = ENil                            -- ^ an empty environment
         | EConsVar Env Name QExp          -- ^ an environment extended with a constant and its binding expression
         | EConsDef Env Name Exp Exp       -- ^ an environment extended with the definition of a constant
         | EConsSeg Env Name Env           -- ^ an environment extended with a segment, the declarations within the segment form a nested
                                           ---  environment
-- | type checking context
data Cont = CNil                           -- ^ an empty context
          | CConsVar Cont Name Exp         -- ^ a context extended with a constant and its type
          | CConsDef Cont Name Exp Exp     -- ^ a context extended with the definition of a constant
          | CConsSeg Cont Name Cont        -- ^ a context extended with a segment, the declarations within the segment form a nested context

-- | an abstract context for a loaded source file
type AbsContext = [Decl]

prec :: Int
prec = 10

instance Show Exp where
  showsPrec _ U = showString "*"
  showsPrec _ (Var x) = showString x
  showsPrec p (SegVar seg x) = showParen (p > prec) $ showsPrec p seg . showString " . " . showString x
  showsPrec p (App e1 e2) =
    let p1 = case e1 of
               U       -> prec
               Var _   -> prec
               App _ _ -> prec
               _       -> prec + 1
        p2 = case e2 of
               U     -> prec
               Var _ -> prec
               _     -> prec + 1
    in showParen (p > prec) $ showsPrec p1 e1 . showString " " . showsPrec p2 e2
  showsPrec p (Abs "" a e) =
    let s' = case a of
               _a@Abs {} -> showsPrec (prec + 1) a . showString " -> " . showsPrec prec e
               _         -> showsPrec prec a . showString " -> " . showsPrec prec e
    in showParen (p > prec) s'
  showsPrec p (Abs x a e) = showParen (p > prec) $ showString "[ " . showsPrec p (Dec x a) . showString " ] " . showsPrec prec e
  showsPrec p (Let x a b e) = showParen (p > prec) $ showString "[ " . showsPrec p (Def x a b) . showString " ] " . showsPrec prec e
  showsPrec _ (Closure e _) = showParen True $ showsPrec prec e . showString "(...)"

instance Show Decl where
  showsPrec _ d = showDeclWithLayout 0 d

instance Show Seg where
  showsPrec _ s = showSegWithLayout 0 s

-- | show declaration with indentation
-- @param{n} : number of spaces as indentation
-- @param{d} : a declaration
showDeclWithLayout :: Int -> Decl -> ShowS
showDeclWithLayout n d =
  let ss = case d of
             Dec x a -> showString (x ++ " : ") . showsPrec prec a
             Def x a e -> showString (x ++ " : ") . showsPrec prec a . showString " = " . showsPrec prec e
             DSeg x seg -> showString (x ++ " = ") . showSegWithLayout (n + 2) seg
  in showString (replicate n ' ') . ss

-- | show segment with indentation
-- @param{n} : number of spaces as indentation
-- @param{d} : a segment
showSegWithLayout :: Int -> Seg -> ShowS
showSegWithLayout n seg = case seg of
  SDef ds -> let dss  = map (showDeclWithLayout n) ds
                 dss' = map (\s -> s . showString "\n") dss
                 ss   = foldr (.) (showString "") dss'
             in showString "seg {\n" . ss . showString (replicate (n - 2) ' ') . showString "}"
  SRef x  -> showString x
  SInst seg' es -> showSegWithLayout n seg' . showString " " . showList es
  SNest seg' x  -> showSegWithLayout n seg' . showString " . " . showString x

-- -- | string of an id
-- idStr :: Id -> String
-- idStr (Id (_, s)) = s

-- -- | position of an id
-- idPos :: Id -> (Int, Int)
-- idPos (Id (pos, _)) = pos

-- -- | evaluate an expression in a given environment
-- eval :: Exp -> Env -> Val
-- eval e r = case e of
--   U                  -> U
--   Var x              -> getVal r x
--   App e1 e2          -> appVal (eval e1 r) (eval e2 r)
--   Abs Dec {} _       -> Clos e r
--   Abs (Def x a b) e' -> eval e' (EConsDef r x a b)
--   Clos _ _           -> e

-- -- | get the value of a variable from an environment
-- getVal :: Env -> String -> Val
-- getVal ENil x = Var x
-- getVal (EConsVar r x' v) x
--   | x == x'   = v
--   | otherwise = getVal r x
-- getVal (EConsDef r x' _ e) x
--   | x == x'   = eval e r
--   | otherwise = getVal r x

-- -- | application operation on values
-- appVal :: Val -> Val -> Val
-- appVal v1 v2 = case v1 of
--   Clos (Abs (Dec x _) e) r -> eval e (consEVar r x v2)
--   _                        -> App v1 v2

-- -- | get the type of a variable in a given context
-- getType :: Cont -> String -> Maybe Exp
-- getType CNil _ = Nothing
-- getType (CConsVar c x' a) x
--   | x' == x = Just a
--   | otherwise = getType c x
-- getType (CConsDef c x' a _) x
--   | x' == x = Just a
--   | otherwise = getType c x

-- -- | extend an environment with a variable and its value
-- consEVar :: Env -> String -> Val -> Env
-- consEVar r "" _ = r
-- consEVar r x v  = EConsVar r x v

-- -- | extend a type-checking context with a variable and its type
-- consCVar :: Cont -> String -> Val -> Cont
-- consCVar c "" _ = c
-- consCVar c x t  = CConsVar c x t

-- -- | get all variables of a context
-- varsCont :: Cont -> [String]
-- varsCont CNil               = []
-- varsCont (CConsVar c x _)   = reverse (x : varsCont c)
-- varsCont (CConsDef c x _ _) = reverse (x : varsCont c)

-- -- | generate a fresh name based on a list of names
-- freshVar :: String -> [String] -> String
-- freshVar x xs
--   | x `elem` xs = freshVar (x ++ "'") xs
--   | x == "" = freshVar "var" xs
--   | otherwise = x
