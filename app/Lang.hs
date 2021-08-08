{-|
Module          : Lang
Description     : Provides the syntax and semantics of the simple dependent typed language.
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Lang where

import qualified Data.HashMap.Strict.InsOrd as M
import           Text.Printf                (printf)

-- * BEGIN_SECTION: Basic Data types

-- |Type alias for String, referring to the names of variables and constants of the language.
type Name = String

-- |Type alias for a list of string which are used as names of segments.
-- These names together constitute the namespace for the names declared in the last segment.
-- Names in the top level scope have the empty string as their namespace.
type Namespace = [Name]

-- |Type alias for pairs (Exp, Name), which represents the expressions used to instantiate a segment
-- and the corresponding name of the declarations that are instantiated in the segment.
type InstPair = (Exp, Name)

type AbsContext = [Decl]

-- |Syntax for expressions and quasi-expressions
data Exp = U                    -- ^ The type of all small types. U is an element of itself.
         | Var Name             -- ^ A variable or constant.
         | SegVar Seg Name      -- ^ A variable of constant in a segment.
         | App Exp Exp          -- ^ Function application.
         | Abs Name Exp Exp     -- ^ Function abstraction or dependent product type.
         | Let Name Exp Exp Exp -- ^ A let clause. e.g. let x : a = b in e could be expressed as 'Let x a b e'.
         | Closure Exp (Env, Namespace)      -- ^ Function closure.
         deriving Eq

-- |Quasi-expression: the intermediate form of an expression during computation.
type QExp = Exp

-- |Syntax for declarations
data Decl = Dec Name Exp     -- ^ A declaration of a variable with its type.
          | Def Name Exp Exp -- ^ A definition of a constant.
          | DSeg Name Seg    -- ^ A declaration of a segment.
          deriving Eq

-- |Syntax for segments
data Seg = SRef Name            -- ^ A segment could be referenced by a name
         | SNest Seg Name       -- ^ A segment could be nested into another segment
         | SInst Seg [InstPair] -- ^ A segment could be instantiated by a list of expressions
         | SDef [Decl]          -- ^ A segment could be defined as a list of declarations
         deriving Eq

-- |Data structure for keeping the information (value/type) bound to a name.
data Node = Ne QExp                        -- ^ a quasi-expression bound to a name, either as value or type
          | Nd Exp Exp                     -- ^ a definition bound to a name
          | Ns (M.InsOrdHashMap Name Node) -- ^ the context bound to a segment
          deriving Eq

-- |Type checking context, storing a map of Nodes
newtype Cont = Cont { mapCont :: M.InsOrdHashMap Name Node } deriving Eq

-- |Evaluation context, similiar with Cont, storing a map of Nodes
newtype Env  = Env { mapEnv :: M.InsOrdHashMap Name Node } deriving Eq

-- * END_SECTION

-- * BEGIN_SECTION: functions for showing the basic data types

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

instance Show Cont where
  showsPrec _ c =
    let ds  = contToAbsCont c
        dss = map (showDeclWithLayout 0) ds
        dsn = map (\s -> s . showString "\n") dss
    in foldr (.) (showString "") dsn

-- |Show declarations with indentation.
showDeclWithLayout :: Int   -- ^ The number of spaces need to be indented from the left.
                   -> Decl  -- ^ The declaration to be showed.
                   -> ShowS
showDeclWithLayout n d =
  let ss = case d of
             Dec x a -> showString (x ++ " : ") . showsPrec prec a
             Def x a e -> showString (x ++ " : ") . showsPrec prec a . showString " = " . showsPrec prec e
             DSeg x seg -> showString (x ++ " = ") . showSegWithLayout (n + 2) seg
  in showString (replicate n ' ') . ss

-- |Show segments with indentation.
showSegWithLayout :: Int  -- ^ The number of spaces need to be indented from the left.
                  -> Seg  -- ^ The segment to be showed.
                  -> ShowS
showSegWithLayout n seg = case seg of
  SDef ds -> let dss  = map (showDeclWithLayout n) ds
                 dss' = map (\s -> s . showString "\n") dss
                 ss   = foldr (.) (showString "") dss'
             in showString "seg {\n" . ss . showString (replicate (n - 2) ' ') . showString "}"
  SRef x  -> showString x
  SInst seg' es -> showSegWithLayout n seg' . showString " " . showList es
  SNest seg' x  -> showSegWithLayout n seg' . showString " . " . showString x

-- |Restore a cont to a list of declarations
contToAbsCont :: Cont -> AbsContext
contToAbsCont (Cont c) =
  if M.null c
  then []
  else M.foldrWithKey nodeToAbsCont [] c

-- |Restore a node to a declaration
nodeToAbsCont :: Name -> Node -> AbsContext -> AbsContext
nodeToAbsCont x n p = case n of
  Ne a   -> Dec x a : p
  Nd a b -> Def x a b : p
  Ns m   -> let ac = contToAbsCont (Cont m)
                s = SDef ac
            in DSeg x s : p

-- * END_SECTION

-- * BEGIN_SECTION: auxiliary functions

isSegNode :: Node -> Bool
isSegNode Ns {} = True
isSegNode _     = False

-- |Construct a value of segment from a reverse ordered path
buildSegFromPath :: Namespace -> Seg
buildSegFromPath []   = error "empty namesapce"
buildSegFromPath [x]  = SRef x
buildSegFromPath (x:xs) =
  let s = buildSegFromPath xs
  in SNest s x

-- |Get the qualified form of a name with its namespace prepended.
getQualifiedName :: Namespace -> Name -> Name
getQualifiedName ns x = foldr (\a b -> a ++ "." ++ b) x ns

-- |Get the string representation of a namespace
namespaceStr :: Namespace -> String
namespaceStr []  = "(top level namespace)"
namespaceStr [x] = x
namespaceStr ns  = foldr1 (\a b -> a ++ "." ++ b) ns

-- |Extend the environment by binding a variable with an q-expression
-- Do nothing if the variable is a 'dummy variable' (with an empty name)
bindEnvQexp :: Env -> Name -> QExp -> Env
bindEnvQexp r "" _ = r
bindEnvQexp r x  q =
  let v = Ne q
  in Env $ M.insert x v (mapEnv r)

-- |Extend the environment with a constant definition
bindEnvDef :: Env -> Name -> Exp -> Exp -> Env
bindEnvDef r x a b =
  let v = Nd a b
  in Env $ M.insert x v (mapEnv r)

-- |Extend the type checking context with a variable and its type
bindContType :: Cont -> Name -> Exp -> Cont
bindContType c "" _ = c
bindContType c x  t =
  let v = Ne t
  in Cont $ M.insert x v (mapCont c)

-- | get the type of a variable in a given context
getType :: Cont -> Name -> Maybe Exp
getType c x = case M.lookup x (mapCont c) of
  Nothing       -> Nothing
  Just (Ne t)   -> Just t
  Just (Nd t _) -> Just t
  _             -> error "segment has no type"

-- |Get the top level names of a context
topLevelNamesCont :: Cont -> [Name]
topLevelNamesCont c = M.foldrWithKey
  (\k v a ->
      if not $ isSegNode v
      then k : a
      else a) [] (mapCont c)

-- |Generate a fresh name based on a list of names
freshVar :: String -> [String] -> String
freshVar x xs
  | x `elem` xs = freshVar (x ++ "'") xs
  | x == "" = freshVar "var" xs
  | otherwise = x

-- * END_SECTION

-- * BEGIN_SECTION: functions related with evaluation

-- |Evaluate an expression into a quasi-expression under a given local environment (a segment).
-- A global environment is not needed here because expressions in a local environment
-- are not allowed to refer to variables or constants out of its scope.
-- However, the namespace of the local environment is needed to clear off the ambiguity
-- caused by variables of the same name from different environments (segments).
eval :: Env       -- ^ the local environment
     -> Namespace -- ^ namespace to the local environment
     -> Exp       -- ^ the expression to be evaluated
     -> QExp
eval _ _  U             = U
eval r ns (Var x)       = getVal r ns x
eval r ns (SegVar s x)  = getSegVal r ns s x
eval r ns (App e1 e2)   = appVal (eval r ns e1) (eval r ns e2)
eval r ns e@Abs {}      = Closure e (r, ns)
eval r ns (Let x a b e) = let r' = bindEnvDef r x a b in eval r' ns e
eval _ _   q@Closure {} = q

-- |Get the quasi-expression bound to a variable.
getVal :: Env       -- ^ the local environment
       -> Namespace -- ^ namespace to the local environment
       -> Name      -- ^ name of the variable
       -> QExp
getVal r ns x =
  case M.lookup x (mapEnv r) of
    Nothing        -> Var (getQualifiedName ns x)
    Just (Ne q)    -> q
    Just (Nd _ e)  -> eval r ns e
    Just (Ns _)    -> error $ "cannot evaluate a segment with name: " ++ getQualifiedName ns x

-- |Get the quasi-expression bound to a constant in a segment.
getSegVal :: Env       -- ^ the local environment
          -> Namespace -- ^ namespace to the local environment
          -> Seg       -- ^ the segment to which the constant belongs
          -> Name      -- ^ name of the constant
          -> QExp
getSegVal rtop nsInit s var = case s of
  -- the segment 's' in this case must be in the form of 'SInst', this is
  -- imposed by the source code syntax of the language and checked by the lexer
  SInst s' ips ->
    let (rSeg, ns') = locateSeg rtop nsInit s'
        rSegNew     = instSeg rSeg ips
    in eval rSegNew ns' (Var var)
  _            -> error "syntax error"
  where
    -- ^ locate the segment from the local environment and return its path
    locateSeg :: Env -> Namespace -> Seg -> (Env, Namespace)
    locateSeg rho ns' s' = case s' of
      SRef n    -> (matchSegName rho n, ns' ++ [n])
      SNest {}  -> let sp   = reverse $ getSegPathReversed s'
                       rSeg = foldl matchSegName rho sp
                   in (rSeg, ns' ++ sp)
      _         -> error "syntax error"

    -- ^ match a segment with the given name in the environment
    matchSegName :: Env -> Name -> Env
    matchSegName rho n =
      case M.lookup n (mapEnv rho) of
        Just (Ns m) -> Env m
        _           -> error $ "cannot locate segment with name: " ++ n

    -- ^ for nested segment, get its relative path in reverse order
    getSegPathReversed :: Seg -> Namespace
    getSegPathReversed (SRef n)     = [n]
    getSegPathReversed (SNest s' n) = n : getSegPathReversed s'
    getSegPathReversed _            = error "syntax error"

    -- ^ instantiate a segment
    instSeg :: Env -> [InstPair] -> Env
    instSeg rho ips = foldl attachQexp rho ips

    -- ^ attach the name of a declaration with a quasi-expression as its definition
    attachQexp :: Env -> InstPair -> Env
    attachQexp rho (e, n) =
      case M.lookup n (mapEnv rho) of
        Nothing ->
          let q = eval rtop nsInit e              -- note that here we need to evaluate the binding expression in the top local environment
          in bindEnvQexp rho n q
        _       -> error $ printf "cannot instantiate variable, already bound with some term. Name: %s" n

-- |Rules for function application
appVal :: QExp -> QExp -> QExp
appVal q1 q2 = case q1 of
  Closure (Abs x _ e) (r, ns) -> let r' = bindEnvQexp r x q2 in eval r' ns e
  _                           -> App q1 q2

-- * END_SECTION
