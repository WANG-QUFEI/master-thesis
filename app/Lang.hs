{-|
Module          : Lang
Description     : Provides the syntax and semantics of the simple dependent typed language.
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Lang where

import qualified Data.HashMap.Lazy          as Map
import qualified Data.HashMap.Strict.InsOrd as OrdM
import           Data.Maybe                 (fromJust)

-- | == Basic Data types and Classes

-- |Type alias for String, referring to the names of variables and constants of the language.
type Name = String

-- |Type alias for a list of string which are used as names of segments.
-- These names together constitute the namespace for the names declared in the last segment.
-- Names in the top level scope have the empty string as their namespace.
type Namespace = [Name]

-- |Type alias for pairs (Exp, Name), which represent the expressions used to instantiate a segment
-- and the corresponding names of the declarations that are instantiated in the segment.
type ExPos = (Exp, Name)

-- |Reference to names with the presence of namespace
data Ref = Ref {rns :: Namespace, rid :: Name} deriving Eq

-- |Data type for expressions and quasi-expressions
data Exp = U                     -- ^ type of universe
         | Var Name              -- ^ name of a variable
         | SegVar Ref [ExPos]    -- ^ name of a variable withnin a instantiated segment
         | App Exp Exp           -- ^ function application
         | Abs Name Exp Exp      -- ^ function abstraction or dependent product type
         | Let Name Exp Exp Exp  -- ^ let clause. e.g. let x : a = b in e could be expressed as 'Let x a b e'
         | Clos Exp Env          -- ^ function closure.
         deriving Eq

-- |Quasi-expression: the intermediate form of an expression during computation.
type QExp = Exp

-- |Data type for declarations
data Decl = Dec Name Exp             -- ^ declaration of a variable with its type
          | Def Name Exp Exp         -- ^ definition of a constant
          | Seg Name [Decl]          -- ^ declaration of a segment
          | SegInst Name Ref [ExPos] -- ^ declaration of a segment instantiation
          deriving Eq

-- |A context node keeps either (1) the type or definition of a constant or (2) a context of a sub-segment
data CNode = Ct Exp                             -- ^ node that keeps the type of a constant
           | Cd Exp Exp                         -- ^ node that keeps the definition of a constant
           | Cs (OrdM.InsOrdHashMap Name CNode) -- ^ node that keeps the context of a segment
          deriving Eq

-- |An environment node keeps either (1) the value or definition of a constant or (2) an environment of a sub-segment
data ENode = Ev QExp    -- ^ a node that keeps the value of a constant
           | Ed Exp Exp -- ^ a node that keeps the definition of a constant
           | Es (Map.HashMap Name ENode) -- ^ note that keeps the environment of a segment
          deriving Eq

-- |Type checking context, storing a map of Nodes
data Cont = Cont {
  cns     :: Namespace, -- ^ namespace of the context
  mapCont :: OrdM.InsOrdHashMap Name CNode
  } deriving Eq

-- |Evaluation environment
data Env  = Env {
  ens    :: Namespace,  -- ^ namespace of the environment
  mapEnv :: Map.HashMap Name ENode
  } deriving Eq

class SegNest a where
  matchSeg :: Name -> a -> Maybe a

class InformativeError e where
  explain :: e -> [Name]

-- | == Basic Operations

-- |Map a function over the first element of a tuple
mfst :: (a -> b) -> (a, c) -> (b, c)
mfst f (a, c) = (f a, c)

-- |Map a function over the second element of a tuple
msnd :: (c -> d) -> (a, c) -> (a, d)
msnd f (a, c) = (a, f c)

-- |Get the string representation of a namespace
strnsp :: Namespace -> String
strnsp []  = "_root_"
strnsp [x] = x
strnsp ns  = foldr1 (\a b -> a ++ "." ++ b) ns

-- |Show reference in the form of a qualifed name
showRef :: Ref -> String
showRef ref = qualifiedName (rns ref) (rid ref)

-- |Get a value of Ref by a list of reversed names
buildRef :: [Name] -> Ref
buildRef []     = error "error: buildRef"
buildRef [x]    = Ref [] x
buildRef (x:xs) = Ref (reverse xs) x

-- |Get an empty context
emptyCont :: Namespace -> Cont
emptyCont ns = Cont ns OrdM.empty

-- |Get an empty environment
emptyEnv :: Namespace -> Env
emptyEnv ns = Env ns Map.empty

-- |Transform a CNode that represents a segment into a value of context
nodeToCont :: Namespace -> CNode -> Cont
nodeToCont ns (Cs cm) = Cont ns cm
nodeToCont _ _        = error "error: nodeToCont"

-- |A predicate checking whether a context node represents a segment
pSegnode :: CNode -> Bool
pSegnode Cs {} = True
pSegnode _     = False

-- |Get segment by a reversed path
findSeg :: SegNest a => a -> Namespace -> a
findSeg = foldr (\name a -> fromJust (matchSeg name a))

-- |Get the qualified form of a name with its namespace prepended.
qualifiedName :: Namespace -> Name -> Name
qualifiedName _ "" = ""
qualifiedName ns x = foldr (\a b -> a ++ "." ++ b) x ns

-- |Extend the environment by binding a variable with a q-expression
-- Do nothing if the variable is a 'dummy variable' (with an empty name)
bindEnvQ :: Env -> Name -> QExp -> Env
bindEnvQ r "" _ = r
bindEnvQ r x  q =
  let v = Ev q
  in r {mapEnv = Map.insert x v (mapEnv r)}

-- |Extend the environment with a constant definition
bindEnvD :: Env -> Name -> Exp -> Exp -> Env
bindEnvD r x a b =
  let v = Ed a b
  in r {mapEnv = Map.insert x v (mapEnv r)}

-- |Extend the environment with a sub-segment
bindEnvS :: Env -> Name -> ENode -> Env
bindEnvS r x es@Es {} = r {mapEnv = Map.insert x es (mapEnv r)}
bindEnvS _ _ _        = error "error: bindEnvS"

-- |Extend the type checking context with a variable and its type
-- Do nothing if the variable is a 'dummy variable' (with an empty name)
bindConT :: Cont -> Name -> Exp -> Cont
bindConT c "" _ = c
bindConT c x  t =
  let v = Ct t
  in c {mapCont = OrdM.insert x v (mapCont c)}

-- |Extend the type checking context with a constant definition
bindConD :: Cont -> Name -> Exp -> Exp -> Cont
bindConD c x a b =
  let v = Cd a b
  in c {mapCont = OrdM.insert x v (mapCont c)}

-- |Extend the type checking context with a context of segment
bindConS :: Cont -> Name -> CNode -> Cont
bindConS c x cs@Cs {} = c {mapCont = OrdM.insert x cs (mapCont c)}
bindConS _ _ _        = error "error: bindConS"

-- |Get the type of a variable from a context
getType :: Cont -> Name -> Exp
getType c x =
  let mn = OrdM.lookup x (mapCont c)
  in case fromJust mn of
    Ct t   -> t
    Cd t _ -> t
    Cs {}  -> error "error: getType"

-- |Get the definition of a variable from a context
getDef :: Cont -> Name -> Exp
getDef c x =
  let mn = OrdM.lookup x (mapCont c)
  in case fromJust mn of
    Ct _   -> Var x
    Cd _ d -> d
    Cs _   -> error "error: getDef"

-- |Get the definition of a variable from an environment
getDef' :: Env -> Name -> Exp
getDef' r x =
  case Map.lookup x (mapEnv r) of
    Nothing       -> Var x
    Just (Ed _ d) -> d
    _             -> error "error: getDef'"

-- |Get the names of a type checking context (excluding the potential sub-segments)
namesCont :: Cont -> [Name]
namesCont (Cont _ cm) = OrdM.keys cm

-- |Generate a fresh name based on a list of names
freshVar :: Name -> [Name] -> Name
freshVar x xs
  | x `elem` xs = freshVar (x ++ "'") xs
  | x == "" = freshVar "_x" xs
  | otherwise = x

-- |Split a context by the name of a declaration
splitCont :: Name -> Cont -> Cont
splitCont x c =
  let ns = cns c
      ls = OrdM.toList (mapCont c)
      ls' = takeWhile (\(x', _) -> x' /= x) ls
  in Cont ns (OrdM.fromList ls')

-- |A wrapper for error message
errorMsg :: String -> String
errorMsg s = "\10006 " ++ s

-- |A wrapper for affirmative message
okayMsg :: String -> String
okayMsg s = "\10004 " ++ s

-- |A wrapper for normal message
infoMsg :: String -> String
infoMsg = id

-- | == Implementations for Various Classes instances

prec :: Int
prec = 10

instance Show Exp where
  showsPrec _ U       = showString "*"
  showsPrec _ (Var x) = showString x
  showsPrec _ (SegVar ref [])  = showString $ showRef ref
  showsPrec p (SegVar ref eps) = showParen (p > prec) $ showString (strnsp (rns ref)) . showString " " .
                                 showList (map fst eps) . showString " . " . showString (rid ref)
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
  showsPrec _ (Clos e _) = showParen True $ showsPrec prec e . showString "(...)"

instance Show Decl where
  showsPrec _ d = showIndentD 0 d

-- |Show declarations with indentation
showIndentD :: Int   -- ^ The number of spaces to be indented from the left
                   -> Decl  -- ^ The declaration to be showed
                   -> ShowS
showIndentD n d =
  let indent = replicate n ' '
      n' = n + 2
  in case d of
    Dec x a   -> showString indent . showString (x ++ " : ") . showsPrec prec a
    Def x a b -> showString indent . showString (x ++ " : ") . showsPrec prec a . showString " = " . showsPrec prec b
    Seg x ds  -> let sub = foldr1 (.) (map (showIndentD n') ds)
                 in showString indent . showString (x ++ " = seg {\n") . sub . showString ("\n" ++ indent ++ "}")
    SegInst x ref eps -> showString indent . showString (x ++ " = ") . showString (showRef ref) .
                         showString " " . showList (map fst eps)

instance Show Cont where
  showsPrec _ c =
    let ds  = restoreCont c
        dss = map (showIndentD 0) ds
        dsn = map (\s -> s . showString "\n") dss
    in foldr (.) (showString "") dsn

-- |Restore a cont to a list of declarations
restoreCont :: Cont -> [Decl]
restoreCont (Cont ns cm) =
  if OrdM.null cm
  then []
  else OrdM.foldrWithKey restoreCNode [] cm
  where
    restoreCNode :: Name -> CNode -> [Decl] -> [Decl]
    restoreCNode x (Ct a) ds = Dec x a : ds
    restoreCNode x (Cd a b) ds = Def x a b : ds
    restoreCNode x (Cs cnm) ds =
      let ds' = restoreCont (Cont (ns ++ [x]) cnm)
      in Seg x ds' : ds

instance SegNest Cont where
  matchSeg x (Cont ns cm) =
    case OrdM.lookup x cm of
      Just (Cs m) -> Just $ Cont (ns ++ [x]) m
      _           -> Nothing

instance SegNest Env where
  matchSeg x (Env ns em) =
    case Map.lookup x em of
      Just (Es m) -> Just $ Env (ns ++ [x]) m
      _           -> Nothing

-- | == Evaluation Functions

-- |Evaluate an expression into a quasi-expression under a given environment
eval :: Env  -- ^ the local environment
     -> Exp  -- ^ the expression to be evaluated
     -> QExp
eval _ U                = U
eval r (Var x)          = valueOf r x
eval r (SegVar ref eps) =
  let r' = segEnv r (reverse $ rns ref) eps
  in eval r' (Var $ rid ref)
eval r (App e1 e2)   = appVal (eval r e1) (eval r e2)
eval r e@Abs {}      = Clos e r
eval r (Let x a b e) = let r' = bindEnvD r x a b in eval r' e
eval _ q@Clos {}     = q

-- |Get the quasi-expression bound to a variable.
valueOf :: Env  -- ^ the local environment
        -> Name -- ^ name of the variable
        -> QExp
valueOf r x =
  case Map.lookup x (mapEnv r) of
    Nothing       -> Var (qualifiedName (ens r) x)
    Just (Ev q)   -> q
    Just (Ed _ e) -> eval r e
    Just _        -> error "error: valueOf"

-- |Rules for function application
appVal :: QExp -> QExp -> QExp
appVal q1 q2 = case q1 of
  Clos (Abs x _ e) r -> let r' = bindEnvQ r x q2 in eval r' e
  _                  -> App q1 q2

-- |Get the environment of an instantiated segment
segEnv :: Env -> Namespace -> [ExPos] -> Env
segEnv r ps eps =
  let qps = map (mfst $ eval r) eps
      r' = findSeg r ps
  in foldr (\(q, n) r0 -> bindEnvQ r0 n q) r' qps

-- -- |Instantiate a segment with expressions
-- instSeg :: Cont -> Seg -> Cont
-- instSeg c sg =
--   let (sg', ips) = breakSeg sg
--       r = getEnv LockNone c
--       qps = map (mfst $ eval r) ips
--       rpath = revSegPath sg'
--       c' = findSeg c rpath
--   in foldr g c' qps
--   where g :: (QExp, Name) -> Cont -> Cont
--         g (q, x) cont =
--           let Just (Ct t) = OrdM.lookup x (mapCont cont)
--           in bindConD cont x t q
