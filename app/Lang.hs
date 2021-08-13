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
import           Data.Set                   (Set)
import qualified Data.Set                   as Set

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

class SegNest a where
  matchSeg :: Name -> a -> Maybe a

-- |Syntax for expressions and quasi-expressions
data Exp = U                    -- ^ The type of all small types. U is an element of itself.
         | Var Name             -- ^ A variable or constant.
         | SegVar Seg Name      -- ^ A variable of constant in a segment.
         | App Exp Exp          -- ^ Function application.
         | Abs Name Exp Exp     -- ^ Function abstraction or dependent product type.
         | Let Name Exp Exp Exp -- ^ A let clause. e.g. let x : a = b in e could be expressed as 'Let x a b e'.
         | Clos Exp Env      -- ^ Function closure.
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

-- |A context node keeps either (1) the type or definition of a constant or (2) a context of a sub-segment
data CNode = Ct Exp                                    -- ^ a node that keeps the type of a constant
           | Cd Exp Exp                                -- ^ a node that keeps the definition of a constant
           | Cs {csm :: OrdM.InsOrdHashMap Name CNode} -- ^ a node that keeps the context of a segment
          deriving Eq

-- |An environment node keeps the value (a quasi-expression) or definition of a constant
data ENode = Ev QExp    -- ^ a node that keeps the value of a constant
           | Ed Exp Exp -- ^ a node that keeps the definition of a constant
           | Es {esm :: Map.HashMap Name ENode}
          deriving Eq

-- |Type checking context, storing a map of Nodes
data Cont = Cont {
  cns     :: Namespace, -- ^ namespace of the context
  mapCont :: OrdM.InsOrdHashMap Name CNode -- ^ content of the context
  } deriving Eq

-- |Evaluation context
data Env  = Env {
  ens    :: Namespace,  -- ^ namespace of the environment
  mapEnv :: Map.HashMap Name ENode
  } deriving Eq

class InformativeError e where
  explain :: e -> [Name]

class LockStrategy s where
  -- ^ get environment from a type checking context
  getEnv           :: s -> Cont -> Env
  -- ^ add a list of names to be locked
  addLock          :: s -> [Name] -> s
  -- ^ remove a list of names to be locked
  removeLock       :: s -> [Name] -> s
  -- ^ get the names locked from the context
  getNamesLocked   :: s -> Cont -> [Name]
  -- ^ get the names unlocked from the context
  getNamesUnLocked :: s -> Cont -> [Name]

-- | A simple locking/unlocking strategy for constants
-- LockAll  : lock all constants
-- LockNone : lock none constants
-- LockList <varlist>   : a list of constants that are locked
-- UnLockList <varlist> : a list of constants that are unlocked
data SimpleLock = LockAll
                | LockNone
                | LockList [Name]
                | UnLockList [Name]
                deriving (Show)

instance LockStrategy SimpleLock where
  getEnv LockAll         = lockAll
  getEnv LockNone        = lockNone
  getEnv (LockList ls)   = locklist (Set.fromList ls)
  getEnv (UnLockList ls) = unlocklist (Set.fromList ls)

  addLock LockAll        _  = LockAll
  addLock LockNone       xs = LockList xs
  addLock (LockList xs') xs =
    let s1 = Set.fromList xs'
        s2 = Set.fromList xs
        s3 = Set.union s1 s2
    in LockList (Set.toList s3)
  addLock (UnLockList xs') xs =
    let s1 = Set.fromList xs'
        s2 = Set.fromList xs
        s3 = Set.difference s1 s2
    in UnLockList (Set.toList s3)

  removeLock LockAll xs = UnLockList xs
  removeLock LockNone _ = LockNone
  removeLock (LockList xs') xs =
    let s1 = Set.fromList xs'
        s2 = Set.fromList xs
        s3 = Set.difference s1 s2
    in LockList (Set.toList s3)
  removeLock (UnLockList xs') xs =
    let s1 = Set.fromList xs'
        s2 = Set.fromList xs
        s3 = Set.union s1 s2
    in UnLockList (Set.toList s3)

  getNamesLocked = lockedNames

  getNamesUnLocked = unlockedNames

lockAll :: Cont -> Env
lockAll (Cont ns cm) = OrdM.foldrWithKey g (emptyEnv ns) cm
  where g :: Name -> CNode -> Env -> Env
        g x cn@Cs {} r =
          let c' = nodeToCont (ns ++ [x]) cn
              r' = lockAll c'
              en = Es (mapEnv r')
          in bindEnvS r x en
        g _ _ r = r

lockNone :: Cont -> Env
lockNone (Cont ns cm) = OrdM.foldrWithKey g (emptyEnv ns) cm
  where g :: Name -> CNode -> Env -> Env
        g _ Ct {} r = r
        g x (Cd a b) r = bindEnvD r x a b
        g x cn@Cs {} r =
          let c' = nodeToCont (ns ++ [x]) cn
              r' = lockNone c'
              en = Es (mapEnv r')
          in bindEnvS r x en

locklist :: Set Name -> Cont -> Env
locklist lnames (Cont ns cm) = OrdM.foldrWithKey g (emptyEnv ns) cm
  where g :: Name -> CNode -> Env -> Env
        g _ Ct {} r = r
        g x (Cd a b) r =
          let x' = qualifiedName ns x
          in if Set.member x' lnames
             then r
             else bindEnvD r x a b
        g x cn@Cs {} r =
          let x' = qualifiedName ns x
              c' = nodeToCont (ns ++ [x]) cn
          in if Set.member x' lnames
             then let r' = lockAll c'
                      en = Es (mapEnv r')
                  in bindEnvS r x en
             else let r' = locklist lnames c'
                      en = Es (mapEnv r')
                  in bindEnvS r x en

unlocklist :: Set Name -> Cont -> Env
unlocklist unames (Cont ns cm) = OrdM.foldrWithKey g (emptyEnv ns) cm
  where g :: Name -> CNode -> Env -> Env
        g _ Ct {} r = r
        g x (Cd a b) r =
          let x' = qualifiedName ns x
          in if Set.notMember x' unames
             then r
             else bindEnvD r x a b
        g x cn@Cs {} r =
          let x' = qualifiedName ns x
              c' = nodeToCont (ns ++ [x]) cn
          in if Set.member x' unames
             then let r' = lockNone c'
                      en = Es (mapEnv r')
                  in bindEnvS r x en
             else let r' = unlocklist unames c'
                      en = Es (mapEnv r')
                  in bindEnvS r x en

lockedNames :: SimpleLock -> Cont -> [Name]
lockedNames LockAll c = allNames c
lockedNames LockNone _ = []
lockedNames ll@(LockList ls) (Cont ns cm) =
  let lnames = Set.fromList ls
  in OrdM.foldrWithKey (g lnames) [] cm
  where
    g :: Set Name -> Name -> CNode -> [Name] -> [Name]
    g names x v xs =
      let x' = qualifiedName ns x
      in if pSegnode v
         then if Set.member x' names
              then let xs' = allNames (nodeToCont (ns ++ [x]) v) in xs' ++ xs
              else let xs' = lockedNames ll (nodeToCont (ns ++ [x]) v) in xs' ++ xs
         else if Set.member x' names
              then x' : xs else xs
lockedNames ul@(UnLockList ls) (Cont ns cm) =
  let names = Set.fromList ls
  in OrdM.foldrWithKey (g names) [] cm
  where
    g :: Set Name -> Name -> CNode -> [Name] -> [Name]
    g names x v xs =
      let x' = qualifiedName ns x
      in if pSegnode v
         then if Set.member x' names
              then xs
              else let xs' = lockedNames ul (nodeToCont (ns ++ [x]) v) in xs' ++ xs
         else if not $ Set.member x' names
              then x' : xs else xs

unlockedNames :: SimpleLock -> Cont -> [Name]
unlockedNames LockNone cont = allNames cont
unlockedNames LockAll _ = []
unlockedNames ll@(LockList ls) (Cont ns cm) =
  let names = Set.fromList ls
  in OrdM.foldrWithKey (g names) [] cm
  where
    g :: Set Name -> Name -> CNode -> [Name] -> [Name]
    g names x v xs =
      let x' = qualifiedName ns x
      in if pSegnode v
         then if Set.member x' names -- segment is locked
              then xs
              else let xs' = unlockedNames ll (nodeToCont (ns ++ [x]) v) in xs' ++ xs
         else if not $ Set.member x' names
              then x' : xs else xs
unlockedNames ul@(UnLockList ls) (Cont ns cm) =
  let names = Set.fromList ls
  in OrdM.foldrWithKey (g names) [] cm
  where
    g :: Set Name -> Name -> CNode -> [Name] -> [Name]
    g names x v xs =
      let x' = qualifiedName ns x
      in if pSegnode v
         then if Set.member x' names
              then let xs' = allNames (nodeToCont (ns ++ [x]) v) in xs' ++ xs
              else let xs' = unlockedNames ul (nodeToCont (ns ++ [x]) v) in xs' ++ xs
         else if Set.member x' names
              then x' : xs else xs

allNames :: Cont -> [Name]
allNames (Cont ns cm) = OrdM.foldrWithKey g [] cm
  where g :: Name -> CNode -> [Name] -> [Name]
        g x v xs = let x' = qualifiedName ns x in
          if pSegnode v
          then let xs' = allNames (nodeToCont (ns ++ [x]) v) in xs' ++ xs
          else x' : xs

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
  showsPrec _ (Clos e _) = showParen True $ showsPrec prec e . showString "(...)"

instance Show Decl where
  showsPrec _ d = showDeclWithLayout 0 d

instance Show Seg where
  showsPrec _ s = showSegWithLayout 0 s

instance Show Cont where
  showsPrec _ c =
    let ds  = restoreCont c
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
restoreCont :: Cont -> AbsContext
restoreCont (Cont ns c) =
  if OrdM.null c
  then []
  else OrdM.foldrWithKey restoreCNode [] c
  where
    restoreCNode :: Name -> CNode -> AbsContext -> AbsContext
    restoreCNode x (Ct a) ac = Dec x a : ac
    restoreCNode x (Cd a b) ac = Def x a b : ac
    restoreCNode x (Cs cm) ac =
      let ac' = restoreCont (Cont (ns ++ [x]) cm)
          ds  = SDef ac'
      in DSeg x ds : ac

-- * END_SECTION

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

-- * BEGIN_SECTION: auxiliary functions
-- |Map a function over the first element of a tuple
mfst :: (a -> b) -> (a, c) -> (b, c)
mfst f (a, c) = (f a, c)

-- |Map a function over the second element of a tuple
msnd :: (c -> d) -> (a, c) -> (a, d)
msnd f (a, c) = (a, f c)

-- |Get an empty context
emptyCont :: Namespace -> Cont
emptyCont ns = Cont ns OrdM.empty

-- |Get an empty environment
emptyEnv :: Namespace -> Env
emptyEnv ns = Env ns Map.empty

-- |Transform a CNode that represents a segment into a value of context
nodeToCont :: Namespace -> CNode -> Cont
nodeToCont ns cn = Cont ns (csm cn)

-- |A predicate checking whether a context node represents a segment
pSegnode :: CNode -> Bool
pSegnode Cs {} = True
pSegnode _     = False

-- |Get the reversed path of a nested segment
revSegPath :: Seg -> Namespace
revSegPath (SRef x)      = [x]
revSegPath (SNest seg x) = x : revSegPath seg
revSegPath _             = error "error: revSegPath"

-- |Get segment context by a reversed path
getSegByPath :: SegNest a => a -> Namespace -> a
getSegByPath = foldr (\n b -> fromJust (matchSeg n b))

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

-- |Break up an instantiated segment
breakSeg :: Seg -> (Seg, [InstPair])
breakSeg (SInst sg ips) = (sg, ips)
breakSeg _              = error "error:breakSeg"

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

-- * END_SECTION

-- * BEGIN_SECTION: functions related with evaluation

-- |Evaluate an expression into a quasi-expression under a given environment
eval :: Env  -- ^ the local environment
     -> Exp  -- ^ the expression to be evaluated
     -> QExp
eval _ U             = U
eval r (Var x)       = valueOf r x
eval r (SegVar sg x) = let r' = evalSeg r sg in eval r' (Var x)
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

evalSeg :: Env -> Seg -> Env
evalSeg r sg =
  let (sg', ips) = breakSeg sg     -- sg will always be a nested segment, ensured by the syntax
      qps = map (mfst $ eval r) ips
      rpath = revSegPath sg'
      r' = getSegByPath r rpath
  in foldr (\(q, n) r0 -> bindEnvQ r0 n q) r' qps

-- |Instantiate a segment with expressions
instSeg :: Cont -> Seg -> Cont
instSeg c sg =
  let (sg', ips) = breakSeg sg
      r = getEnv LockNone c
      qps = map (mfst $ eval r) ips
      rpath = revSegPath sg'
      c' = getSegByPath c rpath
  in foldr g c' qps
  where g :: (QExp, Name) -> Cont -> Cont
        g (q, x) cont =
          let Just (Ct t) = OrdM.lookup x (mapCont cont)
          in bindConD cont x t q

-- * END_SECTION
