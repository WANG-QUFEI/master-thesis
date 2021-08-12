{-|
Module          : Convertor
Description     : Provides functions to convert the source program from concret syntax to abstract syntax
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Convertor where

import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.HashMap.Strict.InsOrd as M

import           Classes
import           Core.Abs                   (Id (..))
import qualified Core.Abs                   as Abs
import           Core.Print                 (printTree)
import           Data.Maybe                 (fromMaybe)
import           Lang                       (Name, Namespace)
import qualified Lang
import           Monads
import           Text.Printf                (printf)

-- |Data structure used to differentiate between types of declarations
data Tag = TD -- ^ a tag for declaration
         | TF -- ^ a tag for definition
         | TS -- ^ a tag for segment

-- |Data structure used to keep track of the declarations of the source program.
-- Used as the underlying state in the conversion procedure
data Tree = Node {
              -- | tag of the node
              tag    :: Tag,
              -- | source code identifier bound to this node
              tid    :: Id,
              -- | for a node of segment, it has a map of nodes as its children
              leaves :: M.InsOrdHashMap Name Tree}

-- |Monad for conversion checking
type ConvertM a = G ConversionError Tree a

-- |Possible syntax error during conversion checking
data ConversionError
  = DuplicateName      Namespace Id Id
  | InvalidConstRef    Namespace Id
  | InvalidSegRef      Namespace [Id]
  | UnmatchedExps      Namespace String
  | InvalidSegConstRef Namespace [Id] Id
  deriving (Show)

instance InformativeError ConversionError where
  explain (DuplicateName ns id1 id2) =
    ["Duplicated declaration of name!",
     printf "  name '%s' has been declared at %s," (idName id1) (show $ idPos id1),
     printf "  find duplication at %s," (show $ idPos id2),
     printf "  in namespace: %s" (strnsp ns)]
  explain (InvalidConstRef ns (Id (pos, s))) =
    ["Invalid variable reference!",
     printf "  use of undeclared variable '%s' at %s," s (show pos),
     printf "  in namespace: %s" (strnsp ns)]
  explain (InvalidSegRef ns ids) =
    let path = map idName ids
        pos  = idPos (last ids)
    in ["Invalid segment reference!",
        printf "  reference to unknown segment '%s' found at position %s" (strnsp path) (show pos),
        printf "  in namespace: %s" (strnsp ns)]
  explain (UnmatchedExps ns info) =
    ["Invalid segment instantiation!",
     "  the number of expressions provided does not match the number of declarations contained in the segment",
     "  found at " ++ info,
     "  in namespace: " ++ strnsp ns]
  explain (InvalidSegConstRef ns ids ident) =
    let path = map idName ids
        pos  = idPos ident
    in ["Invalid segment variable reference!",
        printf "  segment %s does not contain a constant with name %s" (strnsp path) (idName ident),
        printf "  found at position: %s" (show pos),
        printf "  in namespace: %s" (strnsp ns)]

initTree :: Tree
initTree = Node TS (Abs.Id ((-1, -1), "_top_")) M.empty 

-- |Name of an identifier
idName :: Abs.Id -> String
idName (Abs.Id (_, s)) = s

-- |Position of an identifier
idPos :: Abs.Id -> (Int, Int)
idPos (Abs.Id (p, _)) = p

-- |A predicate testing whether a node represents a segment
pSegnode :: Tree -> Bool
pSegnode tree = case tag tree of
  TS -> True
  _  -> False

-- |A predicate testing whether a node represents a declaration
pDeclnode :: Tree -> Bool
pDeclnode t = case tag t of
  TD -> True
  _  -> False

-- |Mark the instantiation of a node
markInst :: Tree -> Tree
markInst t =
  if pDeclnode t
  then t {tag = TF}
  else t

-- |Get the node bound to an identifier in a segment tree
getNode :: Id -> Tree -> Maybe Tree
getNode ident tree =
  if pSegnode tree
  then let tm = leaves tree
       in M.lookup (idName ident) tm
  else error "error: getNode"

-- |Bind a name to a node in a segment tree
bindNode :: Tag -- ^ the tag of the node
         -> Id  -- ^ the identifier of the node
         -> Maybe (M.InsOrdHashMap Name Tree) -- ^ for a node of segment there is a sub-tree
         -> Tree -- ^ the parent segment
         -> Tree
bindNode tg ident mmap pt =
  if pSegnode pt
  then let name = idName ident
           lmap = fromMaybe undefined mmap
           node = Node {tag = tg, tid = ident, leaves = lmap}
           nl   = M.insert name node (leaves pt)
       in pt {leaves = nl}
  else error "error: bindNode"

-- |Get the path of a nested segment in the reverse order
reversePath :: Abs.Seg -> [Id]
reversePath (Abs.SegRef ident) = [ident]
reversePath (Abs.SegNest seg ident) =
  ident : reversePath seg
reversePath _ = error "error: reversePath"

-- |Match the name of a segment in a segment node
matchSeg :: (Namespace, ([Id], Tree)) -> Id -> ConvertM (Namespace, ([Id], Tree))
matchSeg (ns, (ids, tree)) ident =
  case getNode ident tree of
    Nothing -> throwError $ InvalidSegRef ns ids
    Just node ->
      if pSegnode node
      then return (ns, (ids ++ [ident], node))
      else throwError $ InvalidSegRef ns ids

-- |Get a segment by a path of identifiers
getSegByPath :: Namespace -> [Id] -> ConvertM Tree
getSegByPath ns path = do
  (_, (_, segNode)) <- join $ gets (\t -> foldM matchSeg (ns, ([], t)) path)
  return segNode

-- |Get the names of declarations in a segment
segDecNames :: Tree -> [Name]
segDecNames t =
  if pSegnode t
  then let tm  = leaves t
           tm' = M.filter pDeclnode tm
       in M.keys tm'
  else error "error: segDecNames"

-- |Get the string representation of a namespace
strnsp :: Namespace -> String
strnsp []  = "_root_"
strnsp [x] = x
strnsp ns  = foldr1 (\a b -> a ++ "." ++ b) ns

-- |Construct a nested segment from a reversed path
segfromPath :: Namespace -> Lang.Seg
segfromPath []   = error "empty path"
segfromPath [x]  = Lang.SRef x
segfromPath (x:xs) =
  let s = segfromPath xs
  in Lang.SNest s x

-- |Transform a concrete context into the abstract context.
absCtx :: Abs.Context -> ConvertM Lang.AbsContext
absCtx (Abs.Ctx xs) = mapM (absDecl []) xs

-- |Transform a concrete declaration into an abstract declaration
absDecl :: Namespace -> Abs.Decl -> ConvertM Lang.Decl
absDecl ns (Abs.Dec ident a) = do
  checkDup ns ident
  a' <- absExp ns a
  modify $ bindNode TD ident Nothing
  return $ Lang.Dec (idName ident) a'
absDecl ns (Abs.Def ident a b) = do
  checkDup ns ident
  a' <- absExp ns a
  b' <- absExp ns b
  modify $ bindNode TF ident Nothing
  return $ Lang.Def (idName ident) a' b'
absDecl ns asg@(Abs.DSeg ident seg) = do
  checkDup ns ident
  case seg of
     Abs.SegRef sid -> do
       let path = [sid]
       -- check that segment with id 'segId' exists
       segNode <- getSegByPath ns path
       modify $ bindNode TS ident (Just (leaves segNode))
       return $ Lang.DSeg (idName ident) (Lang.SRef (idName sid))
     Abs.SegNest sg sid -> do
       let rpath = sid : reversePath sg
           path  = reverse rpath
           rns = map idName rpath
       -- check that the nested segment 'sg.sid' exists
       segNode <- getSegByPath ns path
       modify $ bindNode TS ident (Just (leaves segNode))
       return $ Lang.DSeg (idName ident) (segfromPath rns)
     Abs.SegInst sg es -> do
       let rpath = reversePath sg
           path  = reverse rpath
           rns = map idName rpath
       segNode <- getSegByPath ns path
       aes <- mapM (absExp ns) es
       let dnames = segDecNames segNode
       if length aes == length dnames
         then let pairs = zip aes dnames
                  sg' = segfromPath rns
                  name = idName ident
                  nl = M.map markInst (leaves segNode)
              in do { modify $ bindNode TS ident (Just nl)
                    ; return $ Lang.DSeg name (Lang.SInst sg' pairs)}
         else throwError $ UnmatchedExps ns (printTree asg)
     Abs.SegDef ads -> do
       let name = idName ident
       -- 1. retrieve the current segment node
       pseg <- get
       -- 2. put an empty segment node as the underlying conversion checking context
       put (Node TS ident M.empty)
       -- 3. do the conversion checking on the list of declarations 'ads'
       ds <- mapM (absDecl (ns ++ [name])) ads
       -- 4. retrieve the updated child segment node
       segChild <- get
       -- 5. back to the parent segment node
       put pseg
       -- 6. bind the identifier 'ident' to the child segment under the parent segment
       modify $ bindNode TS ident (Just (leaves segChild))
       -- return a declaration of segment in form 's = seg { d1; d2; ... ; dn}'
       return $ Lang.DSeg name (Lang.SDef ds)

-- |Transform a concrete expression into an abstract expression
absExp :: Namespace -> Abs.Exp -> ConvertM Lang.Exp
absExp _  Abs.U = return Lang.U
absExp ns (Abs.Var ident) = do
  mnode <- gets (getNode ident)
  case mnode of
    Nothing   -> throwError $ InvalidConstRef ns ident
    Just node ->
      if pSegnode node
      then throwError $ InvalidConstRef ns ident
      else return (Lang.Var (idName ident))
absExp ns ae@(Abs.SegVar seg es ident) = do
  let rpath = reversePath seg
      path = reverse rpath
      rns = map idName rpath
      name = idName ident
  segNode <- getSegByPath ns path
  aes <- mapM (absExp ns) es
  let dnames = segDecNames segNode
  if length dnames /= length aes
    then throwError $ UnmatchedExps ns (printTree ae)
    else case getNode ident segNode of
           Nothing -> throwError $ InvalidSegConstRef ns path ident
           Just node ->
             if pSegnode node
             then throwError $ InvalidSegConstRef ns path ident
             else let pairs = zip aes dnames
                      sg  = segfromPath rns
                      sg' = Lang.SInst sg pairs
                  in return $ Lang.SegVar sg' name
absExp ns (Abs.App e1 e2) = do
  e1' <- absExp ns e1
  e2' <- absExp ns e2
  return $ Lang.App e1' e2'
absExp ns (Abs.Arr e1 e2) = do
  e1' <- absExp ns e1
  e2' <- absExp ns e2
  return $ Lang.Abs "" e1' e2'
absExp ns (Abs.Abs ident a b) = do
  checkDup ns ident
  a' <- absExp ns a
  t  <- get
  modify $ bindNode TD ident Nothing
  b' <- absExp ns b
  put t
  return $ Lang.Abs (idName ident) a' b'
absExp ns (Abs.Let ident a b e) = do
  checkDup ns ident
  a' <- absExp ns a
  t  <- get
  modify $ bindNode TF ident Nothing
  b' <- absExp ns b
  e' <- absExp ns e
  put t
  return $ Lang.Let (idName ident) a' b' e'

-- |Check the duplicated declaration of names
checkDup :: Namespace -> Abs.Id -> ConvertM ()
checkDup ns ident = do
  mnode <- gets (getNode ident)
  case mnode of
    Just n -> throwError $ DuplicateName ns (tid n) ident
    _      -> return ()
