{-|
Module          : TransUtil
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
import           Lang                       (Name, Namespace, buildSegFromPath,
                                             namespaceStr)
import qualified Lang
import           Monads
import           Text.Printf                (printf)


data Tag = TD -- ^ a tag for declaration
         | TF -- ^ a tag for definition
         | TS -- ^ a tag for segment

-- |A tree structure used to keep track of the declarations of the source program.
-- Used as the underlying state in the conversion process
data Tree = Node {
              -- | type of the node: TD: a node of declaration; TF: a node of definition; TS: a node of segment
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
    ["Duplicated declaration of name:",
     printf "  name '%s' has been declared at %s," (identName id1) (show $ identPos id1),
     printf "  but finding duplication at %s," (show $ identPos id2),
     printf "  parent segment: %s" (namespaceStr ns)]
  explain (InvalidConstRef ns (Id (pos, s))) =
    ["Invalid variable reference:",
     printf "  use of undeclared variable '%s' at %s," s (show pos),
     printf "  parent segment: %s" (namespaceStr ns)]
  explain (InvalidSegRef ns ids) =
    let path = map identName ids
        pos  = identPos (last ids)
    in ["Invalid segment reference:",
        printf "  reference to unknown segment '%s' found at position %s" (namespaceStr path) (show pos),
        printf "  parent segment: %s" (namespaceStr ns)]
  explain (UnmatchedExps ns info) =
    ["Invalid segment instantiation:",
     "  the number of expressions provided does not match the number of declarations contained in the segment.",
     "  found at " ++ info,
     "  parent segment: " ++ namespaceStr ns]
  explain (InvalidSegConstRef ns ids id) =
    let path = map identName ids
        pos  = identPos id
    in ["Invalid segment variable reference",
        printf "  segment %s does not contain a constant with name %s" (namespaceStr path) (identName id),
        printf "  found at position: %s" (show pos),
        printf "  parent segment: %s" (namespaceStr ns)]

-- |Name of an identifier (Abs.Id)
identName :: Abs.Id -> String
identName (Abs.Id (_, s)) = s

-- |Position of an identifier (Abs.Id)
identPos :: Abs.Id -> (Int, Int)
identPos (Abs.Id (pos, _)) = pos

-- |A predicate testing whether a node represents a segment
isSegmentNode :: Tree -> Bool
isSegmentNode tree = case tag tree of
  TS -> True
  _  -> False

-- |A predicate testing whether a node represents a declaration
isDeclNode :: Tree -> Bool
isDeclNode t = case tag t of
  TD -> True
  _  -> False

-- |Get the node bound to an identifier in a segment tree
getNode :: Id -> Tree -> Maybe Tree
getNode ident tree =
  if isSegmentNode tree
  then let tm = leaves tree
       in M.lookup (identName ident) tm
  else error "invalid operation"

-- |Bind a name to a node in a segment tree
bindNode :: Tag        -- ^ the tag of the node
         -> Id         -- ^ the identifier of the node
         -> Maybe (M.InsOrdHashMap Name Tree) -- ^ for a node of segment there is a sub-tree
         -> Tree       -- ^ the parent segment node where the new node is attached
         -> Tree
bindNode tg ident mmap tree =
  if isSegmentNode tree
  then let name = identName ident
           lmap = fromMaybe undefined mmap
           node = Node {tag = tg, tid = ident, leaves = lmap}
           newL = M.insert name node (leaves tree)
       in tree {leaves = newL}
  else error "invalid opearation"

-- |Get the path of a nested segment in the reverse order
getSegPathReversed :: Abs.Seg -> [Id]
getSegPathReversed (Abs.SegRef ident) = [ident]
getSegPathReversed (Abs.SegNest seg ident) =
  ident : getSegPathReversed seg
getSegPathReversed _ = error "syntax error"

-- |Match the name of a segment in a segment node
matchSegName :: (Namespace, ([Id], Tree)) -> Id -> ConvertM (Namespace, ([Id], Tree))
matchSegName (ns, (ids, tree)) ident =
  case getNode ident tree of
    Nothing -> throwError $ InvalidSegRef ns ids
    Just node ->
      if isSegmentNode node
      then return (ns, (ids ++ [ident], node))
      else throwError $ InvalidSegRef ns ids

-- |Get a segment by a path of identifiers
getSegByPath :: Namespace -> [Id] -> ConvertM Tree
getSegByPath ns segPath = do
  (_, (_, segNode)) <- join $ gets (\t -> foldM matchSegName (ns, ([], t)) segPath)
  return segNode

-- |Get the names of declarations in a segment
getSegDeclNames :: Tree -> [Name]
getSegDeclNames t =
  if isSegmentNode t
  then let tm  = leaves t
           tm' = M.filter isDeclNode tm
       in M.keys tm'
  else error "invalid operation"

-- |Transform a concrete context into the abstract context.
absCtx :: Abs.Context -> ConvertM Lang.AbsContext
absCtx (Abs.Ctx xs) = mapM (absDecl []) xs

-- |Transform a concrete declaration into an abstract declaration
absDecl :: Namespace -> Abs.Decl -> ConvertM Lang.Decl
absDecl ns (Abs.Dec ident a) = do
  mnode <- gets (getNode ident)
  case mnode of
    Just node ->
      -- this identifier has been used, report error
      throwError $ DuplicateName ns (tid node) ident
    Nothing  -> do
      -- this is a new identifier, bind this identifier to a declaration node
      modify $ bindNode TD ident Nothing
      let name = identName ident
      a' <- absExp ns a
      -- return a declaration of form 'x : A'
      return $ Lang.Dec name a'
absDecl ns (Abs.Def ident a b) = do
  mnode <- gets (getNode ident)
  case mnode of
    Just node ->
      -- this identifier has been used, report error
      throwError $ DuplicateName ns (tid node) ident
    Nothing -> do
      -- this is a new identifier, bind this identifier to a definition node
      modify $ bindNode TF ident Nothing
      let name = identName ident
      a' <- absExp ns a
      b' <- absExp ns b
      -- return a definition of form 'x : A = B'
      return $ Lang.Def name a' b'
absDecl ns adseg@(Abs.DSeg ident seg) = do
  mnode <- gets (getNode ident)
  case mnode of
    Just node ->
      -- this identifier has been used, report error
      throwError $ DuplicateName ns (tid node) ident
    Nothing -> case seg of
      Abs.SegRef segId -> do
        -- 'seg' refers to an identifier
        let segPath = [segId]
        segNode <- getSegByPath ns segPath
        -- bind the identifier 'ident' to the segment node referred by 'segId'
        modify $ bindNode TS ident (Just (leaves segNode))
        -- return a declaration of segment in form 's = s1'
        return $ Lang.DSeg (identName ident) (Lang.SRef (identName segId))
      Abs.SegNest seg1 segId -> do
        -- 'seg' refers to a nested segment identifier
        -- get the reversed path of 'seg1'
        let rsegPath = segId : getSegPathReversed seg1
            segPath  = reverse rsegPath
            -- get the reversed namespace of 'seg1'
            rns      = map identName rsegPath
        segNode <- getSegByPath ns segPath
        -- bind identifier 'ident' to a segment node
        modify $ bindNode TS ident (Just (leaves segNode))
        -- return a declaration of segment in form 's = s1 . s2 . (...) sn'
        return $ Lang.DSeg (identName ident) (buildSegFromPath rns)
      Abs.SegInst seg1 es  -> do
        -- 'seg' refers to an segment instantiation
        let rsegPath = getSegPathReversed seg1
            segPath  = reverse rsegPath
            rns      = map identName rsegPath
        segNode <- getSegByPath ns segPath
        modify $ bindNode TS ident (Just (leaves segNode))
        aes <- mapM (absExp ns) es
        -- get the names of declarations from the segment 'seg1'
        let dnames = getSegDeclNames segNode
        if length aes == length dnames
          then let pairs = zip aes dnames
                   aseg  = buildSegFromPath rns
               -- return a declaration of segment in form 's = s1 [e1, e2, ..., en]'
               in return $ Lang.DSeg (identName ident) (Lang.SInst aseg pairs)
          else throwError $ UnmatchedExps ns (printTree adseg)
      -- 'seg' refers to a segment declaratoin
      Abs.SegDef ads -> do
        let name = identName ident
        -- 1. retrieve the current segment node
        segParent <- get
        -- 2. put an empty segment node as the underlying conversion checking context
        put (Node TS ident M.empty)
        -- 3. do the conversion checking on the list of declarations 'ads'
        ds <- mapM (absDecl (ns ++ [name])) ads
        -- 4. retrieve the updated child segment node
        segChild <- get
        -- 5. back to the parent segment node
        put segParent
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
      if isSegmentNode node
      then throwError $ InvalidConstRef ns ident
      else return (Lang.Var (identName ident))
absExp ns ae@(Abs.SegVar seg es ident) = do
  let rsegPath = getSegPathReversed seg
      segPath  = reverse rsegPath
      rns      = map identName rsegPath
      name     = identName ident
  segNode <- getSegByPath ns segPath
  aes <- mapM (absExp ns) es
  let dnames = getSegDeclNames segNode
  if length dnames /= length aes
    then throwError $ UnmatchedExps ns (printTree ae)
    else case getNode ident segNode of
           Nothing -> throwError $ InvalidSegConstRef ns segPath ident
           Just node ->
             if isSegmentNode node
             then throwError $ InvalidSegConstRef ns segPath ident
             else let pairs = zip aes dnames
                      aseg  = buildSegFromPath rns
                      aseg' = Lang.SInst aseg pairs
                  in return $ Lang.SegVar aseg' name
absExp ns (Abs.App e1 e2) = do
  e1' <- absExp ns e1
  e2' <- absExp ns e2
  return $ Lang.App e1' e2'
absExp ns (Abs.Arr e1 e2) = do
  e1' <- absExp ns e1
  e2' <- absExp ns e2
  return $ Lang.Abs "" e1' e2'
absExp ns (Abs.Abs ident a b) = do
  mnode <- gets (getNode ident)
  case mnode of
    Just node' -> throwError $ DuplicateName ns (tid node') ident
    Nothing -> do
      a' <- absExp ns a
      t  <- get
      modify $ bindNode TD ident Nothing
      b' <- absExp ns b
      put t
      return $ Lang.Abs (identName ident) a' b'
absExp ns (Abs.Let ident a b e) = do
  mnode <- gets (getNode ident)
  case mnode of
    Just node' -> throwError $ DuplicateName ns (tid node') ident
    Nothing -> do
      a' <- absExp ns a
      t  <- get
      modify $ bindNode TF ident Nothing
      b' <- absExp ns b
      e' <- absExp ns e
      put t
      return $ Lang.Let (identName ident) a' b' e'
