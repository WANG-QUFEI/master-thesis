{-|
Module          : Convertor
Description     : Provides functions to convert the source program from concret syntax to abstract syntax
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Convertor where

import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.HashMap.Strict.InsOrd as OrdM

import           Core.Abs                   (Id (..))
import qualified Core.Abs                   as Abs
import           Core.Print                 (printTree)
import           Data.Maybe                 (fromJust, fromMaybe)
import           Lang
import           Text.Printf                (printf)
import           Util

-- |Data structure used to differentiate between types of declarations
data Tag = TDec -- ^ a tag for declaration
         | TDef -- ^ a tag for definition
         | TSeg -- ^ a tag for segment
         deriving Show

-- |Data structure used to keep track of the declarations of the source program.
-- Used as the underlying state in the conversion procedure
data Tree = Node {
  -- | tag of the node
  tag    :: Tag,
  -- | source code identifier bound to this node
  tid    :: Id,
  -- | for a node of segment, it has a map of nodes as its children
  leaves :: OrdM.InsOrdHashMap Name Tree} deriving Show

-- |Monad for conversion checking
type ConvertM a = G ConversionError Tree a

type CheckConvertM a = G CheckConvertError Cont a

-- |Possible syntax error during conversion checking
data ConversionError
  = MultiDecl   Namespace Id Id
  | UnknownVar  Namespace Id
  | UnknownSeg  Namespace [Id]
  | InstNumErr  Namespace String
  | UnknownSVar Namespace [Id] Id
  | NotKExp     Namespace Exp
  deriving (Show)

data CheckConvertError
  = VarNotKnown  Namespace Name
  | SegNotKnown  Namespace [Name]
  | SVarNotKnown Namespace [Name] Name
  | UnmatchNum   Namespace String
  | CNotKExp     Namespace Exp
  | DupDecl      Namespace Name

instance InformativeError CheckConvertError where
  explain (DupDecl ns n) =
    [printf "name '%s' already exists" n,
     "error found in namespace " ++ strnsp ns]
  explain (VarNotKnown ns n) =
    ["variable not in scope!: " ++ n,
     "error found in namespace: " ++ strnsp ns]
  explain (SegNotKnown ns path) =
    ["unknown segment: " ++ strnsp path,
     "error found in namespace: " ++ strnsp ns]
  explain (UnmatchNum ns info) =
    ["unmatched number of expressions",
     "found at " ++ info,
     "error found in namespace: " ++ strnsp ns]
  explain (CNotKExp ns ae) =
    ["application not in the beta-normal form",
    "expression: " ++ show ae,
    "error found in namespace: " ++ strnsp ns]
  explain (SVarNotKnown ns path name) =
    ["unknown segment variable!",
      printf "  segment %s does not contain a constant with name %s" (strnsp path) name,
      printf "  error found in namespace: %s" (strnsp ns)]


instance InformativeError ConversionError where
  explain (MultiDecl ns id1 id2) =
    [printf "name '%s' has been declared at %s," (idName id1) (show $ idPos id1),
     printf "found duplication at %s," (show $ idPos id2),
     printf "error found in namespace: %s" (strnsp ns)]
  explain (UnknownVar ns (Id (pos, s))) =
    [printf "use of undeclared variable '%s' at %s" s (show pos),
     printf "error found in namespace: %s" (strnsp ns)]
  explain (UnknownSeg ns ids) =
    let path = map idName ids
        pos  = idPos (last ids)
    in [printf "reference to unknown segment '%s' found at position %s" (strnsp path) (show pos),
        printf "error found in namespace: %s" (strnsp ns)]
  explain (InstNumErr ns info) =
    ["invalid segment instantiation!",
     "unmatched number of expressions",
     "found at " ++ info,
     "error found in namespace: " ++ strnsp ns]
  explain (UnknownSVar ns ids ident) =
    let path = map idName ids
        pos  = idPos ident
    in ["unknown segment variable!",
        printf "segment %s does not contain a constant with name %s" (strnsp path) (idName ident),
        printf "found at position: %s" (show pos),
        printf "error found in namespace: %s" (strnsp ns)]
  explain (NotKExp ns ae) =
    ["application not in the beta-normal form",
    "expression: " ++ show ae,
    "error found in namespace: " ++ strnsp ns]


initTree :: Tree
initTree = Node TSeg (Abs.Id ((-1, -1), "_top_")) OrdM.empty

-- |Name of an identifier
idName :: Abs.Id -> String
idName (Abs.Id (_, s)) = s

-- |Position of an identifier
idPos :: Abs.Id -> (Int, Int)
idPos (Abs.Id (p, _)) = p

-- |A predicate testing whether a node represents a segment
isTNodeSeg :: Tree -> Bool
isTNodeSeg t = case tag t of
  TSeg -> True
  _    -> False

-- |A predicate testing whether a node represents a declaration
isTNodeDec :: Tree -> Bool
isTNodeDec t = case tag t of
  TDec -> True
  _    -> False

-- |Mark the instantiation of a node
markInst :: Tree -> Tree
markInst t =
  if isTNodeDec t
  then t {tag = TDef}
  else t

-- |Get the node bound to an identifier in a segment tree
getNodeT :: Id -> Tree -> Maybe Tree
getNodeT ident tree =
  if isTNodeSeg tree
  then let tm = leaves tree
       in OrdM.lookup (idName ident) tm
  else error "error: getNodeT"

-- |Bind a name to a node in a segment tree
bindNode :: Tag -- ^ the tag of the node
         -> Id  -- ^ the identifier of the node
         -> Maybe (OrdM.InsOrdHashMap Name Tree) -- ^ for a node of segment there is a sub-tree
         -> Tree -- ^ the parent segment
         -> Tree
bindNode ntag ident mmap ptree =
  if isTNodeSeg ptree
  then let name = idName ident
           tmap = fromMaybe undefined mmap
           node = Node {tag = ntag, tid = ident, leaves = tmap}
           pmap = OrdM.insert name node (leaves ptree)
       in ptree {leaves = pmap}
  else error "error: bindNode"

-- |Convert a Abs.Ref to a path of identifiers
refPath :: Abs.Ref -> [Id]
refPath (Abs.Rid i)    = [i]
refPath (Abs.Rns rf i) = i : refPath rf

-- |Get a segment by a path of identifiers
findSegT :: Namespace -> [Id] -> ConvertM Tree
findSegT ns path = do
  (_, (_, segNode)) <- join $ gets (\t -> foldM matchTSeg (ns, ([], t)) (reverse path))
  return segNode

-- |Match the name of a segment in a segment node
matchTSeg :: (Namespace, ([Id], Tree)) -> Id -> ConvertM (Namespace, ([Id], Tree))
matchTSeg (ns, (ids, tree)) ident =
  case getNodeT ident tree of
    Nothing -> throwError $ UnknownSeg ns (ids ++ [ident])
    Just node ->
      if isTNodeSeg node
      then return (ns, (ids ++ [ident], node))
      else throwError $ UnknownSeg ns (ids ++ [ident])

-- |Get the names of declarations in a segment
declNamesT :: Tree -> [Name]
declNamesT t =
  if isTNodeSeg t
  then let tm  = leaves t
           tm' = OrdM.filter isTNodeDec tm
       in OrdM.keys tm'
  else error "error: declNames"

-- |Check the duplicated declaration of names
checkDup :: Namespace -> Abs.Id -> ConvertM ()
checkDup ns ident = do
  mnode <- gets (getNodeT ident)
  case mnode of
    Just n -> throwError $ MultiDecl ns (tid n) ident
    _      -> return ()

-- |Transform a concrete context into the abstract context
absCtx :: Abs.Context -> ConvertM [Decl]
absCtx (Abs.Ctx xs) = mapM (absDecl []) xs

-- |Transform a concrete declaration into an abstract declaration
absDecl :: Namespace -> Abs.Decl -> ConvertM Decl
absDecl ns (Abs.Dec ident a) = do
  checkDup ns ident
  a' <- absExp ns a
  modify $ bindNode TDec ident Nothing
  return $ Dec (idName ident) a'
absDecl ns (Abs.Def ident a b) = do
  checkDup ns ident
  a' <- absExp ns a
  b' <- absExp ns b
  modify $ bindNode TDef ident Nothing
  return $ Def (idName ident) a' b'
absDecl ns (Abs.Seg ident ads) = do
  checkDup ns ident
  let name = idName ident
  ptree <- get
  put $ Node TSeg ident OrdM.empty
  ds <- mapM (absDecl (ns ++ [name])) ads
  ctree <- get
  put ptree
  modify $ bindNode TSeg ident (Just (leaves ctree))
  return $ Seg name ds
absDecl ns agst@(Abs.SInst ident ref ces) = do
  checkDup ns ident
  let rp = refPath ref
      rn = map idName rp
  seg <- findSegT ns rp
  aes <- mapM (absExp ns) ces
  let names = declNamesT seg
  if length aes == length names
    then let expns = zip aes names
             ref'  = buildRef rn
             name = idName ident
             lvs = OrdM.map markInst (leaves seg)
         in do { modify $ bindNode TSeg ident (Just lvs)
               ; return $ SegInst name ref' expns}
    else throwError $ InstNumErr ns (printTree agst)

-- |Transform a concrete expression into an abstract expression
absExp :: Namespace -> Abs.Exp -> ConvertM Exp
absExp _  Abs.U = return U
absExp ns (Abs.Var ref) =
  case ref of
    Abs.Rid ident -> do
      mnode <- gets (getNodeT ident)
      case mnode of
        Nothing -> throwError $ UnknownVar ns ident
        Just node ->
          if isTNodeSeg node
          then throwError $ UnknownVar ns ident
          else return $ Var (idName ident)
    Abs.Rns rf ident -> do
      let rp = refPath rf
          rn = map idName rp
      sg <- findSegT ns rp
      case getNodeT ident sg of
        Nothing -> throwError $ UnknownSVar ns (reverse rp) ident
        Just node ->
          if isTNodeSeg node
          then throwError $ UnknownSVar ns (reverse rp) ident
          else let rf' = buildRef $ idName ident : rn
               in return $ SVar rf' []
absExp ns (Abs.SVar ref [] ident) =
  let ref' = Abs.Rns ref ident
  in absExp ns (Abs.Var ref')
absExp ns aev@(Abs.SVar ref es ident) = do
  let rp = refPath ref
      rn = map idName rp
      name = idName ident
  sg <- findSegT ns rp
  ae <- mapM (absExp ns) es
  let names = declNamesT sg
  if length names /= length ae
    then throwError $ InstNumErr ns (printTree aev)
    else case getNodeT ident sg of
           Nothing -> throwError $ UnknownSVar ns (reverse rp) ident
           Just node ->
             if isTNodeSeg node
             then throwError $ UnknownSVar ns (reverse rp) ident
             else let prs = zip ae names
                      rf  = buildRef $ name : rn
                  in return $ SVar rf prs
absExp ns (Abs.App e1 e2) = do
  e1' <- absExp ns e1
  e2' <- absExp ns e2
  let e = App e1' e2'
  if isKexp e1'
    then return e
    else throwError $ NotKExp ns e
absExp ns (Abs.Arr e1 e2) = do
  e1' <- absExp ns e1
  e2' <- absExp ns e2
  return $ Abs "" e1' e2'
absExp ns (Abs.Abs ident a b) = do
  checkDup ns ident
  a' <- absExp ns a
  t  <- get
  modify $ bindNode TDec ident Nothing
  b' <- absExp ns b
  put t
  return $ Abs (idName ident) a' b'
absExp ns (Abs.Let ident a b e) = do
  checkDup ns ident
  a' <- absExp ns a
  b' <- absExp ns b
  t  <- get
  modify $ bindNode TDef ident Nothing
  e' <- absExp ns e
  put t
  return $ Let (idName ident) a' b' e'

-----------------------------------------------------------------------
-----------------------------------------------------------------------
-----------------------------------------------------------------------
-- convert concrete syntax to abstract syntax using context
-----------------------------------------------------------------------
convertCtx :: Abs.Context -> CheckConvertM [Decl]
convertCtx (Abs.Ctx xs) = mapM convertDecl xs

convertDecl :: Abs.Decl -> CheckConvertM Decl
convertDecl (Abs.Dec ident a) = do
  let name = idName ident
  checkDupCtx ident
  a' <- convertExp a
  modify $ \c -> bindConT c name a'
  return $ Dec name a'
convertDecl (Abs.Def ident a b) = do
  let name = idName ident
  checkDupCtx ident
  a' <- convertExp a
  b' <- convertExp b
  modify $ \c -> bindConD c name a' b'
  return $ Def name a' b'
convertDecl (Abs.Seg ident ads) = do
  let name = idName ident
  checkDupCtx ident
  pc <- get
  ns <- gets cns
  put $ emptyCont (ns ++ [name])
  ds <- mapM convertDecl ads
  cc <- get
  put pc
  modify $ \c -> bindConS c (idName ident) (Cs $ mapCont cc)
  return $ Seg name ds
convertDecl dseg@(Abs.SInst ident ref ces) = do
  checkDupCtx ident
  let rp = refPath ref
      rn = map idName rp
  pc <- get
  seg <- findSegCtx rn pc
  aes <- mapM convertExp ces
  ns  <- gets cns
  let names = declNames seg
  if length aes == length names
    then let expns = zip aes names
             ref' = buildRef rn
             name = idName ident
             seg' = markInst' expns seg
         in do
    modify $ \c -> bindConS c (idName ident) (Cs (mapCont seg'))
    return $ SegInst name ref' expns
    else throwError $ UnmatchNum ns (printTree dseg)

markInst' :: [(Exp, Name)] -> Cont -> Cont
markInst' expns c =
  let cmp = mapCont c
      mp' = foldl g cmp expns
  in c {mapCont = mp'}
  where g :: OrdM.InsOrdHashMap Name CNode -> (Exp, Name) -> OrdM.InsOrdHashMap Name CNode
        g m (e, n) =
          let Ct t = fromJust $ OrdM.lookup n m
          in OrdM.insert n (Cd t e) m

convertExp :: Abs.Exp -> CheckConvertM Exp
convertExp Abs.U = return U
convertExp (Abs.Var ref) =
  case ref of
    Abs.Rid ident -> do
      mnode <- gets (getNodeCtx ident)
      ns <- gets cns
      let name = idName ident
      case mnode of
        Nothing -> throwError $ VarNotKnown ns name
        Just node ->
          if isNodeSeg node
          then throwError $ VarNotKnown ns name
          else return $ Var name
    Abs.Rns rf ident -> do
      let rp = refPath rf
          rn = map idName rp
      pc <- get
      sg <- findSegCtx rn pc
      ns <- gets cns
      let name = idName ident
      case getNodeCtx ident sg of
        Nothing -> throwError $ SVarNotKnown ns (reverse rn) name
        Just node ->
          if isNodeSeg node
          then throwError $ SVarNotKnown ns (reverse rn) name
          else let rf' = buildRef (idName ident : rn)
               in return $ SVar rf' []
convertExp (Abs.SVar ref [] ident) =
  let ref' = Abs.Rns ref ident
  in convertExp (Abs.Var ref')
convertExp aev@(Abs.SVar ref es ident) = do
  let rp = refPath ref
      rn = map idName rp
      name = idName ident
  pc <- get
  sg <- findSegCtx rn pc
  ae <- mapM convertExp es
  ns <- gets cns
  let names = declNames sg
  if length names /= length ae
    then throwError $ UnmatchNum ns (printTree aev)
    else case getNodeCtx ident sg of
           Nothing -> throwError $ SVarNotKnown ns (reverse rn) name
           Just node ->
             if isNodeSeg node
             then throwError $ SVarNotKnown ns (reverse rn) name
             else let prs = zip ae names
                      rf  = buildRef (name : rn)
                  in return (SVar rf prs)
convertExp (Abs.App e1 e2) = do
  e1' <- convertExp e1
  e2' <- convertExp e2
  ns  <- gets cns
  let e = App e1' e2'
  if isKexp e1'
    then return e
    else throwError $ CNotKExp ns e
convertExp (Abs.Arr e1 e2) = do
  e1' <- convertExp e1
  e2' <- convertExp e2
  return $ Abs "" e1' e2'
convertExp (Abs.Abs ident a b) = do
  let name = idName ident
  checkDupCtx ident
  a' <- convertExp a
  pc <- get
  modify $ \c -> bindConT c name a'
  b' <- convertExp b
  put pc
  return $ Abs name a' b'
convertExp (Abs.Let ident a b e) = do
  let name = idName ident
  checkDupCtx ident
  a' <- convertExp a
  b' <- convertExp b
  pc <- get
  modify $ \c -> bindConD c name a' b'
  e' <- convertExp e
  put pc
  return $ Let name a' b' e'

-- |Get the node bound to an identifier in a segment tree
getNodeCtx :: Id -> Cont -> Maybe CNode
getNodeCtx ident ctx =
  let cmp = mapCont ctx
  in OrdM.lookup (idName ident) cmp

-- |Check the duplicated declaration of names
checkDupCtx :: Abs.Id -> CheckConvertM ()
checkDupCtx ident = do
  mnode <- gets (getNodeCtx ident)
  ns <- gets cns
  case mnode of
    Just _ -> throwError $ DupDecl ns (idName ident)
    _      -> return ()

-- |Get segment by a reversed path
findSegCtx :: Namespace -> Cont -> CheckConvertM Cont
findSegCtx path c =
  case foldr g (Just c) path of
    Nothing -> do
      ns <- gets cns
      throwError $ SegNotKnown ns path
    Just c' -> return c'
  where g :: Name -> Maybe Cont -> Maybe Cont
        g _ Nothing   = Nothing
        g n (Just c') = matchSeg n c'
