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
import           Data.Maybe                 (fromMaybe)
import           Lang                       (Name, Namespace, idPos, idStr,
                                             namespaceStr)
import qualified Lang
import           Monads
import           Text.Printf                (printf)


data Tag = TD -- a tag for declaration
         | TF -- a tag for definition
         | TS -- a tag for segment

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
  = DuplicateName  Namespace Id Id
  | UndeclaredName Namespace Id
  | UnknownSegment Namespace String (Int, Int)
  deriving (Show)

instance InformativeError ConversionError where
  explain (DuplicateName ns id1 id2) =
    ["Duplicated declaration of name:",
     printf "  name '%s' has been declared at %s," (idStr id1) (show $ idPos id1),
     printf "  but finding duplication at %s," (show $ idPos id2),
     printf "  from segment: %s" (namespaceStr ns)]
  explain (UndeclaredName ns (Id (pos, s))) =
    [printf "Use of undeclared name '%s' at %s," s (show pos),
     printf "  from segment: %s" (namespaceStr ns)]
  explain (UnknownSegment ns n p) =
    [printf "Reference to unknown segment '%s' found at position %s" n (show p),
     printf "  from segment: %s" (namespaceStr ns)]

-- |A predicate testing whether a node represents a segment
isSegment :: Tree -> Bool
isSegment tree = case tag tree of
  TS -> True
  _  -> False

-- |Get the node bound to an identifier in a segment tree
getNode :: Id -> Tree -> Maybe Tree
getNode ident tree =
  if isSegment tree
  then let tm = leaves tree
       in M.lookup (idStr ident) tm
  else error "invalid operation"

-- |Bind a name to a node in a segment tree
bindNode :: Tag        -- ^ the tag of the node
         -> Id         -- ^ the identifier of the node
         -> Maybe (M.InsOrdHashMap Name Tree) -- ^ for a node of segment there is a sub-tree
         -> Tree       -- ^ the parent segment node where the new node is attached
         -> Tree
bindNode tg td mmap tree =
  if isSegment tree
  then let name = idStr td
           lmap = fromMaybe undefined mmap
           node = Node {tag = tg, tid = td, leaves = lmap}
           newL = M.insert name node (leaves tree)
       in tree {leaves = newL}
  else error "invalid opearation"

-- |Transform a concrete context into the abstract context.
absCtx :: Abs.Context -> ConvertM Lang.AbsContext
absCtx (Abs.Ctx xs) = mapM (absDecl []) xs

-- |Transform a concrete declaration into an abstract declaration
absDecl :: Namespace -> Abs.Decl -> ConvertM Lang.Decl
absDecl ns (Abs.Dec var a) = do
  let name = idStr var
  mnode <- gets (getNode var)
  case mnode of
    Nothing  -> do
      a' <- absExp ns a
      modify $ bindNode TD var Nothing
      return $ Lang.Dec name a'
    Just node' -> throwError $ DuplicateName ns (tid node') var

absExp :: Namespace -> Abs.Exp -> ConvertM Lang.Exp
absExp = undefined
-- absDecl :: CDecl -> ConvertM Decl
-- absDecl (CDec var e) = do
--   let s = idStr var
--   r <- gets $ Map.lookup s
--   case r of
--     Just var' -> throwError $ DupDecl var' var
--     _         -> do
--       e' <- absExp e
--       modify (Map.insert s var)
--       return $ Dec s e'
-- absDecl (CDef var e1 e2) = do
--   let s = idStr var
--   r <- gets $ Map.lookup s
--   case r of
--     Just var' -> throwError $ DupDecl var' var
--     _         -> do
--       e1' <- absExp e1
--       e2' <- absExp e2
--       modify (Map.insert s var)
--       return $ Def s e1' e2'

-- -- |transform a concrete expression into its abstract form
-- absExp :: CExp -> ConvertM Exp
-- absExp e = case e of
--   CU -> return U
--   CVar var -> do
--     let s = idStr var
--     r <- gets (Map.lookup s)
--     case r of
--       Just _ -> return $ Var s
--       _      -> throwError $ VarNotbound var
--   CApp e1 e2 -> do
--     e1' <- absExp e1
--     e2' <- absExp e2
--     return $ App e1' e2'
--   CArr e1 e2 -> do
--     e1' <- absExp e1
--     e2' <- absExp e2
--     return $ Abs (Dec "" e1') e2'
--   CPi var e1 e2 -> do
--     let s = idStr var
--     m <- get
--     case Map.lookup s m of
--       Just var' -> throwError $ DupDecl var' var
--       _         -> do
--         e1' <- absExp e1
--         put (Map.insert s var m)
--         e2' <- absExp e2
--         put m
--         return $ Abs (Dec s e1') e2'
--   CWhere var e1 e2 e3 -> do
--     let s = idStr var
--     m <- get
--     case Map.lookup s m of
--       Just var' -> throwError $ DupDecl var' var
--       _         -> do
--         e1' <- absExp e1
--         put (Map.insert s var m)
--         e2' <- absExp e2
--         e3' <- absExp e3
--         put m
--         return $ Abs (Def s e1' e2') e3'
