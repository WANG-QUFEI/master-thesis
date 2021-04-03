{-|
Module          : TransUtil
Description     : providing the transforming function from the concrete syntax to the abstract syntax
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module TransUtil where

import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.Map as Map

import           Base
import           Core.Abs

-- | monad for converting 
type ConvertM a = G TypeCheckError (Map.Map String Id) a

-- |transform a concrete context into its abstract context,
-- check proper declaration and reference of variables at the same time
absCtx :: Context -> ConvertM AbsCtx
absCtx (Ctx xs) = mapM absDecl xs

-- |transform a concrete declaration (or definition) into its abstract form
absDecl :: CDecl -> ConvertM Decl
absDecl (CDec id e) = do
  r <- gets (Map.lookup (idStr id))
  case r of
    Just id' -> throwError $ DupDecl id' id
    _        -> do
      e' <- absExp e
      modify (\s -> Map.insert (idStr id) id s)
      return $ Dec (idStr id) e'
absDecl (CDef id e1 e2) = do
  r <- gets (Map.lookup (idStr id))
  case r of
    Just id' -> throwError $ DupDecl id' id
    _        -> do
      e1' <- absExp e1
      e2' <- absExp e2
      modify (\s -> Map.insert (idStr id) id s)
      return $ Def (idStr id) e1' e2'

-- |transform a concrete expression into its abstract form
absExp :: CExp -> ConvertM Exp
absExp e = case e of
  CU -> return U
  CVar id -> do
    r <- gets (Map.lookup (idStr id))
    case r of
      Just _ -> return $ Var (idStr id)
      _      -> throwError $ VarNotbound id
  CApp e1 e2 -> do
    e1' <- absExp e1
    e2' <- absExp e2
    return $ App e1' e2'
  CArr e1 e2 -> do
    e1' <- absExp e1
    e2' <- absExp e2
    return $ Abs "" e1' e2'
  CPi id e1 e2 -> do
    m <- get
    case Map.lookup (idStr id) m of
      Just id' -> throwError $ DupDecl id' id
      _        -> do
        e1' <- absExp e1
        put (Map.insert (idStr id) id m)
        e2' <- absExp e2
        put m
        return $ Abs (idStr id) e1' e2'
  CWhere id e1 e2 e3 -> do
    m <- get
    case Map.lookup (idStr id) m of
      Just id' -> throwError $ DupDecl id' id
      _        -> do
        e1' <- absExp e1
        put (Map.insert (idStr id) id m)
        e2' <- absExp e2
        e3' <- absExp e3
        put m
        return $ Where (idStr id) e1' e2' e3'

