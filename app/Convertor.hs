{-|
Module          : TransUtil
Description     : Provides functions to convert the concret syntax to abstract syntax
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Convertor where

import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.Map             as Map

import           Core.Abs
import           Lang
import           Util

-- | monad for converting
type ConvertM a = G ConversionError (Map.Map String Id) a

data ConversionError
  = DupDecl Id Id
  | VarNotbound Id
  deriving (Show)

instance InformativeError ConversionError where
  explain (DupDecl id1 id2) =
    [ "Duplicated declaration of variable",
      idStr id1 ++ " is first declared at " ++ show (idPos id1),
      "Find duplication at " ++ show (idPos id2)]
  explain (VarNotbound (Id (pos, s))) =
    ["Find unbound variable " ++ s ++ ", at " ++ show pos]

-- | Transform a concrete context into the corresponding abstract context,
--   and check the proper declaration and reference of variables during the conversion
absCtx :: Context -> ConvertM [Decl]
absCtx (Ctx xs) = mapM absDecl xs

-- |transform a concrete declaration/definition into its abstract form
absDecl :: CDecl -> ConvertM Decl
absDecl (CDec var e) = do
  let s = idStr var
  r <- gets $ Map.lookup s
  case r of
    Just var' -> throwError $ DupDecl var' var
    _         -> do
      e' <- absExp e
      modify (Map.insert s var)
      return $ Dec s e'
absDecl (CDef var e1 e2) = do
  let s = idStr var
  r <- gets $ Map.lookup s
  case r of
    Just var' -> throwError $ DupDecl var' var
    _         -> do
      e1' <- absExp e1
      e2' <- absExp e2
      modify (Map.insert s var)
      return $ Def s e1' e2'

-- |transform a concrete expression into its abstract form
absExp :: CExp -> ConvertM Exp
absExp e = case e of
  CU -> return U
  CVar var -> do
    let s = idStr var
    r <- gets (Map.lookup s)
    case r of
      Just _ -> return $ Var s
      _      -> throwError $ VarNotbound var
  CApp e1 e2 -> do
    e1' <- absExp e1
    e2' <- absExp e2
    return $ App e1' e2'
  CArr e1 e2 -> do
    e1' <- absExp e1
    e2' <- absExp e2
    return $ Abs "" e1' e2'
  CPi var e1 e2 -> do
    let s = idStr var
    m <- get
    case Map.lookup s m of
      Just var' -> throwError $ DupDecl var' var
      _         -> do
        e1' <- absExp e1
        put (Map.insert s var m)
        e2' <- absExp e2
        put m
        return $ Abs s e1' e2'
  CWhere var e1 e2 e3 -> do
    let s = idStr var
    m <- get
    case Map.lookup s m of
      Just var' -> throwError $ DupDecl var' var
      _         -> do
        e1' <- absExp e1
        put (Map.insert s var m)
        e2' <- absExp e2
        e3' <- absExp e3
        put m
        return $ Let s e1' e2' e3'
