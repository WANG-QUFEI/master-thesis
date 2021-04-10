{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-|
Module          : Base
Description     : A base module that provides the data types and functions essential for the other modules of the project
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Base where

import           Control.Monad.Except
import           Control.Monad.State
import qualified Data.Map             as Map

import           Core.Abs

-- | abstract syntax for expressions, extended with closure as values
data Exp = U
         | Var String
         | App Exp Exp
         | Abs Decl Exp
         | Clos Exp Env
         deriving (Eq)

-- | constants used to control the 'show' behaviour
p_bar, p_low, p_high :: Int
p_bar  = 1
p_low  = p_bar - 1
p_high = p_bar + 1

instance Show Exp where
--  showsPrec p e = show p `trace` showParen (p > p0) sf
  showsPrec p e = showParen (p > p_bar) se
    where
      se :: ShowS
      se = case e of
        U -> showString "*"
        Var x -> showString x
        App e1 e2 ->
          let p1 = case e1 of
                     U       -> p_low
                     Var _   -> p_low
                     App _ _ -> p_low
                     _       -> p_high
              p2 = case e2 of
                     U     -> p_low
                     Var _ -> p_low
                     _     -> p_high
          in showsPrec p1 e1 . showString " " . showsPrec p2 e2
        Abs (Dec "" a) e -> case a of
                              Abs _ _ -> showsPrec p_high a . showString " -> " . showsPrec p_low e
                              _       -> showsPrec p_low a . showString " -> " . showsPrec p_low e
        Abs d@(Dec x _) e  -> showString "[ " . showsPrec p_bar d . showString " ] " . showsPrec p_low e
        Abs d@(Def _ _ _) e -> showString "[ " . showsPrec p_bar d . showString " ] " . showsPrec p_low e
        Clos e r -> showsPrec p_low e . showString " { " . showsPrec p_low r . showString " } "

-- | the syntax for 'Exp' is also used as value in this language
type Val = Exp

-- | abstract syntax for declarations
data Decl = Dec String Exp | Def String Exp Exp deriving (Eq)

instance Show Decl where
  showsPrec _ d = case d of
    Dec "" a  -> showsPrec p_bar a
    Dec x a   -> showString (x ++ " : ") . showsPrec p_bar a
    Def x a e -> showString (x ++ " : ") . showsPrec p_bar a . showString " = " . showsPrec p_bar e

-- | A type-checking context related with an environment
type Cont = [Decl]

-- | environment
data Env = ENil
         | EConsVar Env String Val
         | EConsDef Env String Exp Exp
         deriving (Eq)

instance Show Env where
  showsPrec _ r = showList (reverse . toList $ r)
    where toList :: Env -> [Decl]
          toList ENil               = []
          toList (EConsVar r x v)   = (Dec x v) : (toList r)
          toList (EConsDef r x a e) = (Def x a e) : (toList r)

data TypeCheckError = InvalidApp     Exp
                    | DupDecl        Id Id
                    | VarNotbound    Id
                    | TypeInferErr   Exp
                    | NotConvertible Val Val
                    | ExtendedErr    TypeCheckError [ErrorText]
                    deriving (Show)

-- | a composite monad which contains a state monad and an exception monad
newtype G e s a = G {mkg :: ExceptT e (State s) a}
  deriving (Monad, Applicative, Functor, MonadError e, MonadState s)

-- | run the monad and get the result
runG :: G e s a -> s -> Either e a
runG g s = evalState (runExceptT (mkg g)) s

-- | string of an id
idStr :: Id -> String
idStr (Id (_, id)) = id

-- | position of an id
idPos :: Id -> (Int, Int)
idPos (Id (pos, _)) = pos

type ErrorText = String

-- | turn a TypeCheckError to a list of string for display
errorText :: TypeCheckError -> [ErrorText]
errorText err = case err of
  InvalidApp e                -> ["Invalid application on: " ++ show e]
  DupDecl    id1 id2          -> ["Duplicated declaration of variable: already declared '" ++ idStr id1 ++ "' at " ++ show (idPos id1) ++
                                  ". Find duplication at " ++ show (idPos id2)]
  VarNotbound (Id (pos, id))  -> ["Unbound variable " ++ id ++ ", at " ++ show pos]
  TypeInferErr e              -> ["Can not infer type for: " ++ show e]
  NotConvertible v v'         -> ["Values not convertible", "v1: " ++ show v, "v2: " ++ show v']
  ExtendedErr err ss          -> (errorText err) ++ ss

-- | extend an environment with a variable and its value
consEVar :: Env -> String -> Val -> Env
consEVar r "" v = r
consEVar r x v  = EConsVar r x v

-- | extend a type-checking context with a variable and its type
consCVar :: Cont -> String -> Exp -> Cont
consCVar c "" _ = c
consCVar c x a  = (Dec x a) : c

-- | semantics about how an expression should be evaluated
eval :: Exp -> Env -> Val
eval e r = case e of
  U                  -> U
  Var x              -> getVal x r
  App e1 e2          -> appVal (eval e1 r) (eval e2 r)
  Abs (Dec _ _) _    -> Clos e r
  Abs (Def x a e) e' -> eval e' (EConsDef r x a e)
  Clos _ _           -> e

-- | application operation on values
appVal :: Val -> Val -> Val
appVal v1 v2 = case v1 of
  Clos (Abs (Dec x _) e) r -> eval e (consEVar r x v2)
  _                        -> App v1 v2

-- | get the environment related with a type-checking context
envCont :: Cont -> Env
envCont []                = ENil
envCont ((Dec _ _) : c)   = envCont c
envCont ((Def x a e) : c) = EConsDef (envCont c) x a e

-- | get variable value
getVal :: String -> Env -> Val
getVal x ENil = Var x
getVal x (EConsVar r x' v)
  | x == x'   = v
  | otherwise = getVal x r
getVal x (EConsDef r x' a e)
  | x == x' = eval e r
  | otherwise = getVal x r

-- | get the type of a variable in a given context
getType :: Cont -> String -> Maybe Val
getType [] _ = Nothing
getType ((Dec x' a) : c) x
  | x' == x = Just $ eval a (envCont c)
  | otherwise = getType c x
getType ((Def x' a _) : c) x
  | x' == x = Just $ eval a (envCont c)
  | otherwise = getType c x

-- | get all the variables of a context
varsCont :: Cont -> [String]
varsCont c = map f c
  where f :: Decl -> String
        f (Dec x _)    = x
        f (Def x _ _ ) = x

-- | generate a fresh name based on a list of names
freshVar :: String -> [String] -> String
freshVar x xs = if x `elem` xs
                then freshVar (x ++ "'") xs
                else x
