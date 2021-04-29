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
        Clos e r -> showsPrec p_low e . showString " @env " . showsPrec p_low r

-- | abstract syntax for declarations
data Decl = Dec String Exp | Def String Exp Exp deriving (Eq)

instance Show Decl where
  showsPrec _ d = case d of
    Dec "" a  -> showsPrec p_bar a
    Dec x a   -> showString (x ++ " : ") . showsPrec p_bar a
    Def x a e -> showString (x ++ " : ") . showsPrec p_bar a . showString " = " . showsPrec p_bar e

-- | an abstract context for a loaded source file
type AbsContext = [Decl]

-- | the syntax for 'Exp' is also used as value in this language
type Val = Exp

-- | a datatype defined for the ease of printing Env and Cont
data PrintPair = PrintPair Bool String Val

instance Show PrintPair where
  showsPrec _ (PrintPair True s v) = showString s . showString " = " . showsPrec p_low v
  showsPrec _ (PrintPair False s v) = showString s . showString " : " . showsPrec p_low v

-- | environment that relates a variable to a value
data Env = ENil
         | EConsVar Env String Val
         | EConsDef Env String Exp Exp
         deriving (Eq)

instance Show Env where
  showsPrec _ r = showList (reverse . convert $ r)
    where convert :: Env -> [PrintPair]
          convert ENil = []
          convert (EConsVar r' s v) = (PrintPair True s v) : (convert r')
          convert (EConsDef r' s _ v) = (PrintPair True s v) : (convert r')
          
-- | context that relates a variable to a type
data Cont = CNil
          | CConsVar Cont String Val
          | CConsDef Cont String Exp Exp
          deriving (Eq)

instance Show Cont where
  showsPrec _ c = showList (reverse . convert $ c)
    where convert :: Cont -> [PrintPair]
          convert CNil = []
          convert (CConsVar c' s t) = (PrintPair False s t) : (convert c')
          convert (CConsDef c' s t _) = (PrintPair False s t) : (convert c')

-- | a datatype used as exception in an ExceptT monad
data TypeCheckError = InvalidApp     Exp
                    | DupDecl        Id Id
                    | VarNotbound    Id
                    | TypeInferErr   Exp
                    | NotConvertible Val Val
                    | ExtendedErr    TypeCheckError [ErrorText]
                    deriving (Show)

type ErrorText = String

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

-- | evaluate an expression in a given environment
eval :: Exp -> Env -> Val
eval e r = case e of
  U                  -> U
  Var x              -> getVal x r
  App e1 e2          -> appVal (eval e1 r) (eval e2 r)
  Abs (Dec _ _) _    -> Clos e r
  Abs (Def x a e) e' -> eval e' (EConsDef r x a e)
  Clos _ _           -> e

-- | extend an environment with a variable and its value
consEVar :: Env -> String -> Val -> Env
consEVar r "" _ = r
consEVar r x v  = EConsVar r x v

-- | extend a type-checking context with a variable and its type
consCVar :: Cont -> String -> Val -> Cont
consCVar c "" _ = c
consCVar c x t  = CConsVar c x t

-- | application operation on values
appVal :: Val -> Val -> Val
appVal v1 v2 = case v1 of
  Clos (Abs (Dec x _) e) r -> eval e (consEVar r x v2)
  _                        -> App v1 v2

-- | get the environment related with a type-checking context
envCont :: Cont -> Env
envCont CNil = ENil
envCont (CConsVar c _ _) = envCont c
envCont (CConsDef c x a e) = EConsDef (envCont c) x a e

-- | get the value of a variable from an environment
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
getType CNil _ = Nothing
getType (CConsVar c x' a) x
  | x' == x = Just $ eval a (envCont c)
  | otherwise = getType c x
getType (CConsDef c x' a _) x
  | x' == x = Just $ eval a (envCont c)
  | otherwise = getType c x

-- | get all the variables of a context
varsCont :: Cont -> [String]
varsCont CNil = []
varsCont (CConsVar c x _) = reverse (x : (varsCont c))
varsCont (CConsDef c x _ _) = reverse (x : (varsCont c))

-- | generate a fresh name based on a list of names
freshVar :: String -> [String] -> String
freshVar x xs = if x `elem` xs
                then freshVar (x ++ "'") xs
                else if x == ""
                     then freshVar "var" xs
                     else x
