{-|
Module          : Locking
Description     : Provides locking/unlocking strategies for constants
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
{-# LANGUAGE OverloadedStrings #-}
module Locking where

import           Classes
import qualified Data.HashMap.Lazy          as Map
import qualified Data.HashMap.Strict.InsOrd as OrdM
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Lang

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
  getEnv (LockList ls)   = locklist (Set.fromList ls) []
  getEnv (UnLockList ls) = unlocklist (Set.fromList ls) []

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

  getNamesLocked = lockedNames []

  getNamesUnLocked = unlockedNames []

lockAll :: Cont -> Env
lockAll (Cont cm) = OrdM.foldrWithKey g emptyEnv cm
  where g :: Name -> CNode -> Env -> Env
        g _ Ct {}    r = r
        g _ Cd {}    r = r
        g x cs@Cs {} r = lockSeg lockAll x cs r

lockNone :: Cont -> Env
lockNone (Cont cm) = OrdM.foldrWithKey g emptyEnv cm
  where g :: Name -> CNode -> Env -> Env
        g _ Ct {}    r = r
        g x (Cd a b) r =
          let en = Ed a b
              rm = Map.insert x en (mapEnv r)
          in Env rm
        g x cs@Cs {} r = lockSeg lockNone x cs r

locklist :: Set Name -> Namespace -> Cont -> Env
locklist names ns (Cont cm) = OrdM.foldrWithKey g emptyEnv cm
  where g :: Name -> CNode -> Env -> Env
        g _ Ct {}    r = r
        g x (Cd a b) r =
          let x' = namespaceStr (ns ++ [x])
          in if Set.member x' names
             then r
             else let en = Ed a b
                      rm = Map.insert x en (mapEnv r)
                  in Env rm
        g x cs@Cs {} r =
          let x' = namespaceStr (ns ++ [x])
          in if Set.member x' names -- lock on the whole segment
             then lockSeg lockAll x cs r
             else lockSeg (locklist names (ns ++ [x])) x cs r

unlocklist :: Set Name -> Namespace -> Cont -> Env
unlocklist names ns (Cont cm) = OrdM.foldrWithKey g emptyEnv cm
  where g :: Name -> CNode -> Env -> Env
        g _ Ct {}    r = r
        g x (Cd a b) r =
          let x' = namespaceStr (ns ++ [x])
          in if Set.notMember x' names
             then r
             else let en = Ed a b
                      rm = Map.insert x en (mapEnv r)
                  in Env rm
        g x cs@Cs {} r =
          let x' = namespaceStr (ns ++ [x])
          in if Set.member x' names -- unlock on the whole segment
             then lockSeg lockNone x cs r
             else lockSeg (unlocklist names (ns ++ [x])) x cs r


lockSeg :: (Cont -> Env) -> Name -> CNode -> Env -> Env
lockSeg f x (Cs m) r =
  let r' = f (Cont m)
      en = Es (mapEnv r')
      rm = Map.insert x en (mapEnv r)
  in Env rm
lockSeg _ _ _ _ = error "invalid operation"

lockedNames :: Namespace -> SimpleLock -> Cont -> [Name]
lockedNames ns LockAll cont = allNames ns cont
lockedNames _  LockNone _ = []
lockedNames ns ll@(LockList ls) (Cont cm) =
  let names = Set.fromList ls
  in OrdM.foldrWithKey (g names) [] cm
  where
    g :: Set Name -> Name -> CNode -> [Name] -> [Name]
    g names x v xs =
      let x' = namespaceStr (ns ++ [x])
      in if isSegCNode v
         then if Set.member x' names
              then let xs' = lockedNames (ns ++ [x]) LockAll (transNodeCont v) in xs' ++ xs
              else let xs' = lockedNames (ns ++ [x]) ll (transNodeCont v) in xs' ++ xs
         else if Set.member x' names
              then x' : xs else xs
lockedNames ns ul@(UnLockList ls) (Cont cm) =
  let names = Set.fromList ls
  in OrdM.foldrWithKey (g names) [] cm
  where
    g :: Set Name -> Name -> CNode -> [Name] -> [Name]
    g names x v xs =
      let x' = namespaceStr (ns ++ [x])
      in if isSegCNode v
         then if Set.member x' names
              then  xs
              else let xs' = lockedNames (ns ++ [x]) ul (transNodeCont v) in xs' ++ xs
         else if not $ Set.member x' names
              then x' : xs else xs

unlockedNames :: Namespace -> SimpleLock -> Cont -> [Name]
unlockedNames ns LockNone cont = allNames ns cont
unlockedNames _  LockAll _ = []
unlockedNames ns ll@(LockList ls) (Cont cm) =
  let names = Set.fromList ls
  in OrdM.foldrWithKey (g names) [] cm
  where
    g :: Set Name -> Name -> CNode -> [Name] -> [Name]
    g names x v xs =
      let x' = namespaceStr (ns ++ [x])
      in if isSegCNode v
         then if Set.member x' names -- segment is locked
              then xs
              else let xs' = unlockedNames (ns ++ [x]) ll (transNodeCont v) in xs' ++ xs
         else if not $ Set.member x' names
              then x' : xs else xs
unlockedNames ns ul@(UnLockList ls) (Cont cm) =
  let names = Set.fromList ls
  in OrdM.foldrWithKey (g names) [] cm
  where
    g :: Set Name -> Name -> CNode -> [Name] -> [Name]
    g names x v xs =
      let x' = namespaceStr (ns ++ [x])
      in if isSegCNode v
         then if Set.member x' names
              then let xs' = unlockedNames (ns ++ [x]) LockNone (transNodeCont v) in xs' ++ xs
              else let xs' = unlockedNames (ns ++ [x]) ul (transNodeCont v) in xs' ++ xs
         else if Set.member x' names
              then x' : xs else xs

allNames :: Namespace -> Cont -> [Name]
allNames ns (Cont cm) = OrdM.foldrWithKey g [] cm
  where g :: Name -> CNode -> [Name] -> [Name]
        g x v xs =
          let x' = namespaceStr (ns ++ [x])
          in if isSegCNode v
             then let xs' = allNames (ns ++ [x]) (transNodeCont v) in xs' ++ xs
             else x' : xs
