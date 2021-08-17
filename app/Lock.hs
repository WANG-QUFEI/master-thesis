{-|
Module          : Lock
Description     : providing functions that type check the abstract syntax
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Lock where

import           Lang

import qualified Data.HashMap.Strict.InsOrd as OrdM
import           Data.Set                   (Set)
import qualified Data.Set                   as Set

class LockStrategy s where
  getEnv           :: s -> Cont -> Env     -- ^ get an environment from a type checking context
  addLock          :: s -> [Name] -> s     -- ^ add a list of names to be locked
  removeLock       :: s -> [Name] -> s     -- ^ remove a list of names from being locked
  getNamesLocked   :: s -> Cont -> [Name]  -- ^ get the names locked from the context
  getNamesUnLocked :: s -> Cont -> [Name]  -- ^ get the names unlocked from the context

-- |A simple lock strategy
data SimpleLock = LockAll            -- ^ lock all constants
                | LockNone           -- ^ lock none constants
                | LockList [Name]    -- ^ lock a list of constants
                | UnLockList [Name]  -- ^ unlock a list of constants
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

