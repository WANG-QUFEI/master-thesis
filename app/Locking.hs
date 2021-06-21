{-|
Module          : Locking
Description     : Provides locking/unlocking strategies for constants
Maintainer      : wangqufei2009@gmail.com
Portability     : POSIX
-}
module Locking where

import           Classes
import           Lang

import qualified Data.Set as Set

-- | A simple locking/unlocking strategy for constants
-- LockAll  : lock all constants
-- LockNone : lock none constants
-- LockList <varlist>   : a list of constants that are locked
-- UnLockList <varlist> : a list of constants that are unlocked
data SimpleLock = LockAll
                | LockNone
                | LockList [String]
                | UnLockList [String]
                deriving (Show)

instance LockStrategy SimpleLock where
  getEnv LockAll _ = ENil
  getEnv LockNone c =
    case c of
      CNil -> ENil
      CConsVar c' _ _ -> getEnv LockNone c'
      CConsDef c' x a e ->
        let r = getEnv LockNone c'
        in EConsDef r x a e
  getEnv ls@(UnLockList vars) c =
    case c of
      CNil -> ENil
      CConsVar c' _ _ -> getEnv ls c'
      CConsDef c' x a e ->
        let r = getEnv ls c'
        in if x `notElem` vars
           then r
           else EConsDef r x a e
  getEnv ls@(LockList vars) c =
    case c of
      CNil -> ENil
      CConsVar c' _ _ -> getEnv ls c'
      CConsDef c' x a e ->
        let r = getEnv ls c'
        in if x `elem` vars
           then r
           else EConsDef r x a e

  addLock LockAll _ = LockAll
  addLock LockNone ss = LockList ss
  addLock (LockList ss') ss =
    let set1 = Set.fromList ss'
        set2 = Set.fromList ss
        set3 = Set.union set1 set2
    in LockList (Set.toList set3)
  addLock (UnLockList ss') ss =
    let set1 = Set.fromList ss'
        set2 = Set.fromList ss
        set3 = Set.difference set1 set2
    in UnLockList (Set.toList set3)

  removeLock LockAll ss = UnLockList ss
  removeLock LockNone _ = LockNone
  removeLock (LockList ss') ss =
    let set1 = Set.fromList ss'
        set2 = Set.fromList ss
        set3 = Set.difference set1 set2
    in LockList (Set.toList set3)
  removeLock (UnLockList ss') ss =
    let set1 = Set.fromList ss'
        set2 = Set.fromList ss
        set3 = Set.union set1 set2
    in UnLockList (Set.toList set3)

  getConstsLocked s c =
    let vars = varsCont c
    in case s of
      LockAll -> vars
      LockNone -> []
      LockList ss ->
        let set1 = Set.fromList vars
            set2 = Set.fromList ss
        in Set.toList (Set.intersection set1 set2)
      UnLockList ss ->
        let set1 = Set.fromList vars
            set2 = Set.fromList ss
        in Set.toList (Set.difference set1 set2)

  getConstsUnLocked s c =
    let vars = varsCont c
    in case s of
      LockNone -> vars
      LockAll -> []
      LockList ss ->
        let set1 = Set.fromList vars
            set2 = Set.fromList ss
        in Set.toList (Set.difference set1 set2)
      UnLockList ss ->
        let set1 = Set.fromList vars
            set2 = Set.fromList ss
        in Set.toList (Set.intersection set1 set2)

