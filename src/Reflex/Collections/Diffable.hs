{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE LambdaCase            #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.Diffable
  (
    Diffable(..)
  , MapLike(..)
  , createPatch
  , applyDiff
  , diff
  , diffNoEq
  , diffOnlyKeyChanges
  , editDiffLeavingDeletes
  ) where

import           Reflex.Collections.KeyedCollection (KeyedCollection(..))

import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)
import           Data.Align             (Align(..))
import           Data.These             (These(..))
import           Data.Maybe             (isNothing)

import           Data.Map               (Map)
import qualified Data.Map               as M
import           Data.IntMap            (IntMap)
import qualified Data.IntMap            as IM
import           Data.Hashable          (Hashable)
import           Data.HashMap.Strict    (HashMap)
import qualified Data.HashMap.Strict    as HM
import           Data.Array             (Array, Ix)
import qualified Data.Array             as A
import qualified Data.Sequence          as S
import qualified Data.Foldable          as F

class Functor f => MapLike f where
  mlEmpty :: f a
  mlUnion :: f a -> f a -> f a -- left preferring union
  mlDifference :: f a -> f b -> f a -- remove from left any element whose key appears in right
  mlFilter :: (a -> Bool) -> f a -> f a
  mlMapMaybe :: (a -> Maybe b) -> f a -> f b  -- is this always `mlMaybe f = mlFilter (maybe False (const True) . f) `?
  mlDifferenceWith :: (a -> b -> Maybe a) -> f a -> f b -> f a 

instance Ord k => MapLike (M.Map k) where
  mlEmpty = M.empty
  mlUnion = M.union
  mlDifference = M.difference
  mlFilter = M.filter
  mlMapMaybe = M.mapMaybe
  mlDifferenceWith = M.differenceWith

instance (Eq k, Hashable k) => MapLike (HM.HashMap k) where
  mlEmpty = HM.empty
  mlUnion = HM.union
  mlDifference = HM.difference
  mlFilter = HM.filter
  mlMapMaybe = HM.mapMaybe
  mlDifferenceWith = HM.differenceWith

instance MapLike IntMap where
  mlEmpty = IM.empty
  mlUnion = IM.union
  mlDifference = IM.difference
  mlFilter = IM.filter
  mlMapMaybe = IM.mapMaybe
  mlDifferenceWith = IM.differenceWith

-- (f a) is the container
-- (Diff f a) has the operations to make and combine subsets, usually using Diff f (Maybe a)
-- we make a new f using and old f and Diff, since sometimes Diff loses information required to reconstruct. E.g., Diff (Array k) = Map k
-- and (Array k) needs a value for each key which Map may not have one.

-- this class has the one law: patch _ (toDiff x) = x
class ( KeyedCollection f
      , KeyedCollection (Diff f)
      , MapLike (Diff f)
      , Align (Diff f)) => Diffable (f :: Type -> Type) where
  type Diff f :: Type -> Type -- keyed collection of ElemUpdates
  toDiff :: f a -> Diff f a -- a diff such that patch _ (toDiff x) = x
  patch :: f a -> Diff f a -> f a -- update f using a Diff, often ignores initial argument 

instance Ord k => Diffable (Map k) where
  type Diff (Map k) = Map k
  toDiff = id
  patch _ = id

instance (Eq k, Hashable k) => Diffable (HashMap k) where
  type Diff (HashMap k) = HashMap k
  toDiff = id
  patch _ = id

instance Diffable IntMap where
  type Diff IntMap = IntMap
  toDiff = id
  patch _ = id

instance Diffable ([]) where
  type Diff ([]) = IntMap
  toDiff = IM.fromAscList . zip [0..]
  patch _ = fmap snd . IM.toAscList

instance Diffable (S.Seq) where
  type Diff (S.Seq) = IntMap
  toDiff = IM.fromAscList . zip [0..] . F.toList
  patch _ = S.fromList . fmap snd . IM.toAscList
  
instance (Enum k, Ix k) => Diffable (Array k) where
  type Diff (Array k) = IntMap
  toDiff = IM.fromAscList . fmap (\(k,v) -> (fromEnum k, v)) . A.assocs
  patch old x = old A.// (fmap (\(n,v) -> (toEnum n,v)) $ IM.toAscList x) -- Array must keep old ones if no update.  It's "Total"
  
-- a patch is ready to be made back into the original type but how depends on the type, via "patch"
createPatch :: Diffable f => Diff f (Maybe v) -> f v -> Diff f v
createPatch d old =
  let deletions = mlFilter isNothing d
      insertions = mlMapMaybe id  $ d `mlDifference` deletions
  in insertions `mlUnion` ((toDiff old) `mlDifference` deletions)

applyDiff :: Diffable f => Diff f (Maybe v) -> f v -> f v
applyDiff d f = patch f (createPatch d f)

diffNoEq :: Diffable f => f v -> f v -> Diff f (Maybe v)
diffNoEq old new =  flip fmap (align (toDiff old) (toDiff new)) $ \case
  This _ -> Nothing -- delete
  That x -> Just x -- add
  These _ x -> Just x -- might be a change so add

diff :: (Diffable f, Eq v) => f v -> f v -> Diff f (Maybe v)
diff old new = flip mlMapMaybe (align (toDiff old) (toDiff new)) $ \case
  This _ -> Just Nothing -- delete
  That x -> Just $ Just x -- add
  These x y -> if x == y then Nothing else (Just $ Just y)

diffOnlyKeyChanges :: Diffable f => f v -> f v -> Diff f (Maybe v)
diffOnlyKeyChanges old new = flip mlMapMaybe (align (toDiff old) (toDiff new)) $ \case
  This _ -> Just Nothing
  These _ _ -> Nothing
  That n -> Just $ Just n
  
editDiffLeavingDeletes :: Diffable f => Proxy f -> Diff f (Maybe v) -> Diff f b -> Diff f (Maybe v)
editDiffLeavingDeletes _ da db =
  let relevantPatch p _ = case p of
        Nothing -> Just Nothing -- it's a delete
        Just _  -> Nothing -- remove from diff
  in mlDifferenceWith relevantPatch da db
