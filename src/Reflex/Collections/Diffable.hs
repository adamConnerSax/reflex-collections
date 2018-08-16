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
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.Diffable
  (
    Diffable(..)
  , ArrayDiff(..)
  , MapDiff
  , toDiff
  ) where

import           Reflex.Collections.KeyedCollection ( KeyedCollection(..)
                                                    , composeMaybeMapWithKey)

import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)
import           Data.Functor.Compose   (Compose(..))
import           Data.Align             (Align(..))
import           Data.These             (These(..))
import           Data.Foldable          (foldl')
import           Data.Maybe             (isNothing)
import           Data.Monoid            (Monoid(mempty))
--import           Data.Witherable        (Filterable(..))

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

-- | Given a diffable collection that has an empty state, we can make a diff such that "applyDiff empty . toDiff = id"  
-- We are using the existence of a monoid instance to indicate a meaningful empty state (mempty)
toDiff :: (Monoid (f v), Diffable f) => f v -> Diff f v
toDiff = flip diffNoEq mempty

-- encapsulates the ability to diff two containers and then apply the diff to regain the original
-- also supports a Map.difference style operation on the diff itself (for splitting out value updates)
-- diffOnlyKeyChanges and editDiffLeavingDeletes are both too specific, I think.
-- NB: applyDiffD (diffD x y) y = x
class Diffable (f :: Type -> Type) where
  type Diff f :: Type -> Type
  mapDiffWithKey :: KeyedCollection f => Proxy f -> (Key f -> a -> b) -> Diff f a -> Diff f b
  diffNoEq :: f v -> f v -> Diff f v 
  diff :: Eq v => f v -> f v -> Diff f v
  applyDiff :: Diff f v -> f v -> f v
  diffOnlyKeyChanges :: f v -> f v -> Diff f v 
  editDiffLeavingDeletes :: Proxy f -> Diff f v -> Diff f u -> Diff f v -- this removes 2nd diff from first, except when first indicates a delete. May not generalize.

newtype ArrayDiff k v = ArrayDiff { unArrayDiff :: [(k,v)] }

instance Functor (ArrayDiff k) where
  fmap f = ArrayDiff . fmap (\(k,v) -> (k,f v)) . unArrayDiff

instance KeyedCollection (ArrayDiff k) where
  type Key (ArrayDiff k) = k
  mapWithKey h = ArrayDiff . fmap (\(k,v) -> (k, h k v)) . unArrayDiff 
  toKeyValueList = unArrayDiff
  fromKeyValueList = ArrayDiff

instance Ix k => Diffable (Array k) where
  type Diff (Array k) = ArrayDiff k
  mapDiffWithKey _ h = ArrayDiff . fmap (\(k,v) -> (k, h k v)) . unArrayDiff
  diffNoEq _ new = ArrayDiff $ A.assocs new
  diff old new =
    let oldList = A.assocs old
        newList = A.assocs new
    in ArrayDiff $ foldl' (\diffs ((_,o),(kn,n)) -> if (o /= n) then (kn,n) : diffs else diffs) [] (zip oldList newList)
  applyDiff (ArrayDiff diffs) a = a A.// diffs
  diffOnlyKeyChanges _ _ = ArrayDiff []
  editDiffLeavingDeletes _ _ _ = ArrayDiff [] -- we could implement this partially but I don't think we need it.

type MapDiff f = Compose f Maybe

instance Ord k => Diffable (Map k) where
  type Diff (Map k) = MapDiff (Map k)
  mapDiffWithKey _ = mapDiffMapWithKey 
  diffNoEq = mapDiffNoEq
  diff = mapDiff M.mapMaybe
  applyDiff = mapApplyDiff M.union M.difference M.filter M.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges M.mapMaybe
  editDiffLeavingDeletes _ = mapEditDiffLeavingDeletes M.differenceWith

instance (Eq k, Hashable k) => Diffable (HashMap k) where
  type Diff (HashMap k) = MapDiff (HashMap k)
  mapDiffWithKey _ = mapDiffMapWithKey 
  diffNoEq = mapDiffNoEq
  diff = mapDiff HM.mapMaybe
  applyDiff = mapApplyDiff HM.union HM.difference HM.filter HM.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges HM.mapMaybe
  editDiffLeavingDeletes _ = mapEditDiffLeavingDeletes HM.differenceWith

instance Diffable IntMap where
  type Diff IntMap = MapDiff IntMap
  mapDiffWithKey _ = mapDiffMapWithKey 
  diffNoEq = mapDiffNoEq
  diff = mapDiff IM.mapMaybe
  applyDiff = mapApplyDiff IM.union IM.difference IM.filter IM.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges IM.mapMaybe
  editDiffLeavingDeletes _ = mapEditDiffLeavingDeletes IM.differenceWith

-- we do [] and Seq by zipping and transforming to IntMap (for diffing) and then back (when applying).  Is there a better way?
-- especially for diffOnlyKeyChanges, the workhorse?
instance Diffable ([]) where
  type Diff ([]) = MapDiff IntMap
  mapDiffWithKey _ = mapDiffMapWithKey
  diffNoEq old new = mapDiffNoEq (listToIntMap old) (listToIntMap new) 
  diff old new = mapDiff IM.mapMaybe (listToIntMap old) (listToIntMap new) 
  applyDiff diff old = fmap snd . IM.toList $ mapApplyDiff IM.union IM.difference IM.filter IM.mapMaybe diff (listToIntMap old)
  diffOnlyKeyChanges old new = mapDiffOnlyKeyChanges IM.mapMaybe (IM.fromAscList . zip [0..] $ old) (listToIntMap new)
  editDiffLeavingDeletes _ = mapEditDiffLeavingDeletes IM.differenceWith

listToIntMap :: [v] -> IntMap v
listToIntMap = IM.fromAscList . zip [0..]

instance Diffable (S.Seq) where
  type Diff (S.Seq) = MapDiff IntMap
  mapDiffWithKey _ = mapDiffMapWithKey
  diffNoEq old new = mapDiffNoEq (seqToIntMap old) (seqToIntMap new) 
  diff old new = mapDiff IM.mapMaybe (seqToIntMap old) (seqToIntMap new) 
  applyDiff diff old = S.fromList . fmap snd . IM.toList $ mapApplyDiff IM.union IM.difference IM.filter IM.mapMaybe diff (seqToIntMap old)
  diffOnlyKeyChanges old new = mapDiffOnlyKeyChanges IM.mapMaybe (seqToIntMap old) (seqToIntMap new)
  editDiffLeavingDeletes _ = mapEditDiffLeavingDeletes IM.differenceWith


seqToIntMap :: S.Seq v -> IntMap v
seqToIntMap = IM.fromAscList . zip [0..] . F.toList

mapDiffMapWithKey :: KeyedCollection f => (Key f -> a -> b) -> MapDiff f a -> MapDiff f b
mapDiffMapWithKey = composeMaybeMapWithKey
  
mapDiffNoEq :: (Functor f, Align f) => f v -> f v -> MapDiff f v
mapDiffNoEq old new =  Compose $ flip fmap (align old new) $ \case
  This _ -> Nothing -- in old but not new, so delete
  That v -> Just v -- in new but not old, so put in patch
  These _ v -> Just v -- in both and, without Eq, we don't know if the value changed, so put possibly new value in patch

mapDiff :: (Eq v, Functor f, Align f) =>  (forall a b.((a -> Maybe b) -> f a  -> f b)) -> f v -> f v -> MapDiff f v
mapDiff mapMaybe old new = Compose $ flip mapMaybe (align old new) $ \case
  This _ -> Just Nothing -- in old but not new, so delete
  That v -> Just $ Just v -- in new but not old, so put in patch
  These oldV newV -> if oldV == newV then Nothing else Just $ Just newV -- in both and without Eq I don't know if the value changed, so put possibly new value in patch

mapApplyDiff ::
  (forall a. (f a -> f a -> f a)) -- union
  -> (forall a b. (f a -> f b -> f a)) -- difference
  -> (forall a. ((a -> Bool) -> f a -> f a)) -- filter
  -> (forall a b. ((a -> Maybe b) -> f a -> f b)) -- mapMaybe
  -> MapDiff f v
  -> f v
  -> f v
mapApplyDiff mapUnion mapDifference mapFilter mapMaybe patch old =  
    let deletions = mapFilter isNothing (getCompose patch)
        insertions = mapMaybe id  $ (getCompose patch) `mapDifference` deletions
    in insertions `mapUnion` (old `mapDifference` deletions)

mapDiffOnlyKeyChanges :: (Align f, Functor f) => (forall a b.((a -> Maybe b) -> f a -> f b)) -> f v -> f v -> MapDiff f v
mapDiffOnlyKeyChanges mapMaybe old new = Compose $ flip mapMaybe (align old new) $ \case
  This _ -> Just Nothing
  These _ _ -> Nothing
  That n -> Just $ Just n

mapEditDiffLeavingDeletes :: (forall a b.(a -> b -> Maybe a) -> f a -> f b -> f a) -> MapDiff f v -> MapDiff f u -> MapDiff f v
mapEditDiffLeavingDeletes mapDifferenceWith da db =
  let relevantPatch patch _ = case patch of
        Nothing -> Just Nothing -- it's a delete
        Just _  -> Nothing -- remove from diff
  in Compose $ mapDifferenceWith relevantPatch (getCompose da) (getCompose db)

