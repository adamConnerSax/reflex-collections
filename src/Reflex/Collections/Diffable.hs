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
    HasEmpty(..)
  , Diffable(..)
  , toDiff
  ) where

import           Reflex.Collections.ToPatchType (ArrayDiff(..)) 

import qualified Reflex                 as R
import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)
import           Data.Functor.Compose    (Compose)

import           Data.Map               (Map)
import qualified Data.Map               as M
import           Data.IntMap            (IntMap)
import qualified Data.IntMap            as IM
import           Data.Hashable          (Hashable)
import           Data.HashMap.Strict    (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.Array             (Array, Ix)


-- | Given a diffable collection that has an empty state, we can make a diff such that "applyDiff empty . toDiff = id"  
toDiff :: (HasEmpty (f v), Diffable f df) => f v -> df v
toDiff = flip diffNoEq empty


-- | Not all containers have a zero state.
-- Maps and lists do, but a total map (Array) doesn't unless the element type does
-- Should this be something more connected to Diff?
class HasEmpty a where
  empty :: a

instance Ord k => HasEmpty (Map k v) where
  empty = M.empty

instance Hashable k => HasEmpty (HashMap k v) where
  empty = HM.empty

instance HasEmpty (IntMap v) where
  empty = IM.empty

-- encapsulates the ability to diff two containers and then apply the diff to regain the original
-- also supports a Map.difference style operation on the diff itself (for splitting out value updates)
-- diffOnlyKeyChanges and editDiffLeavingDeletes are both too specific, I think.
-- NB: applyDiffD (diffD x y) y = x
class Diffable (f :: Type -> Type) (df :: Type -> Type) where
  diffNoEq :: f v -> f v -> df v
  diff :: Eq v => f v -> f v -> df v
  applyDiff :: df v -> f v -> f v
  diffOnlyKeyChanges :: f v -> f v -> df v
  editDiffLeavingDeletes :: Proxy f -> df v -> df k -> df v -- this removes 2nd diff from first, except when first indicates a delete. May not generalize.

instance Ix k => Diffable (Array k) (ArrayDiff k) where
  diffNoEq old new = ArrayDiff $ A.assocs new
  diff old new =
    let oldList = A.assocs old
        newList = A.assocs new
    in ArrayDiff $ foldl' (\diffs ((ko,o),(kn,n)) -> if (o /= n) then (kn,n) : diffs else diffs) [] (zip oldList newList)
  applyDiff (ArrayDiff diffs) a = a A.// diffs
  diffOnlyKeyChanges _ _ = ArrayDiff []
  editDiffLeavingDeletes _ d1 d2 = ArrayDiff [] -- we could implement this partially but I don't think we need it.

instance Ord k => Diffable (Map k) (Compose (Map k) Maybe v) where
  diffNoEq = mapDiffNoEq
  diff = mapDiff M.mapMaybe
  applyDiff = mapApplyDiff M.union M.difference M.filter M.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges M.mapMaybe
  editDiffLeavingDeletes = mapEditDiffLeavingDeletes M.mapDifferenceWith

instance Hashable k => Diffable (HashMap k) (Compose (HashMap k) Maybe v) where
  diffNoEq = mapDiffNoEq
  diff = mapDiff HM.mapMaybe
  applyDiff = mapApplyDiff HM.union HM.difference HM.filter HM.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges HM.mapMaybe
  editDiffLeavingDeletes = mapEditDiffLeavingDeletes HM.mapDifferenceWith

instance Diffable IntMap (Compose IntMap Maybe v) where
  diffNoEq = mapDiffNoEq
  diff = mapDiff IM.mapMaybe
  applyDiff = mapApplyDiff IM.union IM.difference IM.filter IM.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges IM.mapMaybe
  editDiffLeavingDeletes = mapEditDiffLeavingDeletes IM.mapDifferenceWith
 
mapDiffNoEq :: (Functor f, Align f) => f v -> f v -> Compose f Maybe v
mapDiffNoEq old new =  Compose $ flip fmap (align old new) $ \case
  This _ -> Nothing -- in old but not new, so delete
  That v -> Just v -- in new but not old, so put in patch
  These _ v -> Just v -- in both and, without Eq, we don't know if the value changed, so put possibly new value in patch

mapDiff :: (Eq v, Functor f, Align f) => (f (Maybe v) -> f v) -> f v -> f v -> Compose f Maybe v
mapDiff mapMaybe old new = Compose $ flip mapMaybe (align old new) $ \case
  This _ -> Just Nothing -- in old but not new, so delete
  That v -> Just $ Just v -- in new but not old, so put in patch
  These oldV newV -> if oldV == newV then Nothing else Just $ Just newV -- in both and without Eq I don't know if the value changed, so put possibly new value in patch

mapApplyDiff ::
  (f v -> f v -> f v) -- union
  -> (f v -> f v -> f v) -- difference, can be implemented as "differenceWith (\_ _ -> Nothing)" 
  -> ((v -> Bool) -> f v -> f v) -- filter
  -> (f (Maybe v) -> f v) -- mapMaybe
  -> Compose f Maybe v
  -> f v
mapApplyDiff mapUnion mapDifference mapDifferenceWith mapFilter mapMaybe patch old =  
    let deletions = mapFilter isNothing (getCompose patch)
        insertions = mapMaybe id  $ (getCompose patch) `mapDifference` deletions
    in insertions `lhfMapUnion` (old `mapDifference` deletions)

mapDiffOnlyKeyChanges :: (Align f, Functor f) => (f (Maybe v) -> f v) -> f v -> f v -> Compose f Maybe v
mapDiffOnlyKeyChanges mapMaybe old new = Compose $ flip mapMaybe (align olds news) $ \case
  This _ -> Just Nothing
  These _ _ -> Nothing
  That new -> Just $ Just new

mapEditDiffLeavingDeletes :: ((v -> v -> Maybe v) -> f v -> f v) -> Compose f Maybe v -> Compose f Maybe v -> Compose f Maybe v
mapEditDiffLeavingDeletes mapDifferenceWith da db =
  let relevantPatch patch _ = case patch of
        Nothing -> Just Nothing -- it's a delete
        Just _  -> Nothing -- remove from diff
  in Compose $ mapDifferenceWith relevantPatch (getCompose da) (getCompose db)

