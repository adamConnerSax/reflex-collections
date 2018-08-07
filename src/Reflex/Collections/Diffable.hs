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
  , toDiff
  ) where

import           Reflex.Collections.KeyedCollection (ArrayDiff(..), MapDiff) 

import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)
import           Data.Functor.Compose   (Compose(..))
import           Data.Align             (Align(..))
import           Data.These             (These(..))
import           Data.Foldable          (foldl')
import           Data.Maybe             (isNothing)
import           Data.Monoid            (Monoid(mempty))

import           Data.Map               (Map)
import qualified Data.Map               as M
import           Data.IntMap            (IntMap)
import qualified Data.IntMap            as IM
import           Data.Hashable          (Hashable)
import           Data.HashMap.Strict    (HashMap)
import qualified Data.HashMap.Strict as HM
import           Data.Array             (Array, Ix)
import qualified Data.Array          as A



-- | Given a diffable collection that has an empty state, we can make a diff such that "applyDiff empty . toDiff = id"  
-- We are using the existence of a monoid instance to indicate a meaningful empty state (mempty)
toDiff :: (Monoid (f v), Diffable f df) => f v -> df v
toDiff = flip diffNoEq mempty


-- encapsulates the ability to diff two containers and then apply the diff to regain the original
-- also supports a Map.difference style operation on the diff itself (for splitting out value updates)
-- diffOnlyKeyChanges and editDiffLeavingDeletes are both too specific, I think.
-- NB: applyDiffD (diffD x y) y = x
class Diffable (f :: Type -> Type) (df :: Type -> Type) where
  diffNoEq :: f v -> f v -> df v
  diff :: Eq v => f v -> f v -> df v
  applyDiff :: df v -> f v -> f v
  diffOnlyKeyChanges :: f v -> f v -> df v
  editDiffLeavingDeletes :: Proxy f -> df v -> df u -> df v -- this removes 2nd diff from first, except when first indicates a delete. May not generalize.

instance Ix k => Diffable (Array k) (ArrayDiff k) where
  diffNoEq _ new = ArrayDiff $ A.assocs new
  diff old new =
    let oldList = A.assocs old
        newList = A.assocs new
    in ArrayDiff $ foldl' (\diffs ((_,o),(kn,n)) -> if (o /= n) then (kn,n) : diffs else diffs) [] (zip oldList newList)
  applyDiff (ArrayDiff diffs) a = a A.// diffs
  diffOnlyKeyChanges _ _ = ArrayDiff []
  editDiffLeavingDeletes _ _ _ = ArrayDiff [] -- we could implement this partially but I don't think we need it.

instance Ord k => Diffable (Map k) (MapDiff (Map k)) where
  diffNoEq = mapDiffNoEq
  diff = mapDiff M.mapMaybe
  applyDiff = mapApplyDiff M.union M.difference M.filter M.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges M.mapMaybe
  editDiffLeavingDeletes _ = mapEditDiffLeavingDeletes M.differenceWith

instance (Eq k, Hashable k) => Diffable (HashMap k) (MapDiff (HashMap k)) where
  diffNoEq = mapDiffNoEq
  diff = mapDiff HM.mapMaybe
  applyDiff = mapApplyDiff HM.union HM.difference HM.filter HM.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges HM.mapMaybe
  editDiffLeavingDeletes _ = mapEditDiffLeavingDeletes HM.differenceWith

instance Diffable IntMap (MapDiff IntMap) where
  diffNoEq = mapDiffNoEq
  diff = mapDiff IM.mapMaybe
  applyDiff = mapApplyDiff IM.union IM.difference IM.filter IM.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges IM.mapMaybe
  editDiffLeavingDeletes _ = mapEditDiffLeavingDeletes IM.differenceWith
 
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

