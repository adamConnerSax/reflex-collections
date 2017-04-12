{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Reflex.Dom.Contrib.ListHoldFunctions.Maps
  (
    diffMapNoEq
  , diffMap
  , applyMapDiff
  , R.distributeMapOverDynPure  -- from Reflex
  , listHoldWithKeyMap
  , listWithKeyMap
  , diffIntMapNoEq
  , diffIntMap
  , applyIntMapDiff
  , distributeIntMapOverDynPure
  , listWithKeyShallowDiffMap
  , listHoldWithKeyIntMap
  , listWithKeyIntMap
  , listWithKeyShallowDiffIntMap
  , diffHashMapNoEq
  , diffHashMap
  , applyHashMapDiff
  , distributeHashMapOverDynPure
  , listHoldWithKeyHashMap
  , listWithKeyHashMap
  , listWithKeyShallowDiffHashMap
  ) where

import           Reflex.Dom.Contrib.ListHoldFunctions.Core

import           Data.Dependent.Map                        (DMap, DSum ((:=>)))
import qualified Data.Dependent.Map                        as DM

import           Data.Functor.Misc                         (Const2 (..),
                                                            dmapToMap,
                                                            mapToDMap,
                                                            mapWithFunctorToDMap)
import qualified Reflex                                    as R
import qualified Reflex.Dom                                as RD
import           Reflex.Patch                              (ComposeMaybe (..),
                                                            PatchDMap (..))

import           Data.Map                                  (Map)
import qualified Data.Map                                  as Map

import           Data.IntMap                               (IntMap)
import qualified Data.IntMap                               as IM

import           Data.Hashable                             (Hashable)
import           Data.HashMap.Strict                       (HashMap)
import qualified Data.HashMap.Strict                       as HM

import           Data.Functor.Compose                      (Compose (Compose, getCompose))

import           Control.Monad.Fix                         (MonadFix)
import           Control.Monad.Identity                    (Identity (..), void)
import           Data.Align                                (Align (..))
import           Data.Maybe                                (isNothing)
import           Data.These                                (These (..))


instance (DM.GCompare (Const2 k a), Ord k)=>Sequenceable DM.DMap PatchDMap (Const2 k a) where
  sequenceWithPatch = R.sequenceDMapWithAdjust

class LHFMap (f :: * -> *) where
  type LHFMapKey f :: *
  lhfMapToDMap::f v -> DM.DMap (Const2 (LHFMapKey f) v) Identity
  lhfMapWithFunctorToDMap::Functor g=>f (g v) -> DM.DMap (Const2 (LHFMapKey f) v) g
  dmapToLHFMap::DM.DMap (Const2 (LHFMapKey f) v) Identity -> f v
  lhfEmptyMap::f v
  lhfMapWithKey::(LHFMapKey f -> v -> a) -> f v -> f a
  lhfMapMaybe::(a -> Maybe b) -> f a -> f b
  lhfMapFilter::(v -> Bool) -> f v -> f v
  lhfMapUnion::f v -> f v -> f v
  lhfMapIntersection::f v->f v->f v
  lhfMapDifferenceWith::(a->b->Maybe a)->f a->f b->f a


lhfFanMap::(LHFMap f, Ord (LHFMapKey f), R.Reflex t) => R.Event t (f v) -> R.EventSelector t (Const2 (LHFMapKey f) v)
lhfFanMap = R.fan . fmap lhfMapToDMap

newtype WrapMap f v = WrapMap { unWrap::f v } deriving (Functor) -- newtype to allow instancing specifically for maps

instance LHFMap f=>LHFMap (WrapMap f) where
  type LHFMapKey (WrapMap f) = LHFMapKey f
  lhfMapToDMap = lhfMapToDMap . unWrap
  lhfMapWithFunctorToDMap = lhfMapWithFunctorToDMap . unWrap
  dmapToLHFMap = WrapMap . dmapToLHFMap
  lhfEmptyMap = WrapMap lhfEmptyMap
  lhfMapWithKey h = WrapMap . lhfMapWithKey h . unWrap
  lhfMapMaybe h = WrapMap . lhfMapMaybe h . unWrap
  lhfMapFilter h = WrapMap . lhfMapFilter h . unWrap
  lhfMapUnion a b = WrapMap $ lhfMapUnion (unWrap a) (unWrap b)
  lhfMapIntersection a b = WrapMap $ lhfMapIntersection (unWrap a) (unWrap b)
  lhfMapDifferenceWith h a b = WrapMap $ lhfMapDifferenceWith h (unWrap a) (unWrap b)

instance Align f => Align (WrapMap f) where
  nil = WrapMap nil
  align a b = WrapMap $ align (unWrap a) (unWrap b) 

instance (LHFMap (WrapMap f), LHFMapKey (WrapMap f) ~ k)=>ToPatchType (WrapMap f) k v a where
  type Diff (WrapMap f) k = Compose (WrapMap f) Maybe
  type SeqType (WrapMap f) k = DM.DMap
  type SeqPatchType (WrapMap f) k = PatchDMap
  type SeqTypeKey (WrapMap f) k a = Const2 k a
  toSeqTypeWithFunctor h = lhfMapWithFunctorToDMap . lhfMapWithKey h 
  makePatchSeq _ h = PatchDMap . lhfMapWithFunctorToDMap . lhfMapWithKey (\k mv -> ComposeMaybe $ fmap (h k) mv) . getCompose 
  fromSeqType _ _ = dmapToLHFMap


instance (LHFMap (WrapMap f), Align (WrapMap f), Functor (WrapMap f))=>Diffable (WrapMap f) (Compose (WrapMap f) Maybe) where
  emptyContainer _ = lhfEmptyMap
  toDiff = Compose . fmap Just
  diff old new = Compose $ flip fmap (align old new) $ \case
    This _ -> Nothing -- in old but not new, so delete
    That v -> Just v -- in new but not old, so put in patch
    These _ v -> Just v -- in both and without Eq I don't know if the value changed, so put possibly new value in patch

  applyDiff patch old = insertions `lhfMapUnion` (old `mapDifference` deletions) where
    deletions = lhfMapFilter isNothing (getCompose patch)
    insertions = lhfMapMaybe id  $ (getCompose patch) `mapDifference ` deletions
    mapDifference = lhfMapDifferenceWith (\_ _ -> Nothing)

  diffOnlyKeyChanges olds news = Compose $ flip lhfMapMaybe (align olds news) $ \case
    This _ -> Just Nothing
    These _ _ -> Nothing
    That new -> Just $ Just new

  editDiffLeavingDeletes _ da db =
    let relevantPatch patch _ = case patch of
          Nothing -> Just Nothing -- it's a delete
          Just _ -> Nothing -- remove from diff
    in Compose $ lhfMapDifferenceWith relevantPatch (getCompose da) (getCompose db)


instance (LHFMap (WrapMap f), Ord (LHFMapKey (WrapMap f)))=>HasFan (WrapMap f) v where
  type FanInKey (WrapMap f) = LHFMapKey (WrapMap f)
  type FanSelKey (WrapMap f) v = Const2 (LHFMapKey (WrapMap f)) v
  doFan _ = lhfFanMap --R.fanMap . unLHMap {- . fmap (Map.mapMaybe id) . fmap getCompose -}
  makeSelKey _ _ = Const2

instance (LHFMap (WrapMap f), Ord (LHFMapKey (WrapMap f)))=>HasFan (Compose (WrapMap f) Maybe) v where
  type FanInKey (Compose (WrapMap f) Maybe) = LHFMapKey (WrapMap f)
  type FanSelKey (Compose (WrapMap f) Maybe) v = Const2 (LHFMapKey (WrapMap f)) v
  doFan _ = lhfFanMap . fmap (lhfMapMaybe id) . fmap getCompose 
  makeSelKey _ _ = Const2


instance Ord k=>LHFMap (Map k) where
  type LHFMapKey (Map k) = k
  lhfMapToDMap = mapToDMap
  lhfMapWithFunctorToDMap = mapWithFunctorToDMap
  dmapToLHFMap = dmapToMap
  lhfEmptyMap = Map.empty
  lhfMapWithKey = Map.mapWithKey
  lhfMapMaybe = Map.mapMaybe
  lhfMapFilter = Map.filter
  lhfMapUnion = Map.union
  lhfMapIntersection = Map.intersection
  lhfMapDifferenceWith = Map.differenceWith

{-
instance Ord k=>Diffable (Map k) (Compose (Map k) Maybe) where
  emptyContainer _ = Map.empty
  toDiff = Compose . fmap Just
  diffNoEq old new = Compose $ flip fmap (align old new) $ \case
    This _ -> Nothing -- in old but not new, so delete
    That v -> Just v -- in new but not old, so put in patch
    These _ v -> Just v -- in both and without Eq I don't know if the value changed, so put possibly new value in patch

  diff old new = Compose $ flip Map.mapMaybe (align old new) $ \case
    This _ -> Just Nothing -- in old but not new, so delete
    That v -> Just $ Just v -- in new but not old, so put in patch
    These oldV newV -> if oldV == newV then Nothing else Just $ Just newV -- in both and without Eq I don't know if the value changed, so put possibly new value in patch

  -- NB: I'm sure Ryan's way is better here but this is clearer to me so I'll keep it for development
  applyDiff patch old = insertions `Map.union` (old `Map.difference` deletions) where
    deletions = Map.filter isNothing (getCompose patch)
    insertions = Map.mapMaybe id  $ (getCompose patch) `Map.difference` deletions

  diffOnlyKeyChanges olds news = Compose $ flip Map.mapMaybe (align olds news) $ \case
    This _ -> Just Nothing
    These _ _ -> Nothing
    That new -> Just $ Just new

  editDiffLeavingDeletes _ da db =
    let relevantPatch patch _ = case patch of
          Nothing -> Just Nothing -- it's a delete
          Just _ -> Nothing -- remove from diff
    in Compose $ Map.differenceWith relevantPatch (getCompose da) (getCompose db)


instance Ord k=>ToPatchType (Map k) k v a where
  type Diff (Map k) k = Compose (Map k) Maybe
  type SeqType (Map k) k = DM.DMap
  type SeqPatchType (Map k) k = PatchDMap
  type SeqTypeKey (Map k) k a = Const2 k a
  toSeqTypeWithFunctor h = mapWithFunctorToDMap . Map.mapWithKey h
  makePatchSeq _ h = PatchDMap . mapWithFunctorToDMap . Map.mapWithKey (\k mv -> ComposeMaybe $ fmap (h k) mv) . getCompose
  fromSeqType _ _ = dmapToMap

instance Ord k=>HasFan (Map k) v where
  type FanInKey (Map k) = k
  type FanSelKey (Map k) v = Const2 k v
  doFan _ = R.fanMap {- . fmap (Map.mapMaybe id) . fmap getCompose -}
  makeSelKey _ _ = Const2


instance Ord k=>HasFan (Compose (Map k) Maybe) v where
  type FanInKey (Compose (Map k) Maybe) = k
  type FanSelKey (Compose (Map k) Maybe) v = Const2 k v
  doFan _ = R.fanMap . fmap (Map.mapMaybe id) . fmap getCompose
  makeSelKey _ _ = Const2

-}

diffMapNoEq::Diffable (WrapMap f) (Compose (WrapMap f) Maybe)=>f v -> f v -> f (Maybe v)
diffMapNoEq old new = unWrap . getCompose $ diffNoEq (WrapMap old) (WrapMap new)

diffMap::(Diffable (WrapMap f) (Compose (WrapMap f) Maybe), Eq v)=>f v -> f v -> f (Maybe v)
diffMap old new = unWrap . getCompose $ diff (WrapMap old) (WrapMap new)

applyMapDiff::Diffable (WrapMap f) (Compose (WrapMap f) Maybe)=>f (Maybe v) -> f v -> f v
applyMapDiff d a = unWrap $ applyDiff  (Compose $ WrapMap d) (WrapMap a) 

listHoldWithKeyMap::forall t m k v a. (RD.DomBuilder t m, R.MonadHold t m, Ord k)=>Map k v->R.Event t (Map k (Maybe v))->(k->v->m a)->m (R.Dynamic t (Map k a))
listHoldWithKeyMap c diffCEv f = fmap unWrap <$> listHoldWithKeyGeneral (WrapMap c) (Compose . WrapMap <$> diffCEv) f

listWithKeyShallowDiffMap::forall t m k v a. (RD.DomBuilder t m, MonadFix m, R.MonadHold t m, Ord k)
  => Map k v -> R.Event t (Map k (Maybe v)) -> (k -> v -> R.Event t v -> m a) -> m (R.Dynamic t (Map k a))
listWithKeyShallowDiffMap c diffCEv  f = fmap unWrap <$> listWithKeyShallowDiffGeneral (WrapMap c) (Compose . WrapMap <$> diffCEv) f

listWithKeyMap::forall t m k v a. (RD.DomBuilder t m, MonadFix m, R.MonadHold t m, RD.PostBuild t m, Ord k)
  =>R.Dynamic t (Map k v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (Map k a))
listWithKeyMap dc f = fmap unWrap <$> listWithKeyGeneral (WrapMap <$> dc) f

-- intMap


intMapWithFunctorToDMap :: IntMap (f v) -> DMap (Const2 Int v) f
intMapWithFunctorToDMap = DM.fromDistinctAscList . fmap (\(k, v) -> Const2 k :=> v) . IM.toAscList

intMapToDMap :: IntMap v -> DMap (Const2 Int v) Identity
intMapToDMap = intMapWithFunctorToDMap . fmap Identity

dmapToIntMap :: DMap (Const2 Int v) Identity -> IntMap v
dmapToIntMap = IM.fromDistinctAscList . fmap (\(Const2 k :=> Identity v) -> (k, v)) . DM.toAscList

distributeIntMapOverDynPure::R.Reflex t=>IntMap (R.Dynamic t v) -> R.Dynamic t (IntMap v)
distributeIntMapOverDynPure = fmap dmapToIntMap . R.distributeDMapOverDynPure . intMapWithFunctorToDMap

instance Diffable IntMap (Compose IntMap Maybe) where
  emptyContainer _ = IM.empty
  toDiff = Compose . fmap Just
  diffNoEq old new = Compose $ flip fmap (align old new) $ \case
    This _ -> Nothing -- in old but not new, so delete
    That v -> Just v -- in new but not old, so put in patch
    These _ v -> Just v -- in both and without Eq I don't know if the value changed, so put possibly new value in patch

  diff old new = Compose $ flip IM.mapMaybe (align old new) $ \case
    This _ -> Just Nothing -- in old but not new, so delete
    That v -> Just $ Just v -- in new but not old, so put in patch
    These oldV newV -> if oldV == newV then Nothing else Just $ Just newV -- in both and without Eq I don't know if the value changed, so put possibly new value in patch


  -- NB: I'm sure Ryan's way is better here but this is clearer to me so I'll keep it for development
  applyDiff patch old = insertions `IM.union` (old `IM.difference` deletions) where
    deletions = IM.filter isNothing (getCompose patch)
    insertions = IM.mapMaybe id  $ (getCompose patch) `IM.difference` deletions

  diffOnlyKeyChanges olds news = Compose $ flip IM.mapMaybe (align olds news) $ \case
    This _ -> Just Nothing
    These _ _ -> Nothing
    That new -> Just $ Just new

  editDiffLeavingDeletes _ da db =
    let relevantPatch patch _ = case patch of
          Nothing -> Just Nothing -- it's a delete
          Just _ -> Nothing -- remove from diff
    in Compose $ IM.differenceWith relevantPatch (getCompose da) (getCompose db)

instance ToPatchType IntMap Int v a where
  type Diff IntMap Int = Compose IntMap Maybe
  type SeqType IntMap Int = DM.DMap
  type SeqPatchType IntMap Int = PatchDMap
  type SeqTypeKey IntMap Int a = Const2 Int a
  toSeqTypeWithFunctor h = intMapWithFunctorToDMap . IM.mapWithKey h
  makePatchSeq _ h = PatchDMap . intMapWithFunctorToDMap . IM.mapWithKey (\k mv -> ComposeMaybe $ fmap (h k) mv) . getCompose
  fromSeqType _ _ = dmapToIntMap

instance HasFan IntMap v where
  type FanInKey IntMap = Int
  type FanSelKey IntMap v = Const2 Int v
  doFan _ =  R.fan . fmap intMapToDMap
  makeSelKey _ _ = Const2

instance HasFan (Compose IntMap Maybe) v where
  type FanInKey (Compose IntMap Maybe) = Int
  type FanSelKey (Compose IntMap Maybe) v = Const2 Int v
  doFan _ = R.fan . fmap intMapToDMap . fmap (IM.mapMaybe id) . fmap getCompose
  makeSelKey _ _ = Const2

diffIntMapNoEq::IntMap v -> IntMap v -> IntMap (Maybe v)
diffIntMapNoEq old new = getCompose $ diffNoEq old new

diffIntMap::Eq v=>IntMap v -> IntMap v -> IntMap (Maybe v)
diffIntMap old new = getCompose $ diff old new

applyIntMapDiff::IntMap (Maybe v) -> IntMap v -> IntMap v
applyIntMapDiff = applyDiff . Compose

  
listHoldWithKeyIntMap::forall t m v a. (RD.DomBuilder t m, R.MonadHold t m)
  =>IntMap v->R.Event t (IntMap (Maybe v))->(Int->v->m a)->m (R.Dynamic t (IntMap a))
listHoldWithKeyIntMap c diffCEv = listHoldWithKeyGeneral c (Compose <$> diffCEv)

listWithKeyShallowDiffIntMap::forall t m v a. (RD.DomBuilder t m, MonadFix m, R.MonadHold t m)
  => IntMap v -> R.Event t (IntMap (Maybe v)) -> (Int -> v -> R.Event t v -> m a) -> m (R.Dynamic t (IntMap a))
listWithKeyShallowDiffIntMap c diffCEv  = listWithKeyShallowDiffGeneral c (Compose <$> diffCEv)

listWithKeyIntMap::forall t m v a. (RD.DomBuilder t m, MonadFix m, R.MonadHold t m, RD.PostBuild t m)
  =>R.Dynamic t (IntMap v) -> (Int -> R.Dynamic t v -> m a) -> m (R.Dynamic t (IntMap a))
listWithKeyIntMap = listWithKeyGeneral

-- HashMap

hashMapWithFunctorToDMap ::(Ord k, Hashable k)=>HashMap k (f v) -> DMap (Const2 k v) f
hashMapWithFunctorToDMap = DM.fromList . fmap (\(k, v) -> Const2 k :=> v) . HM.toList

hashMapToDMap::(Ord k, Hashable k)=>HashMap k v -> DMap (Const2 k v) Identity
hashMapToDMap = hashMapWithFunctorToDMap . fmap Identity

dmapToHashMap ::(Hashable k, Eq k)=>DMap (Const2 k v) Identity -> HashMap k v
dmapToHashMap = HM.fromList . fmap (\(Const2 k :=> Identity v) -> (k, v)) . DM.toList

distributeHashMapOverDynPure::(R.Reflex t, Ord k, Hashable k)=>HashMap k (R.Dynamic t v) -> R.Dynamic t (HashMap k v)
distributeHashMapOverDynPure = fmap dmapToHashMap . R.distributeDMapOverDynPure . hashMapWithFunctorToDMap


instance (Hashable k, Ord k)=>Diffable (HashMap k) (Compose (HashMap k) Maybe) where
  emptyContainer _ = HM.empty
  toDiff = Compose . fmap Just

  diffNoEq old new = Compose $ flip fmap (align old new) $ \case
    This _ -> Nothing -- in old but not new, so delete
    That v -> Just v -- in new but not old, so put in patch
    These _ v -> Just v -- in both and without Eq I don't know if the value changed, so put possibly new value in patch

  diff old new = Compose $ flip HM.mapMaybe (align old new) $ \case
    This _ -> Just Nothing -- in old but not new, so delete
    That v -> Just $ Just v -- in new but not old, so put in patch
    These oldV newV -> if oldV == newV then Nothing else Just $ Just newV -- in both and without Eq I don't know if the value changed, so put possibly new value in patch


  -- NB: I'm sure Ryan's way is better here but this is clearer to me so I'll keep it for development
  applyDiff patch old = insertions `HM.union` (old `HM.difference` deletions) where
    deletions = HM.filter isNothing (getCompose patch)
    insertions = HM.mapMaybe id  $ (getCompose patch) `HM.difference` deletions

  diffOnlyKeyChanges olds news = Compose $ flip HM.mapMaybe (align olds news) $ \case
    This _ -> Just Nothing
    These _ _ -> Nothing
    That new -> Just $ Just new

  editDiffLeavingDeletes _ da db =
    let relevantPatch patch _ = case patch of
          Nothing -> Just Nothing -- it's a delete
          Just _ -> Nothing -- remove from diff
    in Compose $ HM.differenceWith relevantPatch (getCompose da) (getCompose db)

instance (Hashable k, Ord k)=>ToPatchType (HashMap k) k v a where
  type Diff (HashMap k) k = Compose (HashMap k) Maybe
  type SeqType (HashMap k) k = DM.DMap
  type SeqPatchType (HashMap k) k = PatchDMap
  type SeqTypeKey (HashMap k) k a = Const2 k a
  toSeqTypeWithFunctor h = hashMapWithFunctorToDMap . HM.mapWithKey h
  makePatchSeq _ h = PatchDMap . hashMapWithFunctorToDMap . HM.mapWithKey (\k mv -> ComposeMaybe $ fmap (h k) mv) . getCompose
  fromSeqType _ _ = dmapToHashMap

instance (Hashable k, Ord k)=>HasFan (HashMap k) v where
  type FanInKey (HashMap k) = k
  type FanSelKey (HashMap k)  v = Const2 k v
  doFan _ = R.fan . fmap hashMapToDMap {- . fmap (Map.mapMaybe id) . fmap getCompose -}
  makeSelKey _ _ = Const2


instance (Hashable k,Ord k)=>HasFan (Compose (HashMap k) Maybe) v where
  type FanInKey (Compose (HashMap k) Maybe) = k
  type FanSelKey (Compose (HashMap k) Maybe) v = Const2 k v
  doFan _ = R.fan . fmap hashMapToDMap . fmap (HM.mapMaybe id) . fmap getCompose
  makeSelKey _ _ = Const2


diffHashMapNoEq::(Ord k, Hashable k)=>HashMap k v -> HashMap k v -> HashMap k (Maybe v)
diffHashMapNoEq old new = getCompose $ diffNoEq old new

diffHashMap::(Ord k, Hashable k, Eq v)=>HashMap k v -> HashMap k v -> HashMap k (Maybe v)
diffHashMap old new = getCompose $ diff old new

applyHashMapDiff::(Hashable k, Ord k)=>HashMap k (Maybe v) -> HashMap k v -> HashMap k v
applyHashMapDiff = applyDiff . Compose


listHoldWithKeyHashMap::forall t m k v a. (RD.DomBuilder t m, R.MonadHold t m, Ord k, Hashable k)
  =>HashMap k v->R.Event t (HashMap k (Maybe v))->(k->v->m a)->m (R.Dynamic t (HashMap k a))
listHoldWithKeyHashMap c diffCEv = listHoldWithKeyGeneral c (Compose <$> diffCEv)

listWithKeyShallowDiffHashMap::forall t m k v a. (RD.DomBuilder t m, MonadFix m, R.MonadHold t m, Ord k, Hashable k)
  => HashMap k v -> R.Event t (HashMap k (Maybe v)) -> (k -> v -> R.Event t v -> m a) -> m (R.Dynamic t (HashMap k a))
listWithKeyShallowDiffHashMap c diffCEv  = listWithKeyShallowDiffGeneral c (Compose <$> diffCEv)

listWithKeyHashMap::forall t m k v a. (RD.DomBuilder t m, MonadFix m, R.MonadHold t m, RD.PostBuild t m, Ord k, Hashable k)
  =>R.Dynamic t (HashMap k v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (HashMap k a))
listWithKeyHashMap = listWithKeyGeneral


-- previous things, failures, etc.
{-
instance Ord k=>ShallowDiffable (Compose (Map k) Maybe) where
  emptyVoidDiff = Compose Map.empty
  voidDiff = void
  diff old new =
    let relevantPatch patch _ = case patch of
          Nothing -> Just Nothing
          Just _ -> Nothing
    in Compose $ Map.differenceWith relevantPatch (getCompose old) (getCompose new)
  applyDiff patch old = Compose $ RD.applyMap (getCompose $ fmap Just patch) (getCompose old)

-}
{-
  --  compactMaybe::MDPatch v -> f v
  union::f v -> f v -> f v
  difference::


  diffNoEq:: f v -> f v -> f (Maybe v)
  diff::Eq v=> f v -> f v -> f (Maybe v)
  apply::f (Maybe v) -> f v -> f v
-}

{-
class ListHoldMap (f :: * -> *) where
  type LHMapKey f :: *
  lhMapToDMap::f v -> DM.DMap (Const2 (LHMapKey f) v) Identity
  lhMapToDMapWithFunctor::Functor g=>f (g v) -> DM.DMap (Const2 (LHMapKey f) v) g
  dmapToLHMap::DM.DMap (Const2 (LHMapKey f) v) Identity -> f v
  lhEmptyMap::f v
  lhMapWithKey::(LHMapKey f -> v -> a) -> f v -> f a
  lhMapMaybe::(a -> Maybe b) -> f a -> f b
  lhMapUnion::f v -> f v -> f v
  lhMapIntersection::f v->f v->f v
  lhMapDifferenceWith::(a->b->Maybe a)->f a->f b->f a
  -- mapDifference is just mapDifferenceWith (\_ _ -> Nothing)


{-
instance ListHoldMap f=>HasFan (Compose f Maybe) v where
  type FanInKey (Compose f Maybe) = LHMapKey f
  type FanSelKey (Compose f Maybe) v = Const2 (LHMapKey f) v
  doFan _ = R.fanMap . fmap (lhMapMaybe id) . fmap getCompose
  makeSelKey _ _ = Const2
-}


instance ListHoldMap (Map k) where
  type LHMapKey (Map k) = k
  lhMapToDMap = mapToDMap
  lhMapToDMapWithFunctor = mapToDMapWithFunctor
  dmapToLHMap = dmapToMap
  lhEmptyMap = Map.empty
  lhMapWithKey = Map.mapWithKey
  lhMapMaybe = Map.mapMaybe
  lhMapUnion = Map.union
  lhMapIntersection = Map.intersection
  lhMapDifferenceWith = Map.differenceWith

-}
