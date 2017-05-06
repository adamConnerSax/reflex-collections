{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecursiveDo                #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
module Reflex.Dom.Contrib.ListHoldFunctions.Maps
  (
    LHFMap(..)
  , listHoldWithKeyLHFMap
  , listWithKeyShallowDiffLHFMap
  , listWithKeyLHFMap
  , selectViewListWithKeyLHFMap
  , lhfMapDiffNoEq
  , lhfMapDiff
  , lhfMapApplyDiff
  , distributeLHFMapOverDynPure
  ) where

import           Reflex.Dom.Contrib.ListHoldFunctions.Core

import           Data.Dependent.Map                        (DMap, DSum ((:=>)))
import qualified Data.Dependent.Map                        as DM

import           Data.Functor.Misc                         (ComposeMaybe (..),
                                                            Const2 (..),
                                                            dmapToMap,
                                                            mapWithFunctorToDMap)
import qualified Reflex                                    as R
import qualified Reflex.Dom                                as RD
import           Reflex.Patch                              (PatchDMap (..))

import           Data.Map                                  (Map)
import qualified Data.Map                                  as Map

import           Data.IntMap                               (IntMap)
import qualified Data.IntMap                               as IM

import           Data.Hashable                             (Hashable)
import           Data.HashMap.Strict                       (HashMap)
import qualified Data.HashMap.Strict                       as HM

import           Data.Functor.Compose                      (Compose (Compose, getCompose))

import           Control.Monad.Fix                         (MonadFix)
import           Control.Monad.Identity                    (Identity (..))
import           Data.Align                                (Align (..))
import           Data.Maybe                                (isNothing)
import           Data.These                                (These (..))


class (Functor f, Align f, Ord (LHFMapKey f))=>LHFMap (f :: * -> *) where
  type LHFMapKey f :: *
  lhfMapNull::f v -> Bool
  lhfEmptyMap::f v
  lhfMapSingleton::LHFMapKey f -> v -> f v
  lhfMapElems::f v->[v]
  lhfMapKeys::f v->[LHFMapKey f]
  lhfMapWithKey::(LHFMapKey f -> v -> a) -> f v -> f a
  lhfMapMaybe::(a -> Maybe b) -> f a -> f b
  lhfMapFilter::(v -> Bool) -> f v -> f v
  lhfMapUnion::f v -> f v -> f v
  lhfMapIntersection::f v->f v->f v
  lhfMapDifferenceWith::(a->b->Maybe a)->f a->f b->f a
  lhfMapWithFunctorToDMap::Functor g=>f (g v) -> DM.DMap (Const2 (LHFMapKey f) v) g
  lhfDMapToMap::DM.DMap (Const2 (LHFMapKey f) v) Identity -> f v


lhfFanMap::(LHFMap f, Ord (LHFMapKey f), R.Reflex t) => R.Event t (f v) -> R.EventSelector t (Const2 (LHFMapKey f) v)
lhfFanMap = R.fan . fmap lhfMapToDMap

lhfMapToDMap::LHFMap f=>f v -> DMap (Const2 (LHFMapKey f) v) Identity
lhfMapToDMap = lhfMapWithFunctorToDMap . fmap Identity

distributeLHFMapOverDynPure::(LHFMap f,R.Reflex t,Ord (LHFMapKey f))=>f (R.Dynamic t v) -> R.Dynamic t (f v)
distributeLHFMapOverDynPure = fmap lhfDMapToMap . R.distributeDMapOverDynPure . lhfMapWithFunctorToDMap


newtype WrapMap f v = WrapMap { unWrapMap::f v } deriving (Functor) -- newtype to allow instancing specifically for maps

instance LHFMap f=>LHFMap (WrapMap f) where
  type LHFMapKey (WrapMap f) = LHFMapKey f
  lhfMapNull = lhfMapNull . unWrapMap
  lhfEmptyMap = WrapMap lhfEmptyMap
  lhfMapSingleton k = WrapMap . lhfMapSingleton k
  lhfMapElems = lhfMapElems . unWrapMap
  lhfMapKeys = lhfMapKeys . unWrapMap
  lhfMapWithKey h = WrapMap . lhfMapWithKey h . unWrapMap
  lhfMapMaybe h = WrapMap . lhfMapMaybe h . unWrapMap
  lhfMapFilter h = WrapMap . lhfMapFilter h . unWrapMap
  lhfMapUnion a b = WrapMap $ lhfMapUnion (unWrapMap a) (unWrapMap b)
  lhfMapIntersection a b = WrapMap $ lhfMapIntersection (unWrapMap a) (unWrapMap b)
  lhfMapDifferenceWith h a b = WrapMap $ lhfMapDifferenceWith h (unWrapMap a) (unWrapMap b)
  lhfMapWithFunctorToDMap = lhfMapWithFunctorToDMap . unWrapMap
  lhfDMapToMap = WrapMap . lhfDMapToMap

instance Align f => Align (WrapMap f) where
  nil = WrapMap nil
  align a b = WrapMap $ align (unWrapMap a) (unWrapMap b)

newtype WrapA a = WrapA { unWrapA::a }  -- also to avoid overlapping instances

fromWrapA::Functor g=>(k -> v -> g (WrapA a))->(k->v->g a)
fromWrapA f x y = unWrapA <$> f x y


instance (LHFMap (WrapMap f), LHFMapKey (WrapMap f) ~ k)=>ToPatchType (WrapMap f) k v (WrapA a) where
  type Diff (WrapMap f) k = Compose (WrapMap f) Maybe
  type SeqType (WrapMap f) k = DM.DMap
  type SeqPatchType (WrapMap f) k = PatchDMap
  type SeqTypeKey (WrapMap f) k (WrapA a) = Const2 k a
  toSeqTypeWithFunctor h = lhfMapWithFunctorToDMap . lhfMapWithKey (fromWrapA h)
  makePatchSeq _ h = PatchDMap . lhfMapWithFunctorToDMap . lhfMapWithKey (\k mv -> ComposeMaybe $ fmap (fromWrapA h k) mv) . getCompose
  fromSeqType _ _ = fmap WrapA . lhfDMapToMap

instance (LHFMap (WrapMap f), Align (WrapMap f), Functor (WrapMap f))=>Diffable (WrapMap f) (Compose (WrapMap f) Maybe) where
  emptyContainer _ = lhfEmptyMap
  toDiff = Compose . fmap Just
  diffNoEq old new = Compose $ flip fmap (align old new) $ \case
    This _ -> Nothing -- in old but not new, so delete
    That v -> Just v -- in new but not old, so put in patch
    These _ v -> Just v -- in both and without Eq I don't know if the value changed, so put possibly new value in patch

  diff old new = Compose $ flip lhfMapMaybe (align old new) $ \case
    This _ -> Just Nothing -- in old but not new, so delete
    That v -> Just $ Just v -- in new but not old, so put in patch
    These oldV newV -> if oldV == newV then Nothing else Just $ Just newV -- in both and without Eq I don't know if the value changed, so put possibly new value in patch
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
          Just _  -> Nothing -- remove from diff
    in Compose $ lhfMapDifferenceWith relevantPatch (getCompose da) (getCompose db)


lhfMapDiffNoEq::Diffable (WrapMap f) (Compose (WrapMap f) Maybe)=>f v -> f v -> f (Maybe v)
lhfMapDiffNoEq old new = unWrapMap . getCompose $ diffNoEq (WrapMap old) (WrapMap new)

lhfMapDiff::(Diffable (WrapMap f) (Compose (WrapMap f) Maybe), Eq v)=>f v -> f v -> f (Maybe v)
lhfMapDiff old new = unWrapMap . getCompose $ diff (WrapMap old) (WrapMap new)

lhfMapApplyDiff::Diffable (WrapMap f) (Compose (WrapMap f) Maybe)=>f (Maybe v) -> f v -> f v
lhfMapApplyDiff d a = unWrapMap $ applyDiff (Compose $ WrapMap d) (WrapMap a)


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

toWrapA::Functor g=>(k -> v -> g a) -> (k -> v -> g (WrapA a))
toWrapA f x y = WrapA <$> f x y


listHoldWithKeyLHFMap::forall f t m k v a. (LHFMap f
                                           , LHFMapKey f ~ k
                                           , Ord k
                                           , RD.DomBuilder t m
                                           , R.MonadHold t m)
  =>f v->R.Event t (f (Maybe v))->(k->v->m a)->m (R.Dynamic t (f a))
listHoldWithKeyLHFMap c diffCEv h = fmap (fmap unWrapA . unWrapMap) <$> listHoldWithKeyGeneral (WrapMap c) (Compose . WrapMap <$> diffCEv) (toWrapA h)

toWrapA3::Functor g=>(k -> v -> e -> g a) -> (k -> v -> e -> g (WrapA a))
toWrapA3 f x y z = WrapA <$> f x y z


listWithKeyShallowDiffLHFMap::forall f t m k v a. (LHFMap f
                                                  , LHFMapKey f ~ k
                                                  , Align f
                                                  , Ord k
                                                  , RD.DomBuilder t m
                                                  , MonadFix m
                                                  , R.MonadHold t m)
  => f v -> R.Event t (f (Maybe v)) -> (k -> v -> R.Event t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyShallowDiffLHFMap c diffCEv  h = fmap (fmap unWrapA . unWrapMap) <$> listWithKeyShallowDiffGeneral (WrapMap c) (Compose . WrapMap <$> diffCEv) (toWrapA3 h)

listWithKeyLHFMap::forall f t m k v a. (LHFMap f
                                       , LHFMapKey f ~ k
                                       , Align f
                                       , Ord k
                                       , RD.DomBuilder t m
                                       , MonadFix m
                                       , R.MonadHold t m
                                       , RD.PostBuild t m)
  =>R.Dynamic t (f v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyLHFMap dc h = fmap (fmap unWrapA . unWrapMap) <$> listWithKeyGeneral (WrapMap <$> dc) (toWrapA h)


instance (LHFMap (WrapMap f), LHFMapKey (WrapMap f) ~ k)=>ToPatchType (WrapMap f) k v (R.Event t (k,a)) where
  type Diff (WrapMap f) k = Compose (WrapMap f) Maybe
  type SeqType (WrapMap f) k = DM.DMap
  type SeqPatchType (WrapMap f) k = PatchDMap
  type SeqTypeKey (WrapMap f) k (R.Event t (k,a)) = Const2 k (R.Event t (k,a))
  toSeqTypeWithFunctor h = lhfMapWithFunctorToDMap . lhfMapWithKey h
  makePatchSeq _ h = PatchDMap . lhfMapWithFunctorToDMap . lhfMapWithKey (\k mv -> ComposeMaybe $ fmap (h k) mv) . getCompose
  fromSeqType _ _ = lhfDMapToMap

instance LHFMap f=>ToElemList (WrapMap f) where
  toElemList = lhfMapElems . unWrapMap


selectViewListWithKeyLHFMap::(LHFMap f
                             , LHFMapKey f ~ k
                             , Align f
                             , Ord k
                             , RD.DomBuilder t m
                             , MonadFix m
                             , R.MonadHold t m
                             , RD.PostBuild t m)
  =>R.Dynamic t k -> R.Dynamic t (f v) -> (k -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -> m (R.Event t (k,a))
selectViewListWithKeyLHFMap selection vals mkChild = selectViewListWithKeyGeneral selection (WrapMap <$> vals) mkChild


-- These Maplike things are the easy cases and all useful for listWithKeyShallowDiff based container widgets
instance Ord k=>LHFMap (Map k) where
  type LHFMapKey (Map k) = k
  lhfMapNull = Map.null
  lhfEmptyMap = Map.empty
  lhfMapSingleton = Map.singleton
  lhfMapElems = Map.elems
  lhfMapKeys = Map.keys
  lhfMapWithKey = Map.mapWithKey
  lhfMapMaybe = Map.mapMaybe
  lhfMapFilter = Map.filter
  lhfMapUnion = Map.union
  lhfMapIntersection = Map.intersection
  lhfMapDifferenceWith = Map.differenceWith
  lhfMapWithFunctorToDMap = mapWithFunctorToDMap
  lhfDMapToMap = dmapToMap

instance LHFMap IntMap where
  type LHFMapKey IntMap = Int
  lhfMapNull = IM.null
  lhfEmptyMap = IM.empty
  lhfMapSingleton = IM.singleton
  lhfMapElems = IM.elems
  lhfMapKeys = IM.keys
  lhfMapWithKey = IM.mapWithKey
  lhfMapMaybe = IM.mapMaybe
  lhfMapFilter = IM.filter
  lhfMapUnion = IM.union
  lhfMapIntersection = IM.intersection
  lhfMapDifferenceWith = IM.differenceWith
  lhfMapWithFunctorToDMap = DM.fromDistinctAscList . fmap (\(k, v) -> Const2 k :=> v) . IM.toAscList
  lhfDMapToMap = IM.fromDistinctAscList . fmap (\(Const2 k :=> Identity v) -> (k, v)) . DM.toAscList


instance (Ord k, Hashable k)=>LHFMap (HashMap k) where
  type LHFMapKey (HashMap k) = k
  lhfMapNull = HM.null
  lhfEmptyMap = HM.empty
  lhfMapSingleton = HM.singleton
  lhfMapElems = HM.elems
  lhfMapKeys = HM.keys
  lhfMapWithKey = HM.mapWithKey
  lhfMapMaybe = HM.mapMaybe
  lhfMapFilter = HM.filter
  lhfMapUnion = HM.union
  lhfMapIntersection = HM.intersection
  lhfMapDifferenceWith = HM.differenceWith
  lhfMapWithFunctorToDMap = DM.fromList . fmap (\(k, v) -> Const2 k :=> v) . HM.toList
  lhfDMapToMap = HM.fromList . fmap (\(Const2 k :=> Identity v) -> (k, v)) . DM.toList



