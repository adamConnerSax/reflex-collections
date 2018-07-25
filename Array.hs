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
module Reflex.Dom.Contrib.ListHoldFunctions.Array
  (
  , listHoldWithKeyArray
  , listWithKeyShallowDiffArray
  , listWithKeyArray
  , selectViewListWithKeyArray
  , arrayDiffNoEq
  , arrayDiff
  , arrayApplyDiff
  , distributeArrayOverDynPure
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

import qualified Data.Array as A

import           Data.Functor.Compose                      (Compose (Compose),
                                                            getCompose)

import           Control.Monad.Fix                         (MonadFix)
import           Control.Monad.Identity                    (Identity (..))
import           Data.Align                                (Align (..))
import           Data.Maybe                                (isNothing)
import           Data.These                                (These (..))

arrayMapWithKey :: Ix k => (k -> v -> a) -> A.Array k v -> A.Array k a
arrayMapWithKey h a =
  let kvPairs = assocs a
      mapped = (\(k,v) -> (k, h k v)) <$> kvPairs
  in A.array (min . fst $ kvPairs, max . fst $ kvPairs) mapped

arrayFan:: (A.Ix k, R.Reflex t) => R.Event t (Array k v) -> R.EventSelector t (Const2 k v)
arrayFan = R.fan . fmap arrayToDMap

arrayWithFunctorToDMap :: A.Ix k => A.Array k v -> DMap (Const2 k v) f
arrayWithFunctorToDMap = DM.fromList . fmap (\(k, v) -> Const2 k := v) . F.toList

arrayToDMap :: Ix k => A.Array k v -> DMap (Const2 k v) Identity
arrayToDMap = arrayWithFunctorToDMap . fmap Identity

dmapToArray :: Ix k => DMap (Const2 k v) Identity -> A.Array k v
dmapToArray dm =
  let kvPairs = fmap (\(Const2 k :=> Identity v) -> (k, v)) $ DM.toList dm
      keys = fst <$> kvPairs
      in A.array (min keys, max keys) kvPairs

distributeArrayOverDynPure::(R.Reflex t, Ix k) => A.Array k (R.Dynamic t v) -> R.Dynamic t (A.Array k v)
distributeArrayOverDynPure = fmap dmapToArray . R.distributeDMapOverDynPure . arrayWithFunctorToDMap

newtype ArrayDiff k v = ArrayDiff { diff :: [(k, Maybe v)] }

instance Functor (ArrayDiff k) where
  fmap f = ArrayDiff . fmap (\(k, mv) -> (k, fmap f mv)) . diff

arrayDiffMapWithKey :: (k -> v -> a) -> ArrayDiff k v -> ArrayDiff k a
arrayDiffMapWithKey h = ArrayDiff . fmap (\(k, mv) -> (k, fmap (h k) mv)) . diff

instance Ix k => ToPatchType (A.Array k) k v a where
  type Diff (A.Array k) k = ArrayDiff k
  type SeqType (Array k) k = DM.DMap
  type SeqPatchType (Array k) k = PatchDMap
  type SeqTypeKey (A.Array k) k a = Const2 k a
  toSeqTypeWithFunctor h = arrayWithFunctorToDMap . arrayMapWithKey h
  makePatchSeq _ h = PatchDMap . DM.fromList . diff . arrayDiffMapWithKey h
  fromSeqType _ _ = dmapToArray

-- HERE

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



