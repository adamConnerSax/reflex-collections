{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.ToPatchType
  (
    ToPatchType(..)
  , SeqTypes(..)
  , Patchable
  , functorMappedToSeqType
  , Distributable
  , distributeOverDynPure
  , Mergeable
  , mergeOver
  ) where

import           Reflex.Collections.ComposedIntMap  (ComposedIntMap (..),
                                                     ComposedPatchIntMap (..))
import           Reflex.Collections.KeyedCollection (KeyedCollection (..))
import           Reflex.Collections.Sequenceable    (DMapConst2 (..),
                                                     PatchDMapConst2 (..),
                                                     PatchSequenceable (..),
                                                     ReflexMergeable (..),
                                                     ReflexSequenceable (..),
                                                     SequenceC)


import           Reflex.Collections.Diffable        (Diffable (..),
                                                     Diff,
                                                     SetLike (slMapMaybe))


import qualified Reflex                             as R

import           Control.Arrow                      (first)
import           Data.Dependent.Map                 (DMap, DSum ((:=>)))
import qualified Data.Dependent.Map                 as DM
import           Data.Functor.Compose               (Compose (..), getCompose)
import           Data.Functor.Identity              (Identity (..), runIdentity)
import           Data.Functor.Misc                  (ComposeMaybe (..),
                                                     Const2 (..), dmapToMap,
                                                     mapToDMap,
                                                     mapWithFunctorToDMap)
import           Data.Kind                          (Type)
import           Data.Proxy                         (Proxy (..))
import           Reflex.Patch                       (PatchDMap (..))

import           Data.Array                         (Array, Ix)
import qualified Data.Array                         as A
import qualified Data.Foldable                      as F
import           Data.Hashable                      (Hashable)
import           Data.HashMap.Strict                (HashMap)
import           Data.IntMap                        (IntMap)
import qualified Data.IntMap                        as IM
import           Data.Map                           (Map)
import qualified Data.Sequence                      as S
import           Data.Tree                          (Tree)


-- some constraint helpers to simplify sigs
type Patchable f = (ToPatchType f, SeqTypes f, PatchSequenceable (SeqType f) (SeqPatchType f))
type Distributable f = (Patchable f, ReflexSequenceable (SeqType f))
type Mergeable f = (Patchable f, ReflexMergeable (SeqType f))

-- | Generalize distributeMapOverDynPure
-- NB: Use of "unsafeFromSeqType" is okay here since we know there is a value for every key in the input
distributeOverDynPure :: (R.Reflex t, Distributable f, SequenceC (SeqType f) v) => f (R.Dynamic t v) -> R.Dynamic t (f v)
distributeOverDynPure = fmap unsafeFromSeqType . sequenceDynamic . withFunctorToSeqType
{-# INLINABLE distributeOverDynPure #-}

-- | Generalizes "mergeMap" to anything with ToPatchType where the Patches are Sequenceable.
mergeOver :: forall t f v. (R.Reflex t, Mergeable f, SequenceC (SeqType f) v) => f (R.Event t v) -> R.Event t (KeyValueSet f v)
mergeOver fEv =
  let id2 = const id :: (k -> R.Event t v -> R.Event t v)
  in fmap (fromSeqType (Proxy :: Proxy f)) . mergeEvents $ functorMappedToSeqType id2 fEv
{-# INLINABLE mergeOver #-}

-- | Type families for the sequenceable and patch types.
class SeqTypes (f :: Type -> Type) where
  type SeqType f :: Type -> (Type -> Type) -> Type
  type SeqPatchType f :: Type -> (Type -> Type) -> Type
  emptySeq :: Proxy f -> Proxy v -> Proxy g -> SeqType f v g
  default emptySeq :: (Monoid (SeqType f v g)) => Proxy f -> Proxy v -> Proxy g -> SeqType f v g
  emptySeq _ _ _ = mempty
  nullSeq :: Proxy f -> Proxy v -> SeqType f v Identity -> Bool

-- This class has the capabilities to translate f v and its difftype into types
-- that are sequenceable, and then bring the original type back
-- This requires that the Diff type be mapped to the correct type for diffing at the sequenceable level (e.g., as a DMap).
-- I think, if we had quantified constraints, we could add (forall v. GCompare (FanSelectKey f v)) here and it would be simpler.
class (KeyedCollection f, Diffable f) => ToPatchType (f :: Type -> Type) where
  type CollectionEventSelector f :: Type -> Type -> Type
  withFunctorToSeqType :: (SeqTypes f, Functor g) => f (g v) -> SeqType f v g
  fromSeqType :: Proxy f -> SeqType f a Identity -> KeyValueSet f a
  unsafeFromSeqType :: SeqType f a Identity -> f a -- may fail for some types if keys are missing
  makePatchSeq :: Functor g => Proxy f -> (Key f -> v -> g u) -> Diff f v -> SeqPatchType f u g
  fanCollection :: (R.Reflex t, SequenceC (SeqType f) v) => R.Event t (f v) -> CollectionEventSelector f t v
  selectCollection :: (R.Reflex t, SequenceC (SeqType f) v) => Proxy f -> CollectionEventSelector f t v -> Key f -> R.Event t v 
  fanDiffMaybe :: (R.Reflex t, SequenceC (SeqType f) v) => Proxy f -> R.Event t (Diff f v) -> CollectionEventSelector f t v

-- The kind of "DMapConst2EventSelector k" matches "R.EventSelectorInt" so we can be polymorphic between them
newtype DMapConst2EventSelector k t a =
  DMapConst2EventSelector { unDMapConst2EventSelector :: R.EventSelector t (Const2 k a)}

-- Map, HashMap and Tree use DMap for merging and sequencing

instance Ord k => SeqTypes (Map k) where
  type SeqType (Map k) = DMapConst2 k
  type SeqPatchType (Map k) = PatchDMapConst2 k
  emptySeq _ _ _ = DMapConst2 DM.empty
  nullSeq _ _ = DM.null . unDMapConst2

instance Ord k => ToPatchType (Map k) where
--  type FanKey (Map k) = Const2 k
  type CollectionEventSelector (Map k) = DMapConst2EventSelector k
  {-# INLINABLE withFunctorToSeqType #-}
  withFunctorToSeqType = DMapConst2 . mapWithFunctorToDMap
  {-# INLINABLE makePatchSeq #-}
  makePatchSeq _ h =
    PatchDMapConst2 . PatchDMap . mapWithFunctorToDMap . mapWithKey (\k mv -> ComposeMaybe $ fmap (h k) mv)
  {-# INLINABLE fromSeqType #-}
  fromSeqType _ = dmapToMap . unDMapConst2
  {-# INLINABLE unsafeFromSeqType #-}
  unsafeFromSeqType = fromCompleteKeyValueSet . fromSeqType (Proxy :: Proxy (Map k))
  {-# INLINABLE fanCollection #-}
  fanCollection =  DMapConst2EventSelector . R.fan . fmap mapToDMap
  {-# INLINABLE selectCollection #-}
  selectCollection _ es k = R.select (unDMapConst2EventSelector es) $ Const2 k 
  {-# INLINABLE fanDiffMaybe #-}
  fanDiffMaybe _ = DMapConst2EventSelector . R.fan . fmap (keyedCollectionToDMap . slMapMaybe id)

instance Ord k => SeqTypes (HashMap k) where
  type SeqType (HashMap k) = DMapConst2 k
  type SeqPatchType (HashMap k) = PatchDMapConst2 k
  emptySeq _ _ _ = DMapConst2 DM.empty
  nullSeq _ _ = DM.null . unDMapConst2

instance (Ord k, Eq k, Hashable k) => ToPatchType (HashMap k) where
  type CollectionEventSelector (HashMap k) = DMapConst2EventSelector k
  {-# INLINABLE withFunctorToSeqType #-}
  withFunctorToSeqType = DMapConst2 . keyedCollectionWithFunctorToDMap
  {-# INLINABLE makePatchSeq #-}
  makePatchSeq _ h =
    PatchDMapConst2 . PatchDMap . keyedCollectionWithFunctorToDMap . mapWithKey (\k mv -> ComposeMaybe $ fmap (h k) mv)
  {-# INLINABLE fromSeqType #-}
  fromSeqType _ = dmapToKeyedCollection . unDMapConst2
  {-# INLINABLE unsafeFromSeqType #-}
  unsafeFromSeqType = fromCompleteKeyValueSet . fromSeqType (Proxy :: Proxy (HashMap k))
  {-# INLINABLE fanCollection #-}
  fanCollection =  DMapConst2EventSelector . R.fan . fmap keyedCollectionToDMap
  {-# INLINABLE selectCollection #-}
  selectCollection _ es k = R.select (unDMapConst2EventSelector es) $ Const2 k 
  {-# INLINABLE fanDiffMaybe #-}
  fanDiffMaybe _ = DMapConst2EventSelector . R.fan . fmap (keyedCollectionToDMap . slMapMaybe id)
  
instance SeqTypes Tree where
  type SeqType Tree = DMapConst2 (S.Seq Int)
  type SeqPatchType Tree = PatchDMapConst2 (S.Seq Int)
  emptySeq _ _ _ = DMapConst2 DM.empty
  nullSeq _ _ = DM.null . unDMapConst2

instance ToPatchType Tree where
  type CollectionEventSelector Tree = DMapConst2EventSelector (S.Seq Int)
  {-# INLINABLE withFunctorToSeqType #-}
  withFunctorToSeqType = DMapConst2 . keyedCollectionWithFunctorToDMap
  {-# INLINABLE makePatchSeq #-}
  makePatchSeq _ h =
    PatchDMapConst2 . PatchDMap . keyedCollectionWithFunctorToDMap . mapWithKey (\k mv -> ComposeMaybe $ fmap (h k) mv)
  {-# INLINABLE fromSeqType #-}
  fromSeqType _ = dmapToKeyedCollection . unDMapConst2
  {-# INLINABLE unsafeFromSeqType #-}
  unsafeFromSeqType = fromCompleteKeyValueSet . fromSeqType (Proxy :: Proxy Tree)
  {-# INLINABLE fanCollection #-}
  fanCollection =  DMapConst2EventSelector . R.fan . fmap keyedCollectionToDMap
  {-# INLINABLE selectCollection #-}
  selectCollection _ es k = R.select (unDMapConst2EventSelector es) $ Const2 k 
  {-# INLINABLE fanDiffMaybe #-}
  fanDiffMaybe _ = DMapConst2EventSelector . R.fan . fmap (keyedCollectionToDMap . slMapMaybe id)

-- IntMap, [], Seq, and Array use IntMap for their merging and sequencing

instance SeqTypes IntMap where
  type SeqType IntMap = ComposedIntMap
  type SeqPatchType IntMap = ComposedPatchIntMap
  nullSeq _ _ (ComposedIntMap cim) = IM.null $ getCompose cim

instance ToPatchType IntMap where
  type CollectionEventSelector IntMap = R.EventSelectorInt
  {-# INLINABLE withFunctorToSeqType #-}
  withFunctorToSeqType = ComposedIntMap . Compose
  {-# INLINABLE fromSeqType #-}
  fromSeqType _ = fmap runIdentity . getCompose . unCI
  {-# INLINABLE unsafeFromSeqType #-}
  unsafeFromSeqType = fromCompleteKeyValueSet . fromSeqType (Proxy :: Proxy IntMap)
  {-# INLINABLE makePatchSeq #-}
  makePatchSeq _ h =
    ComposedPatchIntMap . Compose . R.PatchIntMap . mapWithKey (\n mv -> (fmap (h n) mv))
  {-# INLINABLE fanCollection #-}
  fanCollection = R.fanInt
  {-# INLINABLE selectCollection #-}
  selectCollection _ es n = R.selectInt es n 
  {-# INLINABLE fanDiffMaybe #-}
  fanDiffMaybe _ = R.fanInt . fmap (slMapMaybe id)

instance SeqTypes [] where
  type SeqType [] = ComposedIntMap
  type SeqPatchType [] = ComposedPatchIntMap
  nullSeq _ _ (ComposedIntMap cim) = IM.null $ getCompose cim

instance ToPatchType [] where
  type CollectionEventSelector [] = R.EventSelectorInt
  {-# INLINABLE withFunctorToSeqType #-}
  withFunctorToSeqType = ComposedIntMap . Compose . IM.fromAscList . zip [0..]
  {-# INLINABLE fromSeqType #-}
  fromSeqType _ = fmap runIdentity . getCompose . unCI
  {-# INLINABLE unsafeFromSeqType #-}
  unsafeFromSeqType = fromCompleteKeyValueSet . fromSeqType (Proxy :: Proxy [])
  {-# INLINABLE makePatchSeq #-}
  makePatchSeq _ h =
    ComposedPatchIntMap . Compose . R.PatchIntMap . mapWithKey (\n mv -> (fmap (h n) mv))
  {-# INLINABLE fanCollection #-}
  fanCollection = R.fanInt . fmap (IM.fromAscList . zip [0..])
  {-# INLINABLE selectCollection #-}
  selectCollection _ es n = R.selectInt es n 
  {-# INLINABLE fanDiffMaybe #-}
  fanDiffMaybe _ = R.fanInt . fmap (IM.mapMaybe id)

instance SeqTypes S.Seq where
  type SeqType S.Seq = ComposedIntMap
  type SeqPatchType S.Seq = ComposedPatchIntMap
  nullSeq _ _ (ComposedIntMap cim) = IM.null $ getCompose cim

instance ToPatchType S.Seq where
  type CollectionEventSelector S.Seq = R.EventSelectorInt
  {-# INLINABLE withFunctorToSeqType #-}
  withFunctorToSeqType = ComposedIntMap . Compose . IM.fromAscList . zip [0..] . F.toList
  {-# INLINABLE fromSeqType #-}
  fromSeqType _ = fmap runIdentity . getCompose . unCI
  {-# INLINABLE unsafeFromSeqType #-}
  unsafeFromSeqType = fromCompleteKeyValueSet . fromSeqType (Proxy :: Proxy S.Seq)
  {-# INLINABLE makePatchSeq #-}
  makePatchSeq _ h =
    ComposedPatchIntMap . Compose . R.PatchIntMap . mapWithKey (\n mv -> fmap (h n) mv)
  {-# INLINABLE fanCollection #-}
  fanCollection = R.fanInt . fmap (IM.fromAscList . zip [0..] . F.toList)
  {-# INLINABLE selectCollection #-}
  selectCollection _ es n = R.selectInt es n 
  {-# INLINABLE fanDiffMaybe #-}
  fanDiffMaybe _ = R.fanInt . fmap (IM.mapMaybe id . IM.fromAscList . zip [0..] . F.toList)

-- this only works for an array which has an element for every value of the key
-- could be made slightly more general, getting the ints from position in a larger set
-- but would be finicky and sacrifice some performance in the conversions. I think.
-- NB: Performing mergeOver on an array will lead to errors since the result won't have an event for each value of the key. Could we fix with never?
-- should it be mergeOver :: f (Event t a) -> Event t (Diff f a) ?  return a Diff? With maybe a "simpleMerge" version that returns the same type?
instance SeqTypes (Array k) where
  type SeqType (Array k) = ComposedIntMap
  type SeqPatchType (Array k) = ComposedPatchIntMap
  nullSeq _ _ (ComposedIntMap cim) = IM.null $ getCompose cim

instance (Enum k, Bounded k, Ix k) => ToPatchType (Array k) where
  type CollectionEventSelector (A.Array k) = R.EventSelectorInt
  {-# INLINABLE withFunctorToSeqType #-}
  withFunctorToSeqType = ComposedIntMap . Compose . IM.fromAscList . zip [0..] . fmap snd . A.assocs
  {-# INLINABLE fromSeqType #-}
  fromSeqType _ = fmap runIdentity . getCompose . unCI
  {-# INLINABLE unsafeFromSeqType #-}
  unsafeFromSeqType = fromCompleteKeyValueSet . fromSeqType (Proxy :: Proxy (Array k))
  {-# INLINABLE makePatchSeq #-}
  makePatchSeq _ h =
    ComposedPatchIntMap . Compose . R.PatchIntMap . mapWithKey (\n mv -> fmap (h $ toEnum n) mv)
  {-# INLINABLE fanCollection #-}
  fanCollection = R.fanInt . fmap (IM.fromAscList . zip [0..] . fmap snd . A.assocs)
  {-# INLINABLE selectCollection #-}
  selectCollection _ es k = R.selectInt es (fromEnum k) 
  {-# INLINABLE fanDiffMaybe #-}
  fanDiffMaybe _ = R.fanInt . fmap (IM.mapMaybe id)

-- various utilities for converting to and from underlying Patchable types

functorMappedToSeqType :: (SeqTypes f, ToPatchType f) => Functor g => (Key f -> v -> g u) -> f v -> SeqType f u g
functorMappedToSeqType h = withFunctorToSeqType . mapWithKey h
{-# INLINABLE functorMappedToSeqType #-}

toSeqType :: (Functor f, SeqTypes f, ToPatchType f) => f v -> SeqType f v Identity
toSeqType = withFunctorToSeqType . fmap Identity
{-# INLINABLE toSeqType #-}

-- generic to and fromDMap for Keyed collections
-- can be optimized for collections that have to/from ascending lists
keyedCollectionWithFunctorToDMap :: (Functor g, KeyedCollection f, Ord (Key f)) => f (g v) -> DMap (Const2 (Key f) v) g
keyedCollectionWithFunctorToDMap = DM.fromList . fmap (\(k, gv) -> Const2 k :=> gv) . toKeyValueList
{-# INLINABLE keyedCollectionWithFunctorToDMap #-}

keyedCollectionToDMap :: (KeyedCollection f, Ord (Key f)) => f v -> DMap (Const2 (Key f) v) Identity
keyedCollectionToDMap = DM.fromList . fmap (\(k, v) -> Const2 k :=> Identity v) . toKeyValueList
{-# INLINABLE keyedCollectionToDMap #-}

keyedCollectionToDMapWithKey :: (KeyedCollection f, Ord k) => (Key f -> k) -> f v -> DMap (Const2 k v) Identity
keyedCollectionToDMapWithKey g = DM.fromList . fmap (\(k,v) -> Const2 (g k) :=> Identity v) . toKeyValueList
{-# INLINABLE keyedCollectionToDMapWithKey #-}

dmapToKeyedCollection :: KeyedCollection f => DMap (Const2 (Key f) v) Identity -> f v
dmapToKeyedCollection = fromKeyValueList . fmap (\(Const2 k :=> Identity v) -> (k, v)) . DM.toList
{-# INLINABLE dmapToKeyedCollection #-}

intMapWithFunctorToDMap :: IntMap (g v) -> DMap (Const2 Int v) g
intMapWithFunctorToDMap = DM.fromAscList . fmap (\(n, gv) -> Const2 n :=> gv) . IM.toAscList
{-# INLINABLE intMapWithFunctorToDMap #-}

intMapToDMap :: IntMap v -> DMap (Const2 Int v) Identity
intMapToDMap = DM.fromAscList . fmap (\(n, v) -> Const2 n :=> Identity v) . IM.toAscList
{-# INLINABLE intMapToDMap #-}

-- NB: This assumes the f :: Int -> Key function is order preserving, that is
-- compare (f n) (f m) = compare n m
intMapToDMapWithKey :: Ord k => (Int -> k) -> IntMap v -> DMap (Const2 k v) Identity
intMapToDMapWithKey f = DM.fromAscList . fmap (\(n, v) -> Const2 (f n) :=> Identity v) . IM.toAscList
{-# INLINABLE intMapToDMapWithKey #-}

-- generic to and from ComposedIntMap for Keyed collections
-- can be optimized for collections that have to/from ascending lists
keyedCollectionWithFunctorToComposedIntMap :: (Functor g, KeyedCollection f) => (Key f -> Int) -> f (g v) -> ComposedIntMap v g
keyedCollectionWithFunctorToComposedIntMap toInt = ComposedIntMap . Compose . IM.fromList . fmap (first toInt) . toKeyValueList
{-# INLINABLE keyedCollectionWithFunctorToComposedIntMap #-}

keyedCollectionToComposedIntMap :: KeyedCollection f => (Key f -> Int) -> f v -> ComposedIntMap v Identity
keyedCollectionToComposedIntMap toInt = keyedCollectionWithFunctorToComposedIntMap toInt . fmap Identity
{-# INLINABLE keyedCollectionToComposedIntMap #-}

composedIntMapToKeyedCollection :: KeyedCollection f => (Int -> Key f) -> ComposedIntMap v Identity -> f v
composedIntMapToKeyedCollection toKey = fromKeyValueList . fmap (first toKey) . IM.toList . fmap runIdentity . getCompose . unCI
{-# INLINABLE composedIntMapToKeyedCollection #-}
