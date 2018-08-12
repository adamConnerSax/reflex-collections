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
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.ToPatchType
  (
    SeqType
  , SeqPatchType
  , ToPatchType(..)
  , SeqTypes(..)
  , toSeqType
  , functorMappedToSeqType
  , distributeOverDynPure
  , mergeOver
--  , DMappable(..)
  , MapDiff
  , ArrayDiff(..)
  ) where

import           Reflex.Collections.KeyedCollection (KeyedCollection(..))
import           Reflex.Collections.Sequenceable ( ReflexMergeable(..)
                                                 , PatchSequenceable(..)
                                                 , ReflexSequenceable(..)
                                                 , ComposedIntMap(..)
                                                 , ComposedPatchIntMap (..))
import           Reflex.Collections.DMapIso (DMapIso(..))
import           Reflex.Collections.Diffable (Diffable(..), MapDiff, ArrayDiff(..))

import qualified Reflex as R

import           Data.Dependent.Map      (DMap, DSum ((:=>)))
import qualified Data.Dependent.Map      as DM
import           Reflex.Patch            (PatchDMap (..))
import           Data.Functor.Compose    (Compose(..), getCompose)
import           Data.Functor.Misc       (ComposeMaybe (..), Const2 (..),
                                          dmapToMap, mapWithFunctorToDMap)
import           Data.Functor.Identity   (Identity(..), runIdentity)                 
import           Data.Proxy              (Proxy (..))
import           Data.Kind               (Type)
import           Data.Monoid             (Monoid(..))

import           Data.Map (Map)
import qualified Data.Map as M
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import           Data.Hashable           (Hashable)
import           Data.HashMap.Strict     (HashMap)
import qualified Data.HashMap.Strict     as HM
import           Data.Array (Array, Ix)



toSeqType :: (Functor f, SeqTypes f v, ToPatchType f) => f v -> SeqType f v Identity
toSeqType = withFunctorToSeqType . fmap Identity

-- | Generalize distributeMapOverDynPure
distributeOverDynPure :: ( R.Reflex t
                         , ToPatchType f
                         , SeqTypes f v
                         , PatchSequenceable (SeqType f v) (SeqPatchType f v)
                         , ReflexSequenceable (SeqType f v))
  => f (R.Dynamic t v) -> R.Dynamic t (f v)
distributeOverDynPure = fmap fromSeqType . sequenceDynamic . withFunctorToSeqType

-- | Generalizes "mergeMap" to anything with ToPatchType where the Patches are Sequenceable.
mergeOver :: forall t f v. ( R.Reflex t
                           , ToPatchType f
                           , SeqTypes f v
                           , PatchSequenceable (SeqType f v) (SeqPatchType f v)
                           , ReflexMergeable (SeqType f v))
  => f (R.Event t v) -> R.Event t (f v)
mergeOver fEv =
  let id2 = const id :: (k -> R.Event t v -> R.Event t v)
  in fmap fromSeqType . mergeEvents $ functorMappedToSeqType id2 fEv

-- generic to and fromDMap for Keyed collections
-- can be optimized for collections that have to/from ascending lists
keyedCollectionToDMapWithFunctor :: (KeyedCollection f, Ord (Key f)) => f (g v) -> DMap (Const2 (Key f) v) g
keyedCollectionToDMapWithFunctor = DM.fromList . fmap (\(k, v) -> Const2 k :=> v) . toKeyValueList

keyedCollectionToDMap :: (KeyedCollection f, Ord (Key f)) => f v -> DMap (Const2 (Key f) v) Identity
keyedCollectionToDMap = keyedCollectionToDMapWithFunctor . fmap Identity

dmapToKeyedCollection :: KeyedCollection f => DMap (Const2 (Key f) v) Identity -> f v
dmapToKeyedCollection = fromKeyValueList . fmap (\(Const2 k :=> Identity v) -> (k, v)) . DM.toList 

makePatchFromMapDiff :: ( Functor g
                        , KeyedCollection f
                        , Ord (Key f)
                        , Diff f ~ MapDiff f)
                     => Proxy f -> (Key f -> v -> g u) -> Diff f v -> PatchDMap (Const2 (Key f) u) g
makePatchFromMapDiff _ h =
  PatchDMap . keyedCollectionToDMapWithFunctor . mapWithKey (\k mv -> ComposeMaybe $ (fmap (h k) mv)) . getCompose                     

-- | Type families for the sequenceable and patch types.  Always DMap for now
class SeqTypes (f :: Type -> Type) (v :: Type) where
  type SeqType f v  :: (Type -> Type) -> Type
  type SeqPatchType f v :: (Type -> Type) -> Type

-- This class has the capabilities to translate f v and its difftype into types
-- that are sequenceable, and then bring the original type back
-- This requires that the Diff type be mapped to the correct type for diffing at the sequenceable level (e.g., as a DMap).
class (KeyedCollection f, Diffable f) => ToPatchType (f :: Type -> Type) where
  type FanSelectKey f :: Type -> Type -> Type -- NB: This is a key for a DMap since fan uses DMap
  withFunctorToSeqType :: SeqTypes f v => Functor g => f (g v) -> SeqType f v g
  fromSeqType :: SeqTypes f a => SeqType f a Identity -> f a
  makePatchSeq :: (Functor g, SeqTypes f u) => Proxy f -> (Key f -> v -> g u) -> Diff f v -> SeqPatchType f u g
  makeSelectKey :: Proxy f -> Proxy v -> Key f -> FanSelectKey f v v
  doFan :: (R.Reflex t, DM.GCompare (FanSelectKey f v))=> R.Event t (f v) -> R.EventSelector t (FanSelectKey f v)
  diffToFanType :: Proxy f -> Diff f v -> DMap (FanSelectKey f v) Identity 
  doDiffFan :: (R.Reflex t, DM.GCompare (FanSelectKey f v)) => Proxy f -> R.Event t (Diff f v) -> R.EventSelector t (FanSelectKey f v)
  doDiffFan pf = R.fan . fmap (diffToFanType pf) 
  
functorMappedToSeqType :: (SeqTypes f u, ToPatchType f) => Functor g => (Key f -> v -> g u) -> f v -> SeqType f u g
functorMappedToSeqType h = withFunctorToSeqType . mapWithKey h 

-- these are all boring, just using DMapIso and DiffToPatchDMap
-- but we can't instance them directly without overlapping instances for anything else
instance SeqTypes (Map k) v where
  type SeqType (Map k) v = DMap (Const2 k v)
  type SeqPatchType (Map k) v = PatchDMap (Const2 k v)

instance Ord k => ToPatchType (Map k) where
  type FanSelectKey (Map k) = Const2 k 
  withFunctorToSeqType = toDMapWithFunctor
  makePatchSeq = makePatch 
  fromSeqType = fromDMap
  makeSelectKey _ _ = Const2
  doFan =  R.fan . fmap (toDMapWithFunctor . fmap Identity)
  diffToFanType _ = withFunctorToSeqType . fmap Identity . M.mapMaybe id . getCompose

instance SeqTypes (HashMap k) v where
  type SeqType (HashMap k) v = DMap (Const2 k v)
  type SeqPatchType (HashMap k) v = PatchDMap (Const2 k v)

instance (Ord k, Eq k, Hashable k) => ToPatchType (HashMap k) where
  type FanSelectKey (HashMap k) = Const2 k
  withFunctorToSeqType = toDMapWithFunctor
  makePatchSeq = makePatch
  fromSeqType = fromDMap
  makeSelectKey _ _ = Const2
  doFan =  R.fan . fmap (toDMapWithFunctor . fmap Identity)
  diffToFanType _ = withFunctorToSeqType . fmap Identity . HM.mapMaybe id . getCompose
  
instance SeqTypes IntMap v where
  type SeqType IntMap v = ComposedIntMap v
  type SeqPatchType IntMap v = ComposedPatchIntMap v

toComposedIntMapWithFunctor :: Functor g => IntMap (g v) -> ComposedIntMap v g
toComposedIntMapWithFunctor = ComposedIntMap . Compose 

fromComposedIntMap :: ComposedIntMap v Identity -> IntMap v
fromComposedIntMap = fmap runIdentity . getCompose . unCI

-- This assumes GCompare (DMap (Const2 Int v)) is compatible with (Ord Int)
dmapToIntMap :: DMap (Const2 Int v) g -> IntMap (g v)
dmapToIntMap = IM.fromAscList . fmap (\((Const2 n) :=> gv) -> (n, gv)) . DM.toAscList

intMapToDMap :: IntMap (g v) -> DMap (Const2 Int v) g
intMapToDMap = DM.fromAscList . fmap (\(n, gv) -> (Const2 n) :=> gv) . IM.toAscList 

instance ToPatchType IntMap where
  type FanSelectKey IntMap = Const2 Int 
  withFunctorToSeqType = toComposedIntMapWithFunctor
  fromSeqType = fromComposedIntMap
  makePatchSeq _ h = ComposedPatchIntMap . Compose . R.PatchIntMap . mapWithKey (\k mv -> (fmap (h k) mv)) . getCompose
  makeSelectKey _ _ = Const2
  doFan = R.fan . fmap (intMapToDMap . fmap Identity)
  diffToFanType _ = intMapToDMap . fmap Identity . IM.mapMaybe id . getCompose

instance SeqTypes (Array k) v where
  type SeqType (Array k) v = DMap (Const2 k v)
  type SeqPatchType (Array k) v = PatchDMap (Const2 k v)

instance Ix k => ToPatchType (Array k) where
  type FanSelectKey (Array k) = Const2 k
  withFunctorToSeqType = toDMapWithFunctor
  fromSeqType = fromDMap
  makePatchSeq = makePatch
  makeSelectKey _ _ = Const2
  doFan = R.fan . fmap (withFunctorToSeqType . fmap Identity)
  diffToFanType _ = DM.fromList . fmap (\(k,v) -> Const2 k :=> Identity v) . unArrayDiff

{-
newtype DMappable f v = DMappable { unDMappable :: f v } deriving (Functor, Foldable)

instance KeyedCollection f => KeyedCollection (DMappable f) where
  type Key (DMappable f) = Key f
  mapWithKey h = DMappable . mapWithKey h . unDMappable
  toKeyValueList = toKeyValueList . unDMappable
  fromKeyValueList = DMappable . fromKeyValueList

instance (KeyedCollection f, Diffable f) => Diffable (DMappable f) where
  type Diff (DMappable f) = Diff f
  mapDiffWithKey _ = mapDiffWithKey (Proxy :: Proxy f) -- use version from Diffable f since Diff is the same 
  diffNoEq old new = diffNoEq (unDMappable old) (unDMappable new) 
  diff old new = diff (unDMappable old) (unDMappable new)
  applyDiff patch old = DMappable $ applyDiff patch (unDMappable old)
  diffOnlyKeyChanges old new = diffOnlyKeyChanges (unDMappable old) (unDMappable new)
  editDiffLeavingDeletes _ = editDiffLeavingDeletes (Proxy :: Proxy f)

instance Monoid (f v) => Monoid (DMappable f v) where
  mempty = DMappable mempty
  mappend a b = DMappable $ mappend (unDMappable a) (unDMappable b) 
    
instance DMapIso f => SeqTypes (DMappable f) v where
  type SeqType (DMappable f) v = DMap (DMapKey f v) 
  type SeqPatchType (DMappable f) v = PatchDMap (DMapKey f v)

--instance DMapIso f => DMapIso (DMappable f) where
--  type DMapKey (DMappable f) = DMapKey f
--  toDMapWithFunctor = toDMapWithFunctor . unDMappable
--  fromDMap = DMappable . fromDMap

--instance DiffToPatchDMap f => DiffToPatchDMap (DMappable f) where
--  makePatch _ = makePatch (Proxy :: Proxy f)

instance (KeyedCollection f, DMapIso f, DiffToPatchDMap f) => ToPatchType (DMappable f) where
  withFunctorToSeqType = toDMapWithFunctor . unDMappable
  fromSeqType = DMappable . fromDMap
  makePatchSeq _ = makePatch (Proxy :: Proxy f)
-}
