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
{-# LANGUAGE ConstraintKinds #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.ToPatchType
  (
    ToPatchType(..)
  , SeqTypes(..)
  , toSeqType
  , functorMappedToSeqType
  , distributeOverDynPure
  , mergeOver
  , MapDiff
  , ArrayDiff(..)
  ) where

import           Reflex.Collections.KeyedCollection (KeyedCollection(..))
import           Reflex.Collections.ComposedIntMap ( ComposedIntMap(..)
                                                   , ComposedPatchIntMap (..))
import           Reflex.Collections.Sequenceable ( ReflexMergeable(..)
                                                 , PatchSequenceable(..)
                                                 , ReflexSequenceable(..))
                 
import qualified Reflex.Collections.DMapIso as DMI
import qualified Reflex.Collections.IntMapIso as IMI
import           Reflex.Collections.Diffable (Diffable(..), MapDiff, ArrayDiff(..))


import qualified Reflex as R

import           Data.Dependent.Map      (DMap, DSum ((:=>)))
import qualified Data.Dependent.Map      as DM
import           Reflex.Patch            (PatchDMap (..))
import           Data.Functor.Compose    (Compose(..), getCompose)
import           Data.Functor.Misc       (Const2 (..))
import           Data.Functor.Identity   (Identity(..), runIdentity)                 
import           Data.Proxy              (Proxy (..))
import           Data.Kind               (Type)

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

-- NB: Performing mergeOver on an array will lead to errors since the result won't have an event for each value of the key. Could we fix with never?
-- should it be mergeOver :: f (Event t a) -> Event t (Diff f a) ?  return a Diff? With maybe a "simpleMerge" version that returns the same type?



-- | Type families for the sequenceable and patch types.  Always DMap for now
class SeqTypes (f :: Type -> Type) (v :: Type) where
  type SeqType f v  :: (Type -> Type) -> Type
  type SeqPatchType f v :: (Type -> Type) -> Type

-- This class has the capabilities to translate f v and its difftype into types
-- that are sequenceable, and then bring the original type back
-- This requires that the Diff type be mapped to the correct type for diffing at the sequenceable level (e.g., as a DMap).
-- I think, if we had quantified constraints, we could add (forall v. GCompare (FanSelectKey f v))
-- might be able to do it now with Data.Constraint.Forall but that would propagate complication
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
  withFunctorToSeqType = DMI.toDMapWithFunctor
  makePatchSeq = DMI.makePatch 
  fromSeqType = DMI.fromDMap
  makeSelectKey pf _ = DMI.makeDMapKey pf
  doFan =  R.fan . fmap (DMI.toDMapWithFunctor . fmap Identity)
  diffToFanType = DMI.diffToFanInput --withFunctorToSeqType . fmap Identity . M.mapMaybe id . g44etCompose

instance SeqTypes (HashMap k) v where
  type SeqType (HashMap k) v = DMap (Const2 k v)
  type SeqPatchType (HashMap k) v = PatchDMap (Const2 k v)

instance (Ord k, Eq k, Hashable k) => ToPatchType (HashMap k) where
  type FanSelectKey (HashMap k) = Const2 k
  withFunctorToSeqType = DMI.toDMapWithFunctor
  makePatchSeq = DMI.makePatch
  fromSeqType = DMI.fromDMap
  makeSelectKey _ _ = Const2
  doFan =  R.fan . fmap (DMI.toDMapWithFunctor . fmap Identity)
  diffToFanType = DMI.diffToFanInput --withFunctorToSeqType . fmap Identity . HM.mapMaybe id . getCompose
  

{-
toComposedIMWithFunctor :: Functor g => IntMap (g v) -> ComposedIntMap v g
toComposedIntMapWithFunctor = ComposedIntMap . Compose 

fromComposedIntMap :: ComposedIntMap v Identity -> IntMap v
fromComposedIntMap = fmap runIdentity . getCompose . unCI

-- This assumes GCompare (DMap (Const2 Int v)) is compatible with (Ord Int)
dmapToIntMap :: DMap (Const2 Int v) g -> IntMap (g v)
dmapToIntMap = IM.fromAscList . fmap (\((Const2 n) :=> gv) -> (n, gv)) . DM.toAscList
-}

intMapToDMap :: IntMap (g v) -> DMap (Const2 Int v) g
intMapToDMap = DM.fromAscList . fmap (\(n, gv) -> (Const2 n) :=> gv) . IM.toAscList 

-- these will all come from IntMapIso functions

instance SeqTypes IntMap v where
  type SeqType IntMap v = ComposedIntMap v
  type SeqPatchType IntMap v = ComposedPatchIntMap v

instance ToPatchType IntMap where
  type FanSelectKey IntMap = Const2 Int 
  withFunctorToSeqType = IMI.toComposedIntMapWithFunctor
  fromSeqType = IMI.fromComposedIntMap
  makePatchSeq = IMI.makePatch 
  makeSelectKey pf _ = IMI.makeDMapKey pf
  doFan = R.fan . fmap (intMapToDMap . fmap Identity)
  diffToFanType = IMI.diffToFanInput 

instance SeqTypes (Array k) v where
  type SeqType (Array k) v = ComposedIntMap v
  type SeqPatchType (Array k) v = ComposedPatchIntMap v

instance (Enum k, Bounded k, Ix k) => ToPatchType (Array k) where
  type FanSelectKey (Array k) = Const2 k
  withFunctorToSeqType = IMI.toComposedIntMapWithFunctor
  fromSeqType = IMI.fromComposedIntMap
  makePatchSeq = IMI.makePatch
  makeSelectKey pf _  = IMI.makeDMapKey pf
  doFan = R.fan . fmap (DMI.keyedCollectionToDMapWithFunctor . fmap Identity)
  diffToFanType = IMI.diffToFanInput



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
