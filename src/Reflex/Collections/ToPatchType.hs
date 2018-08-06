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
{-# LANGUAGE DefaultSignatures #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.ToPatchType
  (
    SeqType
  , SeqPatchType
  , ToPatchType(..)
  , toSeqType
  , distributeOverDynPure
  , mergeOver
  , MapDiff
  , ArrayDiff(..)
  ) where

import           Reflex.Collections.KeyedCollection (KeyedCollection(..), MapDiff, ArrayDiff(..))
import           Reflex.Collections.Sequenceable (ReflexSequenceable(..), PatchSequenceable(..))

import qualified Reflex as R

import           Data.Dependent.Map      (DMap, DSum ((:=>)))
import qualified Data.Dependent.Map      as DM
import           Reflex.Patch            (PatchDMap (..))
import           Data.Functor.Compose    (getCompose)
import           Data.Functor.Misc       (ComposeMaybe (..), Const2 (..),
                                          dmapToMap, mapWithFunctorToDMap)
import           Data.Functor.Identity   (Identity(..))                 
import           Data.Proxy              (Proxy (..))
import           Data.Kind               (Type)

import           Data.Map (Map)
--import qualified Data.Map as M
import           Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import           Data.Hashable           (Hashable)
import           Data.HashMap.Strict     (HashMap)
import           Data.Array (Array, Ix)



toSeqType :: (Functor f, ToPatchType f) => f v -> SeqType f v Identity
toSeqType = withFunctorToSeqType . fmap Identity

-- | Generalize distributeMapOverDynPure
distributeOverDynPure :: ( R.Reflex t
                         , ToPatchType f 
                         , PatchSequenceable (SeqType f v) (SeqPatchType f v)
                         , ReflexSequenceable (SeqType f v))
  => f (R.Dynamic t v) -> R.Dynamic t (f v)
distributeOverDynPure = fmap fromSeqType . sequenceDynamic . withFunctorToSeqType

-- | Generalizes "mergeMap" to anything with ToPatchType where the Patches are Sequenceable.
mergeOver :: forall t f v. ( R.Reflex t
                           , ToPatchType f
                           , PatchSequenceable (SeqType f v) (SeqPatchType f v)
                           , ReflexSequenceable (SeqType f v))
  => f (R.Event t v) -> R.Event t (f v)
mergeOver fEv =
  let id2 = const id :: (k -> R.Event t v -> R.Event t v)
  in fmap fromSeqType . mergeEvents $ toSeqTypeWithFunctor id2 fEv

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
type family SeqType (f :: Type -> Type) (v :: Type) :: ((Type -> Type) -> Type)
type family SeqPatchType (f :: Type -> Type) (v :: Type) :: ((Type -> Type) -> Type)


-- This class has the capabilities to translate f v and its difftype into types
-- that are sequenceable, and then bring the original type back
-- This requires that the Diff type be mapped to the correct type for diffing at the sequenceable level (e.g., as a DMap).
class KeyedCollection f => ToPatchType (f :: Type -> Type) where
  withFunctorToSeqType :: Functor g => f (g v) -> SeqType f v g
  fromSeqType :: SeqType f a Identity -> f a
  
  toSeqTypeWithFunctor :: Functor g => (Key f -> v -> g u) -> f v -> SeqType f u g
  toSeqTypeWithFunctor h = withFunctorToSeqType . mapWithKey h 

  makePatchSeq :: Functor g => Proxy f -> (Key f -> v -> g u) -> Diff f v -> SeqPatchType f u g

type instance SeqType (Map k) v = DMap (Const2 k v)
type instance SeqPatchType (Map k) v = PatchDMap (Const2 k v)

instance Ord k => ToPatchType (Map k) where
  withFunctorToSeqType = mapWithFunctorToDMap
  makePatchSeq _ h = PatchDMap . mapWithFunctorToDMap . mapWithKey (\k mv -> ComposeMaybe $ (fmap (h k) mv)) . getCompose
  fromSeqType = dmapToMap

type instance SeqType (HashMap k) v = DMap (Const2 k v)
type instance SeqPatchType (HashMap k) v = PatchDMap (Const2 k v)

instance (Ord k, Eq k, Hashable k) => ToPatchType (HashMap k) where
  withFunctorToSeqType = keyedCollectionToDMapWithFunctor --hashMapWithFunctorToDMap
  makePatchSeq = makePatchFromMapDiff
  fromSeqType = dmapToKeyedCollection

type instance SeqType IntMap v = DMap (Const2 Int v)
type instance SeqPatchType IntMap v = PatchDMap (Const2 Int v)

instance ToPatchType IntMap where
  withFunctorToSeqType = intMapWithFunctorToDMap
  makePatchSeq _ h = PatchDMap .  intMapWithFunctorToDMap . mapWithKey (\k mv -> ComposeMaybe $ (fmap (h k) mv)) . getCompose
  fromSeqType = IM.fromDistinctAscList . fmap (\(Const2 k :=> Identity v) -> (k, v)) . DM.toAscList

-- this one is more efficient since it uses the ascending list
intMapWithFunctorToDMap :: Functor g => IntMap (g v) -> DMap (Const2 Int v) g
intMapWithFunctorToDMap = DM.fromDistinctAscList . fmap (\(k, v) -> Const2 k :=> v) . IM.toAscList

type instance SeqType (Array k) v = DMap (Const2 k v)
type instance SeqPatchType (Array k) v = PatchDMap (Const2 k v)

instance Ix k => ToPatchType (Array k) where
  withFunctorToSeqType = keyedCollectionToDMapWithFunctor --arrayWithFunctorToDMap
  fromSeqType = dmapToKeyedCollection
  makePatchSeq _ h (ArrayDiff ad) = PatchDMap .  DM.fromList $ fmap (\(k, v) -> Const2 k :=> (ComposeMaybe . Just $ h k v)) ad
