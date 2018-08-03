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
    ToPatchType(..)
  , toSeqType
  , distributeOverDynPure
  , mergeOver
  ) where

import           Reflex.Collections.KeyMappable (KeyMappable(..))
import           Reflex.Collections.Sequenceable (ReflexSequenceable(..), PatchSequenceable(..))

import qualified Reflex as R

import           Data.Dependent.Map      (DMap, DSum ((:=>)))
import qualified Data.Dependent.Map      as DM
import           Reflex.Patch            (PatchDMap (..))
import           Data.Functor.Compose    (Compose, getCompose)
import           Data.Functor.Misc       (ComposeMaybe (..), Const2 (..),
                                          dmapToMap, mapWithFunctorToDMap)
import           Data.Functor.Identity   (Identity(..))                 
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
import qualified Data.Array as A



toSeqType :: forall f k v. (Functor f, ToPatchType f k v v) => Proxy k -> f v -> (SeqType f k (SeqTypeKey f k v) Identity)
toSeqType pk = withFunctorToSeqType pk (Proxy :: Proxy v) . fmap Identity

-- | Generalize distributeMapOverDynPure
distributeOverDynPure :: forall t f k v. ( R.Reflex t
                                         , ToPatchType f k v v
                                         , PatchSequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k v)
                                         , ReflexSequenceable ((SeqType f k) (SeqTypeKey f k v)))
  => Proxy k -> f (R.Dynamic t v) -> R.Dynamic t (f v)
distributeOverDynPure pk =
  let pv = Proxy :: Proxy v
  in fmap (fromSeqType pk pv) . traverseDynamic . (withFunctorToSeqType pk pv)

-- | Generalizes "mergeMap" to anything with ToPatchType where the Patches are Sequenceable.
mergeOver :: forall t f k v. ( R.Reflex t
                             , ToPatchType f k (R.Event t v) v
                             , PatchSequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k v)
                             , ReflexSequenceable ((SeqType f k) (SeqTypeKey f k v)))
  => Proxy k -> f (R.Event t v) -> R.Event t (f v)
mergeOver pk fEv =
  let id2 = const id :: (k -> R.Event t v -> R.Event t v)
  in fmap (fromSeqType pk (Proxy :: Proxy (R.Event t v))) . mergeEvents $ toSeqTypeWithFunctor id2 fEv


-- This class has the capabilities to translate f v and its difftype into types
-- that are sequenceable, and then bring the original type back
-- This requires that the Diff type be mapped to the correct type for diffing at the sequenceable level (e.g., as a DMap).
class KeyMappable f k v => ToPatchType (f :: Type -> Type) k v a where
  type Diff f k :: Type -> Type
  type SeqType f k :: (Type -> Type) -> (Type -> Type) -> Type
  type SeqPatchType f k :: (Type -> Type) -> (Type -> Type) -> Type
  type SeqTypeKey f k a :: Type -> Type
  withFunctorToSeqType :: Functor g => Proxy k -> Proxy v -> f (g a) -> SeqType f k (SeqTypeKey f k a) g
  fromSeqType :: Proxy k -> Proxy v -> SeqType f k (SeqTypeKey f k a) Identity -> f a
  
  toSeqTypeWithFunctor :: Functor g => (k -> v -> g a) -> f v -> SeqType f k (SeqTypeKey f k a) g
  toSeqTypeWithFunctor h = withFunctorToSeqType (Proxy :: Proxy k) (Proxy :: Proxy v) . mapWithKey h 

  makePatchSeq :: Functor g => Proxy f -> (k -> v -> g a) -> Diff f k v -> SeqPatchType f k (SeqTypeKey f k a) g

instance Ord k => ToPatchType (Map k) k v a where
  type Diff (Map k) k = Compose (Map k) Maybe
  type SeqType (Map k) k = DMap
  type SeqPatchType (Map k) k = PatchDMap
  type SeqTypeKey (Map k) k a = Const2 k a
  withFunctorToSeqType _ _ = mapWithFunctorToDMap
  makePatchSeq _ h = PatchDMap . mapWithFunctorToDMap . mapWithKey (\k mv -> ComposeMaybe $ (fmap (h k) mv)) . getCompose
  fromSeqType _ _ = dmapToMap

instance (Ord k, Eq k, Hashable k) => ToPatchType (HashMap k) k v a where
  type Diff (HashMap k) k = Compose (HashMap k) Maybe
  type SeqType (HashMap k) k = DMap
  type SeqPatchType (HashMap k) k = PatchDMap
  type SeqTypeKey (HashMap k) k a = Const2 k a
  withFunctorToSeqType _ _ = hashMapWithFunctorToDMap
  makePatchSeq _ h = PatchDMap .  hashMapWithFunctorToDMap . mapWithKey (\k mv -> ComposeMaybe $ (fmap (h k) mv)) . getCompose
  fromSeqType _ _ = HM.fromList . fmap (\(Const2 k :=> Identity v) -> (k, v)) . DM.toList 

hashMapWithFunctorToDMap :: (Functor g, Ord k, Hashable k) => HashMap k (g v) -> DMap (Const2 k v) g  
hashMapWithFunctorToDMap = DM.fromList . fmap (\(k, v) -> Const2 k :=> v) . HM.toList

instance ToPatchType IntMap Int v a where
  type Diff (IntMap) Int = Compose IntMap Maybe
  type SeqType (IntMap) Int = DMap
  type SeqPatchType (IntMap) Int = PatchDMap
  type SeqTypeKey (IntMap) Int a = Const2 Int a
  withFunctorToSeqType _ _ = intMapWithFunctorToDMap
  makePatchSeq _ h = PatchDMap .  intMapWithFunctorToDMap . mapWithKey (\k mv -> ComposeMaybe $ (fmap (h k) mv)) . getCompose
  fromSeqType _ _ = IM.fromDistinctAscList . fmap (\(Const2 k :=> Identity v) -> (k, v)) . DM.toAscList

intMapWithFunctorToDMap :: Functor g => IntMap (g v) -> DMap (Const2 Int v) g
intMapWithFunctorToDMap = DM.fromDistinctAscList . fmap (\(k, v) -> Const2 k :=> v) . IM.toAscList


newtype ArrayDiff k v = ArrayDiff { diff :: [(k,v)] }

instance Ix k => ToPatchType (Array k) k v a where
  type Diff (Array k) k = ArrayDiff k
  type SeqType (Array k) k = DM.DMap
  type SeqPatchType (Array k) k = PatchDMap
  type SeqTypeKey (Array k) k a = Const2 k a
  withFunctorToSeqType _ _ = arrayWithFunctorToDMap
  fromSeqType _ _ dm = dmapToArray dm
  makePatchSeq _ h (ArrayDiff ad) = PatchDMap .  DM.fromList $ fmap (\(k, v) -> Const2 k :=> (ComposeMaybe . Just $ h k v)) ad

arrayWithFunctorToDMap :: (Functor g, A.Ix k) => A.Array k (g v) -> DMap (Const2 k v) g
arrayWithFunctorToDMap = DM.fromList . fmap (\(k, gv) -> Const2 k :=> gv) . A.assocs

dmapToArray :: Ix k => DMap (Const2 k v) Identity -> Array k v
dmapToArray dm =
  let kvPairs = fmap (\(Const2 k :=> Identity v) -> (k, v)) $ DM.toList dm
      indices = fst <$> kvPairs
      in A.array (minimum indices, maximum indices) kvPairs
