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
module Reflex.Collections.DMapIso
  (
    DMapIso(..)
  , DiffToPatchDMap(..)
  ) where

import           Reflex.Collections.KeyedCollection (KeyedCollection(..))
import           Reflex.Collections.Diffable (Diffable(Diff), MapDiff, ArrayDiff(..))

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


import           Data.Map                (Map)
import qualified Data.Map                as M
import           Data.IntMap             (IntMap)
import qualified Data.IntMap             as IM
import           Data.Hashable           (Hashable)
import           Data.HashMap.Strict     (HashMap)
import qualified Data.HashMap.Strict     as HM
import           Data.Array             (Array, Ix)
import qualified Data.Array             as A


-- generic to and fromDMap for Keyed collections
-- can be optimized for collections that have to/from ascending lists
keyedCollectionToDMapWithFunctor :: (Functor g, KeyedCollection f, Ord (Key f)) => f (g v) -> DMap (Const2 (Key f) v) g
keyedCollectionToDMapWithFunctor = DM.fromList . fmap (\(k, v) -> Const2 k :=> v) . toKeyValueList

keyedCollectionToDMap :: (KeyedCollection f, Ord (Key f)) => f v -> DMap (Const2 (Key f) v) Identity
keyedCollectionToDMap = keyedCollectionToDMapWithFunctor . fmap Identity

dmapToKeyedCollectionWithFunctor :: (Functor g, KeyedCollection f) => DMap (Const2 (Key f) v) g -> f (g v)
dmapToKeyedCollectionWithFunctor = fromKeyValueList . fmap (\(Const2 k :=> gv) -> (k, gv)) . DM.toList

dmapToKeyedCollection :: KeyedCollection f => DMap (Const2 (Key f) v) Identity -> f v
dmapToKeyedCollection = fromKeyValueList . fmap (\(Const2 k :=> Identity v) -> (k, v)) . DM.toList 

-- If we had Quantified Constraints, we might add (forall v. (GCompare (DMapKey f v))) to the constraints
class KeyedCollection f => DMapIso (f :: Type -> Type) where
  type DMapKey f :: Type -> Type -> Type
  makeDMapKey :: Proxy f -> Key f -> DMapKey f v v 
  toDMapWithFunctor :: Functor g => f (g v) -> DMap (DMapKey f v) g
  fromDMap :: DMap (DMapKey f v) Identity -> f v

instance Ord k => DMapIso (Map k) where
  type DMapKey (Map k) = Const2 k
  makeDMapKey _ = Const2
  toDMapWithFunctor = mapWithFunctorToDMap
  fromDMap = dmapToMap

instance (Eq k, Ord k, Hashable k) => DMapIso (HashMap k) where
  type DMapKey (HashMap k) = Const2 k
  makeDMapKey _ = Const2
  toDMapWithFunctor = keyedCollectionToDMapWithFunctor
  fromDMap = dmapToKeyedCollection

instance DMapIso (IntMap) where
  type DMapKey IntMap = Const2 Int
  makeDMapKey _ = Const2
  toDMapWithFunctor = intMapWithFunctorToDMap
  fromDMap = IM.fromDistinctAscList . fmap (\(Const2 k :=> Identity v) -> (k, v)) . DM.toAscList
  
-- this one is more efficient since it uses the ascending list
intMapWithFunctorToDMap :: Functor g => IntMap (g v) -> DMap (Const2 Int v) g
intMapWithFunctorToDMap = DM.fromDistinctAscList . fmap (\(k, v) -> Const2 k :=> v) . IM.toAscList

instance Ix k => DMapIso (Array k) where
  type DMapKey (Array k) = Const2 k
  makeDMapKey _ = Const2
  toDMapWithFunctor = keyedCollectionToDMapWithFunctor
  fromDMap = dmapToKeyedCollection

-- This class seems like it's purely for overloading.
class (DMapIso f, KeyedCollection f, Diffable f) => DiffToPatchDMap (f :: Type -> Type) where
  makePatch :: Functor g => Proxy f -> (Key f -> v -> g u) -> Diff f v -> PatchDMap (DMapKey f u) g

instance Ord k => DiffToPatchDMap (Map k) where
  makePatch _ h = PatchDMap . keyedCollectionToDMapWithFunctor . mapWithKey (\k mv -> ComposeMaybe $ (fmap (h k) mv)) . getCompose   

-- TODO: DO we need Eq and Ord here or is that only because we are relying on KeyedCollection?
instance (Eq k, Ord k, Hashable k) => DiffToPatchDMap (HashMap k) where
  makePatch _ h = PatchDMap . keyedCollectionToDMapWithFunctor . mapWithKey (\k mv -> ComposeMaybe $ (fmap (h k) mv)) . getCompose   

instance DiffToPatchDMap IntMap where
  makePatch _ h = PatchDMap . keyedCollectionToDMapWithFunctor . mapWithKey (\k mv -> ComposeMaybe $ (fmap (h k) mv)) . getCompose   

-- TODO: DO we need Ord here or is that only because we are relying on KeyedCollection?  
instance (Ix k, Ord k) => DiffToPatchDMap (Array k) where
  makePatch _ h (ArrayDiff ad) = PatchDMap .  DM.fromList $ fmap (\(k, v) -> Const2 k :=> (ComposeMaybe . Just $ h k v)) ad

  
