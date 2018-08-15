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
module Reflex.Collections.IntMapIso
  (
    IntMapIso(..)
  ) where

import           Reflex.Collections.KeyedCollection (KeyedCollection(..))
import           Reflex.Collections.Diffable (Diffable(Diff), ArrayDiff(..))
import           Reflex.Collections.ComposedIntMap ( ComposedIntMap(..)
                                                   , ComposedPatchIntMap(..))
import           Reflex.Collections.DMapIso (keyedCollectionToDMapWithFunctor) -- still need DMaps for the fans
                 

import qualified Reflex as R

import           Data.Dependent.Map      (DMap, DSum ((:=>)))
import qualified Data.Dependent.Map      as DM
import           Data.Functor.Compose    (Compose(..),getCompose)
import           Data.Functor.Misc       (Const2 (..))
import           Data.Functor.Identity   (Identity(..))                 
import           Data.Proxy              (Proxy (..))
import           Data.Kind               (Type)

import           Data.IntMap             (IntMap)
import qualified Data.IntMap             as IM
import           Data.Array             (Array, Ix)
import qualified Data.Array             as A


-- generic to and from ComposedIntMap for Keyed collections
-- can be optimized for collections that have to/from ascending lists
keyedCollectionToComposedIntMapWithFunctor :: (Functor g, KeyedCollection f) => (Key f -> Int) -> f (g v) -> ComposedIntMap v g
keyedCollectionToComposedIntMapWithFunctor toInt = ComposedIntMap . Compose . IM.fromList . fmap (\(k, gv) -> ( toInt k,  gv)) . toKeyValueList

keyedCollectionToComposedIntMap :: KeyedCollection f => (Key f -> Int) -> f v -> ComposedIntMap v Identity
keyedCollectionToComposedIntMap toInt = keyedCollectionToComposedIntMapWithFunctor toInt . fmap Identity

composedIntMapToKeyedCollectionWithFunctor :: (Functor g, KeyedCollection f) => (Int -> Key f) -> ComposedIntMap v g -> f (g v)
composedIntMapToKeyedCollectionWithFunctor toKey = fromKeyValueList . fmap (\(n, gv) -> (toKey n, gv)) . IM.toList . getCompose . unCI

composedIntMapToKeyedCollection :: KeyedCollection f => (Int -> Key f) -> ComposedIntMap v Identity -> f v
composedIntMapToKeyedCollection toKey = fmap runIdentity . composedIntMapToKeyedCollectionWithFunctor toKey

class (KeyedCollection f, Diffable f) => IntMapIso (f :: Type -> Type) where
  type DMapKey f :: Type -> Type -> Type
  toComposedIntMapWithFunctor :: Functor g => f (g v) -> ComposedIntMap v g
  fromComposedIntMap :: ComposedIntMap v Identity -> f v
  makePatch :: Functor g => Proxy f -> (Key f -> v -> g u) -> Diff f v -> ComposedPatchIntMap u g
  makeDMapKey :: Proxy f -> Key f -> DMapKey f v v
  toFanInput :: f v -> DMap (DMapKey f v) Identity
  diffToFanInput :: Proxy f -> Diff f v -> DMap (DMapKey f v) Identity
  
instance IntMapIso IntMap where
  type DMapKey IntMap = Const2 Int
  toComposedIntMapWithFunctor = ComposedIntMap . Compose
  fromComposedIntMap = fmap runIdentity . getCompose . unCI
  makePatch _ h =
    ComposedPatchIntMap . Compose . R.PatchIntMap . mapWithKey (\n mv -> (fmap (h n) mv)) . getCompose
  makeDMapKey _ = Const2
  toFanInput = DM.fromAscList . fmap (\(n,v) -> Const2 n :=> Identity v) . IM.toAscList 
  diffToFanInput _ = intMapWithFunctorToDMap . IM.mapMaybe (fmap Identity) . getCompose 

-- this one is more efficient since it uses the ascending list
intMapWithFunctorToDMap :: Functor g => IntMap (g v) -> DMap (Const2 Int v) g
intMapWithFunctorToDMap = DM.fromDistinctAscList . fmap (\(k, v) -> Const2 k :=> v) . IM.toAscList

-- this only works for an array which has an element for every value of the key
-- could be made slightly more general, getting the ints from position in a larger set
-- but would be finicky and sacrifice some performance in the conversions. I think.
instance (Enum k, Bounded k, A.Ix k) => IntMapIso (A.Array k) where
  type DMapKey (Array k) = Const2 k
  toComposedIntMapWithFunctor = ComposedIntMap . Compose . IM.fromAscList . zip [0..] . fmap snd . A.assocs  
  fromComposedIntMap = A.listArray (minBound,maxBound) . fmap runIdentity . fmap snd . IM.toAscList . getCompose . unCI
  makePatch _ h =
    ComposedPatchIntMap . Compose . R.PatchIntMap . IM.fromAscList . zip [0..] . fmap (\(k,v) -> Just $ h k v) . unArrayDiff
  makeDMapKey _ = Const2
  toFanInput = DM.fromDistinctAscList . fmap (\(k,v) -> Const2 k :=> Identity v) . A.assocs
  diffToFanInput _ = DM.fromDistinctAscList . fmap (\(k,v) -> Const2 k :=> Identity v) . unArrayDiff 