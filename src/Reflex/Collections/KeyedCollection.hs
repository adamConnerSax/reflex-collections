{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DefaultSignatures #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.KeyedCollection
  (
    KeyedCollection (..)
  , MapDiff
  , ArrayDiff(..)
  ) where

import           Data.Kind              (Type)
import Data.Functor.Compose (Compose (..))
import Data.Proxy (Proxy (..))

import qualified Data.Map as M
import           Data.Hashable (Hashable)
import qualified Data.HashMap.Strict as HM
import qualified Data.IntMap  as IM
import qualified Data.Array as A



class Functor f => KeyedCollection (f :: Type -> Type) where
  type Key f :: Type
  type Diff f :: Type -> Type
  mapWithKey :: (Key f -> a -> b) -> f a -> f b
  mapDiffWithKey :: Proxy f -> (Key f -> a -> b) -> Diff f a -> Diff f b
  toKeyValueList :: f v -> [(Key f, v)]
  fromKeyValueList :: [(Key f ,v)] -> f v -- assumes Keys are distinct  

type MapDiff f = Compose f Maybe

instance KeyedCollection f => KeyedCollection (MapDiff f) where
  type Key (MapDiff f) = Key f
  type Diff (MapDiff f) = Diff f
  mapWithKey = undefined
  mapDiffWithKey = undefined
  toKeyValueList = undefined
  fromKeyValueList = undefined

mapDiffMapWithKey :: (forall c d. ((k -> c -> d) -> f c -> f d)) -> (k -> a -> b) -> MapDiff f a -> MapDiff f b
mapDiffMapWithKey mwk h =
  let g k = fmap (h k)
  in Compose . mwk g . getCompose

instance Ord k => KeyedCollection (M.Map k) where
  type Key (M.Map k) = k
  type Diff (M.Map k) = MapDiff (M.Map k)
  mapWithKey = M.mapWithKey
  mapDiffWithKey _ = mapDiffMapWithKey mapWithKey
  toKeyValueList = M.toAscList
  fromKeyValueList = M.fromList

instance (Eq k, Hashable k) => KeyedCollection (HM.HashMap k) where
  type Key (HM.HashMap k) = k
  type Diff (HM.HashMap k) = MapDiff (HM.HashMap k)
  mapWithKey = HM.mapWithKey
  mapDiffWithKey _ = mapDiffMapWithKey mapWithKey
  toKeyValueList = HM.toList
  fromKeyValueList = HM.fromList
  
instance KeyedCollection IM.IntMap where
  type Key IM.IntMap = Int
  type Diff IM.IntMap = MapDiff IM.IntMap
  mapWithKey = IM.mapWithKey
  mapDiffWithKey _ = mapDiffMapWithKey mapWithKey
  toKeyValueList = IM.toAscList
  fromKeyValueList = IM.fromList

newtype ArrayDiff k v = ArrayDiff { unArrayDiff :: [(k,v)] }

instance Functor (ArrayDiff k) where
  fmap f = ArrayDiff . fmap (\(k,v) -> (k,f v)) . unArrayDiff

instance KeyedCollection (ArrayDiff k) where
  type Key (ArrayDiff k) = k
  type Diff (ArrayDiff k) = ArrayDiff k
  mapWithKey = undefined
  mapDiffWithKey = undefined
  toKeyValueList = undefined
  fromKeyValueList = undefined

instance A.Ix k => KeyedCollection (A.Array k) where
  type Key (A.Array k) = k
  type Diff (A.Array k) = ArrayDiff k
  mapWithKey = arrayMapWithKey
  mapDiffWithKey _ h = ArrayDiff . fmap (\(k,v) -> (k, h k v)) . unArrayDiff
  toKeyValueList = A.assocs
  fromKeyValueList = arrayFromKeyValueList -- NB: this will be undefined at any key in the range missing from the list

arrayFromKeyValueList :: A.Ix k => [(k,v)] -> A.Array k v
arrayFromKeyValueList l = let keys = fst <$> l in A.array (minimum keys, maximum keys) l

arrayMapWithKey :: A.Ix k => (k -> v -> a) -> A.Array k v -> A.Array k a
arrayMapWithKey h arr =
  let kvPairs = A.assocs arr
      mapped = (\(k,v) -> (k, h k v)) <$> kvPairs
      indices = fst <$> kvPairs
      bounds = (minimum indices, maximum indices)
  in A.array bounds mapped
    
