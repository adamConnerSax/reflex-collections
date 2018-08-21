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
--  , composeMaybeMapWithKey
  ) where

import           Data.Kind             (Type)
import           Data.Functor.Compose  (Compose (..))
import           Data.Maybe            (maybe)
import           Data.These            (These(..))
import           Data.Align            (Align(..))
                                       
--import           Data.Proxy            (Proxy (..))

import qualified Data.Map              as M
import           Data.Hashable         (Hashable)
import qualified Data.HashMap.Strict   as HM
import qualified Data.IntMap           as IM
import qualified Data.Array            as A
import qualified Data.Sequence         as S
import qualified Data.Foldable         as F
import           Data.Witherable        (Filterable(..))

class Functor f => KeyedCollection (f :: Type -> Type) where
  type Key f :: Type
  mapWithKey :: (Key f -> a -> b) -> f a -> f b
  toKeyValueList :: f v -> [(Key f, v)]
  fromKeyValueList :: [(Key f ,v)] -> f v -- assumes Keys are distinct    

instance Ord k => KeyedCollection (M.Map k) where
  type Key (M.Map k) = k
  mapWithKey = M.mapWithKey
  toKeyValueList = M.toAscList
  fromKeyValueList = M.fromList

instance (Eq k, Hashable k) => KeyedCollection (HM.HashMap k) where
  type Key (HM.HashMap k) = k
  mapWithKey = HM.mapWithKey
  toKeyValueList = HM.toList
  fromKeyValueList = HM.fromList
  
instance KeyedCollection IM.IntMap where
  type Key IM.IntMap = Int
  mapWithKey = IM.mapWithKey
  toKeyValueList = IM.toAscList
  fromKeyValueList = IM.fromList

instance A.Ix k => KeyedCollection (A.Array k) where
  type Key (A.Array k) = k
  mapWithKey = arrayMapWithKey
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
    
instance KeyedCollection ([]) where
  type Key ([]) = Int
  mapWithKey h = fmap (uncurry h) . zip [0..]
  toKeyValueList = zip [0..]
  fromKeyValueList = fmap snd

instance KeyedCollection (S.Seq) where
  type Key (S.Seq) = Int
  mapWithKey = S.mapWithIndex
  toKeyValueList = zip[0..] . F.toList
  fromKeyValueList = S.fromList . fmap snd
