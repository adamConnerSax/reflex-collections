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

class (Functor f, Foldable f, Traversable f) => MapLike f where
  mlEmpty :: f a
  mlUnion :: f a -> f a -> f a -- left preferring union
  mlDifference :: f a -> f b -> f a -- remove from left any element whose key appears in right
  mlFilter :: (a -> Bool) -> f a -> f a
  mlMapMaybe :: (a -> Maybe a) -> f a -> f a  -- is this always `mlMaybe f = mlFilter (maybe False (const True) . f) `?
  mlDifferenceWith :: (a -> b -> Maybe a) -> f a -> f b -> f a 

instance Ord k => MapLike (Map k) where
  mlEmpty = M.empty
  mlUnion = M.union
  mlDifference = M.difference
  mlFilter = M.filter
  mlMapMaybe = M.mapMaybe
  mlDifferenceWith = M.differenceWith

instance Hashable k => MapLike (HashMap k) where
  mlEmpty = HM.empty
  mlUnion = HM.union
  mlDifference = HM.difference
  mlFilter = HM.filter
  mlMapMaybe = HM.mapMaybe
  mlDifferenceWith = HM.differenceWith

instance MapLike IntMap where
  mlEmpty = IM.empty
  mlUnion = IM.union
  mlDifference = IM.difference
  mlFilter = IM.filter
  mlMapMaybe = IM.mapMaybe
  mlDifferenceWith = IM.differenceWith

instance MapLike f => MapLike (Compose f Maybe) where
  mlEmpty = Compose $ mlEmpty
  mlUnion a b = Compose $ mlUnion (getCompose a) (getCompose b)
  mlDifference a  b = Compose $ (getCompose a) (getCompose b)
  mlFilter f = let g = maybe False id . fmap f in Compose . mlFilter g . getCompose -- this filters out Nothing and predicate = False
  mlMapMaybe = Compose . fmap Just . mlMapMaybe . fmap join . getCompose 

class Functor f => KeyedCollection (f :: Type -> Type) where
  type Key f :: Type
  mapWithKey :: (Key f -> a -> b) -> f a -> f b
  toKeyValueList :: f v -> [(Key f, v)]
  fromKeyValueList :: [(Key f ,v)] -> f v -- assumes Keys are distinct    

instance (KeyedCollection f, Filterable f) => KeyedCollection (Compose f Maybe) where
  type Key (Compose f Maybe) = Key f
  mapWithKey =  composeMapWithKey
  toKeyValueList = toKeyValueList . mapMaybe id . getCompose
  fromKeyValueList = Compose . fmap Just . fromKeyValueList

composeMapWithKey :: (Functor g, KeyedCollection f) => (Key f -> a -> b) -> Compose f g a -> Compose f g b
composeMapWithKey h =
  let q k = fmap (h k)
  in Compose . mapWithKey q . getCompose

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

-- f is the container
-- Diff f has the operations to make and combine subsets
-- we patch f using Diff 

-- Given that the diff is MapLike, we can write default versions for everything except mapDiffWithkey
class ( KeyedCollection f
      , KeyedCollection (Diff f)
      , Key f ~ Key Diff f
      , MapLike (Diff f)
      , Align (Diff f)) => Diffable (f :: Type -> Type) where
  type Diff f :: Type -> Type -- keyed collection of ElemUpdates
  toDiff :: f a -> Diff f a
  patch :: f a -> Diff f a -> f a

instance Ord k => Diffable (Map k) where
  type Diff (Map k) = Map k
  toDiff = id
  patch _ = id

instance Hashable k => Diffable (HashMap k) where
  type Diff (HashMap k) = HashMap k
  toDiff = id
  patch _ = id

instance Diffable IntMap where
  type Diff IntMap = IntMap
  toDiff = id
  patch _ = id

instance Diffable ([]) where
  type Diff ([]) = IntMap
  toDiff = IM.fromAscList . zip [0..]
  patch _ = fmap snd . IM.toAscList

instance Diffable (S.Seq) where
  type Diff (S.Seq) = IntMap
  toDiff = IM.fromAscList . zip [0..] . F.toList
  patch _ = S.fromList . fmap snd . IM.toAscList
  
instance (Enum k, Ix k) => Diffable (Array k) where
  Diff (Array k) = IntMap
  toDiff = IM.fromAscList . fmap (\(k,v) -> (toEnum k, v)) . A.assocs
  patch old x = old A.// fmap (\(n,v) -> (fromEnum n,v)) . IM.toAscList -- Array must keep old ones if no update.  It's "Total"
  
-- a patch is ready to be made back into the original type but how depends on the type
createPatch :: Diffable f => Diff f (Maybe v) -> f v -> Diff f v
createPatch diff old =
  let deletions = mlFilter isNothing patch
      insertions = mlMapMaybe $ patch `mlDifference` deletions
  in insertions `mlUnion` ((toDiff old) `mlDifference` deletions)

diffNoEq :: Diffable f => f v -> f v -> Diff f (Maybe v)
diffNoEq old new =  flip fmap (align (toDiff old) (toDiff new)) \case
  This _ -> Nothing -- delete
  That x -> Just x -- add
  These _ x -> Just x -- might be a change so add

diff :: (Diffable f, Eq v) => f v -> f v -> Diff f (Maybe v)
diff old new = flip mlMapMaybe (align (toDiff old) (toDiff new)) \case
  This _ -> Just Nothing -- delete
  That x -> Just $ Just x -- add
  These x y -> if x == y then Nothing else (Just $ Just y)

diffOnlyKeyChanges :: Diffable f => f v -> f v -> Diff f (Maybe v)
diffOnlyKeyChanges = flip mlMapMaybe (align (toDiff old) (toDiff new)) \case
  This _ -> Just Nothing
  These _ _ -> Nothing
  That n -> Just $ Just n
  
diffLeavingDeletes :: Diffable f => Diff f (Maybe v) -> Diff f (Maybe v) -> Diff f (Maybe v)
diffLeavingDeletes da db =
  let relevantPatch patch _ = case patch of
        Nothing -> Just Nothing -- it's a delete
        Just _  -> Nothing -- remove from diff
  in mlDifferenceWith relevantPatch da db
