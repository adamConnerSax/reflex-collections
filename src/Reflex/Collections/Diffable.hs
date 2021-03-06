{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE DefaultSignatures     #-}
{-# LANGUAGE LambdaCase            #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
-- | This module has a typeclass to give a common interface to a small subset of map functions (`MapLike`) and
-- then a class to bring together the typeclass requirements for a collection that can be diffed in the way
-- required for the collection functions.  `Diffable` brings these contraints together and adds the the functionality
-- to map a collection to a Diff and, when possible, back.
module Reflex.Collections.Diffable
  (
    Diffable(..)
  , Diff
  , SetLike(..)
  , kvSetDiffNoEq
  ) where

import           Reflex.Collections.KeyedCollection (KeyedCollection(..))

import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)
import           Data.Align             (Align(..))
import           Data.These             (These(..))
import           Data.Maybe             (isNothing)
import           Control.Arrow (first)
import qualified Data.Foldable          as F
import qualified Data.Key               as K


import           Data.Map               (Map)
import qualified Data.Map               as M
import           Data.IntMap            (IntMap)
import qualified Data.IntMap            as IM
import           Data.Hashable          (Hashable)
import           Data.HashMap.Strict    (HashMap)
import qualified Data.HashMap.Strict    as HM
import           Data.Array             (Array, Ix)
import qualified Data.Array             as A
import qualified Data.Sequence          as S
import           Data.Tree              (Tree)

class Functor f => SetLike f where
  slEmpty :: f a
  slNull :: f a -> Bool
  slUnion :: f a -> f a -> f a -- left preferring union
  slDifference :: f a -> f b -> f a -- remove from left any element whose key appears in right
  slDifferenceWith :: (a -> b -> Maybe a) -> f a -> f b -> f a 
  slFilter :: (a -> Bool) -> f a -> f a
  slMapMaybe :: (a -> Maybe b) -> f a -> f b  -- is this always `mapMaybe f = slFilter (maybe False (const True) . f) `?

instance Ord k => SetLike (M.Map k) where
  {-# INLINABLE slEmpty #-}
  slEmpty = M.empty
  {-# INLINABLE slNull #-}
  slNull = M.null
  {-# INLINABLE slUnion #-}
  slUnion = M.union
  {-# INLINABLE slDifference #-}
  slDifference = M.difference
  {-# INLINABLE slFilter #-}
  slFilter = M.filter
  {-# INLINABLE slMapMaybe #-}
  slMapMaybe = M.mapMaybe
  {-# INLINABLE slDifferenceWith #-}
  slDifferenceWith = M.differenceWith

instance (Eq k, Hashable k) => SetLike (HM.HashMap k) where
  {-# INLINABLE slEmpty #-}
  slEmpty = HM.empty
  {-# INLINABLE slNull #-}
  slNull = HM.null
  {-# INLINABLE slUnion #-}
  slUnion = HM.union
  {-# INLINABLE slDifference #-}    
  slDifference = HM.difference
  {-# INLINABLE slFilter #-}  
  slFilter = HM.filter
  {-# INLINABLE slMapMaybe #-}  
  slMapMaybe = HM.mapMaybe
  {-# INLINABLE slDifferenceWith #-}  
  slDifferenceWith = HM.differenceWith

instance SetLike IntMap where
  {-# INLINABLE slEmpty #-}  
  slEmpty = IM.empty
  {-# INLINABLE slNull #-}
  slNull = IM.null
  {-# INLINABLE slUnion #-}  
  slUnion = IM.union
  {-# INLINABLE slDifference #-}      
  slDifference = IM.difference
  {-# INLINABLE slFilter #-}    
  slFilter = IM.filter
  {-# INLINABLE slMapMaybe #-}    
  slMapMaybe = IM.mapMaybe
  {-# INLINABLE slDifferenceWith #-}    
  slDifferenceWith = IM.differenceWith

-- (f a) is the container
-- (KeyValueSet f a) has the operations to make and combine subsets, usually using Diff f a ~ KeyValueSet f (Maybe a)

-- this class has laws:
-- applyDiff (diff a b) a = b
-- applyDiff (diffNoEq a b) a = b
-- fromFullDiff . toDiff = id
type Diff f a = KeyValueSet f (Maybe a)

class ( KeyedCollection f
      , KeyedCollection (KeyValueSet f)      
      , SetLike (KeyValueSet f)
      , Align (KeyValueSet f)) => Diffable (f :: Type -> Type) where
  type KeyValueSet f :: Type -> Type -- keyed collection of ElemUpdates
  toKeyValueSet :: f a -> KeyValueSet f a
  -- NB: Precondition (that the KeyValueSet is complete) is not checked
  fromCompleteKeyValueSet :: KeyValueSet f a -> f a -- must satisfy (fromFullDiff . toDiff = id)
  applyDiff :: Diff f v -> f v -> f v
  applyDiff d old = fromCompleteKeyValueSet $ appliedDiffToKeyValueSet d old
  {-# INLINABLE applyDiff #-}
  updateKeyValueSet :: Proxy f -> KeyValueSet f v -> Diff f v -> KeyValueSet f v
  updateKeyValueSet _ oldKVS d = slMapMaybe id $ slUnion d (Just <$> oldKVS)
  {-# INLINABLE updateKeyValueSet #-}
  diffNoEq :: f v -> f v -> Diff f v
  diffNoEq = alignDiffNoEq
  {-# INLINABLE diffNoEq #-}
  diff :: Eq v => f v -> f v -> Diff f v
  diff = alignDiff
  {-# INLINABLE diff #-}
  diffOnlyKeyChanges :: f v -> f v -> Diff f v
  diffOnlyKeyChanges = alignDiffOnlyKeyChanges
  {-# INLINABLE diffOnlyKeyChanges #-}
  editDiffLeavingDeletes :: Proxy f -> Diff f v -> KeyValueSet f b -> Diff f v
  editDiffLeavingDeletes = defaultEditDiffLeavingDeletes
  {-# INLINABLE editDiffLeavingDeletes #-}
  
instance Ord k => Diffable (Map k) where
  type KeyValueSet (Map k) = Map k
  toKeyValueSet = id
  fromCompleteKeyValueSet = id
  
instance (Eq k, Hashable k) => Diffable (HashMap k) where
  type KeyValueSet (HashMap k) = HashMap k
  toKeyValueSet = id
  fromCompleteKeyValueSet = id

instance Diffable IntMap where
  type KeyValueSet IntMap = IntMap
  toKeyValueSet = id
  fromCompleteKeyValueSet = id

instance Diffable [] where
  type KeyValueSet [] = IntMap
  toKeyValueSet = IM.fromAscList . zip [0..]
  fromCompleteKeyValueSet = fmap snd . IM.toAscList

instance Diffable S.Seq where
  type KeyValueSet S.Seq = IntMap
  toKeyValueSet = IM.fromAscList . zip [0..] . F.toList
  fromCompleteKeyValueSet = S.fromList . fmap snd . IM.toAscList
  
instance (Enum k, Ix k, Bounded k) => Diffable (Array k) where
  type KeyValueSet (Array k) = IntMap
  toKeyValueSet = IM.fromAscList . fmap (first fromEnum) . A.assocs
  fromCompleteKeyValueSet = A.listArray (minBound,maxBound) . fmap snd . IM.toAscList
  {-# INLINABLE fromCompleteKeyValueSet #-}
  applyDiff d old = old A.// fmap (first toEnum) (IM.toAscList $ appliedDiffToKeyValueSet d old)
  {-# INLINABLE applyDiff #-}
  diffNoEq _ new = Just <$> toKeyValueSet new
  {-# INLINABLE diffNoEq #-}
  diffOnlyKeyChanges _ _ = IM.empty
  {-# INLINABLE diffOnlyKeyChanges #-}
  editDiffLeavingDeletes _ _ _ = IM.empty
  {-# INLINABLE editDiffLeavingDeletes #-}

instance Diffable Tree where
  type KeyValueSet Tree = Map (S.Seq Int)
  toKeyValueSet = K.foldMapWithKey M.singleton  --M.froslist . toKeyValueList
  fromCompleteKeyValueSet = fromKeyValueList . M.toAscList 

-- default implementations
appliedDiffToKeyValueSet :: Diffable f => Diff f v -> f v -> KeyValueSet f v
appliedDiffToKeyValueSet d old =
  let deletions = slFilter isNothing d
      insertions = slMapMaybe id  $ d `slDifference` deletions
  in insertions `slUnion` (toKeyValueSet old `slDifference` deletions)
{-# INLINABLE appliedDiffToKeyValueSet #-}

alignDiffNoEq :: forall f v. Diffable f => f v -> f v -> Diff f v
alignDiffNoEq old new =  kvSetDiffNoEq (Proxy :: Proxy f) (toKeyValueSet old) (toKeyValueSet new)
{-# INLINABLE alignDiffNoEq #-}

kvSetDiffNoEq :: Diffable f => Proxy f -> KeyValueSet f a -> KeyValueSet f a -> Diff f a
kvSetDiffNoEq _ kvOld kvNew = flip fmap (align kvOld kvNew) $ \case
  This _ -> Nothing -- in old but not new, Delete
  That x -> Just x -- in new but not old, add
  These _ x -> Just x -- in both, update
{-# INLINABLE kvSetDiffNoEq #-}  

alignDiff :: forall f v. (Diffable f, Eq v) => f v -> f v -> Diff f v
alignDiff old new = kvSetDiff (Proxy :: Proxy f) (toKeyValueSet old) (toKeyValueSet new)
{-# INLINABLE alignDiff #-}

kvSetDiff :: (Eq v, Diffable f) => Proxy f -> KeyValueSet f v -> KeyValueSet f v -> Diff f v
kvSetDiff _ kvOld kvNew = flip slMapMaybe (align kvOld kvNew) $ \case
  This _ -> Just Nothing -- in old but not new, delete
  That x -> Just $ Just x -- in new but not old, add
  These x y -> if x == y then Nothing else Just $ Just y -- in both, update if change
{-# INLINABlE kvSetDiff #-}

alignDiffOnlyKeyChanges :: forall f v. Diffable f => f v -> f v -> Diff f v
alignDiffOnlyKeyChanges old new = kvSetDiffOnlyKeyChanges (Proxy :: Proxy f) (toKeyValueSet old) (toKeyValueSet new)
{-# INLINABLE alignDiffOnlyKeyChanges #-}

kvSetDiffOnlyKeyChanges :: Diffable f => Proxy f -> KeyValueSet f v -> KeyValueSet f v -> Diff f v
kvSetDiffOnlyKeyChanges _ kvOld kvNew = flip slMapMaybe (align kvOld kvNew) $ \case
  This _ -> Just Nothing -- in old but not new, delete
  These _ _ -> Nothing -- in both, ignore
  That n -> Just $ Just n -- in new but not old, add
{-# INLINABLE kvSetDiffOnlyKeyChanges #-}  
  
defaultEditDiffLeavingDeletes :: Diffable f => Proxy f -> Diff f v -> KeyValueSet f b -> Diff f v
defaultEditDiffLeavingDeletes _ da kvb =
  let relevantPatch p _ = case p of
        Nothing -> Just Nothing -- it's a delete
        Just _  -> Nothing -- remove from diff
  in slDifferenceWith relevantPatch da kvb
{-# INLINABLE defaultEditDiffLeavingDeletes #-}
