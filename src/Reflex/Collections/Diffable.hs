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
  , MapLike(..)
  , createPatch
  , applyDiff
  , diff
  , diffNoEq
  , diffOnlyKeyChanges
  , editDiffLeavingDeletes
  ) where

import           Reflex.Collections.KeyedCollection (KeyedCollection(..))

import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)
import           Data.Align             (Align(..))
import           Data.These             (These(..))
import           Data.Maybe             (isNothing)

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
import qualified Data.Foldable          as F

class Functor f => MapLike f where
  mlEmpty :: f a
  mlUnion :: f a -> f a -> f a -- left preferring union
  mlDifference :: f a -> f b -> f a -- remove from left any element whose key appears in right
  mlFilter :: (a -> Bool) -> f a -> f a
  mlMapMaybe :: (a -> Maybe b) -> f a -> f b  -- is this always `mlMaybe f = mlFilter (maybe False (const True) . f) `?
  mlDifferenceWith :: (a -> b -> Maybe a) -> f a -> f b -> f a 

instance Ord k => MapLike (M.Map k) where
  {-# INLINABLE mlEmpty #-}
  mlEmpty = M.empty
  {-# INLINABLE mlUnion #-}
  mlUnion = M.union
  {-# INLINABLE mlDifference #-}
  mlDifference = M.difference
  {-# INLINABLE mlFilter #-}
  mlFilter = M.filter
  {-# INLINABLE mlMapMaybe #-}
  mlMapMaybe = M.mapMaybe
  {-# INLINABLE mlDifferenceWith #-}
  mlDifferenceWith = M.differenceWith

instance (Eq k, Hashable k) => MapLike (HM.HashMap k) where
  {-# INLINABLE mlEmpty #-}
  mlEmpty = HM.empty
  {-# INLINABLE mlUnion #-}
  mlUnion = HM.union
  {-# INLINABLE mlDifference #-}    
  mlDifference = HM.difference
  {-# INLINABLE mlFilter #-}  
  mlFilter = HM.filter
  {-# INLINABLE mlMapMaybe #-}  
  mlMapMaybe = HM.mapMaybe
  {-# INLINABLE mlDifferenceWith #-}  
  mlDifferenceWith = HM.differenceWith

instance MapLike IntMap where
  {-# INLINABLE mlEmpty #-}  
  mlEmpty = IM.empty
  {-# INLINABLE mlUnion #-}  
  mlUnion = IM.union
  {-# INLINABLE mlDifference #-}      
  mlDifference = IM.difference
  {-# INLINABLE mlFilter #-}    
  mlFilter = IM.filter
  {-# INLINABLE mlMapMaybe #-}    
  mlMapMaybe = IM.mapMaybe
  {-# INLINABLE mlDifferenceWith #-}    
  mlDifferenceWith = IM.differenceWith

-- (f a) is the container
-- (Diff f a) has the operations to make and combine subsets, usually using Diff f (Maybe a)
-- we make a new f using and old f and Diff, since sometimes Diff loses information required to reconstruct. E.g., Diff (Array k) = Map k
-- and (Array k) needs a value for each key which Map may not have one.

-- this class has laws:
-- patch _ (toDiff x) = x
-- patch x (createPatch x $ diffNoEq x y) = y
-- patch x (createPatch x $ diff x y) = y
class ( KeyedCollection f
      , KeyedCollection (Diff f)) => Diffable (f :: Type -> Type) where
  type Diff f :: Type -> Type -- keyed collection of ElemUpdates
  toDiff :: f a -> Diff f a -- a diff such that patch _ (toDiff x) = x
  patch :: f a -> Diff f a -> f a -- update f using a Diff, often ignores initial argument
  createPatch :: Diff f (Maybe v) -> f v -> Diff f v
  default createPatch :: MapLike (Diff f) => Diff f (Maybe v) -> f v -> Diff f v
  createPatch = mapLikeCreatePatch
  {-# INLINABLE createPatch #-}
  diffNoEq :: f v -> f v -> Diff f (Maybe v)
  default diffNoEq :: Align (Diff f) => f v -> f v -> Diff f (Maybe v)
  diffNoEq = alignDiffNoEq
  {-# INLINABLE diffNoEq #-}
  diff :: Eq v => f v -> f v -> Diff f (Maybe v)
  default diff :: (Eq v, Align (Diff f), MapLike (Diff f)) => f v -> f v -> Diff f (Maybe v)
  diff = alignMapLikeDiff
  {-# INLINABLE diff #-}
  diffOnlyKeyChanges :: f v -> f v -> Diff f (Maybe v)
  default diffOnlyKeyChanges :: (Align (Diff f), MapLike (Diff f)) => f v -> f v -> Diff f (Maybe v)
  diffOnlyKeyChanges = alignMapLikeDiffOnlyKeyChanges
  {-# INLINABLE diffOnlyKeyChanges #-}
  editDiffLeavingDeletes :: Proxy f -> Diff f (Maybe v) -> Diff f b -> Diff f (Maybe v)
  default editDiffLeavingDeletes :: MapLike (Diff f) => Proxy f -> Diff f (Maybe v) -> Diff f b -> Diff f (Maybe v)
  editDiffLeavingDeletes = mapLikeEditDiffLeavingDeletes
  {-# INLINABLE editDiffLeavingDeletes #-}
  
instance Ord k => Diffable (Map k) where
  type Diff (Map k) = Map k
  {-# INLINABLE toDiff #-}
  toDiff = id
  {-# INLINABLE patch #-}
  patch _ = id

instance (Eq k, Hashable k) => Diffable (HashMap k) where
  type Diff (HashMap k) = HashMap k
  {-# INLINABLE toDiff #-}  
  toDiff = id
  {-# INLINABLE patch #-}  
  patch _ = id

instance Diffable IntMap where
  type Diff IntMap = IntMap
  {-# INLINABLE toDiff #-}    
  toDiff = id
  {-# INLINABLE patch #-}    
  patch _ = id

instance Diffable ([]) where
  type Diff ([]) = IntMap
  {-# INLINABLE toDiff #-}      
  toDiff = IM.fromAscList . zip [0..]
  {-# INLINABLE patch #-}      
  patch _ = fmap snd . IM.toAscList

instance Diffable (S.Seq) where
  type Diff (S.Seq) = IntMap
  {-# INLINABLE toDiff #-}        
  toDiff = IM.fromAscList . zip [0..] . F.toList
  {-# INLINABLE patch #-}        
  patch _ = S.fromList . fmap snd . IM.toAscList
  
instance (Enum k, Ix k) => Diffable (Array k) where
  type Diff (Array k) = IntMap
  {-# INLINABLE toDiff #-}          
  toDiff = IM.fromAscList . fmap (\(k,v) -> (fromEnum k, v)) . A.assocs
  {-# INLINABLE patch #-}        
  patch old x = old A.// (fmap (\(n,v) -> (toEnum n,v)) $ IM.toAscList x) -- Array must keep old ones if no update.  It's "Total"

applyDiff :: Diffable f => Diff f (Maybe v) -> f v -> f v
applyDiff d f = patch f (createPatch d f)
{-# INLINABLE applyDiff #-}

-- default implementations for MapLike and Alignable containers  
-- a patch is ready to be made back into the original type but how depends on the type, via "patch"
mapLikeCreatePatch :: (Diffable f, MapLike (Diff f)) => Diff f (Maybe v) -> f v -> Diff f v
mapLikeCreatePatch d old =
  let deletions = mlFilter isNothing d
      insertions = mlMapMaybe id  $ d `mlDifference` deletions
  in insertions `mlUnion` ((toDiff old) `mlDifference` deletions)
{-# INLINABLE mapLikeCreatePatch #-}

alignDiffNoEq :: (Diffable f, Align (Diff f)) => f v -> f v -> Diff f (Maybe v)
alignDiffNoEq old new =  flip fmap (align (toDiff old) (toDiff new)) $ \case
  This _ -> Nothing -- delete
  That x -> Just x -- add
  These _ x -> Just x -- might be a change so add
{-# INLINABLE alignDiffNoEq #-}

alignMapLikeDiff :: (Diffable f, Align (Diff f), MapLike (Diff f), Eq v) => f v -> f v -> Diff f (Maybe v)
alignMapLikeDiff old new = flip mlMapMaybe (align (toDiff old) (toDiff new)) $ \case
  This _ -> Just Nothing -- delete
  That x -> Just $ Just x -- add
  These x y -> if x == y then Nothing else (Just $ Just y)
{-# INLINABLE alignMapLikeDiff #-}

alignMapLikeDiffOnlyKeyChanges :: (Diffable f, Align (Diff f), MapLike (Diff f)) => f v -> f v -> Diff f (Maybe v)
alignMapLikeDiffOnlyKeyChanges old new = flip mlMapMaybe (align (toDiff old) (toDiff new)) $ \case
  This _ -> Just Nothing
  These _ _ -> Nothing
  That n -> Just $ Just n
{-# INLINABLE alignMapLikeDiffOnlyKeyChanges #-}
  
mapLikeEditDiffLeavingDeletes :: (Diffable f, MapLike (Diff f)) => Proxy f -> Diff f (Maybe v) -> Diff f b -> Diff f (Maybe v)
mapLikeEditDiffLeavingDeletes _ da db =
  let relevantPatch p _ = case p of
        Nothing -> Just Nothing -- it's a delete
        Just _  -> Nothing -- remove from diff
  in mlDifferenceWith relevantPatch da db
{-# INLINABLE mapLikeEditDiffLeavingDeletes #-}
