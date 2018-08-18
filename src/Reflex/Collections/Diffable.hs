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
{-# LANGUAGE DeriveFunctor #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.Diffable
  (
    Diffable(..)
  , ElemUpdate (..)
  , Diff (..)
  , mapDiffWithKey
  , toDiff
--  , ArrayDiff(..)
--  , MapDiff
  ) where

import           Reflex.Collections.KeyedCollection ( KeyedCollection(..)
                                                    , composeMaybeMapWithKey)

import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)
import           Data.Functor.Compose   (Compose(..))
import           Data.Align             (Align(..))
import           Data.These             (These(..))
import           Data.Foldable          (foldl')
import           Data.Maybe             (isNothing)
import           Data.Monoid            (Monoid(mempty))
import           Data.Witherable        (Filterable(..))

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

data ElemUpdate a = NoChange | Delete | NewValue a deriving (Eq,Functor)

newtype Diff f v = Diff { unDiff :: Compose f ElemUpdate v }

instance Functor f => Functor (Diff f) where
  fmap g = Diff . Compose . fmap (fmap g) . getCompose . unDiff 

-- | Given a diffable collection that has an empty state, we can make a diff such that "applyDiff empty . toDiff = id"  
-- We are using the existence of a monoid instance to indicate a meaningful empty state (mempty)
toDiff :: Functor f => f v -> Diff f v
toDiff = Diff . Compose . fmap NewValue 

mapDiffWithKey :: KeyedCollection f => (Key f -> a -> b) -> Diff f a -> Diff f b
mapDiffWithKey h =
  let f k = fmap (h k)
  in Diff . Compose . mapWithKey f . getCompose . unDiff
  
-- encapsulates the ability to diff two containers and then apply the diff to regain the original
-- also supports a Map.difference style operation on the diff itself (for splitting out value updates)
-- diffOnlyKeyChanges and editDiffLeavingDeletes are both too specific, I think.
-- NB: applyDiffD (diffD x y) y = x
class Diffable (f :: Type -> Type) where
--  type Diff f :: Type -> Type
--  mapDiffWithKey :: KeyedCollection f => Proxy f -> (Key f -> a -> b) -> Diff f a -> Diff f b
  diffNoEq :: f v -> f v -> Diff f v 
  diff :: Eq v => f v -> f v -> Diff f v
  applyDiff :: Diff f v -> f v -> f v
  diffOnlyKeyChanges :: f v -> f v -> Diff f v 
  editDiffLeavingDeletes :: Proxy f -> Diff f v -> Diff f u -> Diff f v -- this removes 2nd diff from first, except when first indicates a delete. May not generalize.
{-
newtype ArrayDiff k v = ArrayDiff { unArrayDiff :: [(k,v)] }

instance Functor (ArrayDiff k) where
  fmap f = ArrayDiff . fmap (\(k,v) -> (k,f v)) . unArrayDiff

instance KeyedCollection (ArrayDiff k) where
  type Key (ArrayDiff k) = k
  mapWithKey h = ArrayDiff . fmap (\(k,v) -> (k, h k v)) . unArrayDiff 
  toKeyValueList = unArrayDiff
  fromKeyValueList = ArrayDiff
-}

-- arrays must have the same bounds.  Which ought to be part of the type maybe.
arrayZipWith :: Ix k => (a -> b -> c) -> Array k a -> Array k b -> Array k c
arrayZipWith f as bs =
  let aList = A.assocs as
      bList = A.assocs bs
      doF ((_,x),(k,y)) = (k,f x y)
  in A.array (A.bounds bs) $ fmap doF (zip aList bList)

instance Ix k => Diffable (Array k) where
--  type Diff (Array k) = ArrayDiff k
--  mapDiffWithKey _ h = ArrayDiff . fmap (\(k,v) -> (k, h k v)) . unArrayDiff
  diffNoEq _ = Diff . Compose . fmap NewValue 
  diff old new = Diff . Compose  $ arrayZipWith (\a b -> if a == b then NoChange else NewValue b) old new 
  applyDiff (Diff diffs) a =
    let apply NoChange x = x
        apply Delete x = undefined -- this should never happen for an array.  Would be nice to encode that in the tyoes
        apply (NewValue x) _ = x
    in arrayZipWith apply (getCompose diffs) a
  diffOnlyKeyChanges _ b = Diff . Compose $ A.listArray (A.bounds b) (repeat NoChange)
  editDiffLeavingDeletes _ _ b = Diff . Compose $ A.listArray (A.bounds (getCompose . unDiff $ b)) (repeat NoChange) -- we could implement this partially but I don't think we need it.

instance Ord k => Diffable (Map k) where
  diffNoEq = mapDiffNoEq
  diff = mapDiff M.mapMaybe
  applyDiff = mapApplyDiff M.union M.difference M.filter M.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges M.mapMaybe
  editDiffLeavingDeletes _ = mapEditDiffLeavingDeletes M.differenceWith

instance (Eq k, Hashable k) => Diffable (HashMap k) where
  diffNoEq = mapDiffNoEq
  diff = mapDiff HM.mapMaybe
  applyDiff = mapApplyDiff HM.union HM.difference HM.filter HM.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges HM.mapMaybe
  editDiffLeavingDeletes _ = mapEditDiffLeavingDeletes HM.differenceWith

instance Diffable IntMap where
  diffNoEq = mapDiffNoEq
  diff = mapDiff IM.mapMaybe
  applyDiff = mapApplyDiff IM.union IM.difference IM.filter IM.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges IM.mapMaybe
  editDiffLeavingDeletes _ = mapEditDiffLeavingDeletes IM.differenceWith


mapDiffNoEq :: (Functor f, Align f) => f v -> f v -> Diff f v
mapDiffNoEq old new =  Diff . Compose $ flip fmap (align old new) $ \case
  This _ -> Delete -- in old but not new, so delete
  That v -> NewValue v -- in new but not old, so put in patch
  These _ v -> NewValue v -- in both and, without Eq, we don't know if the value changed, so put possibly new value in patch

mapDiff :: (Eq v, Functor f, Align f) =>  (forall a b.((a -> Maybe b) -> f a  -> f b)) -> f v -> f v -> Diff f v
mapDiff mapMaybe old new = Diff . Compose $ flip fmap (align old new) $ \case
  This _ -> Delete -- in old but not new, so delete
  That v -> NewValue v -- in new but not old, so put in patch
  These oldV newV -> if oldV == newV then NoChange else NewValue newV -- in both and without Eq I don't know if the value changed, so put possibly new value in patch

mapApplyDiff ::
  (forall a. (f a -> f a -> f a)) -- union
  -> (forall a b. (f a -> f b -> f a)) -- difference
  -> (forall a. ((a -> Bool) -> f a -> f a)) -- filter
  -> (forall a b. ((a -> Maybe b) -> f a -> f b)) -- mapMaybe
  -> Diff f v
  -> f v
  -> f v
mapApplyDiff mapUnion mapDifference mapFilter mapMaybe patch old =  
    let p = getCompose . unDiff $ patch
        justNew = \case
          NewValue x -> Just x
          NoChange -> Nothing
          Delete -> Nothing
        justDelete = \case
          NewValue _ -> Nothing
          NoChange -> Nothing
          Delete -> Just Delete
        deletions = mapMaybe justDelete p
        insertions = mapMaybe justNew $ p `mapDifference` deletions
    in insertions `mapUnion` (old `mapDifference` deletions)

mapDiffOnlyKeyChanges :: (Align f, Functor f) => (forall a b.((a -> Maybe b) -> f a -> f b)) -> f v -> f v -> Diff f v
mapDiffOnlyKeyChanges mapMaybe old new = Diff . Compose $ flip mapMaybe (align old new) $ \case
  This _ -> Just Delete
  These _ _ -> Nothing
  That n -> Just $ NewValue n

mapEditDiffLeavingDeletes :: (forall a b.(a -> b -> Maybe a) -> f a -> f b -> f a) -> Diff f v -> Diff f u -> Diff f v
mapEditDiffLeavingDeletes mapDifferenceWith da db =
  let relevantPatch patch _ = case patch of
        Delete -> Just Delete -- it's a delete
        _  -> Nothing -- remove from diff
  in Diff . Compose $ mapDifferenceWith relevantPatch (getCompose . unDiff $ da) (getCompose . unDiff $ db)


instance Diffable ([]) where
  diffNoEq _ new = Diff . Compose $ fmap NewValue new 
  diff = listDiff zipWith length drop (++) 
  applyDiff = listApplyDiff zipWith length drop (++)
  diffOnlyKeyChanges = listDiffOnlyKeyChanges zipWith length drop (++)
  editDiffLeavingDeletes _ = listEditDiffLeavingDeletes zipWith length drop (++)  


instance Diffable (S.Seq) where
  diffNoEq _ new = Diff . Compose $ fmap NewValue new
  diff = listDiff S.zipWith S.length S.drop (S.><) 
  applyDiff = listApplyDiff S.zipWith S.length S.drop (S.><) 
  diffOnlyKeyChanges = listDiffOnlyKeyChanges S.zipWith S.length S.drop (S.><) 
  editDiffLeavingDeletes _ = listEditDiffLeavingDeletes S.zipWith S.length S.drop (S.><) 


listDiff :: (Functor f, Eq v) => 
  (forall a b c. (a -> b -> c) -> f a -> f b -> f c) -- zipWith
  -> (forall a. (f a -> Int)) -- length
  -> (forall a. (Int -> f a -> f a)) -- drop
  -> (forall a. f a -> f a -> f a) -- append
  -> f v
  -> f v
  -> Diff f v
listDiff zipWithF lengthF dropF appendF old new =
  let overlap = zipWithF (\a b -> if a==b then NoChange else NewValue b) old new
  in Diff . Compose $ overlap `appendF` fmap NewValue (dropF (lengthF overlap) new)

listApplyDiff :: (Functor f, Filterable f) => 
  (forall a b c. (a -> b -> c) -> f a -> f b -> f c) -- zipWith
  -> (forall a. (f a -> Int)) -- length
  -> (forall a. (Int -> f a -> f a)) -- drop
  -> (forall a. (f a -> f a -> f a)) -- append
  -> Diff f v
  -> f v
  -> f v
listApplyDiff zipWithF lengthF dropF appendF diff old =
  let d = getCompose . unDiff $ diff
      overlap = zipWithF applyEU d old
      additionalDiff = fmap euToMaybe (dropF (lengthF overlap) d)
      additionalOld = fmap Just (dropF (lengthF overlap) old)
    in mapMaybe id (overlap `appendF` additionalDiff `appendF` additionalOld) 

listDiffOnlyKeyChanges :: Functor f => 
  (forall a b c. (a -> b -> c) -> f a -> f b -> f c) -- zipWith
  -> (forall a. (f a -> Int)) -- length
  -> (forall a. (Int -> f a -> f a)) -- drop
  -> (forall a. f a -> f a -> f a) -- append
  -> f v
  -> f v
  -> Diff f v
listDiffOnlyKeyChanges zipWithF lengthF dropF appendF old new =
  let overlap = zipWithF (\_ _ -> NoChange) old new
      extraOld = Delete <$ (dropF (lengthF overlap) old)
      extraNew = NewValue <$> (dropF (lengthF overlap) new)
  in Diff . Compose $ overlap `appendF` extraOld `appendF` extraNew

listEditDiffLeavingDeletes :: 
  (forall a b c. (a -> b -> c) -> f a -> f b -> f c) -- zipWith
   -> (forall a. (f a -> Int)) -- length
  -> (forall a. (Int -> f a -> f a)) -- drop
  -> (forall a. f a -> f a -> f a) -- append
  -> Diff f v
  -> Diff f u
  -> Diff f v
listEditDiffLeavingDeletes zipWithF lengthF dropF appendF da db =
  let pa = getCompose . unDiff $ da
      pb = getCompose . unDiff $ db
      f x _ = case x of
        Delete -> Delete
        NoChange -> NoChange
        NewValue _ -> NoChange
      overlap = zipWithF f pa pb
  in Diff . Compose $ overlap `appendF` (dropF (lengthF overlap) pa)
  
applyEU :: ElemUpdate a -> a -> Maybe a
applyEU NoChange x = Just x
applyEU Delete x = Nothing
applyEU (NewValue x) _ = Just x

euToMaybe :: ElemUpdate a -> Maybe a
euToMaybe NoChange = Nothing
euToMaybe Delete = Nothing
euToMaybe (NewValue x) = Just x


  

