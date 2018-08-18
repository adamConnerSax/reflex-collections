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
  , elemUpdateToMaybe
  ) where

import           Reflex.Collections.KeyedCollection ( KeyedCollection(..))

import           Data.Kind              (Type)
import           Data.Align             (Align(..))
import           Data.These             (These(..))
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

-- A little more informative than Maybe a
-- So easier to follow logic and removes need for nested Maybe in diffs
data ElemUpdate a = NoChange | Delete | NewValue a deriving (Eq,Functor)

-- This is simple but there is clearly a case to be made for diffs which might
-- differ from the underlying container (IntMap as diff for [], e.g.,)
-- but I think it might be better to handle those cases by transforming the container before using
-- the list management functions. This keeps it straightforward for all manner or collections.
newtype Diff f v = Diff { unDiff :: f (ElemUpdate v) }

instance Functor f => Functor (Diff f) where
  fmap g = Diff . fmap (fmap g) . unDiff 

-- | for a container with a meaningful empty state, toDiff has to satisfy: `applyDiff empty . toDiff = id`

toDiff :: Functor f => f v -> Diff f v
toDiff = Diff . fmap NewValue 

mapDiffWithKey :: KeyedCollection f => (Key f -> a -> b) -> Diff f a -> Diff f b
mapDiffWithKey h = let f k = fmap (h k) in Diff . mapWithKey f . unDiff
  
-- encapsulates the ability to diff two containers and then apply the diff to regain the original
-- also supports a Map.difference style operation on the diff itself (for splitting out value updates)
-- Laws:
-- applyDiff (diff x y) x = y
-- applyDiff (diffNoEq x y) x = y
class Diffable (f :: Type -> Type) where
  diffNoEq :: f v -> f v -> Diff f v 
  diff :: Eq v => f v -> f v -> Diff f v
  applyDiff :: Diff f v -> f v -> f v
  diffOnlyKeyChanges :: f v -> f v -> Diff f v 
  editDiffLeavingDeletes :: Diff f v -> Diff f u -> Diff f v

-- arrays must have the same bounds.  Which ought to be part of the type maybe.
arrayZipWith :: Ix k => (a -> b -> c) -> Array k a -> Array k b -> Array k c
arrayZipWith f as bs =
  let aList = A.assocs as
      bList = A.assocs bs
      doF ((_,x),(k,y)) = (k,f x y)
  in A.array (A.bounds bs) $ fmap doF (zip aList bList)

instance Ix k => Diffable (Array k) where
  diffNoEq _ = Diff . fmap NewValue 
  diff old new = Diff $ arrayZipWith (\a b -> if a == b then NoChange else NewValue b) old new 
  applyDiff (Diff diffs) a =
    let apply NoChange x = x
        apply Delete _ = undefined -- this should never happen for an array.  Would be nice to encode that in the tyoes
        apply (NewValue x) _ = x
    in arrayZipWith apply diffs a
  diffOnlyKeyChanges _ b = Diff $ A.listArray (A.bounds b) (repeat NoChange)
  editDiffLeavingDeletes _ b = Diff $ A.listArray (A.bounds (unDiff b)) (repeat NoChange) -- we could implement this partially but I don't think we need it.

instance Ord k => Diffable (Map k) where
  diffNoEq = mapDiffNoEq
  diff = mapDiff
  applyDiff = mapApplyDiff M.union M.difference M.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges M.mapMaybe
  editDiffLeavingDeletes = mapEditDiffLeavingDeletes M.differenceWith

instance (Eq k, Hashable k) => Diffable (HashMap k) where
  diffNoEq = mapDiffNoEq
  diff = mapDiff 
  applyDiff = mapApplyDiff HM.union HM.difference HM.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges HM.mapMaybe
  editDiffLeavingDeletes = mapEditDiffLeavingDeletes HM.differenceWith

instance Diffable IntMap where
  diffNoEq = mapDiffNoEq
  diff = mapDiff 
  applyDiff = mapApplyDiff IM.union IM.difference IM.mapMaybe
  diffOnlyKeyChanges = mapDiffOnlyKeyChanges IM.mapMaybe
  editDiffLeavingDeletes = mapEditDiffLeavingDeletes IM.differenceWith

mapDiffNoEq :: (Functor f, Align f) => f v -> f v -> Diff f v
mapDiffNoEq old new =  Diff $ flip fmap (align old new) $ \case
  This _ -> Delete -- in old but not new, so delete
  That v -> NewValue v -- in new but not old, so put in patch
  These _ v -> NewValue v -- in both and, without Eq, we don't know if the value changed, so put possibly new value in patch

mapDiff :: (Eq v, Functor f, Align f) =>  f v -> f v -> Diff f v
mapDiff old new = Diff $ flip fmap (align old new) $ \case
  This _ -> Delete -- in old but not new, so delete
  That v -> NewValue v -- in new but not old, so put in patch
  These oldV newV -> if oldV == newV then NoChange else NewValue newV -- in both and without Eq I don't know if the value changed, so put possibly new value in patch

mapApplyDiff ::
  (forall a. (f a -> f a -> f a)) -- union
  -> (forall a b. (f a -> f b -> f a)) -- difference
  -> (forall a b. ((a -> Maybe b) -> f a -> f b)) -- mapMaybe
  -> Diff f v
  -> f v
  -> f v
mapApplyDiff mapUnion mapDifference mapMaybeF patch old =  
    let p = unDiff $ patch
        justNew = \case
          NewValue x -> Just x
          NoChange -> Nothing
          Delete -> Nothing
        justDelete = \case
          NewValue _ -> Nothing
          NoChange -> Nothing
          Delete -> Just Delete
        deletions = mapMaybeF justDelete p
        insertions = mapMaybeF justNew $ p `mapDifference` deletions
    in insertions `mapUnion` (old `mapDifference` deletions)

mapDiffOnlyKeyChanges :: (Align f, Functor f) => (forall a b.((a -> Maybe b) -> f a -> f b)) -> f v -> f v -> Diff f v
mapDiffOnlyKeyChanges mapMaybeF old new = Diff $ flip mapMaybeF (align old new) $ \case
  This _ -> Just Delete
  These _ _ -> Nothing
  That n -> Just $ NewValue n

mapEditDiffLeavingDeletes :: (forall a b.(a -> b -> Maybe a) -> f a -> f b -> f a) -> Diff f v -> Diff f u -> Diff f v
mapEditDiffLeavingDeletes mapDifferenceWith da db =
  let relevantPatch patch _ = case patch of
        Delete -> Just Delete -- it's a delete
        _  -> Nothing -- remove from diff
  in Diff $ mapDifferenceWith relevantPatch (unDiff da) (unDiff db)


instance Diffable ([]) where
  diffNoEq = listDiffNoEq length drop (++)
  diff = listDiff zipWith length drop (++) 
  applyDiff = listApplyDiff zipWith length drop (++)
  diffOnlyKeyChanges = listDiffOnlyKeyChanges zipWith length drop (++)
  editDiffLeavingDeletes = listEditDiffLeavingDeletes zipWith length drop (++)  


instance Diffable (S.Seq) where
  diffNoEq = listDiffNoEq S.length S.drop (S.><)
  diff = listDiff S.zipWith S.length S.drop (S.><) 
  applyDiff = listApplyDiff S.zipWith S.length S.drop (S.><) 
  diffOnlyKeyChanges = listDiffOnlyKeyChanges S.zipWith S.length S.drop (S.><) 
  editDiffLeavingDeletes = listEditDiffLeavingDeletes S.zipWith S.length S.drop (S.><) 


listDiffNoEq :: Functor f =>
  (forall a. (f a -> Int)) -- length
  -> (forall a. (Int -> f a -> f a)) -- drop
  -> (forall a. f a -> f a -> f a) -- append
  -> f v
  -> f v
  -> Diff f v
listDiffNoEq lengthF dropF appendF old new =
  let addNews = fmap NewValue new
      deleteRemainingOlds = fmap (const Delete) (dropF (lengthF new) old)  
  in Diff $ addNews `appendF` deleteRemainingOlds

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
      addExtraNew = fmap NewValue (dropF (lengthF overlap) new)
      deleteRemainingOld = fmap (const Delete) (dropF (lengthF overlap) old)
  in Diff $ overlap `appendF` addExtraNew `appendF` deleteRemainingOld

listApplyDiff :: (Functor f, Filterable f) => 
  (forall a b c. (a -> b -> c) -> f a -> f b -> f c) -- zipWith
  -> (forall a. (f a -> Int)) -- length
  -> (forall a. (Int -> f a -> f a)) -- drop
  -> (forall a. (f a -> f a -> f a)) -- append
  -> Diff f v
  -> f v
  -> f v
listApplyDiff zipWithF lengthF dropF appendF (Diff d) old =
  let overlap = zipWithF applyEU d old
      additionalDiff = fmap elemUpdateToMaybe (dropF (lengthF overlap) d)
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
  in Diff $ overlap `appendF` extraOld `appendF` extraNew

listEditDiffLeavingDeletes :: 
  (forall a b c. (a -> b -> c) -> f a -> f b -> f c) -- zipWith
   -> (forall a. (f a -> Int)) -- length
  -> (forall a. (Int -> f a -> f a)) -- drop
  -> (forall a. f a -> f a -> f a) -- append
  -> Diff f v
  -> Diff f u
  -> Diff f v
listEditDiffLeavingDeletes zipWithF lengthF dropF appendF (Diff da) (Diff db) =
  let f x _ = case x of
        Delete -> Delete
        NoChange -> NoChange
        NewValue _ -> NoChange
      overlap = zipWithF f da db
  in Diff $ overlap `appendF` (dropF (lengthF overlap) da)
  
applyEU :: ElemUpdate a -> a -> Maybe a
applyEU NoChange x = Just x
applyEU Delete _ = Nothing
applyEU (NewValue x) _ = Just x

elemUpdateToMaybe :: ElemUpdate a -> Maybe a
elemUpdateToMaybe NoChange = Nothing
elemUpdateToMaybe Delete = Nothing
elemUpdateToMaybe (NewValue x) = Just x


  

