{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecursiveDo                #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
module Reflex.Collections.TotalArray
  (
    listHoldWithKeyTotalArray
  , listViewWithKeyTotalArray
  , listWithKeyTotalArray
  , ArrayDiff
  , distributeArrayOverDynPure
{-
  , listWithKeyShallowDiffArray
  , listWithKeyArray
  , selectViewListWithKeyArray
  , arrayDiffNoEq
  , arrayDiff
  , arrayApplyDiff

-}
  ) where

import           Reflex.Collections.Core

import           Control.Monad.Fix
import           Data.Dependent.Map      (DMap, DSum ((:=>)))
import qualified Data.Dependent.Map      as DM

import           Data.Functor.Misc       (ComposeMaybe (..), Const2 (..),
                                          dmapToMap, mapWithFunctorToDMap)
import qualified Reflex                  as R
import           Reflex.Patch            (PatchDMap (..))

import qualified Data.Array              as A

import           Data.Foldable           (foldl')
import           Data.Functor.Compose    (Compose (Compose), getCompose)
import           Data.Functor.Identity   (Identity (Identity))

arrayMapWithKey :: A.Ix k => (k -> v -> a) -> A.Array k v -> A.Array k a
arrayMapWithKey h arr =
  let kvPairs = A.assocs arr
      mapped = (\(k,v) -> (k, h k v)) <$> kvPairs
      indices = fst <$> kvPairs
      bounds = (minimum indices, maximum indices)
  in A.array bounds mapped

arrayFan:: (A.Ix k, R.Reflex t) => R.Event t (A.Array k v) -> R.EventSelector t (Const2 k v)
arrayFan = R.fan . fmap arrayToDMap

arrayWithFunctorToDMap :: (Functor f, A.Ix k) => A.Array k (f v) -> DMap (Const2 k v) f
arrayWithFunctorToDMap = DM.fromList . fmap (\(k, fv) -> Const2 k :=> fv) . A.assocs

arrayToDMap :: A.Ix k => A.Array k v -> DMap (Const2 k v) Identity
arrayToDMap = arrayWithFunctorToDMap . fmap Identity

dmapToArray :: A.Ix k => DMap (Const2 k v) Identity -> A.Array k v
dmapToArray dm =
  let kvPairs = fmap (\(Const2 k :=> Identity v) -> (k, v)) $ DM.toList dm
      indices = fst <$> kvPairs
      in A.array (minimum indices, maximum indices) kvPairs

distributeArrayOverDynPure::(R.Reflex t, A.Ix k) => A.Array k (R.Dynamic t v) -> R.Dynamic t (A.Array k v)
distributeArrayOverDynPure = fmap dmapToArray . R.distributeDMapOverDynPure . arrayWithFunctorToDMap

newtype ArrayDiff k v = ArrayDiff { diff :: [(k,v)] }

instance A.Ix k => ToPatchType (A.Array k) k v a where
  type Diff (A.Array k) k = ArrayDiff k
  type SeqType (A.Array k) k = DM.DMap
  type SeqPatchType (A.Array k) k = PatchDMap
  type SeqTypeKey (A.Array k) k a = Const2 k a
  toSeqTypeWithFunctor h a = arrayWithFunctorToDMap $ arrayMapWithKey h a
  makePatchSeq _ h (ArrayDiff ad) = PatchDMap .  DM.fromList $ fmap (\(k, v) -> Const2 k :=> (ComposeMaybe . Just $ h k v)) ad
  fromSeqType _ _ dm = dmapToArray dm


instance (A.Ix k, Ord k) => HasFan (A.Array k) v where
  type FanInKey (A.Array k) = k
  type FanSelKey (A.Array k) v = Const2 k v
  doFan _ = R.fan . fmap arrayToDMap
  makeSelKey _ _ = Const2

instance A.Ix k => Diffable (A.Array k) (ArrayDiff k) where
  diffNoEq old new = ArrayDiff $ A.assocs new
  diff old new =
    let oldList = A.assocs old
        newList = A.assocs new
    in ArrayDiff $ foldl' (\diffs ((ko,o),(kn,n)) -> if (o /= n) then (kn,n) : diffs else diffs) [] (zip oldList newList)
  applyDiff (ArrayDiff diffs) a = a A.// diffs
  diffOnlyKeyChanges _ _ = ArrayDiff []
  editDiffLeavingDeletes _ d1 d2 = ArrayDiff [] -- we could implement this partially but I don't think we need it.


listHoldWithKeyTotalArray :: forall t m k v a. (R.Adjustable t m, MonadFix m, R.MonadHold t m, A.Ix k)
  => A.Array k v -> R.Event t (ArrayDiff k v) -> (k -> v -> m a) -> m (R.Dynamic t (A.Array k a))
listHoldWithKeyTotalArray = listHoldWithKeyGeneral

listWithKeyTotalArray ::  forall t m k v a. (R.Adjustable t m, R.PostBuild t m, MonadFix m, R.MonadHold t m, A.Ix k)
  => R.Dynamic t (A.Array k v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (A.Array k a))
listWithKeyTotalArray = listWithKeyGeneral' sampledDiffableDynamicToInitialPlusKeyDiffEvent

listViewWithKeyTotalArray :: forall t m k v a. (R.Adjustable t m, R.PostBuild t m, MonadFix m, R.MonadHold t m, A.Ix k)
  => R.Dynamic t (A.Array k v) -> (k -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (A.Array k a))
listViewWithKeyTotalArray = listViewWithKeyGeneral' sampledDiffableDynamicToInitialPlusKeyDiffEvent


