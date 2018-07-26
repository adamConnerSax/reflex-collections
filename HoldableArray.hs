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
module Reflex.Dom.Contrib.ListHoldFunctions.HoldableArray
  (
   listHoldWithKeyHoldableArray
{-
  , listWithKeyShallowDiffArray
  , listWithKeyArray
  , selectViewListWithKeyArray
  , arrayDiffNoEq
  , arrayDiff
  , arrayApplyDiff
  , distributeArrayOverDynPure
-}
  ) where

import           Reflex.Dom.Contrib.ListHoldFunctions.Core

import           Data.Dependent.Map                        (DMap, DSum ((:=>)))
import qualified Data.Dependent.Map                        as DM

import           Data.Functor.Misc                         (ComposeMaybe (..),
                                                            Const2 (..),
                                                            dmapToMap,
                                                            mapWithFunctorToDMap)
import qualified Reflex                                    as R
import qualified Reflex.Dom                                as RD
import           Reflex.Patch                              (PatchDMap (..))

import qualified Data.Array                                as A

import           Data.Functor.Compose                      (Compose (Compose),
                                                            getCompose)

import           Control.Monad.Fix                         (MonadFix)
import           Control.Monad.Identity                    (Identity (..))
import           Data.Align                                (Align (..))
import qualified Data.Foldable                             as F
import           Data.Maybe                                (isNothing)
import           Data.These                                (These (..))

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

data HoldableArray k v = EmptyHoldableArray | FullHoldableArray (A.Array k v)

data HoldableArrayDiff k v = FromEmpty (A.Array k v) | PartialDiff [(k, Maybe v)]

instance Functor (HoldableArrayDiff k) where
  fmap f (FromEmpty a)    = FromEmpty (fmap f a)
  fmap f (PartialDiff pd) = PartialDiff $ fmap (\(k, mv) -> (k, fmap f mv)) pd

arrayDiffMapWithKey :: A.Ix k => (k -> v -> a) -> HoldableArrayDiff k v -> HoldableArrayDiff k a
arrayDiffMapWithKey h (PartialDiff p) = PartialDiff $ fmap (\(k, mv) -> (k, fmap (h k) mv)) p
arrayDiffMapWithKey h (FromEmpty a) = FromEmpty $ arrayMapWithKey h a

instance A.Ix k => ToPatchType (HoldableArray k) k v a where
  type Diff (HoldableArray k) k = HoldableArrayDiff k
  type SeqType (HoldableArray k) k = DM.DMap
  type SeqPatchType (HoldableArray k) k = PatchDMap
  type SeqTypeKey (HoldableArray k) k a = Const2 k a
  toSeqTypeWithFunctor h ha = case ha of
    EmptyHoldableArray  -> DM.empty
    FullHoldableArray a -> arrayWithFunctorToDMap $ arrayMapWithKey h a
  makePatchSeq _ h had =
    let toList x = case x of
          (FromEmpty a)    -> A.assocs $ fmap Just a
          (PartialDiff pd) -> pd
    in PatchDMap .  DM.fromList . fmap (\(k, mgv) -> Const2 k :=> ComposeMaybe mgv) . toList $ arrayDiffMapWithKey h had
  fromSeqType _ _ dm = if (DM.null dm) then EmptyHoldableArray else FullHoldableArray (dmapToArray dm)

listHoldWithKeyHoldableArray :: forall t m k v a.(RD.DomBuilder t m, MonadFix m, R.MonadHold t m, A.Ix k)
  => HoldableArray k v -> R.Event t (HoldableArrayDiff k v) -> (k -> v -> m a) -> m (R.Dynamic t (HoldableArray k a))
listHoldWithKeyHoldableArray = listHoldWithKeyGeneral

{-
instance A.Ix k => Diffable (HoldableArray k) (HoldableArrayDiff k) where
  emptyContainer _ = EmptyHoldableArray
  toDiff ha = case ha of
    EmptyHoldableArray -> PartialDiff []
    FullHoldableArray arr -> A.assocs arr
  diffNoEq EmptyHoldableArray EmptyHoldableArray = PartialDiff []
  diffNoEq EmptyHoldableArray (FullHoldableArray arr) = FromEmpty arr
  diffNoEq (FullHoldableArray a) EmptyHoldableArray = undefined
  diffNoEq (FullHoldableArray old) (FullHoldableArray new) = PartialDiff $ A.assocs new
  diff EmptyHoldableArray EmptyHoldableArray = PartialDiff []
  diff EmptyHoldableArray (FullHoldableArray arr) = FromEmpty arr
  diff (FullHoldableArray a) EmptyHoldableArray = undefined
  diff (FullHoldableArray old) (FullHoldableArray new) =
    let oldList = A.assocs old

-}


