{-# LANGUAGE CPP                        #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE RecursiveDo                #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE UndecidableSuperClasses    #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.IntMappable
  (
    IntMappable(..)
  ) where


import           Reflex.Collections.ComposedIntMap  (ComposedIntMap (..),
                                                     ComposedPatchIntMap (..))
import           Reflex.Collections.Diffable        (Diffable (..))
import           Reflex.Collections.IntMapIso       (IntMapIso (..))
import           Reflex.Collections.KeyedCollection (KeyedCollection (..))
import           Reflex.Collections.ToPatchType     (SeqTypes (..),
                                                     ToPatchType (..))

import qualified Reflex                             as R
--import           Reflex.Patch                       (PatchDMap (..))

import           Data.Dependent.Map                 (DMap)
import           Data.Functor.Identity              (Identity (..))
import qualified Data.IntMap                        as IM
import           Data.Monoid                        (Monoid (..))
import           Data.Proxy                         (Proxy (..))

-- This is just a wrapper so that we can make instances using IntMapIso without overlaps
-- to make all the IntMapIso based collection functions work for a collection type (f :: Type -> Type) (e.g., Map k) you need
-- KeyedCollection f
-- Diffable f
-- IntMapIso f
-- Monoid (f v)
-- from which we can derive, for (IntMappable f) the above, as well as,
-- SeqTypes (IntMappable f)
-- ToPatchType (IntMappable f)

newtype IntMappable f v = IntMappable { unIntMappable :: f v } deriving (Functor, Foldable)

instance KeyedCollection f => KeyedCollection (IntMappable f) where
  type Key (IntMappable f) = Key f
  mapWithKey h = IntMappable . mapWithKey h . unIntMappable
  toKeyValueList = toKeyValueList . unIntMappable
  fromKeyValueList = IntMappable . fromKeyValueList

instance (KeyedCollection f, Diffable f) => Diffable (IntMappable f) where
  type Diff (IntMappable f) = Diff f
  mapDiffWithKey _ = mapDiffWithKey (Proxy :: Proxy f) -- use version from Diffable f since Diff is the same
  diffNoEq old new = diffNoEq (unIntMappable old) (unIntMappable new)
  diff old new = diff (unIntMappable old) (unIntMappable new)
  applyDiff patch old = IntMappable $ applyDiff patch (unIntMappable old)
  diffOnlyKeyChanges old new = diffOnlyKeyChanges (unIntMappable old) (unIntMappable new)
  editDiffLeavingDeletes _ = editDiffLeavingDeletes (Proxy :: Proxy f)

instance Monoid (f v) => Monoid (IntMappable f v) where
  mempty = IntMappable mempty
  mappend a b = IntMappable $ mappend (unIntMappable a) (unIntMappable b)

instance IntMapIso f => SeqTypes (IntMappable f) v where
  type SeqType (IntMappable f) v = ComposedIntMap v
  type SeqPatchType (IntMappable f) v = ComposedPatchIntMap v

instance IntMapIso f => IntMapIso (IntMappable f) where
  type DMapKey (IntMappable f) = DMapKey f
  keyToInt _ = keyToInt (Proxy :: Proxy f)
  intToKey _ = intToKey (Proxy :: Proxy f)
  toComposedIntMapWithFunctor = toComposedIntMapWithFunctor . unIntMappable
  fromComposedIntMap = IntMappable . fromComposedIntMap
  makePatch _ = makePatch (Proxy :: Proxy f)
  makeDMapKey _ = makeDMapKey (Proxy :: Proxy f)
  toFanInput = toFanInput . unIntMappable
  diffToFanInput _ = diffToFanInput (Proxy :: Proxy f)

instance (KeyedCollection f, IntMapIso f) => ToPatchType (IntMappable f) where
  type FanSelectKey (IntMappable f) = DMapKey f
  withFunctorToSeqType = toComposedIntMapWithFunctor . unIntMappable
  fromSeqType = IntMappable . fromComposedIntMap
  makePatchSeq _ = makePatch (Proxy :: Proxy f)
  makeSelectKey pf _ = makeDMapKey pf
  doFan = R.fan . fmap toFanInput
  diffToFanType pf = diffToFanInput pf
