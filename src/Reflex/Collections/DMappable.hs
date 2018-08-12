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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.DMappable
  (
    DMappable(..)
  ) where


import           Reflex.Collections.Diffable        (Diffable (..))
import           Reflex.Collections.DMapIso         (DMapIso (..))
import           Reflex.Collections.KeyedCollection (KeyedCollection (..))
import           Reflex.Collections.ToPatchType     (SeqTypes (..),
                                                     ToPatchType (..))

import qualified Reflex                             as R
import           Reflex.Patch                       (PatchDMap (..))

import           Data.Dependent.Map                 (DMap)
import           Data.Functor.Identity              (Identity (..))
import           Data.Monoid                        (Monoid (..))
import           Data.Proxy                         (Proxy (..))

-- This is just a wrapper so that we can make instances using DMapIso without overlaps
-- to make all the DMapIso based collection functions work for a collection type (f :: Type -> Type) (e.g., Map k) you need
-- KeyedCollection f
-- Diffable f
-- DMapIso f
-- DiffToPatchDMap f
-- Monoid (f v)
-- from which we can derive, for (DMappable f) the above, as well as,
-- SeqTypes (DMappable f)
-- ToPatchType (DMappable f)



newtype DMappable f v = DMappable { unDMappable :: f v } deriving (Functor, Foldable)

instance KeyedCollection f => KeyedCollection (DMappable f) where
  type Key (DMappable f) = Key f
  mapWithKey h = DMappable . mapWithKey h . unDMappable
  toKeyValueList = toKeyValueList . unDMappable
  fromKeyValueList = DMappable . fromKeyValueList

instance (KeyedCollection f, Diffable f) => Diffable (DMappable f) where
  type Diff (DMappable f) = Diff f
  mapDiffWithKey _ = mapDiffWithKey (Proxy :: Proxy f) -- use version from Diffable f since Diff is the same
  diffNoEq old new = diffNoEq (unDMappable old) (unDMappable new)
  diff old new = diff (unDMappable old) (unDMappable new)
  applyDiff patch old = DMappable $ applyDiff patch (unDMappable old)
  diffOnlyKeyChanges old new = diffOnlyKeyChanges (unDMappable old) (unDMappable new)
  editDiffLeavingDeletes _ = editDiffLeavingDeletes (Proxy :: Proxy f)

instance Monoid (f v) => Monoid (DMappable f v) where
  mempty = DMappable mempty
  mappend a b = DMappable $ mappend (unDMappable a) (unDMappable b)

instance DMapIso f => SeqTypes (DMappable f) v where
  type SeqType (DMappable f) v = DMap (DMapKey f v)
  type SeqPatchType (DMappable f) v = PatchDMap (DMapKey f v)

instance DMapIso f => DMapIso (DMappable f) where
  type DMapKey (DMappable f) = DMapKey f
  makeDMapKey _ = makeDMapKey (Proxy :: Proxy f)
  toDMapWithFunctor = toDMapWithFunctor . unDMappable
  fromDMap = DMappable . fromDMap
  diffToFanInput _ = diffToFanInput (Proxy :: Proxy f) 
  makePatch _ = makePatch (Proxy :: Proxy f) 

instance (KeyedCollection f, DMapIso f) => ToPatchType (DMappable f) where
  type FanSelectKey (DMappable f) = DMapKey f
  withFunctorToSeqType = toDMapWithFunctor . unDMappable
  fromSeqType = DMappable . fromDMap
  makePatchSeq _ = makePatch (Proxy :: Proxy f)
  makeSelectKey pf _ = makeDMapKey pf
  doFan = R.fan . fmap (toDMapWithFunctor . fmap Identity . DMappable)
  diffToFanType pf = diffToFanInput pf
  doDiffFan pf = R.fan . fmap (diffToFanType pf) 
