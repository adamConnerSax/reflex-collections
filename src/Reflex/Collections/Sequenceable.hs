{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.Sequenceable
  (
    ReflexSequenceable(..)
  , PatchSequenceable(..)
  ) where

import qualified Reflex                 as R
import           Reflex.Patch           (PatchDMap (..), PatchIntMap)

import           Reflex.Collections.DMapIso (DMapIso (..))

import           Data.Dependent.Map     (DMap, GCompare)
import           Data.Functor.Misc      (Const2 (..))
import           Control.Monad.Identity (Identity (..))
import           Data.Kind              (Type)
import           Data.IntMap            (IntMap)
import           Data.Functor.Compose   (Compose(..), getCompose)
import           Data.Semigroup         (Semigroup(..),stimesIdempotentMonoid)
import           Data.Monoid            (Monoid)
import           Data.Foldable          (Foldable)
import           Data.Traversable       (Traversable)

-- | This class carries the ability to do an efficient event merge and also sequence a collection of Dynamics.
-- "Merge a collection of events.  The resulting event will occur if at least one input event is occuring
-- and will contain all simultaneously occurring events."
class ReflexSequenceable (dk :: (Type -> Type) -> Type) where
  mergeEvents :: R.Reflex t => dk (R.Event t) -> R.Event t (dk Identity)
  sequenceDynamic :: R.Reflex t => dk (R.Dynamic t) -> R.Dynamic t (dk Identity)

instance GCompare k => ReflexSequenceable (DMap k) where
  mergeEvents = R.merge
  sequenceDynamic = R.distributeDMapOverDynPure

-- | This class carries the ability to sequence patches in the way of MonadAdjust And then turn the result into a Dynamic.
-- sequenceWithPatch takes a static d containing adjustable (m a), e.g., widgets, and event carrying patches, that is
-- new widgets for some keys k, and "pulls out" (sequences) the m.
-- patchPairToDynamic is a sort of inverse, turning a static d containing values and events with patches to it, new values at some keys,
-- and returns an adjustable monad containing a Dynamic of a value containing d.
-- |


class ( R.Patch (pd Identity)
      , R.PatchTarget (pd Identity) ~ d Identity)
  => PatchSequenceable d pd  where
  sequenceWithPatch :: R.Adjustable t m => d m -> R.Event t (pd m) -> m (d Identity, R.Event t (pd Identity))
  patchPairToDynamic :: (R.MonadHold t m, R.Reflex t) => d Identity -> R.Event t (pd Identity) -> m (R.Dynamic t (d Identity))

-- | DMaps are our prime example of something sequenceable
instance (GCompare (Const2 k a), Ord k) => PatchSequenceable (DMap (Const2 k a)) (PatchDMap (Const2 k a)) where
  sequenceWithPatch :: R.Adjustable t m
                    => DMap (Const2 k a) m
                    -> R.Event t (PatchDMap (Const2 k a) m)
                    -> m (DMap (Const2 k a) Identity, R.Event t (PatchDMap (Const2 k a) Identity))
  sequenceWithPatch = R.sequenceDMapWithAdjust

  patchPairToDynamic :: (R.MonadHold t m, R.Reflex t)
                     => DMap (Const2 k a) Identity
                     -> R.Event t (PatchDMap (Const2 k a) Identity)
                     -> m (R.Dynamic t (DMap (Const2 k a) Identity))
  patchPairToDynamic a0 a' = R.incrementalToDynamic <$> R.holdIncremental a0 a'


newtype ComposedIntMap a f = ComposedIntMap { unCI :: Compose IntMap f a } 
newtype ComposedPatchIntMap a f = ComposedPatchIntMap { unCPI :: Compose PatchIntMap f a }

fromComposed :: Functor f => Compose f Identity a -> f a
fromComposed = fmap runIdentity . getCompose

toComposed :: Functor f => f a -> Compose f Identity a
toComposed = Compose . fmap Identity

instance Monoid (ComposedPatchIntMap a Identity) where
  mempty = ComposedPatchIntMap . toComposed $ mempty
  mappend (ComposedPatchIntMap a) (ComposedPatchIntMap b) = ComposedPatchIntMap . toComposed $ mappend (fromComposed a) (fromComposed b)

instance R.Patch (ComposedPatchIntMap a Identity) where
  type PatchTarget (ComposedPatchIntMap a Identity) = ComposedIntMap a Identity
  apply (ComposedPatchIntMap p) (ComposedIntMap v) = ComposedIntMap . toComposed <$> R.apply (fromComposed p) (fromComposed v)



instance Semigroup (ComposedPatchIntMap a Identity) where
  (ComposedPatchIntMap a) <> (ComposedPatchIntMap b) = ComposedPatchIntMap . toComposed $ (fromComposed a) <> (fromComposed b)
   -- PatchMap is idempotent, so stimes n is id for every n
#if MIN_VERSION_semigroups(0,17,0)
  stimes = stimesIdempotentMonoid
#else
  times1p n x = case compare n 0 of
    LT -> error "stimesIdempotentMonoid: negative multiplier"
    EQ -> mempty
    GT -> x
#endif
  
instance PatchSequenceable (ComposedIntMap a) (ComposedPatchIntMap a) where  
  sequenceWithPatch :: R.Adjustable t m
                    => ComposedIntMap a m
                    -> R.Event t (ComposedPatchIntMap a m)
                    -> m (ComposedIntMap a Identity, R.Event t (ComposedPatchIntMap a Identity))
  sequenceWithPatch (ComposedIntMap ci) cpEv =
    let f (im, pim) = (ComposedIntMap . Compose $ im, fmap (ComposedPatchIntMap . Compose) pim)
    in f <$> R.traverseIntMapWithKeyWithAdjust (\_ -> fmap Identity) (getCompose ci) (fmap (getCompose . unCPI) cpEv) 

  patchPairToDynamic :: (R.MonadHold t m, R.Reflex t)
                     => ComposedIntMap a Identity
                     -> R.Event t (ComposedPatchIntMap a Identity)
                     -> m (R.Dynamic t (ComposedIntMap a Identity))
  patchPairToDynamic a0 a' = R.incrementalToDynamic <$> R.holdIncremental a0 a'

