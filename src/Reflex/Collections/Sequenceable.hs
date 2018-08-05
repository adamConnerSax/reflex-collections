{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE ScopedTypeVariables   #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.Sequenceable
  (
    ReflexSequenceable(..)
  , PatchSequenceable(..)
  ) where

import qualified Reflex                 as R

import           Data.Dependent.Map     (DMap, GCompare)
import           Data.Functor.Compose   (Compose (Compose, getCompose))
import           Data.Functor.Misc      (Const2 (..))
import           Reflex.Patch           (PatchDMap (..))


import           Control.Monad.Fix      (MonadFix)
import           Control.Monad.Identity (Identity (..), void)

import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)


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
class ( R.Patch (pd k Identity)
      , R.PatchTarget (pd k Identity) ~ d k Identity)
  => PatchSequenceable (d :: (Type -> Type) -> (Type -> Type) -> Type)
                  (pd :: (Type -> Type) -> (Type -> Type) -> Type)  (k :: Type -> Type) where
  sequenceWithPatch :: R.Adjustable t m => d k m -> R.Event t (pd k m) -> m (d k Identity, R.Event t (pd k Identity))
  patchPairToDynamic :: (R.MonadHold t m, R.Reflex t) =>d k Identity -> R.Event t (pd k Identity) -> m (R.Dynamic t (d k Identity))

-- | DMaps are our prime example of something sequenceable
instance (GCompare (Const2 k a), Ord k) => PatchSequenceable DMap PatchDMap (Const2 k a) where
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

