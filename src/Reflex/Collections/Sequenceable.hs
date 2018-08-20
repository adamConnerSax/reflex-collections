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
    ReflexMergeable (..)
  , PatchSequenceable(..)
  , ReflexSequenceable(..)
  ) where

import qualified Reflex                 as R
import           Reflex.Patch           (PatchDMap (..))

import Reflex.Collections.ComposedIntMap ( ComposedIntMap(..)
                                         , ComposedPatchIntMap(..))

import           Data.Dependent.Map     (DMap, GCompare)
import           Data.Functor.Misc      (Const2 (..))
import           Control.Monad.Identity (Identity (..))
import           Data.Kind              (Type)
import qualified Data.IntMap            as IM
import           Data.Functor.Compose   (Compose(..), getCompose)

-- | This class carries the ability to do an efficient event merge
-- "Merge a collection of events.  The resulting event will occur if at least one input event is occuring
-- and will contain all simultaneously occurring events."
class ReflexMergeable (f :: (Type -> Type) -> Type) where
  mergeEvents :: R.Reflex t => f (R.Event t) -> R.Event t (f Identity)

instance GCompare k => ReflexMergeable (DMap k) where
  mergeEvents = R.merge

instance ReflexMergeable (ComposedIntMap a) where
  mergeEvents = fmap (ComposedIntMap . Compose . fmap Identity) . R.mergeInt . getCompose  . unCI


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


class ReflexSequenceable (f :: (Type -> Type) -> Type) where
  sequenceDynamic :: R.Reflex t => f (R.Dynamic t) -> R.Dynamic t (f Identity)

instance GCompare k => ReflexSequenceable (DMap k) where
  sequenceDynamic = R.distributeDMapOverDynPure 

instance ReflexSequenceable (ComposedIntMap a) where
  sequenceDynamic cim =
    let im = (getCompose . unCI $ cim) 
    in case IM.toList im of 
      [] -> fmap (ComposedIntMap . Compose) $ R.constDyn IM.empty
      [(n, v)] -> fmap (ComposedIntMap . Compose . IM.singleton n . Identity) v
      _ ->
        let getInitial = IM.traverseWithKey (\_ -> fmap Identity . R.sample . R.current) im
            edmPre = fmap (fmap Identity) . R.mergeInt $ IM.map R.updated im
            result = R.unsafeBuildDynamic getInitial $ flip R.pushAlways edmPre $ \news -> do
              olds <- R.sample $ R.current result
              return $ IM.unionWithKey (\_ _ new -> new) olds news
        in fmap (ComposedIntMap . Compose) result


