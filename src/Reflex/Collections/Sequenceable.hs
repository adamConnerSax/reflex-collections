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
import           Reflex.Patch           (PatchDMap (..), PatchIntMap)

import           Reflex.Collections.DMapIso (DMapIso (..))

import           Data.Dependent.Map     (DMap, GCompare)
import           Data.Functor.Misc      (Const2 (..))
import           Control.Monad.Identity (Identity (..))
import           Data.Kind              (Type)
import           Data.IntMap            (IntMap)
import qualified Data.IntMap            as IM
import           Data.Functor.Compose   (Compose(..), getCompose)
import           Data.Semigroup         (Semigroup(..),stimesIdempotentMonoid)
import           Data.Monoid            (Monoid)
import           Data.Foldable          (Foldable)
import           Data.Traversable       (Traversable)

-- | This class carries the ability to do an efficient event merge
-- "Merge a collection of events.  The resulting event will occur if at least one input event is occuring
-- and will contain all simultaneously occurring events."
class ReflexMergeable (f :: (Type -> Type) -> Type) where
  mergeEvents :: R.Reflex t => f (R.Event t) -> R.Event t (f Identity)

instance GCompare k => ReflexMergeable (DMap k) where
  mergeEvents = R.merge

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

instance ReflexMergeable (ComposedIntMap a) where
  mergeEvents = fmap (ComposedIntMap . Compose . fmap Identity) . R.mergeInt . getCompose  . unCI

fromComposed :: Functor f => Compose f Identity a -> f a
fromComposed = fmap runIdentity . getCompose

toComposed :: Functor f => f a -> Compose f Identity a
toComposed = Compose . fmap Identity

newtype ComposedPatchIntMap a f = ComposedPatchIntMap { unCPI :: Compose PatchIntMap f a }

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


{-
-- Seems like I ought to be able to abstract out the collection requirements for sequenceing to work but I'm
-- lost in the dependent-typing
class SeqCollection (f :: (Type -> Type) -> Type) where  
  type RSKey :: Type -> Type
  type RSKeyValue :: Type
  rsEmpty :: Functor g => f g
  rsSingleton :: Functor g => RSKey a -> g a -> f g
  rsToList :: Functor g => f g -> RSKeyValue
  rsTraverseWithKey :: (Functor g, Functor h, Applicative t) => (forall a. RSKey -> g a -> t (h a)) -> f g -> t (f h)
  rsUnionWithKey :: Functor g => (RSKey -> g a -> g a -> g a) -> f g -> f g -> f g


instance GCompare k => SeqCollection (DMap k) where
  type RSKey (DMap k) = Const2 k a
  

distributeSequenceableOverDynPure :: (ReflexMergeable f, SeqCollection f) => f (Dynamic t a) -> Dynamic t (f Identity)
distributeSequenceableOverDynPure =
-}
