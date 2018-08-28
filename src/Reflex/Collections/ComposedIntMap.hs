{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
-- | This module implements the `ComposedIntMap` and `ComposedPatchIntMap` classes, in order to have a version
-- of IntMap and PatchIntMap which have the same kind as DMap.  More specificially
-- `DMap k :: (Type -> Type) -> Type`, that is `DMap k` and `ComposedIntMap a` both take a type constructor
-- (a thing of kind `Type -> Type`) and produce a type.
-- This allows us to reuse the same machinery for both types so we can have DMap-backed collections and IntMap-backed
-- collections handled in a similar way.
module Reflex.Collections.ComposedIntMap
  (
    ComposedIntMap(..)
  , ComposedPatchIntMap(..)
  ) where

import qualified Reflex                 as R
import           Reflex.Patch           (PatchIntMap)

import           Control.Monad.Identity (Identity (..))
import           Data.Functor.Compose   (Compose (..), getCompose)
import           Data.IntMap            (IntMap)
import           Data.Monoid            (Monoid)
import           Data.Semigroup         (Semigroup (..), stimesIdempotentMonoid)


newtype ComposedIntMap a f = ComposedIntMap { unCI :: Compose IntMap f a }

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



