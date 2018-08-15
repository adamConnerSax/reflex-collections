{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DefaultSignatures     #-}
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
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.CollectionsIM
  (
    listHoldWithKeyIM
  , listWithKeyIM
  , listViewWithKeyIM
  , listWithKeyShallowDiffIM
  , selectViewListWithKeyIM
  ) where


import           Reflex.Collections.Diffable        (Diffable (..))
import           Reflex.Collections.IntMappable     (IntMappable (..))
import           Reflex.Collections.KeyedCollection (KeyedCollection (Key))

import           Reflex.Collections.Collections     (FanSelectKey,
                                                     listHoldWithKeyGeneral,
                                                     listViewWithKeyGeneral,
                                                     listWithKeyGeneral,
                                                     listWithKeyShallowDiffGeneral,
                                                     selectViewListWithKeyGeneral)

import           Reflex.Collections.IntMapIso       (IntMapIso (DMapKey))

import           Control.Monad.Fix                  (MonadFix)
import           Data.Dependent.Map                 (GCompare)
import           Data.Functor.Misc                  (Const2)

import qualified Reflex                             as R

-- This constraint requires f isomorphic to a DMap, that diffs of f can be mapped to DMaps with the same key and that that key is (Const2 k v)
type IntMappableC f = (IntMapIso f, Ord (Key f), DMapKey f ~ Const2 (Key f))

listHoldWithKeyIM :: ( R.Adjustable t m
                     , R.MonadHold t m
                     , IntMappableC f
                     , Diffable f) -- Diffable isn't required but the assocaited type Diff is, so this seems clearer.
  => f v -> R.Event t (Diff f v) -> (Key f -> v -> m a) -> m (R.Dynamic t (f a))
listHoldWithKeyIM fv diffEv = fmap (fmap unIntMappable) . listHoldWithKeyGeneral (IntMappable fv) diffEv


-- for the listWithKey and listWithKeyShallowDiff we need to be able to fan events

-- This constraint requires that f be diffable, that (Diff f) be a functor, and that f and (Diff f) use the same key type
type DiffableC f = (Diffable f, Functor (Diff f), Key f ~ Key (Diff f))

listWithKeyIM :: ( R.Adjustable t m
                 , R.MonadHold t m
                 , R.PostBuild t m
                 , MonadFix m
                 , IntMappableC f
                 , DiffableC f
                 , GCompare (FanSelectKey f v)
                 , Monoid (f v))
  => R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyIM vals = fmap (fmap unIntMappable) . listWithKeyGeneral (IntMappable <$> vals)


listViewWithKeyIM ::  ( R.Adjustable t m
                      , R.PostBuild t m
                      , R.MonadHold t m
                      , MonadFix m
                      , IntMappableC f
                      , DiffableC f
                      , GCompare (FanSelectKey f v)
                      , Monoid (f v))
  => R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (f a))
listViewWithKeyIM vals = fmap (fmap unIntMappable) . listViewWithKeyGeneral (IntMappable <$> vals)


listWithKeyShallowDiffIM :: ( R.Adjustable t m
                            , MonadFix m
                            , R.MonadHold t m
                            , IntMappableC f
                            , DiffableC f
                            , GCompare (FanSelectKey f v)
                            , Monoid (f ()))
  => f v -> R.Event t (Diff f v) -> (Key f -> v -> R.Event t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyShallowDiffIM initialVals dEv = fmap (fmap unIntMappable) . listWithKeyShallowDiffGeneral (IntMappable initialVals) dEv



-- | Create a dynamically-changing set of widgets, one of which is selected at any time.
selectViewListWithKeyIM :: ( R.Adjustable t m
                           , MonadFix m
                           , R.MonadHold t m
                           , R.PostBuild t m
                           , Foldable f -- for toList
                           , IntMappableC f
                           , DiffableC f
                           , GCompare (FanSelectKey f v)
                           , Monoid (f v))
  => R.Dynamic t (Key f)          -- ^ Current selection key
  -> R.Dynamic t (f v)      -- ^ Dynamic container of values
  -> (Key f -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -- ^ Function to create a widget for a given key from Dynamic value and Dynamic Bool indicating if this widget is currently selected
  -> m (R.Event t (Key f, a))        -- ^ Event that fires when any child's return Event fires.  Contains key of an arbitrary firing widget.
selectViewListWithKeyIM selection vals = selectViewListWithKeyGeneral selection (IntMappable <$> vals)

