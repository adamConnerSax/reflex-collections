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
module Reflex.Collections.CollectionsDM
  (
    listHoldWithKeyDM
  , listWithKeyDM
  , listViewWithKeyDM
  , listWithKeyShallowDiffDM
  , selectViewListWithKeyDM
--  , toSeqType
--  , mergeOverDM
--  , distributeOverDynPureDM
  ) where


import           Reflex.Collections.Diffable        (Diffable (..))
import           Reflex.Collections.HasFan          (HasFan (..))
import           Reflex.Collections.KeyedCollection (KeyedCollection (Diff, Key))
import           Reflex.Collections.ToPatchType     (DMappable (..),
                                                     distributeOverDynPure,
                                                     functorMappedToSeqType,
                                                     mergeOver, toSeqType)

import           Reflex.Collections.Collections     (listHoldWithKeyGeneral,
                                                     listViewWithKeyGeneral,
                                                     listWithKeyGeneral,
                                                     listWithKeyShallowDiffGeneral,
                                                     selectViewListWithKeyGeneral)

import           Reflex.Collections.DMapIso         (DMapIso (DMapKey),
                                                     DiffToPatchDMap)

import           Control.Monad.Fix                  (MonadFix)
import           Data.Functor.Misc                  (Const2)
import qualified Reflex                             as R



-- This constraint requires f isomorphic to a DMap, that diffs of f can be mapped to DMaps with the same key and that that key is (Const2 k v)
type DMappableC f = (DMapIso f, DiffToPatchDMap f, Ord (Key f), DMapKey f ~ Const2 (Key f))

-- This constraint requires that f can be fanned using the key of KeyedCollection f
type FannableC f = (HasFan f, FanInKey f ~ Key f)

-- This constraint requires that f be diffable, that (Diff f) be a functor, and that f and (Diff f) use the same key type
type DiffableC f = (Diffable f (Diff f), Functor (Diff f), Key f ~ Key (Diff f))

listHoldWithKeyDM :: ( R.Adjustable t m
                     , R.MonadHold t m
                     , DMappableC f)
  => f v -> R.Event t (Diff f v) -> (Key f -> v -> m a) -> m (R.Dynamic t (f a))
listHoldWithKeyDM fv diffEv = fmap (fmap unDMappable) . listHoldWithKeyGeneral (DMappable fv) diffEv


-- for the listWithKey and listWithKeyShallow diff we need to be able to fan events
listWithKeyDM :: ( R.Adjustable t m
                 , R.MonadHold t m
                 , R.PostBuild t m
                 , MonadFix m
                 , DMappableC f
                 , FannableC f
                 , DiffableC f
                 , Monoid (f v))
  => R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyDM vals = fmap (fmap unDMappable) . listWithKeyGeneral (DMappable <$> vals)


listViewWithKeyDM ::  ( R.Adjustable t m
                      , R.PostBuild t m
                      , R.MonadHold t m
                      , MonadFix m
                      , DMappableC f
                      , FannableC f
                      , DiffableC f
                      , Monoid (f v))
  => R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (f a))
listViewWithKeyDM vals = fmap (fmap unDMappable) . listViewWithKeyGeneral (DMappable <$> vals)


listWithKeyShallowDiffDM :: ( R.Adjustable t m
                            , MonadFix m
                            , R.MonadHold t m
                            , DMappableC f
                            , FannableC (Diff f)
                            , DiffableC f
                            , Monoid (f ()))
  => f v -> R.Event t (Diff f v) -> (Key f -> v -> R.Event t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyShallowDiffDM initialVals dEv = fmap (fmap unDMappable) . listWithKeyShallowDiffGeneral (DMappable initialVals) dEv



-- | Create a dynamically-changing set of widgets, one of which is selected at any time.
selectViewListWithKeyDM :: ( R.Adjustable t m
                           , MonadFix m
                           , R.MonadHold t m
                           , R.PostBuild t m
                           , Foldable f -- for toList
                           , DMappableC f
                           , FannableC f
                           , DiffableC f
                           , Monoid (f v))
  => R.Dynamic t (Key f)          -- ^ Current selection key
  -> R.Dynamic t (f v)      -- ^ Dynamic container of values
  -> (Key f -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -- ^ Function to create a widget for a given key from Dynamic value and Dynamic Bool indicating if this widget is currently selected
  -> m (R.Event t (Key f, a))        -- ^ Event that fires when any child's return Event fires.  Contains key of an arbitrary firing widget.
selectViewListWithKeyDM selection vals = selectViewListWithKeyGeneral selection (DMappable <$> vals)

