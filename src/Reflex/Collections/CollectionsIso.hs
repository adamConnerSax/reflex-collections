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
{-# LANGUAGE UndecidableInstances #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.CollectionsIso
  (
    distributeOverDynPureIso
  , mergeOverIso
  , listHoldWithKeyIso
  , listWithKeyIso
  , listIso
  , listViewWithKeyIso
  , listWithKeyShallowDiffIso
  , selectViewListWithKeyIso
  ) where


import           Reflex.Collections.Diffable        (Diffable (..))
import           Reflex.Collections.DMappable       (DMappable (..))
import           Reflex.Collections.IntMappable     (IntMappable (..))
import           Reflex.Collections.KeyedCollection (KeyedCollection (Key))
import           Reflex.Collections.ToPatchType     (ToPatchType,SeqTypes(..), FanSelectKey)
import           Reflex.Collections.Sequenceable    (PatchSequenceable, ReflexSequenceable, ReflexMergeable)


import           Reflex.Collections.Collections     (distributeOverDynPure,
                                                     mergeOver,
                                                     listHoldWithKeyGeneral,
                                                     listViewWithKeyGeneral,
                                                     listWithKeyGeneral,
                                                     listWithKeyShallowDiffGeneral,
                                                     selectViewListWithKeyGeneral)

import           Reflex.Collections.DMapIso         (DMapIso (DMapKey))
import           Reflex.Collections.IntMapIso         (IntMapIso ())

import           Control.Monad.Fix                  (MonadFix)
import           Data.Dependent.Map                 (GCompare)
import           Data.Functor.Misc                  (Const2)
import           Data.Kind                          (Type, Constraint)

import           Data.Map.Strict                    (Map)
import           Data.Hashable                      (Hashable)
import           Data.HashMap.Strict                (HashMap)
import           Data.IntMap                        (IntMap)
import           Data.Sequence                      (Seq)
import           Data.Array                         (Array, Ix)


import qualified Reflex                             as R


class ( KeyedCollection (Wrapped f)
      , Diffable (Wrapped f)
      , ToPatchType (Wrapped f)
      , Key (Wrapped f) ~ Key f
      , Diff (Wrapped f) ~ Diff f) => HoldableIso (f :: Type -> Type) where
  type Wrapped f :: Type -> Type
  type HoldableC f :: Constraint
  wrap :: f q -> Wrapped f q
  unWrap :: Wrapped f q -> f q
  

type WrappedC f a = (SeqTypes (Wrapped f) a, PatchSequenceable (SeqType (Wrapped f) a) (SeqPatchType (Wrapped f) a), ReflexMergeable (SeqType (Wrapped f) a))


distributeOverDynPureIso :: ( R.Reflex t
                            , WrappedC f v
                            , ReflexSequenceable (SeqType (Wrapped f) v)
                            , HoldableIso f
                            , HoldableC f)
  => f (R.Dynamic t v) -> R.Dynamic t (f v)
distributeOverDynPureIso = fmap unWrap . distributeOverDynPure . wrap   


mergeOverIso :: ( R.Reflex t
                , WrappedC f v
                , HoldableIso f
                , HoldableC f)
  => f (R.Event t v) -> R.Event t (f v)
mergeOverIso = fmap unWrap . mergeOver . wrap   

listHoldWithKeyIso :: ( R.Adjustable t m
                      , R.MonadHold t m
                      , HoldableIso f
                      , HoldableC f
                      , WrappedC f a
                      , Diffable f) -- Diffable isn't required but the associated type Diff is, so this seems clearer.
  => f v -> R.Event t (Diff f v) -> (Key f -> v -> m a) -> m (R.Dynamic t (f a))
listHoldWithKeyIso fv diffEv = fmap (fmap unWrap) . listHoldWithKeyGeneral (wrap fv) diffEv


-- for the listWithKey and listWithKeyShallowDiff we need to be able to fan events

-- This constraint requires that f be diffable, that (Diff f) be a functor, and that f and (Diff f) use the same key type
type DiffableC f = (Diffable f, Functor (Diff f), Key f ~ Key (Diff f))
type WrappedC2 f v a = (WrappedC f a, Monoid ((Wrapped f) v), GCompare (FanSelectKey (Wrapped f) v))

listWithKeyIso :: ( R.Adjustable t m
                  , R.MonadHold t m
                  , R.PostBuild t m
                  , MonadFix m
                  , HoldableIso f
                  , WrappedC2 f v a
                  , DiffableC f)
  => R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyIso vals = fmap (fmap unWrap) . listWithKeyGeneral (wrap <$> vals)

listIso :: ( R.Adjustable t m
           , R.MonadHold t m
           , R.PostBuild t m
           , MonadFix m
           , HoldableIso f
           , WrappedC2 f v a
           , DiffableC f)
  => R.Dynamic t (f v) -> (R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
listIso df mkChild = listWithKeyIso df (\_ dv -> mkChild dv)   


listViewWithKeyIso ::  ( R.Adjustable t m
                       , R.PostBuild t m
                       , R.MonadHold t m
                       , MonadFix m
                       , HoldableIso f
                       , HoldableC f
                       , WrappedC2 f v a
                       , WrappedC f (R.Event t a)
                       , DiffableC f)
  => R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (f a))
listViewWithKeyIso vals = fmap (fmap unWrap) . listViewWithKeyGeneral (wrap <$> vals)


listWithKeyShallowDiffIso :: ( R.Adjustable t m
                             , MonadFix m
                             , R.MonadHold t m
                             , HoldableIso f
                             , HoldableC f
                             , DiffableC f
                             , WrappedC2 f v a
                             , Monoid ((Wrapped f) ()))
  => f v -> R.Event t (Diff f v) -> (Key f -> v -> R.Event t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyShallowDiffIso initialVals dEv = fmap (fmap unWrap) . listWithKeyShallowDiffGeneral (wrap initialVals) dEv



-- | Create a dynamically-changing set of widgets, one of which is selected at any time.
selectViewListWithKeyIso :: ( R.Adjustable t m
                            , MonadFix m
                            , R.MonadHold t m
                            , R.PostBuild t m
                            , Foldable (Wrapped f) -- for toList
                            , HoldableIso f
                            , HoldableC f
                            , WrappedC2 f v a
                            , WrappedC f (R.Event t (Key (Diff f), a))
                            , Ord (Key (Diff f))
                            , DiffableC f)
  => R.Dynamic t (Key f)          -- ^ Current selection key
  -> R.Dynamic t (f v)      -- ^ Dynamic container of values
  -> (Key f -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -- ^ Function to create a widget for a given key from Dynamic value and Dynamic Bool indicating if this widget is currently selected
  -> m (R.Event t (Key f, a))        -- ^ Event that fires when any child's return Event fires.  Contains key of an arbitrary firing widget.
selectViewListWithKeyIso selection vals = selectViewListWithKeyGeneral selection (wrap <$> vals)


-- This constraint requires f isomorphic to a DMap, that diffs of f can be mapped to DMaps with the same key and that that key is (Const2 k v)
type DMappableC f = (DMapIso f, Ord (Key f), DMapKey f ~ Const2 (Key f))

instance Ord k => HoldableIso (Map k) where
  type Wrapped (Map k) = DMappable (Map k)
  type HoldableC (Map k) = DMappableC (Map k)
  wrap = DMappable
  unWrap (DMappable x) = x

instance (Ord k, Hashable k) => HoldableIso (HashMap k) where
  type Wrapped (HashMap k) = DMappable (HashMap k)
  type HoldableC (HashMap k) = DMappableC (HashMap k)
  wrap = DMappable
  unWrap (DMappable x) = x

type IntMappableC f = (IntMapIso f, Ord (Key f), DMapKey f ~ Const2 (Key f))
  
instance HoldableIso IntMap where
  type Wrapped IntMap = IntMappable IntMap
  type HoldableC IntMap = IntMappableC IntMap
  wrap = IntMappable
  unWrap (IntMappable x) = x
  
instance (Enum k, Bounded k, Ix k) => HoldableIso (Array k) where
  type Wrapped (Array k) = IntMappable (Array k)
  type HoldableC (Array k) = IntMappableC (Array k)
  wrap = IntMappable
  unWrap (IntMappable x) = x

instance HoldableIso ([]) where
  type Wrapped ([]) = IntMappable ([])
  type HoldableC ([]) = IntMappableC ([])
  wrap = IntMappable
  unWrap (IntMappable x) = x

instance HoldableIso (Seq) where
  type Wrapped (Seq) = IntMappable (Seq)
  type HoldableC (Seq) = IntMappableC (Seq)
  wrap = IntMappable
  unWrap (IntMappable x) = x

  
 
