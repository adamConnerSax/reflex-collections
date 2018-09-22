{-# LANGUAGE CPP                   #-}
{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
-- | Main module of @reflex-collections@
--
-- In most cases you will likely import just this module.  Other modules in this package may
-- be useful if you want to use the functions in this module on other collection types.
--
-- = Reflex Collection Management
--
-- It's fairly common in reflex to have a dynamic collection of things, say `Dynamic t (f a)` and a widget you want to make for each a,
-- one which responds to changes in the input collection,
-- e.g., `w :: DomBuilder t m => (Dynamic t a -> m (Dynamic t b))`.  The naive way to manage such a collection,
-- fmapping the widget construction over the collection, leaves you with `Dynamic t (f (m (Dynamic t b)))` which, in order to join the Dynamics
-- and sequence the monad, leaving `m (f (Dynamic t b))`, will force you to call some function which rebuilds the entire portion of the network.
--
-- The functions in Reflex.Collection, and replicated here, allow you to do this more efficiently, only rebuilding the necessary parts of the network
-- as the input structure is updated--updating individual widgets when their inputs change
-- and adding/removing widgets when things enter and leave the collection.
--
-- The original versions in Reflex are identical to these (with one exception, noted below) but only work for `Data.Map.Strict`
-- The versions below, with the same names, work exactly the same way as their counterparts but work for more types,
-- including HashMap, IntMap, [], Data.Sequence.Seq, Data.Tree.Tree and Array.
-- The Array case is special, and will only work for arrays that have values for every possible key,
-- representing a sort of total function from the key type (usually a bounded enumeration) to the contained type.
-- Tree and Array will work only with listHoldWithKey because they cannot be empty and the rest of the functions require an
-- empty collection to work.
--
-- This package also provides typeclasses and typefamilies that should make adding support for a new collection type fairly
-- straightforward.
--
-- Because the operations are related, this module also provide generalized versions of Reflex's `distributeMapOverDynPure` and `mergeMap`
--
-- One complication of the more general versions is the introduction of the type "Diff f",
-- specified for each type inside the `Diffable` type class. For map-like types, `Diff f` is the same as f but for other types, e.g. `[]`,
-- we use a more compact representation of Diffs, in this case `type Diff [] = IntMap`.
--
-- For all places where the Reflex versions of these functions work, these functions will be drop in replacements.

module Reflex.Collections.Collections
  (
    listHoldWithKey
  , listWithKey
  , listWithKeyMaybe
  , list
  , listMaybe
  , listViewWithKey
  , listViewWithKeyMaybe
  , listWithKeyShallowDiff
  , listViewWithKeyShallowDiff
  , listViewWithKeyShallowDiffMaybe
  , selectViewListWithKey
  , selectViewListWithKeyMaybe
  , simplifyDynMaybe
  , maybeHelper
  , SequenceableC
  , SequenceableWithEventC
  , FannableC
-- re-exports
  , mergeOver
  , distributeOverDynPure
  , KeyedCollection(..)
  , Diffable (..)
  , MapLike (..)
  , Patchable
  , Distributable
  , Mergeable
  , GCompare
  , SeqTypes
  , WithEmpty
  ) where


import           Reflex.Collections.Diffable        (Diffable (..),
                                                     MapLike (..))
import           Reflex.Collections.KeyedCollection (KeyedCollection (..))
import           Reflex.Collections.Sequenceable    (PatchSequenceable (..),
                                                     SequenceC)
import           Reflex.Collections.ToPatchType     (Distributable, Mergeable,
                                                     Patchable, SeqTypes (..),
                                                     ToPatchType (..),
                                                     distributeOverDynPure,
                                                     functorMappedToSeqType,
                                                     mergeOver)
import           Reflex.Collections.WithEmpty       (WithEmpty (..),
                                                     withEmptyToMaybe)

import qualified Reflex                             as R

import           Control.Monad                      (join, void)
import           Control.Monad.Fix                  (MonadFix)
import           Data.Dependent.Map                 (GCompare)
import           Data.Functor.Misc                  (Const2 (..))
import           Data.Proxy                         (Proxy (..))

-- for specializtions
import           Data.Array                         (Array, Ix)
import           Data.Hashable                      (Hashable)
import           Data.HashMap.Strict                (HashMap)
import           Data.IntMap                        (IntMap)
import           Data.Map                           (Map)
import           Data.Sequence                      (Seq)
import           Data.Tree                          (Tree)

-- If we only want to support ghc8+, we could replace proxies with type application.
-- Quantified constraints would simplify some signatures here, since we often want (forall a. Patchable f a).  But that'll be a while.
-- we could use Data.Constraint to do it, but that's messy as well since we'd need to unwrap the dictionaries at the call site.

type SequenceableC f v = (SequenceC (SeqType f) v, SequenceC (SeqPatchType f) v)
type FannableC f v = SequenceC (SeqType f) v
type SequenceableWithEventC t f v = (SequenceableC f v, SequenceableC f (R.Event t v))

-- | listHoldWithKey is an efficient collection management function when your input is a *static* initial state and an event stream of updates.
-- This version uses a widget that expects a static input and thus the widget will need to be rebuilt if the incoming
-- event changes the value of v for a given k.  What this function does provide is efficient routing of each event to the specific
-- widget that has changed, thus rebuilding only the widgets that have changing inputs.
-- NB: use of unsafeFromSeqType is okay here.  We are updating an initial container which has values for all keys if required.
listHoldWithKey :: forall t m f v a. (R.Adjustable t m, R.MonadHold t m, Patchable f, SequenceableC f a)
  => f v -> R.Event t (Diff f (Maybe v)) -> (Key f -> v -> m a) -> m (R.Dynamic t (f a))
listHoldWithKey c0 c' h = do
  let dc0 = functorMappedToSeqType h c0
      dc' = fmap (makePatchSeq (Proxy :: Proxy f) h) c'
  (a0 ,a') <- sequenceWithPatch dc0 dc'
  fmap unsafeFromSeqType <$> patchPairToDynamic a0 a'
{-# INLINABLE listHoldWithKey #-}

-- | listWithKey handles the case where your input collection is dynamic.  In this case your widget has to handle dynamic inputs.
-- and thus the widget can update without rebuilding when the input value changes.
listWithKey :: ( R.Adjustable t m
               , R.PostBuild t m
               , MonadFix m
               , R.MonadHold t m
               , Patchable f
               , Monoid (f v)
               , SequenceableC f a
               , FannableC f v)
  => R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
listWithKey = listWithKeyGeneral mempty
{-# INLINABLE listWithKey #-}

listWithKeyMaybe :: ( R.Adjustable t m
                    , R.PostBuild t m
                    , MonadFix m
                    , R.MonadHold t m
                    , Patchable (WithEmpty f)
                    , SequenceableC f a
                    , FannableC f v)
  => R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m a) -> m (R.Dynamic t (Maybe (f a)))
listWithKeyMaybe fDyn widget = fmap withEmptyToMaybe <$> listWithKeyGeneral Empty (NonEmpty <$> fDyn) widget
{-# INLINABLE listWithKeyMaybe #-}

listWithKeyGeneral :: forall t m f v a. ( R.Adjustable t m
                                        , R.PostBuild t m
                                        , R.MonadHold t m
                                        , MonadFix m
                                        , Patchable f
                                        , SequenceableC f a
                                        , FannableC f v)
  => f v -- an empty (f v)
  -> R.Dynamic t (f v)
  -> (Key f -> R.Dynamic t v -> m a)
  -> m (R.Dynamic t (f a))
listWithKeyGeneral emptyFV vals mkChild = do
  postBuild <- R.getPostBuild
  let childValChangedSelector = fanCollection $ R.updated vals
  rec sentVals :: R.Dynamic t (f v) <- R.foldDyn applyDiff emptyFV changeVals
      let changeVals :: R.Event t (Diff f (Maybe v))
          changeVals = R.attachWith diffOnlyKeyChanges (R.current sentVals) $ R.leftmost
                       [ R.updated vals
                       , R.tag (R.current vals) postBuild
                       ]
  listHoldWithKey emptyFV changeVals $ \k v ->
    mkChild k =<< R.holdDyn v (selectCollection (Proxy :: Proxy f) childValChangedSelector k)
{-# INLINABLE listWithKeyGeneral #-}

list :: ( R.Adjustable t m
        , R.PostBuild t m
        , MonadFix m
        , R.MonadHold t m
        , Patchable f
        , Monoid (f v)
        , FannableC f v
        , SequenceableC f a)
    => R.Dynamic t (f v) -> (R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
list = listGeneral mempty
{-# INLINABLE list #-}

listMaybe :: ( R.Adjustable t m
             , R.PostBuild t m
             , MonadFix m
             , R.MonadHold t m
             , Patchable (WithEmpty f)
             , SequenceableC f a
             , FannableC f v)
  => R.Dynamic t (f v) -> (R.Dynamic t v -> m a) -> m (R.Dynamic t (Maybe (f a)))
listMaybe fDyn widget = fmap withEmptyToMaybe <$> listGeneral Empty (NonEmpty <$> fDyn) widget
{-# INLINABLE listMaybe #-}

-- | Create a dynamically-changing set of Event-valued widgets. In this case, ones that are indifferent to position
listGeneral :: ( R.Adjustable t m
               , R.PostBuild t m
               , MonadFix m
               , R.MonadHold t m
               , Patchable f  -- for the listHold
               , SequenceableC f a
               , FannableC f v)
  => f v -- must be empty
  -> R.Dynamic t (f v) -> (R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
listGeneral emptyFV fDyn mkChild = listWithKeyGeneral emptyFV fDyn (\_ dv -> mkChild dv)
{-# INLINABLE listGeneral #-}

-- | `listViewWithKey` is a special case of listWithKey for widgets which return Events (which can then be merged to return a smaller structure).
-- NB: This returns Event t (Diff f a) since we can't a-priori, know that we can construct `f a` from `Diff f a`.  Though for maps and lists we can.
-- But for total containers, e.g., Array k, we cannot since we will get events on only some keys but an Array k must have a value for all keys.
listViewWithKey ::  ( R.Adjustable t m
                    , R.PostBuild t m
                    , R.MonadHold t m
                    , MonadFix m
                    , Mergeable f
                    , Monoid (f v)
                    , FannableC f v
                    , SequenceableWithEventC t f a)
  => R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (Diff f a))
listViewWithKey = listViewWithKeyGeneral mempty
{-# INLINABLE listViewWithKey #-}

listViewWithKeyMaybe ::  ( R.Adjustable t m
                         , R.PostBuild t m
                         , R.MonadHold t m
                         , MonadFix m
                         , Mergeable (WithEmpty f)
                         , FannableC f v
                         , SequenceableWithEventC t f a)
  => R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (Diff f a))
listViewWithKeyMaybe fDyn widget = listViewWithKeyGeneral Empty (NonEmpty <$> fDyn) widget
{-# INLINABLE listViewWithKeyMaybe #-}



listViewWithKeyGeneral ::  ( R.Adjustable t m
                           , R.PostBuild t m
                           , R.MonadHold t m
                           , MonadFix m
                           , Mergeable f
                           , FannableC f v
                           , SequenceableWithEventC t f a)
  => f v -- must be empty
  -> R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (Diff f a))
listViewWithKeyGeneral emptyFV vals mkChild =
  R.switch . R.current . fmap mergeOver <$> listWithKeyGeneral emptyFV vals mkChild
{-# INLINABLE listViewWithKeyGeneral #-}


-- | Display the given collection of items (in key order) using the builder function provided, and update it with the given event.
-- A more efficient version of `listHold`, which can use a widget that handles input updates gracefully, rather than rebuilding.
-- 'Nothing' update entries will delete the corresponding children,
-- and 'Just' entries will create them if they do not exist or send an update event to them if they do.
listWithKeyShallowDiff :: forall t m f v a.( R.Adjustable t m
                                           , MonadFix m
                                           , R.MonadHold t m
                                           , Patchable f -- for the listHold
                                           , FannableC f v
                                           , SequenceableC f a)
  => f v -> R.Event t (Diff f (Maybe v)) -> (Key f -> v -> R.Event t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyShallowDiff initialVals valsChanged mkChild = do
  let editDiffLeavingDeletes' = editDiffLeavingDeletes (Proxy :: Proxy f)
      childValChangedSelector = fanDiffMaybe (Proxy :: Proxy f) valsChanged
  sentValsAsDiffDyn <- R.foldDyn (flip $ updateAsDiff (Proxy :: Proxy f)) (toDiff $ void initialVals) $ fmap (fmap void) valsChanged
  listHoldWithKey initialVals (R.attachWith (flip editDiffLeavingDeletes') (R.current sentValsAsDiffDyn) valsChanged) $ \k v ->
    mkChild k v $ selectCollection (Proxy :: Proxy f) childValChangedSelector k
{-# INLINABLE listWithKeyShallowDiff #-}


listViewWithKeyShallowDiff :: forall t m f v a. ( R.Adjustable t m
                                                , MonadFix m
                                                , R.MonadHold t m
                                                , Patchable f -- for the listHold
                                                , FannableC f v
                                                , Mergeable f
                                                , SequenceableWithEventC t f a
                                                , Monoid (f v))
  => Proxy f -> R.Event t (Diff f (Maybe v)) -> (Key f -> v -> R.Event t v -> m (R.Event t a)) -> m (R.Event t (Diff f a))
listViewWithKeyShallowDiff _ changeVals mkChild =
  R.switch . R.current . fmap mergeOver <$> listWithKeyShallowDiff (mempty :: f v) changeVals mkChild

listViewWithKeyShallowDiffMaybe :: forall t m f v a. ( R.Adjustable t m
                                                     , MonadFix m
                                                     , R.MonadHold t m
                                                     , Patchable f -- for the listHold
                                                     , Mergeable f
                                                     , MapLike (Diff f) -- required for "WithEmpty f" to be Diffable
                                                     , FannableC f v
                                                     , SequenceableWithEventC t f a)
  => Proxy f -> R.Event t (Diff f (Maybe v)) -> (Key f -> v -> R.Event t v -> m (R.Event t a)) -> m (R.Event t (Diff f a))
listViewWithKeyShallowDiffMaybe _ = listViewWithKeyShallowDiffGeneral (Empty :: WithEmpty f v)



listViewWithKeyShallowDiffGeneral :: ( R.Adjustable t m
                                     , MonadFix m
                                     , R.MonadHold t m
                                     , Patchable f -- for the listHold
                                     , FannableC f v
                                     , Mergeable f
                                     , SequenceableWithEventC t f a)
  => f v -> R.Event t (Diff f (Maybe v)) -> (Key f -> v -> R.Event t v -> m (R.Event t a)) -> m (R.Event t (Diff f a))
listViewWithKeyShallowDiffGeneral fv changeVals mkChild =
  R.switch . R.current . fmap mergeOver <$> listWithKeyShallowDiff fv changeVals mkChild


-- | Create a dynamically-changing set of widgets, one of which is selected at any time.
-- This version allows you to add in a selection element so rather than display all widgets
-- you can feed a Dynamic of the Key type and the individual widgets will get a Dynamic Bool input
-- so it can handle whether or not it is currently selected.
selectViewListWithKey :: ( R.Adjustable t m
                         , MonadFix m
                         , R.MonadHold t m
                         , R.PostBuild t m
                         , Foldable f
                         , Mergeable f
                         , Monoid (f v)
                         , FannableC f v
                         , SequenceableWithEventC t f a
                         , Ord (Key f))
  => R.Dynamic t (Key f)          -- ^ Current selection key
  -> R.Dynamic t (f v)      -- ^ Dynamic container of values
  -> (Key f -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -- ^ Function to create a widget for a given key from Dynamic value and Dynamic Bool indicating if this widget is currently selected
  -> m (R.Event t (Diff f a))        -- ^ Event that fires when any child's return Event fires.
selectViewListWithKey  = selectViewListWithKeyGeneral mempty

selectViewListWithKeyMaybe :: ( R.Adjustable t m
                              , MonadFix m
                              , R.MonadHold t m
                              , R.PostBuild t m
                              , Foldable f
                              , Mergeable (WithEmpty f)
                              , FannableC f v
                              , SequenceableWithEventC t f a
                              , Ord (Key f))
  => R.Dynamic t (Key f)          -- ^ Current selection key
  -> R.Dynamic t (f v)      -- ^ Dynamic container of values
  -> (Key f -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -- ^ Function to create a widget for a given key from Dynamic value and Dynamic Bool indicating if this widget is currently selected
  -> m (R.Event t (Diff f a))        -- ^ Event that fires when any child's return Event fires.
selectViewListWithKeyMaybe  keyDyn fDyn widget = selectViewListWithKeyGeneral Empty keyDyn (NonEmpty <$> fDyn) widget

selectViewListWithKeyGeneral :: ( R.Adjustable t m
                                , MonadFix m
                                , R.MonadHold t m
                                , R.PostBuild t m
                                , Foldable f
                                , Mergeable f
                                , FannableC f v
                                , SequenceableWithEventC t f a
                                , Ord (Key f))
  => f v -- ^ empty container
  -> R.Dynamic t (Key f)          -- ^ Current selection key
  -> R.Dynamic t (f v)      -- ^ Dynamic container of values
  -> (Key f -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -- ^ Function to create a widget for a given key from Dynamic value and Dynamic Bool indicating if this widget is currently selected
  -> m (R.Event t (Diff f a))        -- ^ Event that fires when any child's return Event fires.
selectViewListWithKeyGeneral emptyFV selection vals mkChild = do
  let selectionDemux = R.demux selection -- For good performance, this value must be shared across all children
  selectChild <- listWithKeyGeneral emptyFV vals $ \k v -> do
    let selected = R.demuxed selectionDemux k
    selectSelf <- mkChild k v selected
    return selectSelf
  return $ R.switchPromptlyDyn (mergeOver <$> selectChild)
{-# INLINABLE selectViewListWithKey #-}

-- for the case when the widget function produces a (Dynamic t (g a)) and we are using the Maybe variant of these functions
-- I would like to include the widget here so that the types show that the widget must return m (Dynamic t (g a)) but I can't get that to
-- compile
simplifyDynMaybe :: (R.Reflex t, R.MonadHold t m, Distributable f, SequenceableC f b)
  => (v -> b)
  -> (R.Dynamic t (f v) -> m (R.Dynamic t (Maybe (f (R.Dynamic t b)))))
  -> R.Dynamic t (f v)
  -> m (R.Dynamic t (f b))
simplifyDynMaybe toB collectionF fDyn = collectionF fDyn  >>= maybeHelper toB fDyn

maybeHelper :: forall t m f v b. (R.Reflex t, R.MonadHold t m, Distributable f, SequenceableC f b)
  => (v -> b) -> R.Dynamic t (f v) -> R.Dynamic t (Maybe (f (R.Dynamic t b))) -> m (R.Dynamic t (f b))
maybeHelper toGA fDyn dynResult = do
  let y :: R.Dynamic t (Maybe (R.Dynamic t (f b))) = fmap distributeOverDynPure <$> dynResult
      newFGEv :: R.Event t (R.Dynamic t (f b)) = R.fmapMaybe id (R.updated y)
  fmap join $ R.holdDyn (fmap toGA <$> fDyn) newFGEv

type ReflexC1 t m = (R.Adjustable t m, R.MonadHold t m)

-- Not sure if we need these but I think this might do the transitive inlining for these types and I'm not sure the INLINABLE does that
{-# SPECIALIZE listHoldWithKey :: (ReflexC1 t m, Ord k, GCompare (Const2 k a)) => Map k v -> R.Event t (Map k (Maybe v)) -> (k -> v -> m a) -> m (R.Dynamic t (Map k a)) #-}
{-# SPECIALIZE listHoldWithKey :: (ReflexC1 t m, Hashable k, Ord k, GCompare (Const2 k a)) => HashMap k v -> R.Event t (HashMap k (Maybe v)) -> (k -> v -> m a) -> m (R.Dynamic t (HashMap k a)) #-}
{-# SPECIALIZE listHoldWithKey :: ReflexC1 t m => IntMap v -> R.Event t (IntMap (Maybe v)) -> (Int -> v -> m a) -> m (R.Dynamic t (IntMap a)) #-}
{-# SPECIALIZE listHoldWithKey :: ReflexC1 t m => [v] -> R.Event t (IntMap (Maybe v)) -> (Int -> v -> m a) -> m (R.Dynamic t [a]) #-}
{-# SPECIALIZE listHoldWithKey :: ReflexC1 t m => Seq v -> R.Event t (IntMap (Maybe v)) -> (Int -> v -> m a) -> m (R.Dynamic t (Seq a)) #-}
{-# SPECIALIZE listHoldWithKey :: (ReflexC1 t m, Ix k, Enum k, Bounded k) => Array k v -> R.Event t (IntMap (Maybe v)) -> (k -> v -> m a) -> m (R.Dynamic t (Array k a)) #-}
{-# SPECIALIZE listHoldWithKey :: ReflexC1 t m => Tree v -> R.Event t (Map (Seq Int) (Maybe v)) -> (Seq Int -> v -> m a) -> m (R.Dynamic t (Tree a)) #-}

-- These are failing to specialize with a "RULE lhs to complex to desugar" message. :(
{-
type ReflexC2 t m = (ReflexC1 t m, MonadFix m, R.PostBuild t m)
{-# SPECIALIZE listWithKey :: (ReflexC2 t m, Ord k) => R.Dynamic t (Map k v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (Map k a)) #-}
{-# SPECIALIZE listWithKey :: (ReflexC2 t m, Hashable k, Ord k, GCompare (Const2 k a)) => R.Dynamic t (HashMap k v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (HashMap k a)) #-}

{-# SPECIALIZE listWithKey :: ReflexC2 t m => R.Dynamic t (IntMap v) -> (Int -> R.Dynamic t v -> m a) -> m (R.Dynamic t (IntMap a)) #-}
{-# SPECIALIZE listWithKey :: ReflexC2 t m => R.Dynamic t [v] -> (Int -> R.Dynamic t v -> m a) -> m (R.Dynamic t [a]) #-}
{-# SPECIALIZE listWithKey :: ReflexC2 t m => R.Dynamic t (Seq v) -> (Int -> R.Dynamic t v -> m a) -> m (R.Dynamic t (Seq a)) #-}
{-# SPECIALIZE listWithKeyMaybe :: ReflexC2 t m => R.Dynamic t (Tree v) -> (Seq Int -> R.Dynamic t v -> m a) -> m (R.Dynamic t (Maybe (Tree a))) #-}
{-# SPECIALIZE listWithKeyMaybe :: (Enum k, Bounded k, Ix k, ReflexC2 t m) => R.Dynamic t (Array k v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (Maybe (Array k a))) #-}


{-# SPECIALIZE listViewWithKey :: (ReflexC2 t m, Ord k, GCompare (Const2 k a)) => R.Dynamic t (Map k v) -> (k -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (Map k a)) #-}
{-# SPECIALIZE listViewWithKey :: (ReflexC2 t m, Hashable k, Ord k, GCompare (Const2 k a)) => R.Dynamic t (HashMap k v) -> (k -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (HashMap k a)) #-}
{-# SPECIALIZE listViewWithKey :: ReflexC2 t m => R.Dynamic t (IntMap v) -> (Int -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (IntMap a)) #-}
{-# SPECIALIZE listViewWithKey :: ReflexC2 t m => R.Dynamic t [v] -> (Int -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (IntMap a)) #-}
{-# SPECIALIZE listViewWithKey :: ReflexC2 t m => R.Dynamic t (Seq v) -> (Int -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (IntMap a)) #-}


{-# SPECIALIZE listWithKeyShallowDiff :: (ReflexC2 t m, Ord k, GCompare (Const2 k a)) => Map k v -> R.Event t (Map k (Maybe v)) -> (k -> v -> R.Event t v -> m a) -> m (R.Dynamic t (Map k a)) #-}
{-# SPECIALIZE listWithKeyShallowDiff :: (ReflexC2 t m, Ord k, Hashable k, GCompare (Const2 k a)) => HashMap k v -> R.Event t (HashMap k (Maybe v)) -> (k -> v -> R.Event t v -> m a) -> m (R.Dynamic t (HashMap k a)) #-}
{-# SPECIALIZE listWithKeyShallowDiff :: ReflexC2 t m => IntMap v -> R.Event t (IntMap (Maybe v)) -> (Int -> v -> R.Event t v -> m a) -> m (R.Dynamic t (IntMap a)) #-}
{-# SPECIALIZE listWithKeyShallowDiff :: ReflexC2 t m => [v] -> R.Event t (IntMap (Maybe v)) -> (Int -> v -> R.Event t v -> m a) -> m (R.Dynamic t [a]) #-}
{-# SPECIALIZE listWithKeyShallowDiff :: ReflexC2 t m => Seq v -> R.Event t (IntMap (Maybe v)) -> (Int -> v -> R.Event t v -> m a) -> m (R.Dynamic t (Seq a)) #-}
--{-# SPECIALIZE listWithKeyShallowDiff :: ReflexC2 t m => Tree v -> R.Event t (Map (Seq Int) (Maybe v)) -> (Seq Int -> v -> R.Event t v -> m a) -> m (R.Dynamic t (Tree a)) #-}

{-# SPECIALIZE selectViewListWithKey :: (ReflexC2 t m, Ord k, GCompare (Const2 k a)) => R.Dynamic t k -> R.Dynamic t (Map k v) -> (k -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -> m (R.Event t (Map k a)) #-}
{-# SPECIALIZE selectViewListWithKey :: (ReflexC2 t m, Ord k, Hashable k, GCompare (Const2 k a)) => R.Dynamic t k -> R.Dynamic t (HashMap k v) -> (k -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -> m (R.Event t (HashMap k a)) #-}
{-# SPECIALIZE selectViewListWithKey :: ReflexC2 t m => R.Dynamic t Int -> R.Dynamic t (IntMap v) -> (Int -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -> m (R.Event t (IntMap a)) #-}
{-# SPECIALIZE selectViewListWithKey :: ReflexC2 t m => R.Dynamic t Int -> R.Dynamic t [v] -> (Int -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -> m (R.Event t (IntMap a)) #-}
{-# SPECIALIZE selectViewListWithKey :: ReflexC2 t m => R.Dynamic t Int -> R.Dynamic t (Seq v) -> (Int -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -> m (R.Event t (IntMap a)) #-}
-}
