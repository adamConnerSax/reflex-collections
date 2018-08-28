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
-- including HashMap, IntMap, [], Sequence.Seq and Array.
-- The Array case is special, and will only work for arrays that have values for every possible key,
-- representing a sort of total function from the key type (usually a bounded enumeration) to the contained type.
--
-- This package also provides typeclasses and typefamilies that should make adding support for a new collection type fairly
-- straightforward.
--
-- Because the operations are related, we also provide generalized versions of Reflex's `distributeMapOverDynPure` and `mergeMap`
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
  , list
  , listViewWithKey
  , listWithKeyShallowDiff
  , selectViewListWithKey
  , sampledListWithKey -- CAUTION!! Do not use in recursive context.
  , mergeOver
  , distributeOverDynPure
  ) where


import           Reflex.Collections.Diffable        (Diffable (..), applyDiff,
                                                     diffOnlyKeyChanges,
                                                     editDiffLeavingDeletes)
import           Reflex.Collections.KeyedCollection (KeyedCollection (..))
import           Reflex.Collections.Sequenceable    (PatchSequenceable (..),
                                                     ReflexMergeable (..))
import           Reflex.Collections.ToPatchType     (SeqTypes (..),
                                                     ToPatchType (..),
                                                     distributeOverDynPure,
                                                     functorMappedToSeqType,
                                                     mergeOver)

import qualified Reflex                             as R

import           Control.Monad                      (void)
import           Control.Monad.Fix                  (MonadFix)
import           Data.Dependent.Map                 (GCompare)
import           Data.Foldable                      (Foldable, toList)
import           Data.Proxy                         (Proxy (..))

-- for specializtions
import           Data.Array                         (Array, Ix)
import           Data.Hashable                      (Hashable)
import           Data.HashMap.Strict                (HashMap)
import           Data.IntMap                        (IntMap)
import           Data.Map                           (Map)
import           Data.Sequence                      (Seq)

-- If we only want to support ghc8+, we could replace proxies with type application.

-- NB: This also implies Diffable f (and thus KeyedCollection f, KeyedCollection (Diff f), MapLike (Diff f)) since Diffable is a superclasses of ToPatchType
type PatchSeqC f a = (SeqTypes f a, PatchSequenceable (SeqType f a) (SeqPatchType f a), ToPatchType f)


-- | listHoldWithKey is an efficient collection management function when your input is a *static* initial state and an event stream of updates.
-- This version uses a widget that expects a static input and thus the widget will need to be rebuilt if the incoming
-- event changes the value of v for a given k.  What this function does provide is efficient routing of each event to the specific
-- widget that has changed, thus rebuilding only the widgets that have changing inputs.
-- NB: use of unsafeFromSeqType is okay here.  We are updating an initial container which has values for all keys if required.
listHoldWithKey :: forall t m f v a. ( R.Adjustable t m
                                     , R.MonadHold t m
                                     , PatchSeqC f a)
  => f v -> R.Event t (Diff f (Maybe v)) -> (Key f -> v -> m a) -> m (R.Dynamic t (f a))
listHoldWithKey c0 c' h = do
  let pf = Proxy :: Proxy f
      makePatchSeq' = makePatchSeq pf
      dc0 = functorMappedToSeqType h c0
      dc' = fmap (makePatchSeq' h) c'
  (a0 ,a') <- sequenceWithPatch dc0 dc'
  fmap unsafeFromSeqType <$> patchPairToDynamic a0 a'
{-# INLINABLE listHoldWithKey #-}

-- | listWithKey handles the case where your input collection is dynamic.  In this case your widget has to handle dynamic inputs.
-- and thus the widget can update without rebuilding when the input value changes.
listWithKey :: ( R.Adjustable t m
               , R.PostBuild t m
               , MonadFix m
               , R.MonadHold t m
               , PatchSeqC f a  -- for the listHold
               , Monoid (f v)
               , Functor (Diff f)
               , GCompare (FanKey f v))
  => R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
listWithKey = listWithKey' hasEmptyDiffableDynamicToInitialPlusKeyDiffEvent
{-# INLINABLE listWithKey #-}

listWithKey' :: forall t m f v a. ( R.Adjustable t m
                                  , R.PostBuild t m
                                  , R.MonadHold t m
                                  , PatchSeqC f a
                                  , GCompare (FanKey f v))
  => (R.Dynamic t (f v) -> m (f v, R.Event t (Diff f (Maybe v))))
  -> R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
listWithKey' toInitialPlusKeyDiffEvent vals mkChild = do
  let doFan' = doFan
      makeFanKey' = makeFanKey (Proxy :: Proxy f) (Proxy :: Proxy v)
      childValChangedSelector = doFan' $ R.updated vals
  (fv0, edfv) <- toInitialPlusKeyDiffEvent vals
  listHoldWithKey fv0 edfv $ \k v ->
    mkChild k =<< R.holdDyn v (R.select childValChangedSelector $ makeFanKey' k)
{-# INLINABLE listWithKey' #-}

-- | Create a dynamically-changing set of Event-valued widgets. In this case, ones that are indifferent to position
list :: ( R.Adjustable t m
        , R.PostBuild t m
        , MonadFix m
        , R.MonadHold t m
        , PatchSeqC f a  -- for the listHold
        , Monoid (f v)
        , Functor (Diff f)
        , GCompare (FanKey f v))
  => R.Dynamic t (f v) -> (R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
list df mkChild = listWithKey df (\_ dv -> mkChild dv)
{-# INLINABLE list #-}

-- | `listViewWithKey` is a special case of listWithKey for widgets which return Events (which can then be merged to return a smaller structure).
-- NB: This returns Event t (Diff f a) since we can't a-priori, know that we can construct `f a` from `Diff f a`.  Though for maps and lists we can.
-- But for total containers, e.g., Array k, we cannot since we will get events on only some keys but an Array k must have a value for all keys.
listViewWithKey ::  ( R.Adjustable t m
                    , R.PostBuild t m
                    , R.MonadHold t m
                    , MonadFix m
                    , PatchSeqC f a
                    , PatchSeqC f (R.Event t a)
                    , ReflexMergeable (SeqType f a)
                    , Monoid (f v)
                    , GCompare (FanKey f v))
  => R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (Diff f a))
listViewWithKey = listViewWithKey' hasEmptyDiffableDynamicToInitialPlusKeyDiffEvent
{-# INLINABLE listViewWithKey #-}

listViewWithKey' ::  ( R.Adjustable t m
                     , R.PostBuild t m
                     , R.MonadHold t m
                     , PatchSeqC f a
                     , PatchSeqC f (R.Event t a)
                     , ReflexMergeable (SeqType f a)
                     , GCompare (FanKey f v))
  => (R.Dynamic t (f v) -> m (f v, R.Event t (Diff f (Maybe v))))
  -> R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (Diff f a))
listViewWithKey' toEv vals mkChild =
  R.switch . R.current . fmap mergeOver <$> listWithKey' toEv vals mkChild
{-# INLINABLE listViewWithKey' #-}


-- | Display the given collection of items (in key order) using the builder function provided, and update it with the given event.
-- A more efficient version of `listHold`, which can use a widget that handles input updates gracefully, rather than rebuilding.
-- 'Nothing' update entries will delete the corresponding children,
-- and 'Just' entries will create them if they do not exist or send an update event to them if they do.
listWithKeyShallowDiff :: forall t m f v a.( R.Adjustable t m
                                           , MonadFix m
                                           , R.MonadHold t m
                                           , PatchSeqC f a -- for the listHold
                                           , Monoid (f ())
                                           , Functor (Diff f)
                                           , GCompare (FanKey f v))
  => f v -> R.Event t (Diff f (Maybe v)) -> (Key f -> v -> R.Event t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyShallowDiff initialVals valsChanged mkChild = do
  let makeFanKey' = makeFanKey (Proxy :: Proxy f) (Proxy :: Proxy v)
      fanDiff' = doDiffFan (Proxy :: Proxy f)
      editDiffLeavingDeletes' = editDiffLeavingDeletes (Proxy :: Proxy f)
      childValChangedSelector = fanDiff' valsChanged
  sentVals <- R.foldDyn applyDiff (void initialVals) $ fmap (fmap void) valsChanged
  listHoldWithKey initialVals (R.attachWith (flip editDiffLeavingDeletes') (toDiff <$> R.current sentVals) valsChanged) $ \k v ->
    mkChild k v $ R.select childValChangedSelector $ makeFanKey' k
{-# INLINABLE listWithKeyShallowDiff #-}

-- | Create a dynamically-changing set of widgets, one of which is selected at any time.
-- This version allows you to add in a selection element so rather than display all widgets
-- you can feed a Dynamic of the Key type and the individual widgets will get a Dynamic Bool input
-- so it can handle whether or not it is currently selected.
selectViewListWithKey :: ( R.Adjustable t m
                         , MonadFix m
                         , R.MonadHold t m
                         , R.PostBuild t m
                         , Foldable f -- for toList
                         , PatchSeqC f a -- for the listHold
                         , PatchSeqC f (R.Event t (Key f, a)) -- for the listHold
                         , Monoid (f v)
                         , Functor (Diff f)
                         , GCompare (FanKey f v)
                         , Ord (Key f))
  => R.Dynamic t (Key f)          -- ^ Current selection key
  -> R.Dynamic t (f v)      -- ^ Dynamic container of values
  -> (Key f -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -- ^ Function to create a widget for a given key from Dynamic value and Dynamic Bool indicating if this widget is currently selected
  -> m (R.Event t (Key f, a))        -- ^ Event that fires when any child's return Event fires.  Contains key of an arbitrary firing widget.
selectViewListWithKey selection vals mkChild = do
  let selectionDemux = R.demux selection -- For good performance, this value must be shared across all children
  selectChild <- listWithKey vals $ \k v -> do
    let selected = R.demuxed selectionDemux k
    selectSelf <- mkChild k v selected
    return $ fmap ((,) k) selectSelf
  return $ R.switchPromptlyDyn $ R.leftmost . toList <$> selectChild
{-# INLINABLE selectViewListWithKey #-}

-- If we have an empty state and can take diffs, we can use that to make a Dynamic into a initial empty plus diff events
hasEmptyDiffableDynamicToInitialPlusKeyDiffEvent :: forall t m f v. ( Diffable f
                                                                    , Monoid (f v)
                                                                    , R.PostBuild t m
                                                                    , MonadFix m
                                                                    , R.MonadHold t m)
  => R.Dynamic t (f v) -> m (f v, R.Event t (Diff f (Maybe v)))
hasEmptyDiffableDynamicToInitialPlusKeyDiffEvent vals = mdo
  postBuild <- R.getPostBuild
  let emptyContainer' = mempty
  sentVals :: R.Dynamic t (f v) <- R.foldDyn applyDiff emptyContainer' changeVals
  let changeVals :: R.Event t (Diff f (Maybe v))
      changeVals = R.attachWith diffOnlyKeyChanges (R.current sentVals) $ R.leftmost
                   [ R.updated vals
                   , R.tag (R.current vals) postBuild
                   ] --TODO: This should probably be added to the attachWith, not to the updated; if we were using diffMap instead of diffMapNoEq, I think it might not work
  return (emptyContainer', changeVals)
{-# INLINABLE hasEmptyDiffableDynamicToInitialPlusKeyDiffEvent #-}

-- if we don't have an empty state (e.g., Array k v), we can sample but this is..not ideal.
sampledDiffableDynamicToInitialPlusKeyDiffEvent :: forall t m f v. ( R.Reflex t
                                                                   , Diffable f
                                                                   , MonadFix m
                                                                   , R.MonadHold t m)
  => R.Dynamic t (f v) -> m (f v, R.Event t (Diff f (Maybe v)))
sampledDiffableDynamicToInitialPlusKeyDiffEvent vals = do
  v0 <- R.sample . R.current $ vals
  rec sentVals :: R.Dynamic t (f v) <- R.foldDyn applyDiff v0 changeVals
      let changeVals :: R.Event t (Diff f (Maybe v))
          changeVals = R.attachWith diffOnlyKeyChanges (R.current sentVals) $ R.updated vals
  return (v0, changeVals)
{-# INLINABLE sampledDiffableDynamicToInitialPlusKeyDiffEvent #-}

-- NB: This only works in non-recursive widgets.  But that may be enough.
-- But that may be a fit with something like "(Enum k, Bounded k) => k -> v", which has no empty state.
sampledListWithKey :: ( R.Adjustable t m
                      , R.PostBuild t m
                      , MonadFix m
                      , R.MonadHold t m
                      , PatchSeqC f a -- for the listHold
                      , Functor (Diff f)
                      , GCompare (FanKey f v))
  => R.Dynamic t (f v) -> (Key f -> R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
sampledListWithKey = listWithKey' sampledDiffableDynamicToInitialPlusKeyDiffEvent
{-# INLINABLE sampledListWithKey #-}

type ReflexC1 t m = (R.Adjustable t m, R.MonadHold t m)
type ReflexC2 t m = (ReflexC1 t m, MonadFix m, R.PostBuild t m)

-- Not sure if we need these but I think this might do the transitive inlining for at these types and I'm not sure the INLINABLE does that

{-# SPECIALIZE listHoldWithKey :: (ReflexC1 t m, Ord k) => Map k v -> R.Event t (Map k (Maybe v)) -> (k -> v -> m a) -> m (R.Dynamic t (Map k a)) #-}
{-# SPECIALIZE listHoldWithKey :: (ReflexC1 t m, Hashable k, Ord k) => HashMap k v -> R.Event t (HashMap k (Maybe v)) -> (k -> v -> m a) -> m (R.Dynamic t (HashMap k a)) #-}
{-# SPECIALIZE listHoldWithKey :: ReflexC1 t m => IntMap v -> R.Event t (IntMap (Maybe v)) -> (Int -> v -> m a) -> m (R.Dynamic t (IntMap a)) #-}
{-# SPECIALIZE listHoldWithKey :: ReflexC1 t m => [v] -> R.Event t (IntMap (Maybe v)) -> (Int -> v -> m a) -> m (R.Dynamic t [a]) #-}
{-# SPECIALIZE listHoldWithKey :: ReflexC1 t m => Seq v -> R.Event t (IntMap (Maybe v)) -> (Int -> v -> m a) -> m (R.Dynamic t (Seq a)) #-}
{-# SPECIALIZE listHoldWithKey :: (ReflexC1 t m, Ix k, Enum k, Bounded k) => Array k v -> R.Event t (IntMap (Maybe v)) -> (k -> v -> m a) -> m (R.Dynamic t (Array k a)) #-}

{-# SPECIALIZE listWithKey :: (ReflexC2 t m, Ord k) => R.Dynamic t (Map k v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (Map k a)) #-}
{-# SPECIALIZE listWithKey :: (ReflexC2 t m, Hashable k, Ord k) => R.Dynamic t (HashMap k v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (HashMap k a)) #-}
{-# SPECIALIZE listWithKey :: ReflexC2 t m => R.Dynamic t (IntMap v) -> (Int -> R.Dynamic t v -> m a) -> m (R.Dynamic t (IntMap a)) #-}
{-# SPECIALIZE listWithKey :: ReflexC2 t m => R.Dynamic t [v] -> (Int -> R.Dynamic t v -> m a) -> m (R.Dynamic t [a]) #-}
{-# SPECIALIZE listWithKey :: ReflexC2 t m => R.Dynamic t (Seq v) -> (Int -> R.Dynamic t v -> m a) -> m (R.Dynamic t (Seq a)) #-}

{-# SPECIALIZE listViewWithKey :: (ReflexC2 t m, Ord k) => R.Dynamic t (Map k v) -> (k -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (Map k a)) #-}
{-# SPECIALIZE listViewWithKey :: (ReflexC2 t m, Hashable k, Ord k) => R.Dynamic t (HashMap k v) -> (k -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (HashMap k a)) #-}
{-# SPECIALIZE listViewWithKey :: ReflexC2 t m => R.Dynamic t (IntMap v) -> (Int -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (IntMap a)) #-}
{-# SPECIALIZE listViewWithKey :: ReflexC2 t m => R.Dynamic t [v] -> (Int -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (IntMap a)) #-}
{-# SPECIALIZE listViewWithKey :: ReflexC2 t m => R.Dynamic t (Seq v) -> (Int -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (IntMap a)) #-}

{-# SPECIALIZE listWithKeyShallowDiff :: (ReflexC2 t m, Ord k) => Map k v -> R.Event t (Map k (Maybe v)) -> (k -> v -> R.Event t v -> m a) -> m (R.Dynamic t (Map k a)) #-}
{-# SPECIALIZE listWithKeyShallowDiff :: (ReflexC2 t m, Ord k, Hashable k) => HashMap k v -> R.Event t (HashMap k (Maybe v)) -> (k -> v -> R.Event t v -> m a) -> m (R.Dynamic t (HashMap k a)) #-}
{-# SPECIALIZE listWithKeyShallowDiff :: ReflexC2 t m => IntMap v -> R.Event t (IntMap (Maybe v)) -> (Int -> v -> R.Event t v -> m a) -> m (R.Dynamic t (IntMap a)) #-}
{-# SPECIALIZE listWithKeyShallowDiff :: ReflexC2 t m => [v] -> R.Event t (IntMap (Maybe v)) -> (Int -> v -> R.Event t v -> m a) -> m (R.Dynamic t [a]) #-}
{-# SPECIALIZE listWithKeyShallowDiff :: ReflexC2 t m => Seq v -> R.Event t (IntMap (Maybe v)) -> (Int -> v -> R.Event t v -> m a) -> m (R.Dynamic t (Seq a)) #-}

{-# SPECIALIZE selectViewListWithKey :: (ReflexC2 t m, Ord k) => R.Dynamic t k -> R.Dynamic t (Map k v) -> (k -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -> m (R.Event t (k, a)) #-}
{-# SPECIALIZE selectViewListWithKey :: (ReflexC2 t m, Ord k, Hashable k) => R.Dynamic t k -> R.Dynamic t (HashMap k v) -> (k -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -> m (R.Event t (k, a)) #-}
{-# SPECIALIZE selectViewListWithKey :: ReflexC2 t m => R.Dynamic t Int -> R.Dynamic t (IntMap v) -> (Int -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -> m (R.Event t (Int, a)) #-}
{-# SPECIALIZE selectViewListWithKey :: ReflexC2 t m => R.Dynamic t Int -> R.Dynamic t [v] -> (Int -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -> m (R.Event t (Int, a)) #-}
{-# SPECIALIZE selectViewListWithKey :: ReflexC2 t m => R.Dynamic t Int -> R.Dynamic t (Seq v) -> (Int -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -> m (R.Event t (Int, a)) #-}
