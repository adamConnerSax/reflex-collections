{-# LANGUAGE CPP                   #-}
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
{-# LANGUAGE DefaultSignatures #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.Collections
  (
    Sequenceable(..)
  , KeyMappable (..)
  , ToPatchType(..)
  , toSeqType
  , mergeOver
  , listHoldWithKeyGeneral
  , HasFan(..)
  , HasEmpty(..)
  , Diffable(..)
  , listWithKeyGeneral
  , sampledListWithKey
  , listWithKeyShallowDiffGeneral
  , ToElemList(..)
  , selectViewListWithKeyGeneral
  , listViewWithKeyGeneral'
  , listWithKeyGeneral'
  , hasEmptyDiffableDynamicToInitialPlusKeyDiffEvent
  , sampledDiffableDynamicToInitialPlusKeyDiffEvent -- Use with caution!! May cause problems in recursive contexts
  ) where


import Reflex.Collections.Sequenceable (SequenceablePatch(..), ReflexSequenceable(..))
import Reflex.Collections.KeyMappable (KeyMappable(..))
import Reflex.Collections.ToPatchType (ToPatchType(..), toSeqType, distributeOverDynPure, mergeOver)
import Reflex.Collections.Diffable (HasEmpty(..), Diffable(..), toDiff)

import qualified Reflex                 as R

import           Data.Dependent.Map     (DMap, GCompare)
import           Data.Functor.Compose   (Compose (Compose, getCompose))
import           Data.Functor.Misc      (Const2 (..))
import           Reflex.Patch           (PatchDMap (..))


import           Control.Monad.Fix      (MonadFix)
import           Control.Monad.Identity (Identity (..), void)

import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)


-- | Sequenceable and ToPatch are enough for listHoldWithKey
-- listHoldWithKey is an efficient collection management function if your input is a static initial state and events of updates.
-- If your input is a Dynamic structure than you need the ability to take Diffs and to bootstrap a starting point from the dynamic input.
-- That 2nd point would be simpler if you could sample.
-- NB: incrementalToDynamic applies the patch to the original so the Diff type here
-- (or, really, whatever makePatchSeq turns it into), must be consistent.
listHoldWithKeyGeneral :: forall t m f k v a. ( R.Adjustable t m
                                              , R.MonadHold t m
                                              , ToPatchType f k v a
                                              , SequenceablePatch (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k a))
  => f v -> R.Event t (Diff f k v) -> (k->v-> m a) -> m (R.Dynamic t (f a))
listHoldWithKeyGeneral c0 c' h = do
  let pf = Proxy :: Proxy f
      pk = Proxy :: Proxy k
      pv = Proxy :: Proxy v
      makePatchSeq' = makePatchSeq pf
      fromSeqType' = fromSeqType pk pv
      dc0 = toSeqTypeWithFunctor h c0
      dc' = fmap (makePatchSeq' h) c'
  (a0,a') <- sequenceWithPatch dc0 dc'
  fmap fromSeqType' <$> patchPairToDynamic a0 a'


-- These are all generalized over a function "(R.Dynamic t (f v) -> m (f v, R.Event t (Diff f k v)))"
-- for the listWithKey and listWithKeyShallow diff we need to be able to fan events
listWithKeyGeneral' :: forall t m f k v a. ( R.Adjustable t m
                                           , R.PostBuild t m
                                           , R.MonadHold t m
                                           , ToPatchType f k v a
                                           , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k a)
                                           , HasFan f v
                                           , FanInKey f ~ k)
                    => (R.Dynamic t (f v) -> m (f v, R.Event t (Diff f k v)))
                    -> R.Dynamic t (f v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyGeneral' toInitialPlusKeyDiffEvent vals mkChild = do
  let doFan' = doFan (Proxy :: Proxy v)
      makeSelKey' = makeSelKey (Proxy :: Proxy f) (Proxy :: Proxy v)
      childValChangedSelector = doFan' $ R.updated vals
  (fv0, edfv) <- toInitialPlusKeyDiffEvent vals
  listHoldWithKeyGeneral fv0 edfv $ \k v ->
    mkChild k =<< R.holdDyn v (R.select childValChangedSelector $ makeSelKey' k)



-- | Generalizes "listViewWithKey" which is a special case of listWithKey for Events.  The extra constraints are needed because
-- this uses all the machinery of sequencing (DMaps) twice: once for the inner listWithKey and then again for the merging of events.
listViewWithKeyGeneral' ::  forall t m f k v a. ( R.Adjustable t m
                                                , R.PostBuild t m
                                                , R.MonadHold t m
                                                , ToPatchType f k v (R.Event t a)
                                                , ToPatchType f k (R.Event t a) a
                                                , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k (R.Event t a))
                                                , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k a)
                                                , ReflexTraversable ((SeqType f k) (SeqTypeKey f k a))
                                                , HasFan f v
                                                , FanInKey f ~ k)
  => (R.Dynamic t (f v) -> m (f v, R.Event t (Diff f k v)))
  -> R.Dynamic t (f v) -> (k -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (f a))
listViewWithKeyGeneral' toEv vals mkChild =
  R.switch . R.current . fmap (mergeOver (Proxy :: Proxy k)) <$> listWithKeyGeneral' toEv vals mkChild


-- If we have an empty state and can take diffs, we can use that to make a Dynamic into a initial empty plus diff events
hasEmptyDiffableDynamicToInitialPlusKeyDiffEvent :: forall t m f df v. ( Diffable f df
                                                                       , HasEmpty (f v)
                                                                       , R.PostBuild t m
                                                                       , MonadFix m
                                                                       , R.MonadHold t m)
  => R.Dynamic t (f v)
  -> m (f v, R.Event t (df v))
hasEmptyDiffableDynamicToInitialPlusKeyDiffEvent vals = mdo
  postBuild <- R.getPostBuild
  let emptyContainer' = empty
  sentVals :: R.Dynamic t (f v) <- R.foldDyn applyDiff emptyContainer' changeVals
  let changeVals :: R.Event t (df v)
      changeVals = R.attachWith diffOnlyKeyChanges (R.current sentVals) $ R.leftmost
                   [ R.updated vals
                   , R.tag (R.current vals) postBuild
                   ] --TODO: This should probably be added to the attachWith, not to the updated; if we were using diffMap instead of diffMapNoEq, I think it might not work
  return $ (emptyContainer', changeVals)



hasEmptyListWithKey :: forall t m f k v a. ( R.Adjustable t m
                                           , R.PostBuild t m
                                           , MonadFix m
                                           , R.MonadHold t m
                                           , ToPatchType f k v a -- for the listHold
                                           , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k a) -- for the listHold
                                           , Diffable f (Diff f k)
                                           , HasEmpty (f v)
                                           , Functor (Diff f k)
                                           , HasFan f v
                                           , FanInKey f ~ k)
  => R.Dynamic t (f v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
hasEmptyListWithKey vals mkChild = listWithKeyGeneral' hasEmptyDiffableDynamicToInitialPlusKeyDiffEvent vals mkChild



-- | Create a dynamically-changing set of Event-valued widgets.
listWithKeyGeneral :: forall t m f k v a. ( R.Adjustable t m
                                          , R.PostBuild t m
                                          , MonadFix m
                                          , R.MonadHold t m
                                          , ToPatchType f k v a -- for the listHold
                                          , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k a) -- for the listHold
                                          , Diffable f (Diff f k)
                                          , HasEmpty (f v)
                                          , Functor (Diff f k)
                                          , HasFan f v
                                          , FanInKey f ~ k)
  => R.Dynamic t (f v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyGeneral = hasEmptyListWithKey

-- | Display the given map of items (in key order) using the builder function provided, and update it with the given event.
-- | 'Nothing' update entries will delete the corresponding children, and 'Just' entries will create them if they do not exist or send an update event to them if they do.
listWithKeyShallowDiffGeneral :: forall t m f k v a.( R.Adjustable t m
                                                    , MonadFix m
                                                    , R.MonadHold t m
                                                    , ToPatchType f k v a -- for the listHold
                                                    , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k a) -- for the listHold
                                                    , Diffable f (Diff f k)
                                                    , HasEmpty (f ())
                                                    , Functor (Diff f k)
                                                    , HasFan (Diff f k) v
                                                    , FanInKey (Diff f k) ~ k)
  => f v -> R.Event t (Diff f k v) -> (k -> v -> R.Event t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyShallowDiffGeneral initialVals valsChanged mkChild = do
  let makeSelKey' = makeSelKey (Proxy :: Proxy (Diff f k)) (Proxy :: Proxy v)
      doFan' = doFan (Proxy :: Proxy v)
      emptyContainer' :: f ()
      emptyContainer' = empty
      editDiffLeavingDeletes' = editDiffLeavingDeletes (Proxy :: Proxy f)
      childValChangedSelector = doFan' valsChanged
  sentVals <- R.foldDyn applyDiff emptyContainer' $ fmap void valsChanged
  listHoldWithKeyGeneral initialVals (R.attachWith (flip editDiffLeavingDeletes') (R.current (toDiff <$> sentVals)) valsChanged) $ \k v ->
    mkChild k v $ R.select childValChangedSelector $ makeSelKey' k


-- | Create a dynamically-changing set of widgets, one of which is selected at any time.
selectViewListWithKeyGeneral :: forall t m f k v a. ( R.Adjustable t m
                                                    , MonadFix m
                                                    , R.MonadHold t m
                                                    , R.PostBuild t m
                                                    , ToElemList f
                                                    , ToPatchType f k v (R.Event t (k,a)) -- for the listHold
                                                    , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k (R.Event t (k,a))) -- for the listHold
                                                    , Diffable f (Diff f k) -- for the listWithKeyGeneral
                                                    , HasEmpty (f v)
                                                    , Functor (Diff f k)
                                                    , HasFan f v
                                                    , FanInKey f ~ k
                                                    , Ord k)
  => R.Dynamic t k          -- ^ Current selection key
  -> R.Dynamic t (f v)      -- ^ Dynamic container of values
  -> (k -> R.Dynamic t v -> R.Dynamic t Bool -> m (R.Event t a)) -- ^ Function to create a widget for a given key from Dynamic value and Dynamic Bool indicating if this widget is currently selected
  -> m (R.Event t (k, a))        -- ^ Event that fires when any child's return Event fires.  Contains key of an arbitrary firing widget.
selectViewListWithKeyGeneral selection vals mkChild = do
  let selectionDemux = R.demux selection -- For good performance, this value must be shared across all children
  selectChild <- listWithKeyGeneral vals $ \k v -> do
    let selected = R.demuxed selectionDemux k
    selectSelf <- mkChild k v selected
    return $ fmap ((,) k) selectSelf
  return $ R.switchPromptlyDyn $ R.leftmost . toElemList <$> selectChild


-- if we don't have an empty state (e.g., Array k v), we can sample but this is..not ideal.
sampledDiffableDynamicToInitialPlusKeyDiffEvent :: forall t m f df v. ( R.Reflex t
                                                                      , Diffable f df
                                                                      , MonadFix m
                                                                      , R.MonadHold t m)
  => R.Dynamic t (f v)
  -> m (f v, R.Event t (df v))
sampledDiffableDynamicToInitialPlusKeyDiffEvent vals = do
  v0 <- R.sample . R.current $ vals
  rec sentVals :: R.Dynamic t (f v) <- R.foldDyn applyDiff v0 changeVals
      let changeVals :: R.Event t (df v)
          changeVals = R.attachWith diffOnlyKeyChanges (R.current sentVals) $ R.updated vals
  return $ (v0, changeVals)


-- NB: This only works in non-recursive widgets.  But that may be enough.
-- But that may be a fit with something like "(Enum k, Bounded k) => k -> v", which has no empty state.
sampledListWithKey :: forall t m f k v a. ( R.Adjustable t m
                                          , R.PostBuild t m
                                          , MonadFix m
                                          , R.MonadHold t m
                                          , ToPatchType f k v a -- for the listHold
                                          , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k a) -- for the listHold
                                          , Diffable f (Diff f k)
                                          , Functor (Diff f k)
                                          , HasFan f v
                                          , FanInKey f ~ k)
  => R.Dynamic t (f v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
sampledListWithKey vals mkChild = listWithKeyGeneral' sampledDiffableDynamicToInitialPlusKeyDiffEvent vals mkChild




-- Old Code
{-
-- | Create a dynamically-changing set of Event-valued widgets.
listWithKeyGeneral :: forall t m f k v a. ( R.Adjustable t m
                                          , R.PostBuild t m
                                          , MonadFix m
                                          , R.MonadHold t m
                                          , ToPatchType f k v a -- for the listHold
                                          , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k a) -- for the listHold
                                          , Diffable f (Diff f k)
                                          , Functor (Diff f k)
                                          , HasFan f v
                                          , FanInKey f ~ k)
  => R.Dynamic t (f v) -> (k -> R.Dynamic t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyGeneral vals mkChild = do
  postBuild <- R.getPostBuild
  let doFan' = doFan (Proxy :: Proxy v)
      makeSelKey' = makeSelKey (Proxy :: Proxy f) (Proxy :: Proxy v)
      emptyContainer' :: f v = emptyContainer (Proxy :: Proxy (Diff f k))

      childValChangedSelector = doFan' $ R.updated vals
  rec sentVals :: R.Dynamic t (f v) <- R.foldDyn applyDiff emptyContainer' changeVals
      let changeVals :: R.Event t (Diff f k v)
          changeVals = R.attachWith diffOnlyKeyChanges (R.current sentVals) $ R.leftmost
                         [ R.updated vals
                         , R.tag (R.current vals) postBuild --TODO: This should probably be added to the attachWith, not to the updated; if we were using diffMap instead of diffMapNoEq, I think it might not work
                         ]
  listHoldWithKeyGeneral emptyContainer' changeVals $ \k v ->
    mkChild k =<< R.holdDyn v (R.select childValChangedSelector $ makeSelKey' k)
-}
