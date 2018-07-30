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
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.Core
  (
    Sequenceable(..)
  , ToPatchType(..)
  , listHoldWithKeyGeneral
  , HasFan(..)
  , Diffable(..)
  , listWithKeyGeneral
  , listWithKeyShallowDiffGeneral
  , ToElemList(..)
  , selectViewListWithKeyGeneral
  ) where

import qualified Reflex                 as R

import           Data.Dependent.Map     (DMap, GCompare)
import           Data.Functor.Compose   (Compose (Compose, getCompose))
import           Data.Functor.Misc      (Const2 (..))
import           Reflex.Patch           (PatchDMap (..))


import           Control.Monad.Fix      (MonadFix)
import           Control.Monad.Identity (Identity (..), void)

import           Data.Proxy             (Proxy (..))


-- | This class carries the ability to do an efficient event merge
-- "Merge a collection of events.  The resulting event will occur if at least one input event is occuring
-- and will contain all simultaneously occurring events
class Mergeable (dk :: (* -> *) -> *) where
  mergeEvents :: R.Reflex t => dk (R.Event t) -> R.Event t (dk Identity)

instance GCompare k => Mergeable (DMap k) where
  mergeEvents = R.merge

-- | This class carries the ability to sequence patches in the way of MonadAdjust And then turn the result into a Dynamic.
-- sequenceWithPatch takes a static d containing adjustable (m a), e.g., widgets, and event carrying patches, that is
-- new widgets for some keys k, and "pulls out" (sequences) the m.
-- patchPairToDynamic is a sort of inverse, turning a static d containing values and events with patches to it, new values at some keys,
-- and returns an adjustable monad containing a Dynamic of a value containing d.
-- |
class ( R.Patch (pd k Identity)
      , R.PatchTarget (pd k Identity) ~ d k Identity) => Sequenceable (d :: (* -> *) -> (* -> *) -> *) (pd :: (* -> *) -> (* -> *) -> *)  (k :: * -> *) where
  sequenceWithPatch :: R.Adjustable t m => d k m -> R.Event t (pd k m) -> m (d k Identity, R.Event t (pd k Identity))
  patchPairToDynamic :: (R.MonadHold t m, R.Reflex t) =>d k Identity -> R.Event t (pd k Identity) -> m (R.Dynamic t (d k Identity))

-- | DMaps are our prime example of something sequenceable
instance (GCompare (Const2 k a), Ord k) => Sequenceable DMap PatchDMap (Const2 k a) where
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


-- This class has the capabilities to translate f v and its difftype into types that are sequenceable, and then bring the original type back
-- This requires that the Diff type be mapped to the correct type for diffing at the sequenceable level (e.g., as a DMap).
class ToPatchType (f :: * -> *) k v a where
  type Diff f k :: * -> *
  type SeqType  f k :: (* -> *) -> (* -> *) -> *
  type SeqPatchType f k :: (* -> *) -> (* -> *) -> *
  type SeqTypeKey f k a :: * -> *
  toSeqTypeWithFunctor :: Functor g => (k -> v -> g a) -> f v -> SeqType f k (SeqTypeKey f k a) g
  makePatchSeq :: Functor g => Proxy f -> (k -> v -> g a) -> Diff f k v -> SeqPatchType f k (SeqTypeKey f k a) g
  fromSeqType :: Proxy k -> Proxy v -> SeqType f k (SeqTypeKey f k a) Identity -> f a

{-
mergeOverWithKey :: ( ToPatchType f k v v
             , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k v)
             , Mergeable ((SeqType f k) (SeqTypeKey f k v)))
  => (k -> v -> R.Event t v) -> f (R.Event t v) -> R.Event t (f v)
mergeOverWithKey g = fmap (fromSeqType (Proxy :: Proxy k) (Proxy :: Proxy (R.Event t v))) . R.merge . toSeqTypeWithFunctor g
-}


-- | Sequenceable and ToPatch are enough for listHoldWithKey
-- listHoldWithKey is an efficient collection management function if your input is a static initial state and events of updates.
-- If your input is a Dynamic structure than you need the ability to take Diffs and to bootstrap a starting point from the dynamic input.
-- That 2nd point would be simpler if you could sample.
-- NB: incrementalToDynamic applies the patch to the original so the Diff type here (or, really, whatever makePatchSeq turns it into, must be consistent).
listHoldWithKeyGeneral::forall t m f k v a. ( R.Adjustable t m, R.MonadHold t m
                                            , ToPatchType f k v a
                                            , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k a))
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

-- for the listWithKey and listWithKeyShallow diff we need to be able to fan events and the ability to take and apply diffs on the original container
-- We also need to be able to produce an empty container to bootstrap the initial value.  Couldn't we sample?

-- This class encapsuates the types and functionality required to use "fan"
class HasFan (f :: * -> *) v where
  type FanInKey f :: *
  type FanSelKey f v :: * -> *
  makeSelKey :: Proxy f -> Proxy v -> FanInKey f -> FanSelKey f v v
  doFan :: R.Reflex t => Proxy v -> R.Event t (f v) -> R.EventSelector t (FanSelKey f v)


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

{-
listViewWithKeyGeneral' ::  forall t m f k v a. ( R.Adjustable t m
                                                , R.PostBuild t m
                                                , R.MonadHold t m
                                                , ToPatchType f k v a
                                                , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k a)
                                                , HasFan f v
                                                , FanInKey f ~ k)
  => (R.Dynamic t (f v) -> m (f v, R.Event t (Diff f k v)))
  -> R.Dynamic t (f v) -> (k -> R.Dynamic t v -> m (R.Event t a)) -> m (R.Event t (f a))
listViewWithKeyGeneral' val mkChild = R.switch . fmap merge?? <$> listViewWithKeyGeneral' vals mkChild
-}

-- encapsulates the ability to diff two containers and then apply the diff to regain the original
-- also supports a Map.difference style operation on the diff itself (for splitting out value updates)
-- diffOnlyKeyChanges and editDiffLeavingDeletes are both too specific, I think.
-- NB: applyDiffD (diffD x y) y = x
class Diffable (f :: * -> *) (df :: * -> *) where
  emptyContainer :: Proxy df -> f v
  toDiff :: f v -> df v -- this can always be done via toDiff = flip diff emptyContainer
  diffNoEq :: f v -> f v -> df v
  diff :: Eq v => f v -> f v -> df v
  applyDiff :: df v -> f v -> f v
  diffOnlyKeyChanges :: f v -> f v -> df v
  editDiffLeavingDeletes :: Proxy f -> df v -> df k -> df v -- this removes 2nd diff from first, except when first indicates a delete. May not generalize.


diffableDynamicToInitialPlusKeyDiffEvent :: forall t m f df v. ( Diffable f df
                                                               , R.PostBuild t m
                                                               , MonadFix m
                                                               , R.MonadHold t m)
  => R.Dynamic t (f v)
  -> m (f v, R.Event t (df v))
diffableDynamicToInitialPlusKeyDiffEvent vals = mdo
  postBuild <- R.getPostBuild
  let emptyContainer' :: f v = emptyContainer (Proxy :: Proxy df)
  sentVals :: R.Dynamic t (f v) <- R.foldDyn applyDiff emptyContainer' changeVals
  let changeVals :: R.Event t (df v)
      changeVals = R.attachWith diffOnlyKeyChanges (R.current sentVals) $ R.leftmost
                   [ R.updated vals
                   , R.tag (R.current vals) postBuild
                   ] --TODO: This should probably be added to the attachWith, not to the updated; if we were using diffMap instead of diffMapNoEq, I think it might not work
  return $ (emptyContainer', changeVals)


listWithKeyDiffable :: forall t m f k v a. ( R.Adjustable t m
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
listWithKeyDiffable vals mkChild = listWithKeyGeneral' diffableDynamicToInitialPlusKeyDiffEvent vals mkChild

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
listWithKeyGeneral = listWithKeyDiffable

-- | Display the given map of items (in key order) using the builder function provided, and update it with the given event.
-- | 'Nothing' update entries will delete the corresponding children, and 'Just' entries will create them if they do not exist or send an update event to them if they do.
listWithKeyShallowDiffGeneral :: forall t m f k v a.( R.Adjustable t m
                                                    , MonadFix m
                                                    , R.MonadHold t m
                                                    , ToPatchType f k v a -- for the listHold
                                                    , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k a) -- for the listHold
                                                    , Diffable f (Diff f k)
                                                    , Functor (Diff f k)
                                                    , HasFan (Diff f k) v
                                                    , FanInKey (Diff f k) ~ k)
  => f v -> R.Event t (Diff f k v) -> (k -> v -> R.Event t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyShallowDiffGeneral initialVals valsChanged mkChild = do
  let makeSelKey' = makeSelKey (Proxy :: Proxy (Diff f k)) (Proxy :: Proxy v)
      doFan' = doFan (Proxy :: Proxy v)
      emptyContainer'::f ()
      emptyContainer' = emptyContainer (Proxy :: Proxy (Diff f k))
      editDiffLeavingDeletes' = editDiffLeavingDeletes (Proxy :: Proxy f)
      childValChangedSelector = doFan' valsChanged
  sentVals <- R.foldDyn applyDiff emptyContainer' $ fmap void valsChanged
  listHoldWithKeyGeneral initialVals (R.attachWith (flip editDiffLeavingDeletes') (R.current (toDiff <$> sentVals)) valsChanged) $ \k v ->
    mkChild k v $ R.select childValChangedSelector $ makeSelKey' k


class ToElemList (f :: * -> *) where
  toElemList::f v -> [v]

-- | Create a dynamically-changing set of widgets, one of which is selected at any time.
selectViewListWithKeyGeneral :: forall t m f k v a. ( R.Adjustable t m
                                                    , MonadFix m
                                                    , R.MonadHold t m
                                                    , R.PostBuild t m
                                                    , ToElemList f
                                                    , ToPatchType f k v (R.Event t (k,a)) -- for the listHold
                                                    , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k (R.Event t (k,a))) -- for the listHold
                                                    , Diffable f (Diff f k) -- for the listWithKeyGeneral
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
