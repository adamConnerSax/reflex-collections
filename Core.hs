{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE TypeFamilies          #-}
module Reflex.Dom.Contrib.ListHoldFunctions.Core
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
import qualified Reflex.Dom             as RD

import           Data.Dependent.Map                        (DMap,GCompare)
import           Data.Functor.Misc                         (Const2 (..))
import           Reflex.Patch                              (PatchDMap (..))
import           Data.Functor.Compose                      (Compose(Compose,getCompose))


import           Control.Monad.Fix      (MonadFix)
import           Control.Monad.Identity (Identity (..), void)

import           Data.Proxy             (Proxy (..))

-- This class carries the ability to sequence patches in the way of MonadAdjust And then turn the result into a Dynamic. 
class (R.Patch (pd k Identity)
      , R.PatchTarget (pd k Identity) ~ d k Identity)=> Sequenceable (d :: (* -> *) -> (* -> *) -> *) (pd :: (* -> *) -> (* -> *) -> *)  (k :: * -> *) where
  sequenceWithPatch::R.MonadAdjust t m=>d k m -> R.Event t (pd k m) -> m (d k Identity, R.Event t (pd k Identity))
  patchPairToDynamic::(R.Reflex t, R.MonadHold t m)=>d k Identity -> R.Event t (pd k Identity) -> m (R.Dynamic t (d k Identity))

-- In particular, we can do sequencing for DMaps
instance (GCompare (Const2 k a), Ord k)=>Sequenceable DMap PatchDMap (Const2 k a) where
  sequenceWithPatch = R.sequenceDMapWithAdjust
  patchPairToDynamic a0 a' = R.incrementalToDynamic <$> R.holdIncremental a0 a'


-- This class has the capabilities to translate f v and its difftype into types that are sequenceable, and then bring the original type back
-- This requires that the Diff type be mapped to the correct type for diffing at the sequencable level (e.g., as a DMap).
class ToPatchType (f :: * -> *) k v a where
  type Diff f k :: * -> *
  type SeqType  f k :: (* -> *) -> (* -> *) -> *
  type SeqPatchType f k :: (* -> *) -> (* -> *) -> *
  type SeqTypeKey f k a :: * -> *
  toSeqTypeWithFunctor::Functor g=>(k->v->g a) -> f v -> SeqType f k (SeqTypeKey f k a) g
  makePatchSeq::Functor g=>Proxy f->(k->v->g a) -> Diff f k v -> SeqPatchType f k (SeqTypeKey f k a) g
  fromSeqType::Proxy k->Proxy v->SeqType f k (SeqTypeKey f k a) Identity -> f a

-- Sequenceable and ToPatch are enough for listHoldWithKey
-- NB: incrementalToDynamic applies the patch to the original so the Diff type here (or, really, whatever makePatchSeq turns it into, must be consistent). 
listHoldWithKeyGeneral::forall t m f k v a. (RD.DomBuilder t m, R.MonadHold t m
                                            , ToPatchType f k v a
                                            , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k a))
  =>f v -> R.Event t (Diff f k v) -> (k->v-> m a) -> m (R.Dynamic t (f a))
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

-- This class encapsuates the types and functionality required to use "fan"
class HasFan (a :: * -> *) v where
  type FanInKey a :: *
  type FanSelKey a v :: * -> *
  makeSelKey::Proxy a->Proxy v->FanInKey a->FanSelKey a v v
  doFan::R.Reflex t=>Proxy v->R.Event t (a v) -> R.EventSelector t (FanSelKey a v)


-- encapsulates the ability to diff two containers and then apply the diff to regain the original
-- also supports a Map.difference style operation on the diff itself (for splitting out value updates)
-- diffOnlyKeyChanges and editDiffLeavingDeletes are both too specific, I think.
-- NB: applyDiffD (diffD x y) y = x
class Diffable (f :: * -> *) (df :: * -> *) where
  emptyContainer::Proxy df -> f v
  toDiff::f v-> df v -- this can always be done via toDiff = flip diffD emptyContainer
  diffNoEq::f v -> f v -> df v
  diff::Eq v=>f v -> f v -> df v
  applyDiff::df v -> f v -> f v
  diffOnlyKeyChanges::f v -> f v -> df v
  editDiffLeavingDeletes::Proxy f->df v -> df k -> df v -- this removes 2nd diff from first, except when first indicates a delete. May not generalize.


-- | Create a dynamically-changing set of Event-valued widgets.
listWithKeyGeneral :: forall t m f k v a. (RD.DomBuilder t m
                                          , RD.PostBuild t m
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

-- | Display the given map of items (in key order) using the builder function provided, and update it with the given event.
-- | 'Nothing' update entries will delete the corresponding children, and 'Just' entries will create them if they do not exist or send an update event to them if they do.
listWithKeyShallowDiffGeneral :: forall t m f k v a.(RD.DomBuilder t m
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
selectViewListWithKeyGeneral :: forall t m f k v a. (RD.DomBuilder t m
                                                    , MonadFix m
                                                    , R.MonadHold t m
                                                    , RD.PostBuild t m
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
