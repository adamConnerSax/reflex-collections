{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
module Reflex.Dom.Contrib.ListHoldFunctions.Core
  (
  , Sequenceable(..)
  , ToPatchType(..)
  , listHoldWithKeyGeneral
  , HasFan(..)
  , Diffable(..)
  , listWithKeyGeneral
  , listWithKeyShallowDiffGeneral
  ) where

import qualified Reflex                 as R
import qualified Reflex.Dom             as RD
import           Reflex.Patch           (ComposeMaybe (..), PatchDMap (..))

import           Data.Dependent.Map     (DMap, DSum ((:=>)))
import qualified Data.Dependent.Map     as DM

import           Control.Monad.Fix      (MonadFix)
import           Control.Monad.Identity (Identity (..), void)
import           Data.Functor.Compose   (Compose (Compose, getCompose))
                 
import           Data.Proxy             (Proxy (..))



-- This just says we can sequence in the way of monadAdjust
-- And then turn the result into a Dynamic
class DM.GCompare k=>Sequenceable (d :: (* -> *) -> (* -> *) -> *) (pd :: (* -> *) -> (* -> *) -> *)  (k :: * -> *) where
  sequenceWithPatch::(R.Reflex t, R.MonadAdjust t m)=>d k m -> R.Event t (pd k m) -> m (d k Identity, R.Event t (pd k Identity))
--  patchPairToDynamic::Patch p=>PatchTarget p -> R.Event t p -> m (Dynamic t p)

-- This class has the capabilities to translate f v and its difftype into types that are sequenceable, and then bring the original type back
class (RD.Patch (SeqPatchType f k (SeqTypeKey f k a) Identity)
      ,R.PatchTarget (SeqPatchType f k (SeqTypeKey f k a) Identity) ~ SeqType f k (SeqTypeKey f k a) Identity)=>ToPatchType (f :: * -> *) k v a where
  type Diff f k :: * -> *
  type SeqType  f k :: (* -> *) -> (* -> *) -> *
  type SeqPatchType f k :: (* -> *) -> (* -> *) -> *
  type SeqTypeKey f k a :: * -> *
  toSeqTypeWithFunctor::Functor g=>(k->v->g a) -> f v -> SeqType f k (SeqTypeKey f k a) g
  makePatchSeq::Proxy f->(k->v->g a) -> Diff f k v -> SeqPatchType f k (SeqTypeKey f k a) g
  fromSeqType::Proxy k->Proxy v->SeqType f k (SeqTypeKey f k a) Identity -> f a


--Sequenceable and ToPatch are enough for listHoldWithKey

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
  fmap fromSeqType' . R.incrementalToDynamic <$> R.holdIncremental a0 a' --TODO: Move the fromSeqType to the righthand side so it doesn't get fully redone every time

-- for the listWithKey and listWithKeyShallow diff we need fan and the ability to take and apply diffs on the original container

-- This class encapsuates the types and functionality required to use "fan"
class HasFan (a :: * -> *) v where
  type FanInKey a :: *
  type FanSelKey a v :: * -> *
  makeSelKey::Proxy a->Proxy v->FanInKey a->FanSelKey a v v
  doFan::R.Reflex t=>Proxy v->R.Event t (a v) -> R.EventSelector t (FanSelKey a v)


-- encapsulates the ability to diff two containers and then apply the diff to regain the original
-- also supports a Map.difference style operation on the diff itself (for splitting out value updates)
-- NB: applyDiffD (diffD x y) y = x
class Diffable (f :: * -> *) (df :: * -> *) where
  emptyContainer::Proxy df -> f v
  toDiff::f v-> df v -- this can always be done via toDiff = flip diffD emptyContainer
  diff::f v -> f v -> df v
  applyDiff::df v -> f v -> f v
  diffOnlyKeyChanges::f v -> f v -> df v
  editDiffLeavingDeletes::Proxy f->df v -> df k -> df v -- this removes 2nd diff from first, except when first indicates a delete.


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


instance Ord k=>Sequenceable DM.DMap PatchDMap (Const2 k a) where
  sequenceWithPatch = R.sequenceDMapWithAdjust



---- previous things
{-
-- This class encapsulates the relationship between a container and a difftype, which represents changes to the container.
-- This requires the diff type to be keyed, I think. Or maybe just the original container to have an Align instance?
-- I think this might all be subsumed.  diff and applyDiff should be part of general diffing and voidDiff is easy as long as df is a functor.
-- that leaves emptyVoidDiff...which could be its own thing?  Or part of a structure I don't see yet.
class ShallowDiffable (df :: * -> *) where
  emptyVoidDiff::df ()
  voidDiff::df v->df ()
  diff::df v->df ()->df v -- akin to Map.differenceWith (\mv _ -> maybe (Just Nothing) (const Nothing) mv)
  applyDiff::df ()-> df () -> df () -- NB: this is a different type from applyMap


listWithKeyShallowDiffGeneral :: forall t m f k v a.(RD.DomBuilder t m
                                                    , MonadFix m
                                                    , R.MonadHold t m
                                                    , ToPatchType f k v a -- for the listHold
                                                    , Sequenceable (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k a) -- for the listHold
                                                    , ShallowDiffable (Diff f k)
                                                    , HasFan (Diff f k) v
                                                    , FanInKey (Diff f k) ~ k)
  => f v -> R.Event t (Diff f k v) -> (k -> v -> R.Event t v -> m a) -> m (R.Dynamic t (f a))
listWithKeyShallowDiffGeneral initialVals valsChanged mkChild = do
  let makeSelKey' = makeSelKey (Proxy :: Proxy (Diff f k)) (Proxy :: Proxy v)
      doFan' = doFan (Proxy :: Proxy v)
      childValChangedSelector = doFan' valsChanged
  sentVals <- R.foldDyn applyDiff emptyVoidDiff $ fmap voidDiff valsChanged
  listHoldWithKeyGeneral initialVals (R.attachWith (flip diff) (R.current sentVals) valsChanged) $ \k v ->
    mkChild k v $ R.select childValChangedSelector $ makeSelKey' k


instance Ord k=>ShallowDiffable (Compose (Map k) Maybe) where
  emptyVoidDiff = Compose Map.empty
  voidDiff = void
  diff old new =
    let relevantPatch patch _ = case patch of
          Nothing -> Just Nothing
          Just _ -> Nothing
    in Compose $ Map.differenceWith relevantPatch (getCompose old) (getCompose new)
  applyDiff patch old = Compose $ RD.applyMap (getCompose $ fmap Just patch) (getCompose old)


{-
  --  compactMaybe::MDPatch v -> f v
  union::f v -> f v -> f v
  difference::


  diffNoEq:: f v -> f v -> f (Maybe v)
  diff::Eq v=> f v -> f v -> f (Maybe v)
  apply::f (Maybe v) -> f v -> f v
-}
-}

{-

class ListHoldMap (f :: * -> *) where
  type LHMapKey f :: *
  lhMapToDMap::f v -> DM.DMap (Const2 (LHMapKey f) v) Identity
  lhMapToDMapWithFunctor::Functor g=>f (g v) -> DM.DMap (Const2 (LHMapKey f) v) g
  dmapToLHMap::DM.DMap (Const2 (LHMapKey f) v) Identity -> f v
  lhEmptyMap::f v
  lhMapWithKey::(LHMapKey f -> v -> a) -> f v -> f a
  lhMapMaybe::(a -> Maybe b) -> f a -> f b
  lhMapUnion::f v -> f v -> f v
  lhMapIntersection::f v->f v->f v
  lhMapDifferenceWith::(a->b->Maybe a)->f a->f b->f a
  -- mapDifference is just mapDifferenceWith (\_ _ -> Nothing)


lhFanMap::(ListHoldMap f, Ord (LHMapKey f), R.Reflex t) => R.Event t (f v) -> R.EventSelector t (Const2 (LHMapKey f) v)
lhFanMap = R.fan . fmap lhMapToDMap

newtype LHMap f v = LHMap { unLHM::f v } -- newtype to allow instancing specifically for maps

instance (ListHoldMap f, LHMapKey f ~ k)=>ToPatchType (LHMap f) k v a where
  type Diff (LHMap f) k = LHMap (Compose (LHMap f) Maybe)
  type SeqType (LHMap f) k = DM.DMap
  type SeqPatchType (LHMap f) k = PatchDMap
  type SeqTypeKey (LHMap f) k a = Const2 k a
  toSeqTypeWithFunctor h = lhMapToDMapWithFunctor . lhMapWithKey h . unLHM
  makePatchSeq _ h = PatchDMap . lhMapWithFunctorToDMap . lhMapWithKey (\k mv -> ComposeMaybe $ fmap (h k) mv) . getCompose . unLHM
  fromSeqType _ _ = LHMap . dmapToLHMap

instance (ListHoldMap f, Align f, Functor f)=>Diffable (LHMap f) (Compose (LHMap f) Maybe) where
  emptyContainer = LHMap $ lhEmptyMap
  toDiff = LHMap . Compose . fmap Just
  diff old new = LHMap . Compose $ flip fmap (align (unLHM old) (unLHM new)) $ \case
    This _ -> Nothing -- in old but not new, so delete
    That v -> Just v -- in new but not old, so put in patch
    These _ v -> Just v -- in both and without Eq I don't know if the value changed, so put possibly new value in patch

  applyDiff patch old = LHMap $ insertions `lhMapUnion` ((unLHMap old) `mapDifference` deletions) where
    deletions = Map.filter isNothing (getCompose (unLHMap patch))
    insertions = Map.mapMaybe id  $ (getCompose (unLHMap patch)) `Map.difference` deletions
    mapDifference = lhMapDifferenceWith (\_ _ -> Nothing)

  diffOnlyKeyChanges olds news = LHMap . Compose $ flip lhMapMaybe (align (unLHMap olds) (unLHMap news)) $ \case
    This _ -> Just Nothing
    These _ _ -> Nothing
    That new -> Just $ Just new

  editDiffLeavingDeletes _ da db =
    let relevantPatch patch _ = case patch of
          Nothing -> Just Nothing -- it's a delete
          Just _ -> Nothing -- remove from diff
    in LHMap . Compose $ lhMapdifferenceWith relevantPatch (getCompose $ unLHMap da) (getCompose $ unLHMap db)

instance ListHoldMap f=>HasFan (LHMap f) v where
  type FanInKey (LHMap f) = LHMapKey f
  type FanSelKey (LHMap f)  v = Const2 (LHMapKey f) v
  doFan _ = R.fanMap . unLHMap {- . fmap (Map.mapMaybe id) . fmap getCompose -}
  makeSelKey _ _ = Const2


instance ListHoldMap f=>HasFan (Compose f Maybe) v where
  type FanInKey (Compose f Maybe) = LHMapKey f
  type FanSelKey (Compose f Maybe) v = Const2 (LHMapKey f) v
  doFan _ = R.fanMap . fmap (lhMapMaybe id) . fmap getCompose
  makeSelKey _ _ = Const2


instance ListHoldMap (Map k) where
  type LHMapKey (Map k) = k
  lhMapToDMap = mapToDMap
  lhMapToDMapWithFunctor = mapToDMapWithFunctor
  dmapToLHMap = dmapToMap
  lhEmptyMap = Map.empty
  lhMapWithKey = Map.mapWithKey
  lhMapMaybe = Map.mapMaybe
  lhMapUnion = Map.union
  lhMapIntersection = Map.intersection
  lhMapDifferenceWith = Map.differenceWith


-}
