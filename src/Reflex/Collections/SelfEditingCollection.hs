{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE FlexibleContexts      #-}
-- | This module provides functions to efficiently manage collections of widgets where
-- events fired by the widgets may change the structure of the collection itself.
-- The core function, selfEditingCollection, will work with any `f :: Type -> Type`
-- supported by the main collection functions (in Reflex.Collections.Collections) and for which
-- `f a` has an instance of monoid.
module Reflex.Collections.SelfEditingCollection
  (
    selfEditingCollection
  , simpleSelfEditingCollection
  ) where

import qualified Reflex                           as R
import qualified Reflex.Collections.Collections   as RC
import           Control.Monad.Fix                (MonadFix)
import           Data.Proxy                       (Proxy (..))

-- self editing collection when a ~ c
simpleSelfEditingCollection :: ( R.Reflex t
                               , R.MonadHold t m
                               , R.Adjustable t m
                               , R.PostBuild t m
                               , MonadFix m
                               , Monoid (f a)
                               , RC.Patchable f
                               , RC.FannableC f a
                               , RC.Mergeable f
                               , RC.SequenceableWithEventC t f b)
  => (RC.KeyValueSet f a -> RC.KeyValueSet f b -> RC.Diff f a) -- updates to input collection which are not managed by the widgets
  -> (RC.KeyValueSet f a -> RC.KeyValueSet f b -> RC.Diff f a) -- all updates to the output collection
  -> (RC.Key f -> a -> R.Event t a -> m (R.Event t b))
  -> R.Dynamic t (f a)
  -> m (R.Dynamic t (f a))
simpleSelfEditingCollection = selfEditingCollection id updateKeyValueSet where
  updateKeyValueSet :: RC.Diffable f => RC.KeyValueSet f a -> f a -> RC.Diff f a
  updateKeyValueSet dfa fa = RC.slUnion (Just <$> RC.toKeyValueSet fa) (Nothing <$ dfa) -- NB: mlUnion is left biased

selfEditingCollection :: forall t m f a b c. ( R.Reflex t
                                             , R.MonadHold t m
                                             , R.Adjustable t m
                                             , R.PostBuild t m
                                             , MonadFix m
                                             , Monoid (f a)
                                             , RC.Patchable f
                                             , RC.FannableC f a
                                             , RC.Mergeable f
                                             , RC.SequenceableWithEventC t f b)
  => (f a -> f c)
  -> (RC.KeyValueSet f c -> f a -> RC.Diff f a)
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f a) -- updates to input collection which are not managed by the per-item widgets
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f c) -- all updates to the output collection
  -> (RC.Key f -> a -> R.Event t a -> m (R.Event t b))
  -> R.Dynamic t (f a)
  -> m (R.Dynamic t (f c))
selfEditingCollection faTofc updateFromInput updateStructure updateAll itemWidget faDyn = mdo
  postBuild <- R.getPostBuild
  diffBEv <- RC.listViewWithKeyShallowDiff (Proxy :: Proxy f) (R.leftmost [dfMaFromWidgetsEv, dfMaNewInputEv]) itemWidget
  let dfMaFromWidgetsEv = R.attachWith updateStructure (R.current curFcKVDyn) diffBEv
      newInputFaEv = R.leftmost [R.updated faDyn, R.tag (R.current faDyn) postBuild]
      dfMaNewInputEv = R.attachWith updateFromInput (R.current curFcKVDyn) newInputFaEv
      dfMcFromWidgetsEv = R.attachWith updateAll (R.current curFcKVDyn) diffBEv
      curFcKVEv = R.attachWith (RC.slDifferenceWith (const id)) (R.current curFcKVDyn) dfMcFromWidgetsEv
  curFcKVDyn <- R.buildDynamic (R.sample . R.current . fmap (RC.toKeyValueSet . faTofc) $ faDyn) $ R.leftmost [curFcKVEv, RC.toKeyValueSet . faTofc <$> newInputFaEv]
  return $ (RC.fromCompleteKeyValueSet <$> curFcKVDyn)


selfEditingCollectionEv :: forall t m f a b c. ( R.Reflex t
                                               , R.MonadHold t m
                                               , R.Adjustable t m
                                               , R.PostBuild t m
                                               , MonadFix m
                                               , RC.Patchable f
                                               , RC.FannableC f a
                                               , RC.Mergeable f
                                               , RC.SequenceableWithEventC t f b)
  => (a -> c)
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f a) -- updates to input collection which are not managed by the per-item widgets
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f c) -- all updates to the output collection
  -> (RC.Key f -> a -> R.Event t a -> m (R.Event t b))
  -> f a
  -> R.Event t (RC.Diff f a)
  -> m (R.Dynamic t (RC.KeyValueSet f c))
selfEditingCollectionEv aToc updateStructure updateAll itemWidget fa faDiffEv = mdo
  diffBEv <- RC.listViewWithKeyShallowDiffGeneral fa (R.leftmost [dfMaFromWidgetsEv, faDiffEv]) itemWidget
  let dfMaFromWidgetsEv = R.attachWith updateStructure (R.current curFcKVDyn) diffBEv
      dfMcFromWidgetsEv = R.attachWith updateAll (R.current curFcKVDyn) diffBEv
      curFcKVEv = R.attachWith (RC.slDifferenceWith (const id)) (R.current curFcKVDyn) dfMcFromWidgetsEv
      newInputFcKV = R.attachWith (RC.updateKeyValueSet (Proxy :: Proxy f)) (R.current curFcKVDyn) (fmap (fmap aToc) <$> faDiffEv)
  curFcKVDyn <- R.holdDyn (aToc <$> RC.toKeyValueSet fa) $ R.leftmost [newInputFcKV, curFcKVEv]
  return curFcKVDyn 


selfEditingCollection' :: forall t m f a b c. ( R.Reflex t
                                              , R.MonadHold t m
                                              , R.Adjustable t m
                                              , R.PostBuild t m
                                              , MonadFix m
                                              , Monoid (f a)
                                              , RC.Patchable f
                                              , RC.FannableC f a
                                              , RC.Mergeable f
                                              , RC.SequenceableWithEventC t f b)
  => (a -> c)
  -> (RC.KeyValueSet f c -> f a -> RC.Diff f a)
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f a) -- updates to input collection which are not managed by the per-item widgets
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f c) -- all updates to the output collection
  -> (RC.Key f -> a -> R.Event t a -> m (R.Event t b))
  -> R.Dynamic t (f a)
  -> m (R.Dynamic t (f c))
selfEditingCollection' aToc updateFromInput updateStructure updateAll itemWidget faDyn = mdo
  postBuild <- R.getPostBuild
  let newInputFaEv = R.leftmost [R.updated faDyn, R.tag (R.current faDyn) postBuild]
      dfMaNewInputEv = R.attachWith updateFromInput (R.current curFcKVDyn) newInputFaEv
  curFcKVDyn <- selfEditingCollectionEv aToc updateStructure updateAll itemWidget (mempty :: (f a)) dfMaNewInputEv
  return $ (RC.fromCompleteKeyValueSet <$> curFcKVDyn)
{-  
  diffBEv <- RC.listViewWithKeyShallowDiff (Proxy :: Proxy f) (R.leftmost [dfMaFromWidgetsEv, dfMaNewInputEv]) itemWidget
  let dfMaFromWidgetsEv = R.attachWith updateStructure (R.current curFcKVDyn) diffBEv
  
  
      dfMcFromWidgetsEv = R.attachWith updateAll (R.current curFcKVDyn) diffBEv
      curFcKVEv = R.attachWith (RC.slDifferenceWith (const id)) (R.current curFcKVDyn) dfMcFromWidgetsEv
  curFcKVDyn <- R.buildDynamic (R.sample . R.current . fmap (RC.toKeyValueSet . faTofc) $ faDyn) $ R.leftmost [curFcKVEv, RC.toKeyValueSet . faTofc <$> newInputFaEv]
  return $ (RC.fromCompleteKeyValueSet <$> curFcKVDyn)
-}
