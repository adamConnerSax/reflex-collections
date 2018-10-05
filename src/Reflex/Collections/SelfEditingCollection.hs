{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE Rank2Types #-}
-- | This module provides functions to efficiently manage collections of widgets where
-- events fired by the widgets may change the structure of the collection itself.
-- The core function, selfEditingCollection, will work with any `f :: Type -> Type`
-- supported by the main collection functions (in Reflex.Collections.Collections) and for which
-- `f a` has an instance of monoid.
module Reflex.Collections.SelfEditingCollection
  (
    selfEditingCollection
  , selfEditingCollectionMaybe
  , selfEditingCollectionGeneral
  , selfEditingCollectionWithChanges
  , selectSelfEditingCollectionWithChanges
  , simpleSelfEditingCollection
  ) where

import qualified Reflex                           as R
import qualified Reflex.Collections.Collections   as RC
import qualified Reflex.Collections.WithEmpty      as RC
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
simpleSelfEditingCollection = selfEditingCollection id diffFromKVAndNew where
  diffFromKVAndNew :: RC.Diffable f => RC.KeyValueSet f a -> f a -> RC.Diff f a
  diffFromKVAndNew dfa fa = RC.slUnion (Just <$> RC.toKeyValueSet fa) (Nothing <$ dfa) -- NB: slUnion is left biased so this just deletes things not being replaced



-- These are the core functions, driven by event diffs and returning both
-- the authoritative value as well as an event of just internal changes
-- anything complex should be built around this.
selfEditingCollectionWithChanges :: forall t m f a b c. ( R.Reflex t
                                                        , R.MonadHold t m
                                                        , R.Adjustable t m
                                                        , R.PostBuild t m
                                                        , MonadFix m
                                                        , RC.Patchable f
                                                        , RC.FannableC f a
                                                        , RC.Mergeable f
                                                        , RC.SequenceableWithEventC t f b)
  => (RC.Diff f a -> RC.Diff f c)
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f a) -- updates to input collection which are not managed by the per-item widgets
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f c) -- all updates to the output collection
  -> (RC.Key f -> a -> R.Event t a -> m (R.Event t b))
  -> f a
  -> R.Event t (RC.Diff f a)
  -> m (R.Dynamic t (RC.KeyValueSet f c), R.Event t (RC.Diff f c)) -- KeyValueSet is current value; event only fires on internal changes
selfEditingCollectionWithChanges dfaTodfc updateStructure updateAll itemWidget fa dfaEv = mdo
  kvbEv <- RC.listViewWithKeyShallowDiffGeneral fa (R.leftmost [dfaFromWidgetsEv, dfaEv]) itemWidget
  let dfaFromWidgetsEv = R.attachWith updateStructure (R.current curFcKVDyn) kvbEv
      dfcFromWidgetsEv = R.attachWith updateAll (R.current curFcKVDyn) kvbEv
      curFcKVEv = R.attachWith (RC.slDifferenceWith (const id)) (R.current curFcKVDyn) dfcFromWidgetsEv
      newInputFcKV = R.attachWith (RC.updateKeyValueSet (Proxy :: Proxy f)) (R.current curFcKVDyn) (dfaTodfc <$> dfaEv)      
  curFcKVDyn <- R.holdDyn (diffMapToKVMap (Proxy :: Proxy f) dfaTodfc . RC.toKeyValueSet $ fa) $ R.leftmost [newInputFcKV, curFcKVEv]
  return (curFcKVDyn, dfcFromWidgetsEv)


selectSelfEditingCollectionWithChanges :: forall t m f a b c. ( R.Reflex t
                                                              , R.MonadHold t m
                                                              , R.Adjustable t m
                                                              , R.PostBuild t m
                                                              , MonadFix m
                                                              , RC.Patchable f
                                                              , RC.FannableC f a
                                                              , RC.Mergeable f
                                                              , Ord (RC.Key f)
                                                              , RC.SequenceableWithEventC t f b)
  => (RC.Diff f a -> RC.Diff f c)
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f a) -- updates to input collection which are not managed by the per-item widgets
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f c) -- all updates to the output collection
  -> (forall x. R.Dynamic t Bool -> m x -> m x) -- make the widget "m x" visible only when the dynamic is "True"
  -> R.Dynamic t (RC.Key f)
  -> (RC.Key f -> R.Dynamic t a -> m (R.Event t b))
  -> f a
  -> R.Event t (RC.Diff f a)
  -> m (R.Dynamic t (RC.KeyValueSet f c), R.Event t (RC.Diff f c)) -- KeyValueSet is current value; event only fires on internal changes
selectSelfEditingCollectionWithChanges dfaTodfc updateStructure updateAll dynamicallyVisible keyDyn itemWidget fa dfaEv = mdo
  let selectWidget k aDyn visDyn = dynamicallyVisible visDyn $ itemWidget k aDyn
  kvbEv <- RC.selectViewListWithKeyShallowDiff keyDyn fa (R.leftmost [dfaEv, dfaFromWidgetsEv]) selectWidget
  let dfaFromWidgetsEv = R.attachWith updateStructure (R.current curFcKVDyn) kvbEv
      dfcFromWidgetsEv = R.attachWith updateAll (R.current curFcKVDyn) kvbEv
      curFcKVEv = R.attachWith (RC.slDifferenceWith (const id)) (R.current curFcKVDyn) dfcFromWidgetsEv
      newInputFcKV = R.attachWith (RC.updateKeyValueSet (Proxy :: Proxy f)) (R.current curFcKVDyn) (dfaTodfc <$> dfaEv)      
  curFcKVDyn <- R.holdDyn (diffMapToKVMap (Proxy :: Proxy f) dfaTodfc . RC.toKeyValueSet $ fa) $ R.leftmost [newInputFcKV, curFcKVEv]
  return (curFcKVDyn, dfcFromWidgetsEv)  


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
  => (RC.Diff f a -> RC.Diff f c)
  -> (RC.KeyValueSet f c -> f a -> RC.Diff f a)
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f a) -- updates to input collection which are not managed by the per-item widgets
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f c) -- all updates to the output collection
  -> (RC.Key f -> a -> R.Event t a -> m (R.Event t b))
  -> R.Dynamic t (f a)
  -> m (R.Dynamic t (f c))
selfEditingCollection = selfEditingCollectionGeneral (mempty :: f a)


selfEditingCollectionMaybe :: forall t m f a b c. ( R.Reflex t
                                                  , R.MonadHold t m
                                                  , R.Adjustable t m
                                                  , R.PostBuild t m
                                                  , MonadFix m
                                                  , RC.Patchable f
                                                  , RC.FannableC f a
                                                  , RC.Mergeable f
                                                  , RC.SequenceableWithEventC t f b)
  => (RC.Diff f a -> RC.Diff f c)
  -> (RC.KeyValueSet f c -> f a -> RC.Diff f a)
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f a) -- updates to input collection which are not managed by the per-item widgets
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f c) -- all updates to the output collection
  -> (RC.Key f -> a -> R.Event t a -> m (R.Event t b))
  -> R.Dynamic t (f a)
  -> m (R.Dynamic t (Maybe (f c)))
selfEditingCollectionMaybe dfaTodfc updateFromInput updateStructure updateAll itemWidget faDyn = let
  f kvc RC.Empty = Nothing <$ kvc
  f kvc (RC.NonEmpty fa) = updateFromInput kvc fa
  in fmap RC.withEmptyToMaybe <$> selfEditingCollectionGeneral (RC.Empty :: RC.WithEmpty f a) dfaTodfc f updateStructure updateAll itemWidget (RC.NonEmpty <$> faDyn) where


-- This version translates a dynamic input to diff events and reconstitutes the output to make a simpler interface.
-- Use this when all internal changes are driven by per-item widgets.
selfEditingCollectionGeneral :: forall t m f a b c. ( R.Reflex t
                                             , R.MonadHold t m
                                             , R.Adjustable t m
                                             , R.PostBuild t m
                                             , MonadFix m
                                             , RC.Patchable f
                                             , RC.FannableC f a
                                             , RC.Mergeable f
                                             , RC.SequenceableWithEventC t f b)
  => f a -- empty value
  -> (RC.Diff f a -> RC.Diff f c)
  -> (RC.KeyValueSet f c -> f a -> RC.Diff f a)
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f a) -- updates to input collection which are not managed by the per-item widgets
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f c) -- all updates to the output collection
  -> (RC.Key f -> a -> R.Event t a -> m (R.Event t b))
  -> R.Dynamic t (f a)
  -> m (R.Dynamic t (f c))
selfEditingCollectionGeneral emptyfa dfaTodfc updateFromInput updateStructure updateAll itemWidget faDyn = mdo
  postBuild <- R.getPostBuild
  let newInputFaEv = R.leftmost [R.updated faDyn, R.tag (R.current faDyn) postBuild]
      dfaNewInputEv = R.attachWith updateFromInput (R.current curFcKVDyn) newInputFaEv
  (curFcKVDyn, _) <- selfEditingCollectionWithChanges dfaTodfc updateStructure updateAll itemWidget emptyfa dfaNewInputEv
  return $ (RC.fromCompleteKeyValueSet <$> curFcKVDyn)

diffMapToKVMap :: RC.Diffable f => Proxy f -> (RC.Diff f a -> RC.Diff f b) -> RC.KeyValueSet f a -> RC.KeyValueSet f b
diffMapToKVMap _ g = RC.slMapMaybe id . g . fmap Just 


{-
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
  => (RC.Diff f a -> RC.Diff f c)
  -> (RC.KeyValueSet f c -> f a -> RC.Diff f a)
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f a) -- updates to input collection which are not managed by the per-item widgets
  -> (RC.KeyValueSet f c -> RC.KeyValueSet f b -> RC.Diff f c) -- all updates to the output collection
  -> (RC.Key f -> a -> R.Event t a -> m (R.Event t b))
  -> R.Dynamic t (f a)
  -> m (R.Dynamic t (f c))
selfEditingCollection dfaTodfc updateFromInput updateStructure updateAll itemWidget faDyn = mdo
  postBuild <- R.getPostBuild
  diffBEv <- RC.listViewWithKeyShallowDiff (Proxy :: Proxy f) (R.leftmost [dfMaFromWidgetsEv, dfMaNewInputEv]) itemWidget
  let dfMaFromWidgetsEv = R.attachWith updateStructure (R.current curFcKVDyn) diffBEv
      newInputFaEv = R.leftmost [R.updated faDyn, R.tag (R.current faDyn) postBuild]
      dfMaNewInputEv = R.attachWith updateFromInput (R.current curFcKVDyn) newInputFaEv
      dfMcFromWidgetsEv = R.attachWith updateAll (R.current curFcKVDyn) diffBEv
      curFcKVEv = R.attachWith (RC.slDifferenceWith (const id)) (R.current curFcKVDyn) dfMcFromWidgetsEv
      faToKVc = diffMapToKVMap (Proxy :: Proxy f) dfaTodfc . RC.toKeyValueSet
  curFcKVDyn <- R.buildDynamic (R.sample . R.current . fmap faToKVc $ faDyn) $ R.leftmost [curFcKVEv, faToKVc <$> newInputFaEv]
  return $ (RC.fromCompleteKeyValueSet <$> curFcKVDyn)
-}
