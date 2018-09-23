{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TupleSections         #-}
import           GHCJS.DOM.Types                  (JSM)
import           Language.Javascript.JSaddle.Warp (run)
import           Reflex
import qualified Reflex                           as R
import           Reflex.Dom                       hiding (Delete, mainWidget,
                                                   run)
--import qualified Reflex.Dom                       as RD
import           Reflex.Dom.Core                  (mainWidget)
import           Reflex.Dom.Old                   (MonadWidget)

import           Control.Monad                    (join)
import           Control.Monad.Fix                (MonadFix)
import           Data.Bool                        (bool)
import qualified Data.Foldable                    as F
import           Data.Monoid                      ((<>))
import           Data.Proxy                       (Proxy (..))

import qualified Data.Array                       as A
import qualified Data.IntMap                      as IM
import qualified Data.Map                         as M
import qualified Data.Sequence                    as S
import qualified Data.Text                        as T

import           System.Process                   (spawnProcess)
import           Text.Read                        (Read, readMaybe)


import qualified Reflex.Collections.Collections   as RC

-- NB: This is just for warp.
main::IO ()
main = do
  let port :: Int = 3702
  _ <- spawnProcess "open" ["-a","/Applications/Safari.App/Contents/MacOs/Safari", "http://localhost:" ++ show port]
  run port testWidget

type ReflexConstraints t m = (MonadWidget t m, DomBuilder t m, PostBuild t m, MonadFix m, MonadHold t m, DomBuilderSpace m ~ GhcjsDomSpace)

staticMapHold :: (Ord k, ReflexConstraints t m) => M.Map k v -> (k -> Dynamic t v -> m (Event t v)) -> m (Event t (M.Map k v))
staticMapHold x w = fmap (mergeMap . M.fromList) . sequence . fmap (\(k,v) -> (k,) <$> w k (constDyn v)) $ M.toList x

naiveMapHold :: (Ord k, ReflexConstraints t m) => Dynamic t (M.Map k v) -> (k -> Dynamic t v -> m (Event t v)) -> m (Event t (M.Map k v))
naiveMapHold xDyn w = join $ switchPromptly never <$> (dyn $ flip staticMapHold w <$> xDyn)

data ListElementChange a = NewValue a | Delete | MoveUp a | MoveDown a deriving (Show)

-- NB: This widget must not fire events when its input is updated
-- NB: This widget must track its own key since the underlying returned event might not be in the right slot for
-- things like [] or Seq
listElementWidget :: (Show a, Read a, ReflexConstraints t m) => Int -> Dynamic t a -> m (R.Event t (Int, ListElementChange a))
listElementWidget n aDyn = do
  editEv <- fmap NewValue <$> (el "span" $ fieldWidgetEv (readMaybe . T.unpack) aDyn)
  deleteEv <- fmap (const Delete) <$> (el "span" $ buttonNoSubmit "x")
  moveUpEv <- R.attachWith (\a _ -> MoveUp a) (R.current aDyn) <$> (el "span" $ buttonNoSubmit "up")
  moveDownEv <- R.attachWith (\a _ -> MoveDown a) (R.current aDyn) <$> (el "span" $ buttonNoSubmit "dn")
  return $ (n,) <$> R.leftmost [editEv, deleteEv, moveUpEv, moveDownEv]

diffFromChangeNonEdit :: IM.IntMap a -> (Int, ListElementChange a) -> IM.IntMap (Maybe a)
diffFromChangeNonEdit _ (_, NewValue _) = IM.empty
diffFromChangeNonEdit _ (n, Delete) = IM.singleton n Nothing
diffFromChangeNonEdit im (n, MoveUp a) =
  let mAbove = IM.lookupLT n im -- Maybe (Int, a)
  in maybe IM.empty (\(m,a') -> IM.fromList [(m, Just a),(n, Just a')]) mAbove
diffFromChangeNonEdit im (n, MoveDown a) =
  let mBelow = IM.lookupGT n im
  in maybe IM.empty (\(m,a') -> IM.fromList [(n, Just a'),(m, Just a)]) mBelow

diffFromChange :: IM.IntMap a -> (Int, ListElementChange a) -> IM.IntMap (Maybe a)
diffFromChange _ (n, NewValue a) = IM.singleton n (Just a)
diffFromChange im x              = diffFromChangeNonEdit im x

resultDiffFromChanges :: IM.IntMap a -> IM.IntMap (Int, ListElementChange a) -> IM.IntMap (Maybe a)
resultDiffFromChanges curAsIntMap changes = F.foldMap (diffFromChange curAsIntMap) . fmap snd $ IM.toList changes

widgetInputDiffFromChanges :: IM.IntMap a -> IM.IntMap (Int, ListElementChange a) -> IM.IntMap (Maybe a)
widgetInputDiffFromChanges curAsIntMap changes = F.foldMap (diffFromChangeNonEdit curAsIntMap) . fmap snd $ IM.toList changes


reorderingList :: (Show a, Read a, ReflexConstraints t m) => R.Dynamic t [a] -> m (R.Dynamic t [a])
reorderingList listDyn =
  let widget n a0 aEv = el "div" $ R.holdDyn a0 aEv >>= listElementWidget n
  in simpleManagedCollection widgetInputDiffFromChanges resultDiffFromChanges widget listDyn

-- Managed collection when a ~ c
simpleManagedCollection :: ( ReflexConstraints t m
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
simpleManagedCollection = managedCollection id updateKeyValueSet where
  updateKeyValueSet :: RC.Diffable f => RC.KeyValueSet f a -> f a -> RC.Diff f a
  updateKeyValueSet dfa fa = RC.slUnion (Just <$> RC.toKeyValueSet fa) (Nothing <$ dfa) -- NB: mlUnion is left biased


-- we need a bunch of reflex constraints and a bunch of collection constraints
managedCollection :: forall t m f a b c. ( ReflexConstraints t m
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
managedCollection faTofc updateFromInput updateStructure updateAll itemWidget faDyn = mdo
  postBuild <- R.getPostBuild
  diffBEv <- RC.listViewWithKeyShallowDiff (Proxy :: Proxy f) (R.leftmost [dfMaFromWidgetsEv, dfMaNewInputEv]) itemWidget
  let dfMaFromWidgetsEv = R.attachWith updateStructure (R.current curFcDiffDyn) diffBEv
      newInputFaEv = R.leftmost [R.updated faDyn, tag (R.current faDyn) postBuild]
      dfMaNewInputEv = R.attachWith updateFromInput (R.current curFcDiffDyn) newInputFaEv
      dfMcFromWidgetsEv = R.attachWith updateAll (R.current curFcDiffDyn) diffBEv
      curFcDiffEv = R.attachWith (RC.slDifferenceWith (const id)) (R.current curFcDiffDyn) dfMcFromWidgetsEv
  curFcDiffDyn <- R.buildDynamic (R.sample . R.current . fmap (RC.toKeyValueSet . faTofc) $ faDyn) $ R.leftmost [curFcDiffEv, RC.toKeyValueSet . faTofc <$> newInputFaEv]
  return $ (RC.fromCompleteKeyValueSet <$> curFcDiffDyn)

buttonNoSubmit :: DomBuilder t m => T.Text -> m (Event t ())
buttonNoSubmit t = (domEvent Click . fst) <$> elAttr' "button" ("type" =: "button") (text t)

testWidget :: JSM()
testWidget = mainWidget $ do
  let xMap :: M.Map T.Text Int = M.fromList [("A",1),("B",2),("C",3)]
      xIntMap :: IM.IntMap Double = IM.fromAscList [(1,1.0),(2,2.0),(3,3.0)]
      xList :: [Int] = [1,2,3,4]
--      xSeq : S.Seq Int = S.fromList xList
  el "h1" $ text "reflex-collections \"listView\" Function Family Examples"
  smallBreak
  el "h3" $ text "First, directly--mapping the widget over the map as a list, tagging the events with their keys, sequencing, making back into a map and then running mergeMap."
  mapEv0 <- staticMapHold xMap (pairWidget id) --fmap (mergeMap . M.fromList) . sequence . fmap (\(k,v) -> (k,) <$> pairWidget k (constDyn v)) $ M.toList x0
  mapDyn0 <- foldDyn M.union xMap mapEv0
  dynText $ fmap (T.pack . show) mapDyn0
  el "h3" $ text "Now we feed the dynamic result into a dynamic version (fmapping the static version and then using dyn and switchPromptly) of the same thing to show how it rebuilds for all changes to the input."
  mapEv1 <- naiveMapHold mapDyn0 (pairWidget id)
  mapDyn1 <- foldDyn M.union xMap mapEv1
  dynText $ fmap (T.pack . show) mapDyn1
  bigBreak

  el "h3" $ text "Now we feed it instead to listViewWithKey to show that the widgets are not rebuilt. But notice that *all* even when any 1 input changes. Can we fix that too?"
  mapEv2 <- RC.listViewWithKey mapDyn0 (pairWidget id)
  mapDyn2 <- foldDyn M.union xMap mapEv2
  dynText $ fmap (T.pack . show) mapDyn2

  el "h3" $ text "We feed it again to listViewWithKey, this time the native reflex one to compare codegen."
  mapEv3 <- listViewWithKey mapDyn0 (pairWidget id)
  mapDyn3 <- foldDyn M.union xMap mapEv2
  dynText $ fmap (T.pack . show) mapDyn3

  bigBreak
  el "h3" $ text "Now an IntMap example using IntMap underneath instead of DMap"
  intMapEv0 <- RC.listViewWithKey (constDyn xIntMap) (pairWidget (T.pack . show))
  intMapDyn0 <- foldDyn IM.union xIntMap intMapEv0
  dynText $ fmap (T.pack . show) intMapDyn0

  smallBreak
  intMapEv1 <- RC.listViewWithKey intMapDyn0 (pairWidget (T.pack . show))
  intMapDyn1 <- foldDyn IM.union xIntMap intMapEv1
  dynText $ fmap (T.pack . show) intMapDyn1

  bigBreak
  el "h3" $ text "Now a List example (using IntMap underneath)"
  listMDyn0 <- fmap sequence . join . fmap sequence <$> RC.listWithKey (constDyn xList) (pairWidgetDyn (T.pack . show))
  listDyn0 <- holdDyn xList (fmapMaybe id . updated $ listMDyn0) -- hold not fold.  The dynamic list output is the new list. ??
  dynText $ fmap (T.pack . show) listDyn0

  -- NB: fmap sequence . join . fmap sequence :: Dynamic [Dynamic (Maybe a)] -> Dynamic (Maybe [a])

  bigBreak
  el "h3" $ text "Now a managedCollection example"
  listDyn1 <- reorderingList listDyn0
  dynText $ fmap (T.pack . show) listDyn1
  return ()


smallBreak::DomBuilder t m=>m ()
smallBreak =   el "br" blank >> el "br" blank

bigBreak::DomBuilder t m=>m()
bigBreak =   el "br" blank >> el "h1" (text "") >> el "br" blank

-- takes a Dynamic t a and makes it an event but also traces and notifies of postbuild
traceDynAsEv :: PostBuild t m => (a -> String) -> Dynamic t a -> m (Event t (Bool,a))
traceDynAsEv f dyn = do
  postbuild <- getPostBuild
  let f' prefix x = prefix ++ f x
      pbEv = fmap (True,) $ traceEventWith (f' "postbuild-") $ tagPromptlyDyn dyn postbuild
      upEv = fmap (False,) $ traceEventWith (f' "update-") $ updated dyn
  return $ leftmost [upEv, pbEv]


rebuildStyle, updateStyle, restingStyle :: M.Map T.Text T.Text
rebuildStyle = ("style" =: "background-color:#D98880")
updateStyle  = ("style" =: "background-color:#F9E79F")
restingStyle = ("style" =: "background-color:#7DCEA0")

fieldWidgetEv :: (ReflexConstraints t m, Show v) => (T.Text -> Maybe v) -> Dynamic t v -> m (Event t v)
fieldWidgetEv parse vDyn = do
  inputEv' <- traceDynAsEv (\x->"editWidgetDyn' input: v=" ++ show x) vDyn -- traced so we can see when widgets are updated vs rebuilt vs left alone
  updatedDelayedEv <- delay 1.0 inputEv'
  let styleIs = bool updateStyle rebuildStyle
      inputEv = T.pack . show . snd <$> inputEv'
  attrs <- foldDyn const M.empty $ leftmost [styleIs . fst <$> inputEv', restingStyle <$ updatedDelayedEv]
  let config = TextInputConfig "text" "" inputEv attrs
  fmapMaybe parse . _textInput_input <$> textInput config -- Dynamic t (Maybe v)

pairWidget :: (Read a, Show a, ReflexConstraints t m) => (k -> T.Text) -> k -> Dynamic t a -> m (Event t a)
pairWidget toText k iDyn = do
  el "span" $ text (toText k)
  el "span" $ fieldWidgetEv (readMaybe . T.unpack) iDyn


pairWidgetDyn :: (Read a, Show a, ReflexConstraints t m) => (k -> T.Text) -> k -> Dynamic t a -> m (Dynamic t (Maybe a))
pairWidgetDyn toText k iDyn = do
  pb <- getPostBuild
  upd <- fmap Just <$> pairWidget toText k iDyn
  holdDyn Nothing $ leftmost [upd, Just <$> tag (current iDyn) pb]
