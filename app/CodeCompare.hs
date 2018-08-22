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
import           Reflex.Dom                       hiding (mainWidget, run)
import           Reflex.Dom.Core                  (mainWidget)
import           Reflex.Dom.Old                   (MonadWidget)

import           Control.Monad                    (join)
import           Control.Monad.Fix                (MonadFix)
import           Data.Bool                        (bool)


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
  pHandle <- spawnProcess "open" ["http://localhost:" ++ show port]
  run port testWidget

type ReflexConstraints t m = (MonadWidget t m, DomBuilder t m, PostBuild t m, MonadFix m, MonadHold t m, DomBuilderSpace m ~ GhcjsDomSpace)

staticMapHold :: (Ord k, ReflexConstraints t m) => M.Map k v -> (k -> Dynamic t v -> m (Event t v)) -> m (Event t (M.Map k v))
staticMapHold x w = fmap (mergeMap . M.fromList) . sequence . fmap (\(k,v) -> (k,) <$> w k (constDyn v)) $ M.toList x

testWidget :: JSM()
testWidget = mainWidget $ do
  let xMap :: M.Map T.Text Int = M.fromList [("A",1),("B",2),("C",3)]
  el "h1" $ text "reflex-collections \"listView\" Code generation comparison."
  smallBreak
  el "h3" $ text "First, directly--mapping the widget over the map as a list, tagging the events with their keys, sequencing, making back into a map and then running mergeMap."
  mapEv0 <- staticMapHold xMap (pairWidget id) --fmap (mergeMap . M.fromList) . sequence . fmap (\(k,v) -> (k,) <$> pairWidget k (constDyn v)) $ M.toList x0
  mapDyn0 <- foldDyn M.union xMap mapEv0
  dynText $ fmap (T.pack . show) mapDyn0

  el "h3" $ text "Now we feed it to listViewWithKey (this library version)."
  mapEv1 <- RC.listViewWithKey mapDyn0 (pairWidget id)
  mapDyn1 <- foldDyn M.union xMap mapEv1
  dynText $ fmap (T.pack . show) mapDyn1

  el "h3" $ text "We feed it again to listViewWithKey, this time the native reflex one to compare codegen."
  mapEv2 <- listViewWithKey mapDyn0 (pairWidget id)
  mapDyn2 <- foldDyn M.union xMap mapEv2
  dynText $ fmap (T.pack . show) mapDyn2

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

{-
pairWidgetDyn :: (Read a, Show a, ReflexConstraints t m) => (k -> T.Text) -> k -> Dynamic t a -> m (Dynamic t (Maybe a))
pairWidgetDyn toText k iDyn = do
  pb <- getPostBuild
  upd <- fmap Just <$> pairWidget toText k iDyn
  holdDyn Nothing $ leftmost [upd, Just <$> tag (current iDyn) pb]
-}
