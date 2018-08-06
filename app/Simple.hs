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

import           Language.Javascript.JSaddle.Warp (run)
import           Reflex
import           Reflex.Dom                       hiding (mainWidget, run)
import           Reflex.Dom.Core                  (mainWidget)
import           Reflex.Dom.Old                   (MonadWidget)

import           Control.Monad                    (join)
import           Control.Monad.Fix                (MonadFix)
import           Data.Functor.Compose             (Compose (..))

import qualified Data.Array                       as A
import qualified Data.Map                         as M
import           Data.Maybe                       (fromJust, isNothing)
import           Data.Monoid                      ((<>))
import           Data.Proxy                       (Proxy (..))
import qualified Data.Text                        as T

import           System.Process                   (spawnProcess)
import           Text.Read                        (readMaybe)

import           Safe                             (headMay)

import           Reflex.Collections.Collections


-- NB: This is just for warp.
main::IO ()
main = return ()
{-
do
  let port :: Int = 3702
  pHandle <- spawnProcess "open" ["http://localhost:" ++ show port]
  run port testWidget

type ReflexConstraints t m = (MonadWidget t m, DomBuilder t m, PostBuild t m, MonadFix m, MonadHold t m, DomBuilderSpace m ~ GhcjsDomSpace)
type WidgetConstraints t m k v = (ReflexConstraints t m, Show v, Read v, Ord k, Show k, Read k)

data MyEnum = A | B | C | D deriving (Show, Read, Enum, Eq, Ord, Bounded, A.Ix)

fieldWidgetDyn' :: (ReflexConstraints t m, Show v) => (T.Text -> Maybe v) -> (TWidget t m -> TWidget t m) -> FieldWidgetDyn t m v
fieldWidgetDyn' parse f mvDyn = do
  inputEv' <- maybe (return never) (traceDynAsEv (\x->"editWidgetDyn' input: v=" ++ show x)) mvDyn -- traced so we can see when widgets are updated vs rebuilt vs left alone
  let inputEv = T.pack . show <$> inputEv'
      config = TextInputConfig "text" "" inputEv (constDyn M.empty)
  valDyn <- _textInput_value <$> f textInput config
  return $ parse <$> valDyn


pairWidget :: ReflexConstraints t m => String -> Dynamic t Int -> m (Dynamic t Int)
pairWidget s iDyn = do
  pb <- getPostBuild
  let inputEv = leftmost [updated iDyn, tag pb iDyn]
      config = TextInputConfig "text" "" inputEv (constDyn M.empty)
  el "span" $ text (T.unpack s)



testWidget::JSM()
testWidget = mainWidget $ do
  let simpleWidget = FWDyn $ fieldWidgetDyn' (readMaybe . T.unpack)  (restrictWidget' blurOrEnter)
      textWidget = FWDyn $ fieldWidgetDyn' Just (restrictWidget' blurOrEnter)
      keyedWidget = addFixedKeyToWidget id simpleWidget
      arrayWidget = addFixedKeyToWidget (T.pack . show) $ FWDyn $ fieldWidgetDyn' (readMaybe . T.unpack) (restrictWidget' blurOrEnter)
      x0 :: M.Map T.Text Int = M.fromList [("A",1),("B",2),("C",3)]
      a0 :: A.Array MyEnum Int = A.listArray (minBound, maxBound) [1,2,3,4]
  el "h1" $ text "reflex-dom \"listView\" Function Family Examples"
  smallBreak
  el "p" $ text "These editor widgets are each made using one of the listView family of functions.  I used each to build the same basic widget for editing a map.  The basic editor is then extended to support removing elements from the map and then adding them as well.  It turns out this can be done generically: using value widgets returning (Just v) for an edit and Nothing for a delete, and tacking an additional widget on to handle the addition of new elements."
  el "p" $ text "I include all 3 variations for the listWithKey version and then only the edit, delete and add versions for the other listView functions."
  el "p" $ text "Each widget's output is sent to the next as input in order to test that dynamic input is correctly handled."

  bigBreak
  el "h2" $ text "Using ListWithKey"
  res1 <- el "div" $ buildLBEMapLWK keyedWidget $ constDyn x0
  res2 <- el "div" $ buildLBEMapWithDelete buildLBEMapLWK keyedWidget res1
  res3 <- el "div" $ buildLBEMapWithAdd (buildLBEMapWithDelete buildLBEMapLWK keyedWidget) textWidget simpleWidget res2

  el "h2" $ text "Using ListViewWithKey"
  res4 <- buildLBEMapWithAdd (buildLBEMapWithDelete buildLBEMapLVWK keyedWidget) textWidget simpleWidget res3

  el "h2" $ text "Using ListViewWithKeyShallowDiff"
  res5 <- buildLBEMapWithAdd (buildLBEMapWithDelete buildLBEMapLVWKSD keyedWidget) textWidget simpleWidget res4

  el "h2" $ text "Using SelectViewListWithKey"
  res6 <- buildLBEMapWithAdd (buildLBEMapWithDelete buildLBEMapSVLWK keyedWidget) textWidget simpleWidget res5
  smallBreak
  el "span" $ text "result: "
  _ <- buildLBEMapLWK (addFixedKeyToWidget id (FWDyn $ readOnlyFieldWidget)) res6

  bigBreak
  el "p" $ text "Simple editor for a total array (an array indexed by a bounded enum with all values present"
  totalArrayRes <- totalArrayBuildLBELWK arrayWidget $ constDyn a0
  dynText $ fmap (T.pack . show) totalArrayRes

  return ()


smallBreak::DomBuilder t m=>m ()
smallBreak =   el "br" blank >> el "br" blank

bigBreak::DomBuilder t m=>m()
bigBreak =   el "br" blank >> el "h1" (text "") >> el "br" blank


type EditF t m k v = Dynamic t (M.Map k v)->m (Dynamic t (M.Map k v))
type ArrayEditF t m k v = Dynamic t (A.Array k v)->m (Dynamic t (Maybe (A.Array k v)))

-- simplest.  Use listWithKey.  This will be for ReadOnly and fixed element (no adds or deletes allowed) uses.
-- Just make widget into right form and do the distribute over the result
buildLBEMapLWK :: WidgetConstraints t m k v=>FieldWidgetWithKey t m k v->EditF t m k v
buildLBEMapLWK editOneValueWK mapDyn0 = do
  let editW k vDyn =  el "br" blank >> fieldWidgetDyn (editOneValueWK k) (Just vDyn)
  mapOfDyn <- listWithKeyGeneral mapDyn0 editW -- Dynamic t (M.Map k (Dynamic t (Maybe v)))
  return $ M.mapMaybe id <$> (join $ distributeMapOverDynPure <$> mapOfDyn)

totalArrayBuildLBELWK :: forall t m k v. ( A.Ix k
                                         , Bounded k
                                         , WidgetConstraints t m k v)
                      => FieldWidgetWithKey t m k v -> ArrayEditF t m k v
totalArrayBuildLBELWK editOneValueWK totalArrayDyn0 = do
  let editW k vDyn =  el "br" blank >> fieldWidgetDyn (editOneValueWK k) (Just vDyn)
  arrayOfDyn <- sampledListWithKey totalArrayDyn0 editW -- Dynamic t (A.Array k (Dynamic t (Maybe v)))
  let x = join $ distributeOverDynPure <$> arrayOfDyn
  return $ sequence <$> x

-- NB: ListViewWithKey returns an Event t (M.Map k v) but it contains only the keys for which things have changed
-- So we use applyMap to put those edits into the output.
buildLBEMapLVWK::WidgetConstraints t m k v=>FieldWidgetWithKey t m k v->EditF t m k v
buildLBEMapLVWK editOneValueWK mapDyn0 = mdo
  let editW k vDyn = el "br" blank >> fieldWidgetEv (editOneValueWK k) (Just vDyn)
  newInputMapEv <- dynAsEv mapDyn0
  mapEditsEv  <- listViewWithKeyGeneral mapDyn0 editW -- Event t (M.Map k (Maybe v)), carries only updates
  let editedMapEv = attachWith (flip applyMap) (current mapDyn) mapEditsEv
      mapEv = leftmost [newInputMapEv, editedMapEv]
  mapDyn <- holdDyn M.empty mapEv
  return mapDyn

-- now with ListViewWithKeyShallowDiff, just so I understand things.
-- ListViewWithKeyShallowDiff takes an (Event t (Map k, (Maybe v))) as input rather than the dynamic map.
-- so there would be more efficient ways to do, e.g., adds, in this case.
buildLBEMapLVWKSD :: WidgetConstraints t m k v => FieldWidgetWithKey t m k v -> EditF t m k v
buildLBEMapLVWKSD editOneValueWK mapDyn0 = mdo
  let editW k v0 vEv =  holdDyn v0 vEv >>= \vDyn ->   el "br" blank >> (fieldWidgetEv (editOneValueWK k)) (Just vDyn)
  newInputMapEv <- dynAsEv mapDyn0
  updateEvsDyn <- listWithKeyShallowDiffGeneral M.empty diffMapEv editW -- Dynamic t (Map k (Event t (Maybe v)))
  let mapEditsEv =  switch $ mergeMap <$> current updateEvsDyn -- Event t (Map k (Maybe v))
      diffMapEv = Compose . fmap Just <$> newInputMapEv
      editedMapEv = attachWith (flip applyMap) (current mapDyn) mapEditsEv
      newMapEv = leftmost [newInputMapEv, editedMapEv]
  mapDyn <- holdDyn M.empty newMapEv
  return mapDyn


-- Select-based
-- This one will use selectListViewWithKey to maintain the widget set and a dropdown for controlling selection
-- dropdown will switch out if map is empty and rebuild if default key is forced to change

boolToEither::Bool -> Either () ()
boolToEither True  = Right ()
boolToEither False = Left ()
-- NB: right event fires if true, left if false--(FalseEv,TrueEv)--which fits Either but is not intuitive, at least to me
fanBool::Reflex t=>Event t Bool->(Event t (), Event t ())
fanBool = fanEither . fmap boolToEither

buildLBEMapSVLWK::WidgetConstraints t m k v=>FieldWidgetWithKey t m k v->EditF t m k v
buildLBEMapSVLWK editOneValueWK mapDyn0 = mdo
  newInputMapEv <- dynAsEv mapDyn0
  let editW k vDyn selDyn = fieldWidgetEv (addDynamicVisibility editOneValueWK selDyn k) (Just vDyn) -- (k->Dynamic t v->Dynamic t Bool->m (Event t (Maybe v)))
      selectWidget k0 = mdo
        let ddConfig = def & dropdownConfig_attributes .~ constDyn ("size" =: "1")
            newK0 oldK0 m = if M.member oldK0 m then Nothing else headMay $ M.keys m
            newk0Ev = attachWithMaybe newK0 (current k0Dyn) (updated mapDyn) -- has to be old k0, otherwise causality loop
        k0Dyn <- holdDyn k0 newk0Ev
        let dropdownWidget k =  _dropdown_value <$> dropdown k (M.mapWithKey (\k _ ->T.pack . show $ k) <$> mapDyn) ddConfig -- this needs to know about deletes
        selDyn <- join <$> widgetHold (dropdownWidget k0) (dropdownWidget <$> newk0Ev)
        selectViewListWithKeyGeneral selDyn mapDyn0 editW  -- NB: this map doesn't need updating from edits or deletes

      (nonNullEv,nullEv) = fanBool . updated . uniqDyn $ M.null <$> mapDyn
      nullWidget = el "div" (text "Empty Map") >> return never
      nullWidgetEv = nullWidget <$ nullEv
      defaultKeyEv = fmapMaybe id $ tagPromptlyDyn (headMay . M.keys <$> mapDyn) nonNullEv -- headMay and fmapMaybe id are redundant here but...
      widgetEv = leftmost [nullWidgetEv, selectWidget <$> defaultKeyEv]

  mapEditEvDyn <- widgetHold nullWidget widgetEv -- Dynamic (Event t (k,Maybe v))
  mapEditEvBeh <- hold never (updated mapEditEvDyn)
  let mapEditEv = switch mapEditEvBeh -- Event t (k,Maybe v)
      mapPatchEv = uncurry M.singleton <$> mapEditEv
      editedMapEv = attachWith (flip applyMap) (current mapDyn) mapPatchEv
      updatedMapEv = leftmost [newInputMapEv, editedMapEv] -- order matters here.  mapEditEv on new map will not have the whole map.  Arbitrary patch.
  mapDyn <- holdDyn M.empty updatedMapEv
  return mapDyn


buildLBEMapWithDelete::WidgetConstraints t m k v
  =>(FieldWidgetWithKey t m k v->EditF t m k v)
  ->FieldWidgetWithKey t m k v->EditF t m k v
buildLBEMapWithDelete buildBase valWidgetWK = buildBase (editAndDeleteFieldWidgetWithKey valWidgetWK (constDyn True))


buildLBEMapWithAdd::WidgetConstraints t m k v
  => EditF t m k v -- base map editor
  -> FieldWidget t m k -- single key editor
  -> FieldWidget t m v -- single value editor
  -> EditF t m k v
buildLBEMapWithAdd baseEditor keyWidget valWidget map0Dyn = mdo
  initialMapEv <- dynAsEv map0Dyn
  editedMapDyn <- baseEditor mapDyn -- Dynamic t (M.Map k v)
  el "br" blank
  addEv <- mdo -- Event t (k,v)
    let newMaybePairWidget = mdo
          newKey <- fieldWidgetDyn keyWidget Nothing    -- (Dynamic t (Maybe k)
          newVal <- fieldWidgetDyn valWidget Nothing  -- (Dynamic t (Maybe v)
          return $ (\(ma,mb) -> (,) <$> ma <*> mb) <$> zipDynWith (,) newKey newVal
        addMaybePairWidget = join <$> widgetHold newMaybePairWidget (newMaybePairWidget <$ newPairEv)
    newMaybePairDyn <- addMaybePairWidget
    addButtonEv <- buttonNoSubmit "+" -- Event t ()
    let newPairEv = fmapMaybe id $ tag (current newMaybePairDyn) addButtonEv
    return newPairEv
  let mapWithAdditionEv = attachWith (\m (k,v)->M.insert k v m) (current editedMapDyn) addEv
  mapDyn <- holdDyn M.empty (leftmost [initialMapEv, mapWithAdditionEv])
  return editedMapDyn


-- single field widgets

type FieldWidgetDyn t m v = Maybe (Dynamic t v)-> m (Dynamic t (Maybe v))
type FieldWidgetEv t m v = Maybe (Dynamic t v)-> m (Event t (Maybe v))

data FieldWidget t m v = FWDyn (FieldWidgetDyn t m v) | FWEv (FieldWidgetEv t m v)

fieldWidgetEv :: (Functor m, Reflex t)=>FieldWidget t m v->FieldWidgetEv t m v
fieldWidgetEv (FWEv wEv) mvDyn   = wEv mvDyn
fieldWidgetEv (FWDyn wDyn) mvDyn = updated <$> wDyn mvDyn

fieldWidgetDyn :: MonadHold t m => FieldWidget t m v -> FieldWidgetDyn t m v
fieldWidgetDyn (FWDyn wDyn) mvDyn = wDyn mvDyn
fieldWidgetDyn (FWEv wEv) mvDyn   = wEv mvDyn >>= holdDyn Nothing

applyToFieldWidget::(forall a.m a -> m a)->FieldWidget t m v->FieldWidget t m v
applyToFieldWidget f fw = case fw of
  FWDyn wDyn -> FWDyn $ \mvDyn -> f (wDyn mvDyn)
  FWEv  wEv  -> FWEv  $ \mvDyn -> f (wEv mvDyn)

type FieldWidgetWithKey t m k v = k->FieldWidget t m v

addFixedKeyToWidget :: ReflexConstraints t m => (k -> T.Text) -> FieldWidget t m v -> FieldWidgetWithKey t m k v
addFixedKeyToWidget printK fw k =
  let addKey::ReflexConstraints t m => m a -> m a
      addKey x = el "span" $ text (printK k) >> x
  in applyToFieldWidget addKey fw

type TWidget t m = TextInputConfig t -> m (TextInput t)

fieldWidgetDyn' :: (ReflexConstraints t m, Show v) => (T.Text -> Maybe v) -> (TWidget t m -> TWidget t m) -> FieldWidgetDyn t m v
fieldWidgetDyn' parse f mvDyn = do
  inputEv' <- maybe (return never) (traceDynAsEv (\x->"editWidgetDyn' input: v=" ++ show x)) mvDyn -- traced so we can see when widgets are updated vs rebuilt vs left alone
  let inputEv = T.pack . show <$> inputEv'
      config = TextInputConfig "text" "" inputEv (constDyn M.empty)
  valDyn <- _textInput_value <$> f textInput config
  return $ parse <$> valDyn


readOnlyFieldWidget::(ReflexConstraints t m, Show v)=>FieldWidgetDyn t m v
readOnlyFieldWidget =
  let makeReadOnly wFunc (TextInputConfig iType initialVal setVal dAttrs) =
        let dAttrs' = M.insert "readonly" "" <$> dAttrs
        in wFunc (TextInputConfig iType initialVal setVal dAttrs')
  in fieldWidgetDyn' (const Nothing) makeReadOnly


-- copied from reflex-dom-contrib
blurOrEnter::Reflex t=>TextInput t -> Event t T.Text
blurOrEnter w = tagPromptlyDyn (_textInput_value w) fireEvent
  where
    fireEvent = leftmost [ () <$ (ffilter (==13) $ _textInput_keypress w)
                         , () <$ (ffilter not $ updated $ _textInput_hasFocus w) ]


-- like Reflex.Dom.Contrib.Widgets.Common.restrictWidget but allows the set event to change the "authoritative value"
restrictWidget'::(DomBuilder t m, MonadHold t m)
  =>(TextInput t -> Event t T.Text)
  -> TWidget t m
  -> TWidget t m
restrictWidget' restrictFunc wFunc cfg = do
  w <- wFunc cfg
  let e = leftmost [_textInputConfig_setValue cfg, restrictFunc w]
  v <- holdDyn (_textInputConfig_initialValue cfg) e
  return $ w { _textInput_value = v
             , _textInput_input = e
             }

editAndDeleteFieldWidgetWithKey::(ReflexConstraints t m, Read v, Show v)=>FieldWidgetWithKey t m k v->Dynamic t Bool->FieldWidgetWithKey t m k v
editAndDeleteFieldWidgetWithKey baseWidgetWK visibleDyn k = FWEv $ \mvDyn -> mdo
  let widgetAttrs = (\x -> if x then visibleCSS else hiddenCSS) <$> visibleDyn'
      newInputEv = maybe never updated mvDyn
  (visibleDyn',outEv) <- elDynAttr "div" widgetAttrs $ do
    resEv <-  fieldWidgetEv (baseWidgetWK k) mvDyn
    delButtonEv <- buttonNoSubmit "-"
    selEv <- dynAsEv visibleDyn
    visDyn <-  holdDyn True $ leftmost
               [
                 selEv
               , False <$ delButtonEv -- delete button pressed, so hide
               , True <$ newInputEv -- value updated so make sure it's visible (in case of re-use of deleted key)
               ]
    let outEv' = leftmost
                 [
                   Just <$> fmapMaybe id resEv
                 , Nothing <$ delButtonEv
                 ]
    return (visDyn,outEv')
  return outEv


addDynamicVisibility::ReflexConstraints t m=>FieldWidgetWithKey t m k v->Dynamic t Bool->FieldWidgetWithKey t m k v
addDynamicVisibility fwwk visDyn k =
  let divAttrs = (\x -> if x then visibleCSS else hiddenCSS) <$> visDyn
  in applyToFieldWidget (elDynAttr "div" divAttrs) (fwwk k)

buttonNoSubmit::DomBuilder t m=>T.Text -> m (Event t ())
buttonNoSubmit t = (domEvent Click . fst) <$> elAttr' "button" ("type" =: "button") (text t)


dynAsEv::PostBuild t m=>Dynamic t a -> m (Event t a)
dynAsEv d = (\x->leftmost [updated d, tagPromptlyDyn d x]) <$> getPostBuild


traceDynAsEv::PostBuild t m=>(a->String)->Dynamic t a->m (Event t a)
traceDynAsEv f dyn = do
  postbuild <- getPostBuild
  let f' prefix x = prefix ++ f x
      pbEv = traceEventWith (f' "postbuild-") $ tagPromptlyDyn dyn postbuild
      upEv = traceEventWith (f' "update-") $ updated dyn
  return $ leftmost [upEv, pbEv]


hiddenCSS::M.Map T.Text T.Text
hiddenCSS  = "style" =: "display: none"

visibleCSS::M.Map T.Text T.Text
visibleCSS = "style" =: "display: inline"


testSingleWidget::(ReflexConstraints t m, Show v, Read v)=>T.Text->FieldWidget t m v->v->m ()
testSingleWidget label valWidget v0 = do
  el "h2" $ text label >> el "br" blank
  el "span" $ text $ "widget:  "
  widgetEv <- fieldWidgetEv valWidget (Just $ constDyn v0)
  resDyn <- holdDyn Nothing (Just <$> fmapMaybe id widgetEv)
  el "br" blank
  el "span" (text "dynText of holdDyn of widget events: ")
  dynText $ T.pack . show <$> resDyn
  bigBreak


-}
