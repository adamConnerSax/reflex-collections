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
module Reflex.Collections.Core
  (
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

import Reflex.Collections.KeyMappable (KeyMappable(..))
import Reflex.Collections.SequenceableClasses (ReflexSequenceable(..), SequenceablePatch(..))

import           Data.Dependent.Map      (DMap, DSum ((:=>)))
import qualified Data.Dependent.Map      as DM
import           Reflex.Patch            (PatchDMap (..))
import           Data.Functor.Misc       (ComposeMaybe (..), Const2 (..),
                                          dmapToMap, mapWithFunctorToDMap)
                 
import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)

import Data.Map (Map)
import qualified Data.Map as M
import Data.IntMap (IntMap)
import qualified Data.IntMap as IM
import           Data.Hashable           (Hashable)
import           Data.HashMap.Strict     (HashMap)
import qualified Data.HashMap.Strict     as HM
import Data.Array (Array, Ix)
import qualified Data.Array as A



toSeqType :: forall f k v. (Functor f, ToPatchType f k v v) => Proxy k -> f v -> (SeqType f k (SeqTypeKey f k v) Identity)
toSeqType pk = withFunctorToSeqType pk (Proxy :: Proxy v) . fmap Identity

-- | Generalize distributeMapOverDynPure
distributeOverDynPure :: forall t f k v. ( R.Reflex t
                                         , ToPatchType f k v v
                                         , SequenceablePatch (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k v)
                                         , ReflexSequenceable ((SeqType f k) (SeqTypeKey f k v)))
  => Proxy k -> f (R.Dynamic t v) -> R.Dynamic t (f v)
distributeOverDynPure pk =
  let pv = Proxy :: Proxy v
  in fmap (fromSeqType pk pv) . traverseDynamic . (withFunctorToSeqType pk pv)

-- | Generalizes "mergeMap" to anything with ToPatchType where the Patches are Sequenceable.
mergeOver :: forall t f k v. ( R.Reflex t
                             , ToPatchType f k (R.Event t v) v
                             , SequenceablePatch (SeqType f k) (SeqPatchType f k) (SeqTypeKey f k v)
                             , ReflexSequenceable ((SeqType f k) (SeqTypeKey f k v)))
  => Proxy k -> f (R.Event t v) -> R.Event t (f v)
mergeOver pk fEv =
  let id2 = const id :: (k -> R.Event t v -> R.Event t v)
  in fmap (fromSeqType pk (Proxy :: Proxy (R.Event t v))) . mergeEvents $ toSeqTypeWithFunctor id2 fEv


-- This class has the capabilities to translate f v and its difftype into types that are sequenceable, and then bring the original type back
-- This requires that the Diff type be mapped to the correct type for diffing at the sequenceable level (e.g., as a DMap).
class KeyMappable f k v => ToPatchType (f :: Type -> Type) k v a where
  type Diff f k :: Type -> Type
  type SeqType f k :: (Type -> Type) -> (Type -> Type) -> Type
  type SeqPatchType f k :: (Type -> Type) -> (Type -> Type) -> Type
  type SeqTypeKey f k a :: Type -> Type
  withFunctorToSeqType :: Functor g => Proxy k -> Proxy v -> f (g a) -> SeqType f k (SeqTypeKey f k a) g
  fromSeqType :: Proxy k -> Proxy v -> SeqType f k (SeqTypeKey f k a) Identity -> f a
  
  toSeqTypeWithFunctor :: Functor g => (k -> v -> g a) -> f v -> SeqType f k (SeqTypeKey f k a) g
  toSeqTypeWithFunctor h = withFunctorToSeqType (Proxy :: Proxy k) (Proxy :: Proxy v) . mapWithKey h 

  makePatchSeq :: Functor g => Proxy f -> (k -> v -> g a) -> Diff f k v -> SeqPatchType f k (SeqTypeKey f k a) g


instance Ord k => ToPatchType (Map k) k v a where
  type Diff (Map k) k = Map k (Maybe v)
  type SeqType (Map k) k = DMap
  type SeqPatchType (Map k) k = PatchDMap
  type SeqTypeKey (Map k) k a = Const2 k a
  withFunctorToSeqType _ _ = mapWithFunctorToDMap
  makePatchSeq _ h = PatchDMap . mapWithFunctorToDMap . mapWithKey (\k mv -> ComposeMaybe $ (fmap h k) mv)
  fromSeqType _ _ = dmapToMap

  
  
