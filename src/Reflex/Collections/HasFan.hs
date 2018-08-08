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
{-# LANGUAGE DefaultSignatures     #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.HasFan
  (
    HasFan(..)
  ) where

import Reflex.Collections.ToPatchType (toSeqType, MapDiff, DMappable(..))
import Reflex.Collections.KeyedCollection (KeyedCollection(Key))
import Reflex.Collections.DMapIso (DMapIso(..))

import qualified Reflex                 as R
import           Data.Functor.Misc      (Const2 (..))
import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)
import           Data.Functor.Compose  (Compose (..))
import           Data.Dependent.Map    (GCompare)

import           Data.Map               (Map)
import qualified Data.Map               as M
import           Data.IntMap            (IntMap)
import qualified Data.IntMap            as IM
import           Data.Hashable          (Hashable)
import           Data.HashMap.Strict    (HashMap)
import qualified Data.HashMap.Strict    as HM
import           Data.Array             (Array, Ix)


class HasFan (f :: Type -> Type) where
  type FanInKey f :: Type
  type FanSelKey f :: Type -> Type -> Type
  makeSelKey :: Proxy f -> Proxy v -> FanInKey f -> FanSelKey f v v
  doFan :: R.Reflex t => R.Event t (f v) -> R.EventSelector t (FanSelKey f v)

instance HasFan f => HasFan (DMappable f) where
  type FanInKey (DMappable f) = FanInKey f
  type FanSelKey (DMappable f) = FanSelKey f
  makeSelKey = makeSelKey
  doFan = doFan . fmap unDMappable

instance Ord k => HasFan (Map k) where
  type FanInKey (Map k) = k
  type FanSelKey (Map k) = Const2 k
  makeSelKey _ _ = Const2
  doFan = R.fan . fmap (toSeqType . DMappable)

instance (Ord k, Hashable k) => HasFan (HashMap k) where
  type FanInKey (HashMap k) = k
  type FanSelKey (HashMap k) = Const2 k
  makeSelKey _ _ = Const2
  doFan = R.fan . fmap (toSeqType . DMappable)

instance HasFan IntMap where
  type FanInKey IntMap = Int
  type FanSelKey IntMap = Const2 Int
  makeSelKey _ _ = Const2
  doFan = R.fan . fmap (toSeqType . DMappable)

instance Ord k => HasFan (MapDiff (Map k)) where
  type FanInKey (MapDiff (Map k)) = k
  type FanSelKey (MapDiff (Map k)) = Const2 k
  makeSelKey _ _ = Const2
  doFan = R.fan . fmap (toSeqType . DMappable . (M.mapMaybe id)  . getCompose)

instance (Ord k, Hashable k) => HasFan (MapDiff (HashMap k)) where
  type FanInKey (MapDiff (HashMap k)) = k
  type FanSelKey (MapDiff (HashMap k)) = Const2 k
  makeSelKey _ _ = Const2
  doFan = R.fan . fmap (toSeqType . DMappable . (HM.mapMaybe id)  . getCompose)

instance HasFan (MapDiff IntMap) where
  type FanInKey (MapDiff IntMap) = Int
  type FanSelKey (MapDiff IntMap) = Const2 Int
  makeSelKey _ _ = Const2
  doFan = R.fan . fmap (toSeqType . DMappable . (IM.mapMaybe id)  . getCompose)

instance (Ix k, Ord k) => HasFan (Array k) where
  type FanInKey (Array k) = k
  type FanSelKey (Array k) = Const2 k
  makeSelKey _ _ = Const2
  doFan = R.fan . fmap (toSeqType . DMappable)


