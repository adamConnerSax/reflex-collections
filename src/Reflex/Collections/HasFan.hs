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

import Reflex.Collections.ToPatchType (toSeqType, MapDiff)

import qualified Reflex                 as R
import           Data.Functor.Misc      (Const2 (..))
import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)
import           Data.Functor.Compose (Compose (..))

import           Data.Map               (Map)
import qualified Data.Map               as M
import           Data.IntMap            (IntMap)
import qualified Data.IntMap            as IM
import           Data.Hashable          (Hashable)
import           Data.HashMap.Strict    (HashMap)
import qualified Data.HashMap.Strict    as HM
import           Data.Array             (Array, Ix)


class HasFan (f :: Type -> Type) v where
  type FanInKey f :: Type
  type FanSelKey f v :: Type -> Type
  makeSelKey :: Proxy f -> Proxy v -> FanInKey f -> FanSelKey f v v
  doFan :: R.Reflex t => Proxy v -> R.Event t (f v) -> R.EventSelector t (FanSelKey f v)

instance Ord k => HasFan (Map k) v where
  type FanInKey (Map k) = k
  type FanSelKey (Map k) v = Const2 k v
  makeSelKey _ _ = Const2
  doFan _ = R.fan . fmap (toSeqType (Proxy :: Proxy k))

instance (Ord k, Hashable k) => HasFan (HashMap k) v where
  type FanInKey (HashMap k) = k
  type FanSelKey (HashMap k) v = Const2 k v
  makeSelKey _ _ = Const2
  doFan _ = R.fan . fmap (toSeqType (Proxy :: Proxy k))

instance HasFan IntMap v where
  type FanInKey IntMap = Int
  type FanSelKey IntMap v = Const2 Int v
  makeSelKey _ _ = Const2
  doFan _ = R.fan . fmap (toSeqType (Proxy :: Proxy Int))

instance Ord k => HasFan (MapDiff (Map k)) v where
  type FanInKey (MapDiff (Map k)) = k
  type FanSelKey (MapDiff (Map k)) v = Const2 k v
  makeSelKey _ _ = Const2
  doFan _ = R.fan . fmap (toSeqType (Proxy :: Proxy k) . (M.mapMaybe id)  . getCompose)

instance (Ord k, Hashable k) => HasFan (MapDiff (HashMap k)) v where
  type FanInKey (MapDiff (HashMap k)) = k
  type FanSelKey (MapDiff (HashMap k)) v = Const2 k v
  makeSelKey _ _ = Const2
  doFan _ = R.fan . fmap (toSeqType (Proxy :: Proxy k) . (HM.mapMaybe id)  . getCompose)

instance HasFan (MapDiff IntMap) v where
  type FanInKey (MapDiff IntMap) = Int
  type FanSelKey (MapDiff IntMap) v = Const2 Int v
  makeSelKey _ _ = Const2
  doFan _ = R.fan . fmap (toSeqType (Proxy :: Proxy Int) . (IM.mapMaybe id)  . getCompose)

instance (Ix k, Ord k) => HasFan (Array k) v where
  type FanInKey (Array k) = k
  type FanSelKey (Array k) v = Const2 k v
  makeSelKey _ _ = Const2
  doFan _ = R.fan . fmap (toSeqType (Proxy :: Proxy k))

