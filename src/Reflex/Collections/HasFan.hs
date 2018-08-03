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

import Reflex.Collections.ToPatchType (ToPatchType(..), toSeqType)

import qualified Reflex                 as R
import           Data.Functor.Misc      (Const2 (..))
import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)
import           Data.Dependent.Map     (DMap, GCompare)

import           Data.Map               (Map)
import           Data.IntMap            (IntMap)
import           Data.Hashable          (Hashable)
import           Data.HashMap.Strict    (HashMap)
import           Data.Array             (Array, Ix)


class HasFan (f :: Type -> Type) v where
  type FanInKey f :: Type
  type FanSelKey f v :: Type -> Type
  makeSelKey :: Proxy f -> Proxy v -> FanInKey f -> FanSelKey f v v
  doFan :: R.Reflex t => Proxy v -> R.Event t (f v) -> R.EventSelector t (FanSelKey f v)
  default doFan :: ( R.Reflex t
                   , Functor f
                   , ToPatchType f (FanInKey f) v v
                   , SeqType f (FanInKey f)  ~ DMap
                   , SeqTypeKey f (FanInKey f) v ~ FanSelKey f v
                   , GCompare (FanSelKey f v))
                => Proxy v -> R.Event t (f v) -> R.EventSelector t (FanSelKey f v)
  doFan _ = R.fan . fmap (toSeqType (Proxy :: Proxy (FanInKey f)))

instance (Ord k) => HasFan (Map k) v where
  type FanInKey (Map k) = k
  type FanSelKey (Map k) v = Const2 k v
  makeSelKey _ _ = Const2

instance (Ord k, Hashable k) => HasFan (HashMap k) v where
  type FanInKey (HashMap k) = k
  type FanSelKey (HashMap k) v = Const2 k v
  makeSelKey _ _ = Const2

instance HasFan IntMap v where
  type FanInKey IntMap = Int
  type FanSelKey IntMap v = Const2 Int v
  makeSelKey _ _ = Const2

instance (Ix k, Ord k) => HasFan (Array k) v where
  type FanInKey (Array k) = k
  type FanSelKey (Array k) v = Const2 k v
  makeSelKey _ _ = Const2
--  doFan _ = R.fan . fmap toSeqType

