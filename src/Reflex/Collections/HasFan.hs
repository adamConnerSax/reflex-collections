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

--import Reflex.Collections.ToPatchType (DMappable(..))
import Reflex.Collections.Diffable (ArrayDiff(..), MapDiff)
import Reflex.Collections.DMapIso (DMapIso(..))

import qualified Reflex                 as R
import           Data.Functor.Misc      (Const2 (..))

import qualified Data.Dependent.Map     as DM
import           Data.Proxy             (Proxy (..))
import           Data.Kind              (Type)
import           Data.Functor.Compose   (Compose (..))
import           Data.Dependent.Map     (GCompare)
import           Data.Functor.Identity  (Identity(..))
import           Data.Witherable        (Filterable(..))

import           Data.Map               (Map)
import           Data.IntMap            (IntMap)
import           Data.Hashable          (Hashable)
import           Data.HashMap.Strict    (HashMap)
import           Data.Array             (Array, Ix)


class HasFan (f :: Type -> Type) where
  type FanInKey f :: Type
  type FanSelKey f :: Type -> Type -> Type
  makeSelKey :: Proxy f -> Proxy v -> FanInKey f -> FanSelKey f v v
  doFan :: GCompare (FanSelKey f v) => R.Reflex t => R.Event t (f v) -> R.EventSelector t (FanSelKey f v)

-- these all flow from DMapIso but we can't instance them directly that way otherwise we will get overlapping instances
-- and we need them for the more general versions, which don't have a DMapIso constraint
instance Ord k => HasFan (Map k) where
  type FanInKey (Map k) = k
  type FanSelKey (Map k) = Const2 k
  makeSelKey _ _ = Const2
  doFan = R.fan . fmap (toDMapWithFunctor . fmap Identity)

instance (Ord k, Hashable k) => HasFan (HashMap k) where
  type FanInKey (HashMap k) = k
  type FanSelKey (HashMap k) = Const2 k
  makeSelKey _ _ = Const2
  doFan = R.fan . fmap (toDMapWithFunctor . fmap Identity)

instance HasFan IntMap where
  type FanInKey IntMap = Int
  type FanSelKey IntMap = Const2 Int
  makeSelKey _ _ = Const2
  doFan = R.fan . fmap (toDMapWithFunctor . fmap Identity)

instance (HasFan f, Filterable f, DMapIso f, DMapKey f ~ FanSelKey f) => HasFan (MapDiff f) where
  type FanInKey (MapDiff f) = FanInKey f
  type FanSelKey (MapDiff f) = FanSelKey f
  makeSelKey _ = makeSelKey (Proxy :: Proxy f)
  doFan = R.fan . fmap (toDMapWithFunctor . fmap Identity . (mapMaybe id)  . getCompose)

instance (Ix k, Ord k) => HasFan (Array k) where
  type FanInKey (Array k) = k
  type FanSelKey (Array k) = Const2 k
  makeSelKey _ _ = Const2
  doFan = R.fan . fmap (toDMapWithFunctor . fmap Identity) 

instance (Ix k, Ord k) => HasFan (ArrayDiff k) where
  type FanInKey (ArrayDiff k) = k
  type FanSelKey (ArrayDiff k) = Const2 k
  makeSelKey _ _ = Const2
  doFan = R.fan . fmap (DM.fromList . fmap (\(k,v) -> Const2 k DM.:=> Identity v) . unArrayDiff)







