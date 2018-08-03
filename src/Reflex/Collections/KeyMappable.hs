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
   KeyMappable (..)
  ) where

import           Data.Dependent.Map     (DMap, GCompare)
import           Data.Kind              (Type)

import qualified Data.Map as M
import           Data.Hashable (Hashable)
import qualified Data.HashMap as HM
import qualified Data.IntMap  as IM
import qualified Data.Array as A


-- recover the ability to map with the key as input
class KeyMappable (f :: Type -> Type) k v where
  mapWithKey :: (k -> v -> a) -> f v -> f a

instance Ord k => KeyMappable (M.Map k) k v where
  mapWithKey = M.mapWithey

instance Hashable k => KeyMappable (HM.HashMap k) k v where
  mapWithKey = HM.mapWithKey

instance KeyMappable IM.IntMap Int v where
  mapWithKey = IM.mapWithKey

instance A.Ix k => KeyMappable (Array k) k v where
  mapWithKey = arrayMapWithKey

arrayMapWithKey :: A.Ix k => (k -> v -> a) -> A.Array k v -> A.Array k a
arrayMapWithKey h arr =
  let kvPairs = A.assocs arr
      mapped = (\(k,v) -> (k, h k v)) <$> kvPairs
      indices = fst <$> kvPairs
      bounds = (minimum indices, maximum indices)
  in A.array bounds mapped
    
