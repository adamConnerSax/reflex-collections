{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE PatternSynonyms  #-}
{-# LANGUAGE DefaultSignatures #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.KeyedCollection
  (
    KeyedCollection (..)
  ) where

import           Data.Kind             (Type)
                                       
import qualified Data.Map              as M
import           Data.Hashable         (Hashable)
import qualified Data.HashMap.Strict   as HM
import qualified Data.IntMap           as IM
import qualified Data.Array            as A
import qualified Data.Sequence         as S
import           Data.Sequence         (ViewR(..))
import qualified Data.Tree             as T
import qualified Data.Key              as K
import           Data.List            (groupBy, sortBy)
import           Data.Monoid          ()

class (Functor f, K.Keyed f, K.FoldableWithKey f) => KeyedCollection (f :: Type -> Type) where
  type Key f :: Type
  mapWithKey :: (Key f -> a -> b) -> f a -> f b
  default mapWithKey :: (Key f ~ K.Key f) => (Key f -> a -> b) -> f a -> f b
  mapWithKey = K.mapWithKey
  toKeyValueList :: f v -> [(Key f, v)]
  default toKeyValueList :: (K.Key f ~ Key f) => f v -> [(Key f, v)]
  toKeyValueList = K.toKeyedList
  fromKeyValueList :: [(Key f ,v)] -> f v -- assumes Keys are distinct
  
  
instance Ord k => KeyedCollection (M.Map k) where
  type Key (M.Map k) = k
  fromKeyValueList = M.fromList

instance (Eq k, Hashable k) => KeyedCollection (HM.HashMap k) where
  type Key (HM.HashMap k) = k
  fromKeyValueList = HM.fromList
  
instance KeyedCollection IM.IntMap where
  type Key IM.IntMap = Int
  fromKeyValueList = IM.fromList

instance A.Ix k => KeyedCollection (A.Array k) where
  type Key (A.Array k) = k
  fromKeyValueList = arrayFromKeyValueList -- NB: this will be undefined at any key in the range missing from the list

arrayFromKeyValueList :: A.Ix k => [(k,v)] -> A.Array k v
arrayFromKeyValueList l = let keys = fst <$> l in A.array (minimum keys, maximum keys) l
{-# INLINABLE arrayFromKeyValueList #-}
  
instance KeyedCollection [] where
  type Key [] = Int
  fromKeyValueList = fmap snd

instance KeyedCollection S.Seq where
  type Key S.Seq = Int
  fromKeyValueList = S.fromList . fmap snd

instance KeyedCollection T.Tree where
  type Key T.Tree = S.Seq Int
  -- kvl can't be empty because the tree can't.
  -- removeTail is the sequence equivalent of inits
  -- sameTail checks if last element of the sequences is the same
  -- this groups the list by the tail of the key, uses the head of the result to make a node with a forest fromt the groups
  -- initial sort is required since the required order is the reverse of the ORD order. TODO: We can fix?
  fromKeyValueList kvl = go $ sortBy compareKey kvl where
    go ((_ , x) : kvs) = T.Node x  $ fmap (go . fmap removeKeyTail) $ groupBy sameTail kvs 
    removeKeyTail (k, y) = let inits :> _ = S.viewr k in (inits, y)
    compareKey (k1 , _) (k2 , _) = compare (S.reverse k1) (S.reverse k2)
    sameTail :: (S.Seq Int, a) -> (S.Seq Int, a) -> Bool
    sameTail (k1,_) (k2,_) = case S.viewr k1 of
      _ :> n  -> case S.viewr k2 of
        _ :> m -> n == m
        _        -> False
      EmptyR    -> case S.viewr k2 of
        EmptyR -> True
        _      -> False
  
