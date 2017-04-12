{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE RecursiveDo           #-}
{-# LANGUAGE ScopedTypeVariables   #-}
module Reflex.Dom.Contrib.ListHoldFunctions.Lens where

import qualified Reflex as R
import qualified Reflex.Dom as RD

import Control.Lens
import Control.Lens.At


-- can we express, with a constraint, that v and v' are related in a way that allows (Index (f v) -> v -> m a) to operate on v' ?
-- how do we do the sequencing/traversing?
-- We want to pull the m out of the final dynamic.  

listHoldWithIxLens'::(Ixed (f v), Ixed (q v'), Index (f v) ~ Index (q v'), IxValue (f v) ~ v)
  => Lens' (f v) (q v') -> (v' -> v) -> f v -> R.Event t (q v') -> (Index (f v) -> v -> m a) -> R.Dynamic t (f (m a))
listHoldWithIxLens' c0 (diffLens, diffData) widgetF = do
  let c0' = over each mapC c0
      cEv = traverseOf mapDiff




{-
listHoldWithLens'::f v
                 -> R.Event t (Lens' (f v) q, q)
                 -> (Lens' (f v) v -> (Lens' (f (m a)) (m a), m a))
                 -> (Lens' q v -> (Lens' m a) -> R.Dynamic t (f (m a))

listHoldWithLens' =
-}
