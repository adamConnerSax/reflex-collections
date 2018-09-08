{-# LANGUAGE CPP                   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
#ifdef USE_REFLEX_OPTIMIZER
{-# OPTIONS_GHC -fplugin=Reflex.Optimizer #-}
#endif
module Reflex.Collections.Sequenceable
  (
    ReflexMergeable (..)
  , PatchSequenceable(..)
  , ReflexSequenceable(..)
  , DMapConst2 (..)
  , PatchDMapConst2 (..)
  ) where

import qualified Reflex                 as R
import           Reflex.Patch           (PatchDMap (..))

import Reflex.Collections.ComposedIntMap ( ComposedIntMap(..)
                                         , ComposedPatchIntMap(..))

import           Data.Dependent.Map     (DMap, GCompare)
import           Data.Functor.Misc      (Const2 (..))
import           Control.Monad.Identity (Identity (..))
import           Data.Kind              (Type)
import qualified Data.IntMap            as IM
import           Data.Functor.Compose   (Compose(..), getCompose)
import           Data.Constraint ((:-)(Sub), Dict(Dict))
import           Data.Constraint.Forall (ForallF, instF)

-- | This class carries the ability to do an efficient event merge
-- "Merge a collection of events.  The resulting event will occur if at least one input event is occuring
-- and will contain all simultaneously occurring events."
class ReflexMergeable (f :: Type -> (Type -> Type) -> Type) where
  mergeEvents :: R.Reflex t => f a (R.Event t) -> R.Event t (f a Identity)


-- we lose some power by narrowing the classes below to the Const2 case.  We will need new instances
-- for other DMap keys.  But we gain constraint simplification, effectively quantifying over the element type.
-- Once quantified constraints are usable in all versions of GHC we want to support we could
-- probably fix these.
-- As it is, we need to quantify the GCompare (Const2 k a) constraint. Which we do via the constraints package.
newtype DMapConst2 k a f = DMapConst2  { unDMapConst2 :: DMap (Const2 k a) f }
newtype PatchDMapConst2 k a f = PatchDMapConst2 { unPatchDMapConst2 :: PatchDMap (Const2 k a) f }

instance (Ord k, ForallF GCompare (Const2 k)) => ReflexMergeable (DMapConst2 k) where
  {-# INLINABLE mergeEvents #-}
  mergeEvents :: forall t a. R.Reflex t => DMapConst2 k a (R.Event t) -> R.Event t (DMapConst2 k a Identity)
  mergeEvents =
    case instF :: ForallF GCompare (Const2 k) :- GCompare (Const2 k a) of
      Sub Dict -> fmap DMapConst2 . R.merge . unDMapConst2

instance ReflexMergeable ComposedIntMap where
  {-# INLINABLE mergeEvents #-}
  mergeEvents = fmap (ComposedIntMap . Compose . fmap Identity) . R.mergeInt . getCompose  . unCI


-- | This class carries the ability to sequence patches in the way of MonadAdjust And then turn the result into a Dynamic.
-- sequenceWithPatch takes a static d containing adjustable (m a), e.g., widgets, and event carrying patches, that is
-- new widgets for some keys k, and "pulls out" (sequences) the m.
-- patchPairToDynamic is a sort of inverse, turning a static d containing values and events with patches to it, new values at some keys,
-- and returns an adjustable monad containing a Dynamic of a value containing d.
-- |
class PatchSequenceable (d :: Type -> (Type -> Type) -> Type) (pd :: Type -> (Type -> Type) -> Type)  where
  sequenceWithPatch :: R.Adjustable t m => d a m -> R.Event t (pd a m) -> m (d a Identity, R.Event t (pd a Identity))
  patchPairToDynamic :: (R.MonadHold t m, R.Reflex t) => d a Identity -> R.Event t (pd a Identity) -> m (R.Dynamic t (d a Identity))

-- | DMap (Const2 k a) and IntMap a are our prime examples of something sequenceable
instance (Ord k, ForallF GCompare (Const2 k), Ord k) => PatchSequenceable (DMapConst2 k) (PatchDMapConst2 k) where
  {-# INLINABLE sequenceWithPatch #-}
  sequenceWithPatch :: forall t m a. R.Adjustable t m
    => DMapConst2 k a m
    -> R.Event t (PatchDMapConst2 k a m)
    -> m (DMapConst2 k a Identity, R.Event t (PatchDMapConst2 k a Identity))
  sequenceWithPatch dmc2 pdmc2Ev =
    case instF :: ForallF GCompare (Const2 k) :- GCompare (Const2 k a) of 
      Sub Dict -> fmap (\(dm, pdEv) -> (DMapConst2 dm, fmap PatchDMapConst2 pdEv)) $ R.sequenceDMapWithAdjust (unDMapConst2 dmc2) (unPatchDMapConst2 <$> pdmc2Ev)

  {-# INLINABLE patchPairToDynamic #-} 
  patchPairToDynamic :: forall t m a. (R.MonadHold t m, R.Reflex t)
    => DMapConst2 k a Identity
    -> R.Event t (PatchDMapConst2 k a Identity)
    -> m (R.Dynamic t (DMapConst2 k a Identity))
  patchPairToDynamic a0 a' =
    case instF :: ForallF GCompare (Const2 k) :- GCompare (Const2 k a) of
      Sub Dict -> fmap DMapConst2 <$> R.incrementalToDynamic <$> R.holdIncremental (unDMapConst2 a0) (unPatchDMapConst2 <$> a')


instance PatchSequenceable ComposedIntMap ComposedPatchIntMap where
  {-# INLINABLE sequenceWithPatch #-}  
  sequenceWithPatch :: R.Adjustable t m
                    => ComposedIntMap a m
                    -> R.Event t (ComposedPatchIntMap a m)
                    -> m (ComposedIntMap a Identity, R.Event t (ComposedPatchIntMap a Identity))
  sequenceWithPatch (ComposedIntMap ci) cpEv =
    let f (im, pim) = (ComposedIntMap . Compose $ im, fmap (ComposedPatchIntMap . Compose) pim)
    in f <$> R.traverseIntMapWithKeyWithAdjust (\_ -> fmap Identity) (getCompose ci) (fmap (getCompose . unCPI) cpEv) 

  {-# INLINABLE patchPairToDynamic #-} 
  patchPairToDynamic :: (R.MonadHold t m, R.Reflex t)
                     => ComposedIntMap a Identity
                     -> R.Event t (ComposedPatchIntMap a Identity)
                     -> m (R.Dynamic t (ComposedIntMap a Identity))
  patchPairToDynamic a0 a' = R.incrementalToDynamic <$> R.holdIncremental a0 a'


class ReflexSequenceable (f :: Type -> (Type -> Type) -> Type) where  
  sequenceDynamic :: R.Reflex t => f a (R.Dynamic t) -> R.Dynamic t (f a Identity)

instance (Ord k, ForallF GCompare (Const2 k)) => ReflexSequenceable (DMapConst2 k) where
  {-# INLINABLE sequenceDynamic #-}
  sequenceDynamic :: forall t a. R.Reflex t => DMapConst2 k a (R.Dynamic t) -> R.Dynamic t (DMapConst2 k a Identity)
  sequenceDynamic =
    case instF :: ForallF GCompare (Const2 k) :- GCompare (Const2 k a) of
      Sub Dict -> fmap DMapConst2 . R.distributeDMapOverDynPure . unDMapConst2 

instance ReflexSequenceable ComposedIntMap where
  {-# INLINABLE sequenceDynamic #-}
  sequenceDynamic cim =
    let im = (getCompose . unCI $ cim) 
    in case IM.toList im of 
      [] -> fmap (ComposedIntMap . Compose) $ R.constDyn IM.empty
      [(n, v)] -> fmap (ComposedIntMap . Compose . IM.singleton n . Identity) v
      _ ->
        let getInitial = IM.traverseWithKey (\_ -> fmap Identity . R.sample . R.current) im
            edmPre = fmap (fmap Identity) . R.mergeInt $ IM.map R.updated im
            result = R.unsafeBuildDynamic getInitial $ flip R.pushAlways edmPre $ \news -> do
              olds <- R.sample $ R.current result
              return $ IM.unionWithKey (\_ _ new -> new) olds news
        in fmap (ComposedIntMap . Compose) result


