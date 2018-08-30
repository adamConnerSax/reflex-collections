{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeOperators              #-}
module Reflex.Collections.WithEmpty
  (
    WithEmpty (..)
  , withEmptyToMaybe
  ) where

import Reflex.Collections.KeyedCollection (KeyedCollection(..))
import Reflex.Collections.Diffable (MapLike(..), Diffable(..))
import Reflex.Collections.ToPatchType (SeqTypes(..), ToPatchType(..))

import Reflex (fmapMaybe)
import Data.Proxy (Proxy(..))
import Data.Kind (Type)
import Data.Functor.Identity (Identity)
import Data.Constraint (Dict(Dict), (:-)(Sub))
import Data.Constraint.Forall (Forall, inst)

data WithEmpty (f :: Type -> Type) (a :: Type) = Empty | NonEmpty (f a)

instance Functor f => Functor (WithEmpty f) where
  fmap _ Empty = Empty
  fmap g (NonEmpty t) = NonEmpty $ fmap g t

instance Foldable f => Foldable (WithEmpty f) where
  foldMap _ Empty = mempty
  foldMap f (NonEmpty x) = foldMap f x

instance Show (f a) => Show (WithEmpty f a) where
  show Empty = "Empty"
  show (NonEmpty x) = "NonEmpty (" ++ show x ++ ")"

withEmptyToMaybe :: WithEmpty f a -> Maybe (f a)
withEmptyToMaybe Empty = Nothing
withEmptyToMaybe (NonEmpty x) = Just x

instance KeyedCollection f => KeyedCollection (WithEmpty f) where
  type Key (WithEmpty f) = Key f
  mapWithKey _ Empty = Empty
  mapWithKey h (NonEmpty t) = NonEmpty $ mapWithKey h t
  toKeyValueList Empty = []
  toKeyValueList (NonEmpty t) = toKeyValueList t
  fromKeyValueList [] = Empty
  fromKeyValueList kvs = NonEmpty $ fromKeyValueList kvs
  
instance (Diffable f, MapLike (Diff f)) => Diffable (WithEmpty f) where
  type Diff (WithEmpty f) = Diff f
  toDiff Empty = mlEmpty
  toDiff (NonEmpty t) = toDiff t
  fromFullDiff d = if mlNull d then Empty else NonEmpty $ fromFullDiff d
  diffNoEq = liftDiff diffNoEq
  diff = liftDiff diff
  diffOnlyKeyChanges = liftDiff diffOnlyKeyChanges

liftDiff :: (Diffable f, MapLike (Diff f)) => (f v -> f v -> Diff f (Maybe v)) -> WithEmpty f v -> WithEmpty f v -> Diff f (Maybe v)
liftDiff _ Empty Empty = mlEmpty
liftDiff _ Empty (NonEmpty new) = Just <$> toDiff new
liftDiff _ (NonEmpty old) Empty = const Nothing <$> toDiff old
liftDiff dF (NonEmpty old) (NonEmpty new) = dF old new 

instance SeqTypes f v => SeqTypes (WithEmpty f) v where
  type SeqType (WithEmpty f) v = SeqType f v 
  type SeqPatchType (WithEmpty f) v = SeqPatchType f v
  emptySeq _ = emptySeq (Proxy :: Proxy f)
  nullSeq _ = nullSeq (Proxy :: Proxy f)

-- The following use of Data.Constraint.Forall seems necessary here.
-- Without it, GHC cannot resolve the SeqTypes f v constraint.  Which it needs to call typeclass methods in `SeqTypes (With f) v`
-- This will all be much nicer with quantified constraints.
instance (MapLike (Diff f), ToPatchType f, Forall (SeqTypes f)) => ToPatchType (WithEmpty f) where
  type FanKey (WithEmpty f) = FanKey f
  {-# INLINABLE withFunctorToSeqType #-}
  withFunctorToSeqType (Empty :: WithEmpty f (g v))  = emptySeq (Proxy :: Proxy (WithEmpty f)) (Proxy :: Proxy v) (Proxy :: Proxy (g :: Type -> Type))
  withFunctorToSeqType (NonEmpty t :: WithEmpty f (g v)) =
    case inst :: Forall (SeqTypes f) :- SeqTypes f v of
      Sub Dict -> withFunctorToSeqType t
  {-# INLINABLE makePatchSeq #-}
  makePatchSeq _ h = makePatchSeq (Proxy :: Proxy f) h
  {-# INLINABLE fromSeqType #-}     
  fromSeqType _ = fromSeqType (Proxy :: Proxy f)   
  {-# INLINABLE unsafeFromSeqType #-}
  unsafeFromSeqType = go where
    go :: forall a. SeqType (WithEmpty f) a Identity -> (WithEmpty f) a   -- a signature required here to scope the 'a'
    go x = case (inst :: Forall (SeqTypes f) :- SeqTypes f a) of
      Sub Dict -> if nullSeq (Proxy :: Proxy (WithEmpty f)) (Proxy :: Proxy a) x then Empty else NonEmpty $ unsafeFromSeqType x
  {-# INLINABLE makeFanKey #-}  
  makeFanKey _ pv = makeFanKey (Proxy :: Proxy f) pv
  {-# INLINABLE doFan #-}  
  doFan =  doFan . fmapMaybe withEmptyToMaybe  
  {-# INLINABLE diffToFanType #-}  
  diffToFanType _ = diffToFanType (Proxy :: Proxy f)

  

  
