{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
module Main where
import           Control.Monad                      (replicateM)
import           Data.Array                         (Array, Ix, listArray)
import           Data.IntMap                        (IntMap)
import qualified Data.Key                           as K
import           Data.Map                           (Map)
import           Data.Proxy                         (Proxy (..))
import           Data.Sequence                      (Seq)
import           Data.Tree                          (Tree)

import           Reflex.Collections.Diffable        (Diff, Diffable (..),
                                                     SetLike (..))
import           Reflex.Collections.KeyedCollection (KeyedCollection (..))
import           Reflex.Collections.WithEmpty       (WithEmpty (..))
import           Test.Hspec
import           Test.Invariant
import           Test.QuickCheck                    hiding (NonEmpty)
import           Test.QuickCheck.Instances
import           Text.Show.Functions

prop_KC_mapPreservesKeys :: (Eq k, KeyedCollection f, k ~ Key f) => (k -> a -> b) -> f a -> Bool
prop_KC_mapPreservesKeys g f =
  let keys = fmap fst . toKeyValueList
  in keys f == keys (mapWithKey g f)

equalKC :: (KeyedCollection f , Eq (Key f) , Eq a) => f a -> f a -> Bool
equalKC a b = (toKeyValueList a) == (toKeyValueList b)

emptyKC :: KeyedCollection f => f a -> Bool
emptyKC = null . toKeyValueList

prop_KC_keyValueListIso :: forall f a k. (KeyedCollection f, k ~ Key f, Eq k, Eq a) => f a -> Bool
prop_KC_keyValueListIso c =
  let asList = toKeyValueList c
  in equalKC asList $ (toKeyValueList . (fromKeyValueList :: [(k, a)] -> f a) $ asList)

prop_SetLike_FilterAll :: (KeyedCollection f, SetLike f) => f a -> Bool
prop_SetLike_FilterAll  = emptyKC . slFilter (const False)

prop_SetLike_DiffSelf :: (KeyedCollection f, SetLike f) => f a -> Bool
prop_SetLike_DiffSelf a = emptyKC $ slDifference a a

prop_SetLike_UnionAfterDifference :: (KeyedCollection f, SetLike f, Eq a, Eq (Key f)) => f a -> f a -> Bool
prop_SetLike_UnionAfterDifference a b = equalKC (slUnion a b) (slUnion a (slDifference b a))

prop_Diffable_DiffIso :: (Eq (Key f), Eq a, Diffable f) => f a -> Bool
prop_Diffable_DiffIso a = equalKC a (fromCompleteKeyValueSet $ toKeyValueSet a)

prop_Diffable_DiffLawNoEq :: (Diffable f, Eq a, Eq (Key f)) => f a -> f a -> Bool
prop_Diffable_DiffLawNoEq a b = equalKC b (applyDiff (diffNoEq a b) a)

prop_Diffable_DiffLaw :: (Diffable f, Eq a, Eq (Key f)) => f a -> f a -> Bool
prop_Diffable_DiffLaw a b = equalKC b (applyDiff (diff a b) a)

-- an array that must have values for all keys
newtype TotalArray k a = TotalArray { unTA :: Array k a } deriving (Functor, Show, Foldable, K.Keyed)

type instance K.Key (TotalArray k) = K.Key (Array k)

instance Ix k => K.FoldableWithKey (TotalArray k) where
  foldMapWithKey h (TotalArray a) = K.foldMapWithKey h a

instance Ix k => KeyedCollection (TotalArray k) where
  type Key (TotalArray k) = Key (Array k)
  mapWithKey h = TotalArray . mapWithKey h . unTA
  toKeyValueList = toKeyValueList . unTA
  fromKeyValueList = TotalArray . fromKeyValueList

instance (Enum k, Bounded k, Ord k, Ix k) => Diffable (TotalArray k) where
  type KeyValueSet (TotalArray k) = KeyValueSet (Array k)
  toKeyValueSet = toKeyValueSet . unTA
  fromCompleteKeyValueSet = TotalArray . fromCompleteKeyValueSet
  applyDiff d old = TotalArray $ applyDiff d (unTA old)
  diffNoEq old new = diffNoEq (unTA old) (unTA new)
  diffOnlyKeyChanges old new = diffOnlyKeyChanges (unTA old) (unTA new)
  editDiffLeavingDeletes _ d kv = editDiffLeavingDeletes (Proxy :: Proxy (Array k)) d kv

-- the Arbitrary instance for Array uses a random contiguous subset of indices.  We need them all.
-- We generate an arbitrary list of values of the right length and then fmap to get a TotalArray
instance (Arbitrary k, Bounded k, Enum k, Ix k, Arbitrary a) => Arbitrary (TotalArray k a) where
  arbitrary = fmap (TotalArray . listArray (minBound, maxBound)) $ replicateM (length [(minBound :: k) .. (maxBound :: k)]) arbitrary

data ArrayKeys = A | B | C | D | E | F deriving (Show, Bounded, Enum, Ord, Eq, Ix)
instance Arbitrary ArrayKeys where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary (f a) => Arbitrary (WithEmpty f a) where
  arbitrary = withEmptyFromMaybe <$> arbitrary where
    withEmptyFromMaybe Nothing  = Empty
    withEmptyFromMaybe (Just x) = NonEmpty x

main :: IO ()
main = hspec $ do
  let smallSize = mapSize (\x -> x `div` 2)
  describe "Keyed Collection: mapWithKey properties" $
    do it "prop_KC_mapPreservesKeys (Map Int Int)" $ property (prop_KC_mapPreservesKeys :: (Int -> Int -> Int) -> Map Int Int -> Bool)
       it "prop_KC_mapPreservesKeys (IntMap String)" $ property (prop_KC_mapPreservesKeys :: (Int -> String -> String) -> IntMap String -> Bool)
  describe "Keyed Collection: keyValueList properties" $
    do it "prop_KC_keyValueListIso ([Int])" $ property (prop_KC_keyValueListIso :: [Int] -> Bool)
       it "prop_KC_keyValueListIso (Seq Int)" $ property (prop_KC_keyValueListIso :: Seq Int -> Bool)
       it "prop_KC_keyValueListIso (Map Int Int)" $ property (prop_KC_keyValueListIso :: Map Int Int -> Bool)
       it "prop_KC_keyValueListIso (IntMap Double)" $ property (prop_KC_keyValueListIso :: IntMap Double -> Bool)
       it "prop_KC_keyValueListIso (Tree Char)" $ property (prop_KC_keyValueListIso :: Tree Char -> Bool)
  describe "MapLike: filter & mapMaybe" $
    do it "prop_SetLike_FilterAll (Map Int Int)" $ property (prop_SetLike_FilterAll :: Map Int Int -> Bool)
  describe "SetLike: union and intersection" $
    do it "prop_SetLike_DiffSelf (Map Int Int)" $ property (prop_SetLike_DiffSelf :: Map Int Int -> Bool)
       it "prop_SetLike_UnionAfterDifference (Map Int Int)" $ property (prop_SetLike_UnionAfterDifference :: Map Int Int -> Map Int Int -> Bool)
  describe "Diffable: fromFullDiff . toDiff = id" $
    do it "prop_Diffable_DiffIso (Map Int Int)" $ property (prop_Diffable_DiffIso :: Map Int Int -> Bool)
       it "prop_Diffable_DiffIso (IntMap Int)" $ property (prop_Diffable_DiffIso :: IntMap Int -> Bool)
       it "prop_Diffable_DiffIso (TotalArray ArrayKeys Int)" $ property (prop_Diffable_DiffIso :: TotalArray ArrayKeys Int -> Bool)
       it "prop_Diffable_DiffIso (Tree Int)" $ smallSize $ property (prop_Diffable_DiffIso :: Tree Int -> Bool)
       it "prop_Diffable_DiffIso (WithEmpty (TotalArray ArrayKeys) Int)" $ property (prop_Diffable_DiffIso :: WithEmpty (TotalArray ArrayKeys) Int -> Bool)
  describe "Diffable: diff laws" $
    do it "prop_Diffable_DiffLawNoEq (Map Int Int)" $ property (prop_Diffable_DiffLawNoEq :: Map Int Int -> Map Int Int -> Bool)
       it "prop_Diffable_DiffLawNoEq (IntMap String)" $ property (prop_Diffable_DiffLawNoEq :: IntMap String -> IntMap String -> Bool)
       it "prop_Diffable_DiffLawNoEq (TotalArray ArrayKeys Int)" $ property (prop_Diffable_DiffLawNoEq :: TotalArray ArrayKeys Int -> TotalArray ArrayKeys Int -> Bool)
       it "prop_Diffable_DiffLawNoEq (Tree Char)" $ property (prop_Diffable_DiffLawNoEq :: Tree Char -> Tree Char -> Bool)
       it "prop_Diffable_DiffLaw (Map Int Int)" $ property (prop_Diffable_DiffLaw :: Map Int Int -> Map Int Int -> Bool)
       it "prop_Diffable_DiffLaw (IntMap String)" $ property (prop_Diffable_DiffLaw :: IntMap String -> IntMap String -> Bool)
       it "prop_Diffable_DiffLaw (TotalArray ArrayKeys Int)" $ property (prop_Diffable_DiffLaw :: TotalArray ArrayKeys Int -> TotalArray ArrayKeys Int -> Bool)
       it "prop_Diffable_DiffLaw (Tree Char)" $ smallSize $ property (prop_Diffable_DiffLaw :: Tree Char -> Tree Char -> Bool)
       it "prop_Diffable_DiffLaw (WithEmpty Tree Char)" $ smallSize $ property (prop_Diffable_DiffLaw :: WithEmpty Tree Char -> WithEmpty Tree Char -> Bool)
