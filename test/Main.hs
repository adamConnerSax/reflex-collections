{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE UndecidableInstances       #-}
module Main where
import           Control.Monad                      (replicateM)
import           Data.Array                         (Array, Ix, listArray)
import           Data.IntMap                        (IntMap)
import           Data.Map                           (Map)
import           Data.Sequence                      (Seq)
import           Reflex.Collections.Diffable        (Diffable (..),
                                                     MapLike (..))
import           Reflex.Collections.KeyedCollection (KeyedCollection (..))
import           Test.Hspec
import           Test.QuickCheck
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

prop_MapLike_FilterAll :: (KeyedCollection f, MapLike f) => f a -> Bool
prop_MapLike_FilterAll  = emptyKC . mlFilter (const False)

prop_MapLike_DiffSelf :: (KeyedCollection f, MapLike f) => f a -> Bool
prop_MapLike_DiffSelf a = emptyKC $ mlDifference a a

prop_MapLike_UnionAfterDifference :: (KeyedCollection f, MapLike f, Eq a, Eq (Key f)) => f a -> f a -> Bool
prop_MapLike_UnionAfterDifference a b = equalKC (mlUnion a b) (mlUnion a (mlDifference b a))

prop_Diffable_PatchLaw :: (Diffable f, Eq a, Eq (Key f)) => f a -> f a -> Bool
prop_Diffable_PatchLaw c d = equalKC c $ patch d (toDiff c)

-- an array that must have values for all keys
newtype TotalArray k a = TotalArray { unTA :: Array k a } deriving (Functor, KeyedCollection, Diffable, Show)


instance (Arbitrary k, Bounded k, Enum k, Ix k, Arbitrary a) => Arbitrary (TotalArray k a) where
  arbitrary = fmap (TotalArray . listArray (minBound, maxBound)) $ replicateM (length [(minBound :: k) .. (maxBound :: k)]) arbitrary

data ArrayKeys = A | B | C | D | E | F deriving (Show, Bounded, Enum, Ord, Eq, Ix)
instance Arbitrary ArrayKeys where
  arbitrary = arbitraryBoundedEnum


main :: IO ()
main = hspec $ do
  describe "Keyed Collection: mapWithKey properties" $
    do it "prop_KC_mapPreservesKeys (Map Int Int)" $ property (prop_KC_mapPreservesKeys :: (Int -> Int -> Int) -> Map Int Int -> Bool)
       it "prop_KC_mapPreservesKeys (IntMap String)" $ property (prop_KC_mapPreservesKeys :: (Int -> String -> String) -> IntMap String -> Bool)
  describe "Keyed Collection: keyValueList properties" $
    do it "prop_KC_keyValueListIso (Map Int Int)" $ property (prop_KC_keyValueListIso :: Map Int Int -> Bool)
       it "prop_KC_keyValueListIso (IntMap Double)" $ property (prop_KC_keyValueListIso :: IntMap Double -> Bool)
  describe "MapLike: filter & mapMaybe" $
    do it "prop_MapLike_FilterAll (Map Int Int)" $ property (prop_MapLike_FilterAll :: Map Int Int -> Bool)
  describe "MapLike: union and intersection" $
    do it "prop_MapLike_DiffSelf (Map Int Int)" $ property (prop_MapLike_DiffSelf :: Map Int Int -> Bool)
       it "prop_MapLike_UnionAfterDifference (Map Int Int)" $ property (prop_MapLike_UnionAfterDifference :: Map Int Int -> Map Int Int -> Bool)
  describe "Diffable: patch law" $
    do it "prop_Diffable_PatchLaw (Map Int Int)" $ property (prop_Diffable_PatchLaw :: Map Int Int -> Map Int Int -> Bool)
       it "prop_Diffable_PatchLaw (TotalArray ArrayKeys Int)" $ property (prop_Diffable_PatchLaw :: TotalArray ArrayKeys Int -> TotalArray ArrayKeys Int -> Bool)
