reflex-collections

A re-implementation of the collection functions from Reflex.  

This library reimplements `listHoldWithKey`, `listWithKey`, `list`, `listViewWithKey`, and `selectViewListWithKey` using some typeclass and associated type-family machinery to make these functions
more polymorphic. In addition, it adds versions which have a `Maybe` in the return type to facilitiate use with collections that have no empty state (e.g. `Tree` or `Array`). The originals operate only on `Ord k => Data.Map.Map k`, these will operate on `Ord k => Map k`, `IntMap`, `(Hashable k, Ord k) => HashMap k`, `[]`, `Data.Sequence.Seq`, and, for `listHoldWithKey`, `listWithKeyShallowDiff` and the "`Maybe`" versions of the rest, will also 
work on `Tree` (a rose tree from `Data.Tree`) and `(Enum k, Bounded k, Ix k) => Data.Array k`, a sort of "Total Map", holding a value for every `k`.  It should also be straightforward to add class instances for other collections so these functions will work on them directly.

Along the way, we get more polymorphic versions of `Reflex.mergeMap` (`Reflex.Collections.Collections.mergeOver`) and `distributeMapOverDynPure` (`Reflex.Collections.Collections.distributeOverDynPure`).  `mergeOver` returns `Event t (Diff f a)` rather than `Event t (f a)` since events will only fire on subsets and subsets don't make sense for all containers, though they do for all diffs. For the various map-like types (`Map`, `HashMap`, `IntMap`), the diffs are the same type as the collection itself so this change is invisible.

There are several typeclasses, each of which abstracts out a piece of the functionality required for the listXXX functions to operate on a collection:

There are three typeclasses representing types that Reflex can efficiently merge and sequence incrementally.  You are unlikely to want to implement any of these for a new type since it requires deep support within Reflex itself, in the Adjustable class.  If types are added there, they should be added here as well:
1. A typeclass supporting efficient "merging" for the `Reflex.Event` type. That is, turning a collection of events into an event of a collection with members only for fired events: `Reflex.Collections.Sequenceable.ReflexMergeable` (with instances for `DMap` and `IntMap`)
2. A typeclass supporting efficient sequencing (`m (t a) -> t (m a)`) for the `Reflex.Dynamic` type: `Reflex.Collections.Sequenceable.ReflexSequenceable` (with instances for `DMap` and `IntMap`)
3. A typeclass with a collection and patch type supporting efficient sequencing of a collection and patch as well as reconstruction of that pair into a `Reflex.Dynamic`: `Reflex.Collections.Sequenceable.PatchSequenceable` (with an instance for the pair `DMap` and `PatchDMap` as well the pair `ComposedIntMap` and `ComposedPatchIntMap`)

And there are three typeclasses to support mapping of collections into and out of the reflex-efficient types above:
1. A class defining the key type for each collection, and implementing mapWithKey and to/from lists of key/value pairs: `Reflex.Collections.KeyedCollection.KeyedCollection` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap`, `Tree` and `Ix k => Array k`). For types with instances of `Data.Key.Keyed` and `Data.Key.FoldableWithKey` the only thing requiring implementation is `fromKeyValueList`.
2. A class defining the "diff" type for a collection and providing implementations of various functions to take diffs and apply them: `Reflex.Collections.Diffable.Diffable` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap`, `Tree` and `(Enum k, Bounded k, Ix k) => Array k`).  For collections with diffs that are map-like (Map or HashMap or IntMap), all you need to implement are the `toDiff` and `fromFullDiff` functions.
3. A class which implements the necessary functions to transform collections and their diffs to the types which Reflex can merge and sequence and fan efficiently: `Reflex.Collections.ToPatchType` (with instances for `Ord k => Map k`, `(Ord k, Hashable k) => HashMap k`, `IntMap`, `Tree` and `(Enum k, Bounded k, Ix k) => Array k`).  This class also contains functions for doing event fans on the container and its Diff.

To add a new collection type, you need instances of these second three (`KeyedCollection`, `Diffable` and `ToPatchType`) for your collection. (TODO: An example of this in its own file).

There's a quickcheck test setup for checking that your classes are lawful (e.g., that a KeyedCollection to and from key/value lists is isomorphic, that `applyDiff (diff a b) a = b`, etc.).  So if you add a type, you can add tests to check that you are implementing things correctly.  

Notes:
1.  If we could build a Dynamic starting from the current value of another Dynamic but without the perils of sample, we could get rid of the Monoid constraint. This would be useful for Array and Tree which cannot be empty.  We get around this for now by using the "WithEmpty" type (which is isomorphic to Maybe but is higher-kinded, that is `WithEmpty f a` is isomorphic to `Maybe (f a)`, and having special versions of the collection functions which return `Dynamic t (Maybe (f a))` rather than `Dynamic t (f a)` for types with no natural empty state.  We also have a combinator for simplifying the frequent case where the widget returns `m (Dynamic t (g a))`, yielding a `Dynamic t (Maybe (f (Dynamic t a)))` result which can be "flattened" to `Dynamic t (Maybe (f a))` in most cases. 
2. I've changed the interface for listViewWithKey slightly, returning `R.Event t (Diff f v)` instead of `R.Event t (f v)`.  For a total container, one with items for all keys, the original version doesn't make sense.  Our events will be for subsets of the keys. This doesn't change anything for `Map k` since `Map k` is its own diff type.
----

Building:
This is set up with reflex-platform (as a git submodule). So on any machine with nix:
```
git clone https://github.com/adamConnerSax/reflex-collections
cd reflex-collections
git submodule init
git submodule update
nix-shell -A shells.ghc
cabal new-build all
```

Running the demos:
`cabal new-build all` should finish with a `Linking...` line.  Run that executable and it should spawn a browser pointing at the demo.  
If not, you may need to comment out the line in
`app/Main.hs` containing `spawnProcess` and then rebuild, run the exe and manually open a browser tab pointing to `localhost:XXX` where XXX is the port specified in `Main.hs` or `Simple.hs`

The "Simple" demo is much more straightforward but shows fewer functions in action.  I'm planning to add more...

Running the tests:
`cabal new-test`



