reflex-collections

A re-implementation of the [collection](https://github.com/reflex-frp/reflex/blob/develop/src/Reflex/Collection.hs) 
functions from [Reflex](https://github.com/reflex-frp/reflex) and some useful additions.

This library reimplements `listHoldWithKey`, `listWithKey`, `list`, `listViewWithKey`, `listWithKeyShallowDiff` and `selectViewListWithKey` 
using some typeclass and associated type-family machinery to make these functions
more polymorphic. In addition, it adds versions which have a `Maybe` in the return type to facilitiate use 
with collections that have no empty state (e.g. `Tree` or `Array`). The originals operate only on `Ord k => Data.Map.Map k`, 
these will operate on `Ord k => Map k`, `IntMap`, `(Hashable k, Ord k) => HashMap k`, `[]`, `Data.Sequence.Seq`, and, 
for `listHoldWithKey`, `listWithKeyShallowDiff` and the "`Maybe`" versions of the rest, will also 
work on `Tree` (a rose tree from `Data.Tree`) and `(Enum k, Bounded k, Ix k) => Data.Array k`, 
a sort of "Total Map", holding a value for every `k`.  
It should also be straightforward to add class instances for other collections so these functions will work on them directly.

There is one added collection function, `listViewWithKeyShallowDiff`, which specializes `listWithKeyShallowDiff` for the case when the widget returns `m (Event t b)` 
in the same way that `listViewWithKey` specializes `listWithKey` for that case.

The library also contains a useful function for handling collections of widgets which fire events that can result in changes to the collection itself, 
e.g., a delete, move-up or move-down button for a list.  This is `selfEditingCollection` in the module `Reflex.Collections.SelfEditingCollection`.  
This function requires input functions to specify how to convert the type returned by a widget event into a change of structure of the collection.  
It then manages the book-keeping to update the displayed collection and the output dynamic.   

Along the way, we get more polymorphic versions of `Reflex.mergeMap` (`Reflex.Collections.Collections.mergeOver`) and 
`distributeMapOverDynPure` (`Reflex.Collections.Collections.distributeOverDynPure`).  
`mergeOver` returns `Event t (KeyValueSet f a)`. 
`KeyValueSet f a` is some container of Key/Value pairs which has set operations (union, difference, filter, etc.) on the keys. 
`KeyValueSet f a` is, for all `f` so far, some sort of Map (`Map` itself, or `HashMap` or `IntMap`). 
`mergeOver` cannot return `Event t (f a)` since events will only fire on subsets and subsets don't make sense for all containers, 
though they do for all `KeyValueSets`. 
For the various map-like types (`Map`, `HashMap`, `IntMap`), `KeyValueSet f a ~ f a`, so this change is invisible.

There are several typeclasses, each of which abstracts out a piece of the functionality required for the listXXX functions to operate on a collection:

There are three typeclasses representing types that Reflex can efficiently merge and sequence incrementally.  You are unlikely to want to implement any of these for a new type since it requires deep support within Reflex itself, in the Patch type and Adjustable classes.  If types are added there, they should be added here as well:
1. A typeclass supporting efficient "merging" for the `Reflex.Event` type. 
That is, turning a collection of events into an event of a collection with members only for fired events: 
[`Reflex.Collections.Sequenceable.ReflexMergeable`](./src/Reflex/Collections/ReflexSequenceable.hs)) 
(with instances for [`DMap`](https://hackage.haskell.org/package/dependent-map-0.2.4.0) 
and [`IntMap`](https://hackage.haskell.org/package/containers-0.6.0.1))
2. A typeclass supporting efficient sequencing of Dynamics (`f (Dynamic t a) -> Dynamic t (f a)`): 
[`Reflex.Collections.Sequenceable.ReflexSequenceable`](./src/Reflex/Collections/ReflexSequenceable.hs) 
(with instances for [`DMap`](https://hackage.haskell.org/package/dependent-map-0.2.4.0) 
and [`IntMap`](https://hackage.haskell.org/package/containers-0.6.0.1))
3. A typeclass with a collection and patch type supporting efficient sequencing of a collection 
and patch as well as reconstruction of that pair into a `Reflex.Dynamic`: 
[`Reflex.Collections.Sequenceable.PatchSequenceable`](./src/Reflex/Collections/ReflexSequenceable.hs) 
(with an instance for the pair [`DMap`](https://hackage.haskell.org/package/dependent-map-0.2.4.0) 
and [`PatchDMap`](https://github.com/reflex-frp/reflex/blob/develop/src/Reflex/Patch/DMap.hs) 
as well the pair [`ComposedIntMap` and `ComposedPatchIntMap`](./src/Reflex/Collections/ComposedIntMap.hs))

And there are three typeclasses to support mapping of collections into and out of the reflex-efficient types above:
1. A class defining the key type for each collection, and implementing mapWithKey and to/from lists of key/value pairs: 
`Reflex.Collections.KeyedCollection.KeyedCollection` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap`, `Tree` and `Ix k => Array k`). 
For types with instances of `Data.Key.Keyed` and `Data.Key.FoldableWithKey` the only thing requiring implementation is `fromKeyValueList`.
2. A class defining the Key/Value set type and, thus, the  "diff" type (`Diff f a ~ KeyValueSet f (Maybe a)`) 
for a collection and providing implementations of various functions to take diffs and apply them: 
`Reflex.Collections.Diffable.Diffable` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap`, `Tree` and `(Enum k, Bounded k, Ix k) => Array k`).  
For collections with diffs that are map-like (`Map` or `HashMap` or `IntMap`), all you need to implement are the `toDiff` and `fromFullDiff` functions.
3. A class which implements the necessary functions to transform collections and their diffs to the types which Reflex can merge and sequence and fan efficiently: 
`Reflex.Collections.ToPatchType` (with instances for `Ord k => Map k`, `(Ord k, Hashable k) => HashMap k`, `IntMap`, `Tree` 
and `(Enum k, Bounded k, Ix k) => Array k`).  This class also contains functions for doing event fans on the container and its Key/Value set.

To add a new collection type, you need instances of these second three (`KeyedCollection`, `Diffable` and `ToPatchType`) for your collection. 
(TODO: An example of this in its own file).

There's a quickcheck test setup for checking that your classes are lawful 
(e.g., that a KeyedCollection to and from key/value lists is isomorphic, that `applyDiff (diff a b) a = b`, etc.).  
So if you add a type, you can add tests to check that you are implementing things correctly.  

Notes:
1.  Many of the original collection functions require the collection to have an empty state.  
We get around this by using the "WithEmpty" type 
(which is isomorphic to Maybe but only for things wrapped in type-constructor-- `WithEmpty f a` is isomorphic to `Maybe (f a)`--and 
having special versions of the collection functions which return `Dynamic t (Maybe (f a))` 
rather than `Dynamic t (f a)` for types with no natural empty state.  
We also have a combinator for simplifying the frequent case where the widget returns `m (Dynamic t (g a))`, 
yielding a `Dynamic t (Maybe (f (Dynamic t a)))` result, which can be "flattened" to `Dynamic t (Maybe (f a))`. 
2. I've changed the interface for listViewWithKey slightly, returning `R.Event t (KeyValueSet f v)` instead of `R.Event t (f v)`.  
For a total container, one with items for all keys, the original version doesn't make sense.  
Our events will be for subsets of the keys. This doesn't change anything for `Map k` since `Map k` is its own Key/Value set.
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

Running the demos (using the jsaddle-warp runner):
`cabal new-build all` should finish with a `Linking...` line.  Run that executable and it should spawn a browser pointing at the demo.  
If not, you may need to comment out the line in
`app/Main.hs` containing `spawnProcess` and then rebuild, run the exe and manually open a browser tab pointing to `localhost:XXX` where XXX is the port specified in `Main.hs` or `Simple.hs`

The "Simple" demo shows a few of the functions in action, including using `selfEditingCollection` to build a re-orderable list widget.

Running the tests:
`cabal new-test`



