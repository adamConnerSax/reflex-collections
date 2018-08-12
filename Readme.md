reflex-collections

A re-implementation of the collection functions from Reflex.  

This library reimplements `listHoldWithKey`, `listWithKey`, `listViewWithKey`, and `selectViewListWithKey` using some typeclass machinery to make these functions
more polymorphic.  The originals operate only on `Ord k => Data.Map.Map` these will operate on `Map`, `IntMap` and `HashMap` and, if using only `listHoldWithKey`, will also 
work on `(Enum k, Bounded k, Ix k) => Data.Array k`, a sort of "Total Map", holding a value of some sort for every `k`.  It should also be easy to add class instances for many collections so these functions will work on them directly.

Along the way, we get more polymorphic versions of `Reflex.mergeMap` (`Reflex.Collections.Collections.mergeOver`) and `distributeMapOverDynPure` (`Reflex.Collections.Collections.distributeOverDynPure`).

There are several typeclasses, each of which abstracts out a piece of the functionality required for the listXXX functions to operate on a collection:

1. A typeclass supporting efficient merging/sequencing (`m (t a) -> t (m a)`) for the `Reflex.Event` and `Reflex.Dynamic` types: `Reflex.Collections.Sequenceable.ReflexSequenceable` (with an instance for `DMap`)
2. A typeclass with a collection and patch type supporting efficient sequencing of a collection and patch as well as reconstruction of that pair into a `Reflex.Dynamic`: `Reflex.Collections.Sequenceable.PatchSequenceable` (with an instance for the pair `DMap` and `PatchDMap`)
3. A utility class representing the ability to map over the collection using the key (whatever that means for the collection): `Reflex.Collections.KeyedCollection.KeyedCollection` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap` and `Ix k => Array k`)
4. A class representing the difference between two collections: `Reflex.Collections.Diffable.Diffable` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap` and `Ix k => Array k`)
5. A class for keyed, diffable, collection types which can be converted to and from the sequenceable type: `Reflex.Collections.ToPatchType` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap` and `Ix k => Array k`).  This class also contains functions for doing event fans on the container and its Diff.


There are also Typeclasses to simplify support for the case of a collection which is isomorphic to some efficient collection management type for.
1. `DMapIso`, a typeclass representing the isomorphism in (`Reflex.Collections.DMapIso`)
2. (Planned) `IntMapIso`, a typeclass representing the isomorphism in (`Reflex.Collections.IntMapIso`)


The simple way to add a new collection type is to derive instances for `KeyedCollection`, `Diffable`, `DMapIso` or `IntMapIso` (as well as `Monoid`) and use the DM/IM versions of the collection management functions in `Reflex.Collections.CollectionsDM`  or `Reflex.Collections.CollectionsIM`. 

To add a new collection type from scratch, you need instances of `ToPatchType` (which requires `KeyedCollection`) and `Diffable` (for `listHoldWithKey`).

Notes:
1.  If we could build a Dynamic starting from the current value of another Dynamic but without the perils of sample, we could get rid of the Monoid constraint.  Which would also allow containers which are "total," that is have values for all keys, to be used for more than `listHoldWithKey`. 

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
`cabal new-build all` should finish with a `Linking...` line.  Run that executable and it should spawn a browser pointing at the demo.  If not, you may need to comment out the line in
`app/Main.hs` containing `spawnProcess` and then rebuild, run the exe and manually open a browser tab pointing to `localhost:XXX` where XXX is the port specified in `Main.hs` or `Simple.hs`

The "Simple" demo is much more straightforward but shows fewer functions in action.  I'm planning to add more...



