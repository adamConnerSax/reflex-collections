reflex-collections

A re-implementation of the collection functions from Reflex.  

This library reimplements `listHoldWithKey`, `listWithKey`, `list`, `listViewWithKey`, and `selectViewListWithKey` using some typeclass and associted type-family machinery to make these functions
more polymorphic.  The originals operate only on `Ord k => Data.Map.Map k` these will operate on `Map`, `IntMap`, `HashMap`, `[]`, `Data.Sequence.Seq`, and, for only `listHoldWithKey`, will also 
work on `(Enum k, Bounded k, Ix k) => Data.Array k`, a sort of "Total Map", holding a value for every `k`.  It should also be easy to add class instances for many collections so these functions will work on them directly.

Along the way, we get more polymorphic versions of `Reflex.mergeMap` (`Reflex.Collections.Collections.mergeOver`) and `distributeMapOverDynPure` (`Reflex.Collections.Collections.distributeOverDynPure`).

There are several typeclasses, each of which abstracts out a piece of the functionality required for the listXXX functions to operate on a collection:

1. A typeclass supporting efficient "merging" for the `Reflex.Event` type. That is, turning a collection of events into an event of a collection with members only for fired events: `Reflex.Collections.Sequenceable.ReflexMergeable` (with instances for `DMap` and `IntMap`)
2. A typeclass supporting efficient sequencing (`m (t a) -> t (m a)`) for the `Reflex.Dynamic` type: `Reflex.Collections.Sequenceable.ReflexSequenceable` (with instances for `DMap` and `IntMap`)
3. A typeclass with a collection and patch type supporting efficient sequencing of a collection and patch as well as reconstruction of that pair into a `Reflex.Dynamic`: `Reflex.Collections.Sequenceable.PatchSequenceable` (with an instance for the pair `DMap` and `PatchDMap` as well the pair `ComposedIntMap` and `ComposedPatchIntMap`)
4. A class representing the ability to map over the collection using the key (whatever that means for the collection): `Reflex.Collections.KeyedCollection.KeyedCollection` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap`, `Ix k => Array k`, `[]`, and `Data.Sequence.Seq`)
5. A class for computing differences between two collections: `Reflex.Collections.Diffable.Diffable` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap`, `Ix k => Array k`, `[]` and `Data.Sequence.Seq`)
6. A class for keyed, diffable, collection types which can be converted to and from the sequenceable type: `Reflex.Collections.ToPatchType` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap`, `Ix k => Array k`, `[]`, and `Data.Sequence.Seq`).  This class also contains functions for doing event fans on the container and its Diff.

To add a new collection type from scratch, you need instances of `KeyedCollection`, `Diffable` and `ToPatchType`. (TODO: An example of this in its own file).

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



