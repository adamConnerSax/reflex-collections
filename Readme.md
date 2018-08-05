reflex-collections

A re-implementation of the collection functions from Reflex.  

This library reimplements `listHoldWithKey`, `listWithKey`, `listViewWithKey`, and `selectViewListWithKey` using some typeclass machinery to make these functions
more polymorphic.  The originals operate only on `Ord k => Data.Map.Map` these will operate on `Map`, `IntMap` and `HashMap` and, if using only `listHoldWithKey`, will also 
work on `(Enum k, Bounded k, Ix k) => Data.Array k`, a sort of "Total Map", holding a value of some sort for every `k`

Along the way, we get more polymorphic versions of `Reflex.merge` (`Reflex.Collections.Collections.mergeOver`) and `distributeMapOverDynPure` (`Reflex.Collections.Collections.distributeOverDynPure`).

Several ideas are handled more abstractly, via typeclasses:

1. A typeclass supporting efficient sequencing (`m (t a) -> t (m a)`) for the `Reflex.Event` and `Reflex.Dynamic` types: `Reflex.Collections.Sequenceable.ReflexSequenceable` (with an instance for `DMap`)
2. A typeclass with a collection and patch type supporting efficient sequencing of a collection and patch as well as reconstruction of that pair into a `Reflex.Dynamic`: `Reflex.Collections.Sequenceable.PatchSequenceable` (with an instance for the pair `DMap` and `PatchDMap`)
3. A class for collection types which can be converted to and from the sequenceable type: `Reflex.Collections.ToPatchType` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap` and `Ix k => Array k`)
4. A small utility class representing the ability to map over the collection using the key, whatever that means for the collection: `Reflex.Collections.KeyMappable.KeyMappable` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap` and `Ix k => Array k`)
5. A class supporting efficient event fans: `Reflex.Collections.HasFan.HasFan` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap` and `Ix k => Array k`)
6. A class representing the difference between two collections: `Reflex.Collections.Diffable.Diffable` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap` and `Ix k => Array k`)
7. A class for collections which have an empty state (which allows the "bootstrapping" of a new dynamic from an input dynamic using a static initial empty state and diffs): `Reflex.Collections.Diffable.HasEmpty` (with instances for `Ord k => Map k`, `Hashable k => HashMap k`, `IntMap`but *not* `Array k`).

To add a new collection type directly supported by these functions, you need instances of `ToPatchType` (which requires `KeyMappable`) and `Diffable` (for `listHoldWithKey`) and `HasFan` and `HasEmpty` (for `listWithKey`, `listViewWithKey`, and `selectViewListWithKey).  This should be straightforward for any keyed collection and also possible for things like lists and trees once you decide what should play the role of the key. Something like an index for a list and a path to a node for a tree.

----

Building:
This is set up with reflex-platform. SO on any machine with nix:
```
git clone https://github.com/adamConnerSax/reflex-collections
cd reflex-collections
git submodule init
git submodule update
nix-shell -A shells.ghc
cabal new-build all
```

Running the demo:
`cabal new-build all` should finish with a `Linking...` line.  Run that executable and it should spawn a browser pointing at the demo.  If not, you may need to comment out the line in
`app/Main.hs` containing `spawnProcess` and then rebuild, run the exe and manually open a browser tab pointing to `localhost:XXX` where XXX is the port specified in `Main.hs`



