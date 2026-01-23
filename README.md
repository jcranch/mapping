# Mappings

This package offers a general typeclass
[`Mapping`](src/Data/Mapping.hs) for data structures which represent
functions `k -> v` (possibly for fixed `k`, but arbitrary ordered
`v`).

There are some fairly straightforward examples: constant mappings, and
those which build up mappings where `k` is `Either`, or a pair, or
`Maybe`, or `Bool`.

Three less trivial implementations are provided:

* [Decision diagrams](src/Data/Mapping/Decision.hs), with nodes
  which may themselves be an arbitrary `Mapping`;

* [Piecewise constant maps](src/Data/Mapping/Piecewise.hs) on an
  ordered domain `k`;

* [Maps equipped with a default value](src/Data/Mapping/MapWithDefault.hs).

