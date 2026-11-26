# topology_category — topologies in one host type and their normalized continuous maps

The objects are topologies on subsets of one host type `M`. A topology
`T` carries its own set of points, `⋃T`; a morphism is a continuous map
whose values outside that set are fixed to `junk`. The hom sets are
`continuous_hom_set` from `topology/continuous`, and the category is
assembled by `category.CategoryFromHom`.

The identity is normalized on the source carrier. A composite is
normalized again, because ordinary function composition need not keep
the chosen value outside that carrier. Equality of representatives is
therefore exactly equality on the source space. The default value
need not be a point of any space.

This is one category per host type. Continuous maps between distinct
host types remain available in `topology/continuous`; the categorical
record here holds objects and morphisms in fixed types, as
`category/set_category` does.

## The category

| member | statement |
|---|---|
| `TopologyCategoryDef` | `topology_category`: topologies in one host type, with normalized continuous maps, normalized identities and normalized composition |
| `TopologyCategory` | `category(topology_category)` |

## Underlying sets and isomorphisms

The forgetful map sends a topology to its carrier and keeps the
normalized map of each morphism. The statements below prove it a
functor and relate isomorphisms to homeomorphisms. The topology
conjuncts make the source and target category objects; the
normalization conjunct selects the unique representative of a map on
its source carrier.

| member | statement |
|---|---|
| `TopologyForgetfulDef` | `topology_forgetful`: send `T` to `⋃T` and keep the underlying normalized map |
| `TopologyForgetful` | the forgetful map is a functor from `topology_category` to `set_category` |
| `TopologyIsomorphismIff` | `mk_morphism(T, S, f)` is an isomorphism ⇔ `T` and `S` are topologies, `f` is normalized on `⋃T`, and `f` is a homeomorphism |
| `TopologyIsomorphicIff` | `T` and `S` are isomorphic in `topology_category` ⇔ both are topologies and their spaces are homeomorphic |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
