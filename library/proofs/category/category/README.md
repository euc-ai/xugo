# category — categories on two carrier sets as records, their functors, and the construction of a category from its hom data

A category is a record on two carrier sets, `category_ops(A, M)`: a
set `C.objects` of objects of a type `A`, a set `C.morphisms` of
morphisms of a type `M`, the source and target `C.source`, `C.target :
M → A`, the identity `C.identity : A → M` and the composite
`C.compose : M → M → M`, `C.compose(g, f)` for `g` after `f`;
`category(C)` says the record is a category. The composite is total,
as every operation of a structure is, and every law carries the
memberships and the composability `C.target(f) = C.source(g)` as
hypotheses. The two carriers are components because the categories the
corpus builds — the homotopy category of a quasi-category, whose
morphisms are classes of edges — are sets of one type, and a law is
proved once for a category on sets (constitution §Structures, "One
proof per law"). The record is the form because a category is as often
an object as a context: a theorem takes one as a value and states a
property of it, as it does of a group.

A functor is a record of two maps, `functor_ops(A, M, B, N)`, on
objects and on morphisms, preserving the ends, the identities and the
composites; functors compose. A morphism with a two-sided inverse is an
isomorphism, and a groupoid is a category whose every morphism is one;
in any category a left and a right inverse of one morphism agree, by
the unit and associativity laws. The functors between two categories
are collected in `functor_set(C, D)`, normalized with `junk` off the
carriers of `C` (`functions.normalize_on`) so that two functors
agreeing on `C` are one element.

Most categories are given by hom data rather than by two carrier sets:
a set of objects `O`, a set `H(x, y)` of morphism data for each pair,
an identity datum at each object and a composition of data.
`category_from_hom(O, H, e, c)` assembles the record from such data,
its morphisms the data framed by their ends, `mk_morphism(x, y, f)`
with `f` in `H(x, y)`; `CategoryFromHom` says the result is a category
when the data satisfy the laws on the data. Every category the corpus
assembles — the subsets of a type (`set_category`), a preorder
(`preorder_category`), the simplex category
(`simplicial/simplex_category`) — states its hom data and
cites that theorem, so the bookkeeping of ends is proved once.

## The records

| member | statement |
|---|---|
| `CategoryOps` | the record `category_ops(A, M)`: `mk_category(objects, morphisms, source, target, identity, compose)`, its parts read as fields |
| `FunctorOps` | the record `functor_ops(A, M, B, N)`: `mk_functor(obj, map)`, from a category on `A`, `M` to one on `B`, `N` |
| `MorphismTriple` | the record `morphism_triple(A, D)`: `mk_morphism(source, target, map)`, a datum framed by its ends |

## The structure and its axioms

| member | statement |
|---|---|
| `Category` | `category(C)` ⇔ the six clauses below — a structure |
| `MorphismEnds`, `IdentityMorphism`, `CompositeMorphism` | the ends of a morphism are objects; the identity is a morphism from its object to itself; composable morphisms compose, with the ends of the composite |
| `LeftUnit`, `RightUnit`, `Assoc` | `identity(target f) ∘ f = f`; `f ∘ identity(source f) = f`; `h ∘ (g ∘ f) = (h ∘ g) ∘ f` on composable triples |
| `IdentityComposeIdentity` | `identity(x) ∘ identity(x) = identity(x)`: the left unit at `identity(x)`, whose target is `x` |

## Hom sets, isomorphisms and groupoids

A proof that holds its arrows as hom-set memberships, `f ∈ category_hom(C, x, y)`,
cites the hom forms (`ComposeHom`, `AssocHom`, `LeftUnitHom`, `RightUnitHom`,
`InverseHom`, `FunctorPreservesCompositeHom`). One that holds them as morphisms
with their ends — a functor's image read off `FunctorMapEnds`, the legs of a
naturality square, a hom membership split into morphism and endpoints — cites
the raw `Assoc`, `LeftUnit`, `RightUnit` and `FunctorPreservesComposite`, so
neither form is restated to fit the other.

| member | statement |
|---|---|
| `CategoryHomDef` | `category_hom(C, x, y)`: the morphisms of `C` from `x` to `y` |
| `IdentityHom`, `ComposeHom` | the identity at an object lies in its endomorphism hom set; a morphism from `x` to `y` followed by one from `y` to `z` composes into the hom set from `x` to `z` |
| `MorphismInHom` | a morphism lies in the hom set from its source to its target |
| `AssocHom`, `LeftUnitHom`, `RightUnitHom` | composition associates on three consecutive hom sets; on the hom set from `x` to `y` the identity at `y` is a left unit and the identity at `x` a right unit |
| `CategoryIsomorphismDef` | `category_isomorphism(C, f)` ⇔ `f` is a morphism with a two-sided inverse |
| `GroupoidDef` | `groupoid(C)` ⇔ a category whose every morphism is an isomorphism |
| `InverseUnique` | a left inverse `g` and a right inverse `g'` of a morphism `f` are equal, in any category: both are the composite `g ∘ f ∘ g'`, by the two units and associativity on the composable triple `(g', f, g)` |
| `IsomorphismFromInverses` | a morphism with a left inverse and a right inverse is an isomorphism: by `InverseUnique` the two are one, a two-sided inverse |

## Functors

Each clause of a functor is a member of its own, so a proof cites the
clause it uses; the two categories are read the same way.

| member | statement |
|---|---|
| `FunctorDef` | `functor(C, D, F)` ⇔ both categories, objects to objects, morphisms to morphisms with the ends, identities and composites preserved |
| `FunctorSourceCategory`, `FunctorTargetCategory` | the source and the target of a functor are categories |
| `FunctorObjectImage`, `FunctorMapEnds` | a functor carries an object to an object, and a morphism to a morphism from the image of its source to the image of its target |
| `FunctorPreservesIdentity`, `FunctorPreservesComposite` | a functor carries identities to identities and composites to composites |
| `FunctorMapHom` | a functor carries the hom set from `x` to `y` into the hom set between the images of `x` and `y` |
| `FunctorMapInHom` | a functor carries a morphism into the hom set between the images of its source and its target |
| `FunctorPreservesCompositeHom` | a functor carries the composite of a morphism from `x` to `y` and one from `y` to `z` to the composite of their images |
| `FunctorIdentity` | the identity maps form a functor from a category to itself |
| `FunctorCompose` | functors compose: each clause holds of the composite maps as F's clause followed by G's, at the image F places in the middle category |
| `FunctorSetDef` | `functor_set(C, D)`: the functors from `C` to `D` normalized with `junk` off the objects and off the morphisms of `C` |
| `FunctorSetFunctor` | a normalized functor is a functor |
| `NormalizedFunctorSet` | a functor normalized off the carriers of its source is a normalized functor |

## A category from its hom data

| member | statement |
|---|---|
| `CategoryFromHomDef` | `category_from_hom(O, H, e, c)`: objects `O`, morphisms the triples `mk_morphism(x, y, f)` with `x, y ∈ O` and `f ∈ H(x, y)`, source and target the frame, identity `mk_morphism(x, x, e(x))`, composite `mk_morphism(source f, target g, c(source f, target f, target g, map g, map f))` |
| `CategoryFromHom` | the assembled record is a category when `e(x) ∈ H(x, x)`, `c` lands in `H(x, z)` on consecutive hom sets, the identity data are units and composition of data associates |
| `CategoryFromHomHomIff` | a framed datum `mk_morphism(x, y, f)` lies in the hom set from `x` to `y` exactly when `x` and `y` are objects and `f ∈ H(x, y)` |
| `CategoryFromHomIsomorphismIff` | a framed hom datum is an isomorphism exactly when its ends are objects, it belongs to their hom set, and it has two-sided inverse data |
| `FunctorFromHomIff` | the functors out of a hom-data category are exactly the maps preserving objects, hom sets, identities and composition |

## The opposite, isomorphisms and inverses

The opposite of a category keeps its objects, morphisms and record
type, source and target exchanged and the composite read the other way.
An isomorphism has a chosen inverse, `category_inverse`, the one
inverse there is.

| member | statement |
|---|---|
| `OppositeCategoryDef` | `opposite_category(C)`: source and target exchanged, `g ∘ f` read as `f ∘ g` |
| `CategoryIsomorphicDef`, `CategoryInverseDef` | `category_isomorphic(C, x, y)`: an isomorphism from `x` to `y` exists; `category_inverse(C, f)`: a two-sided inverse, chosen |
| `InverseIsomorphism` | the chosen inverse is a two-sided inverse and an isomorphism |
| `InverseHom` | the chosen inverse of an isomorphism from `x` to `y` lies in the hom set from `y` to `x` and inverts it on both sides |
| `CancelInverseLeft`, `CancelInverseRight` | the inverse of an isomorphism `h` undoes composition with `h`: `h⁻¹ ∘ (h ∘ f) = f` and `(f ∘ h) ∘ h⁻¹ = f` on consecutive hom sets |
| `CancelIsomorphismLeft` | an isomorphism `h` undoes composition with its inverse: `h ∘ (h⁻¹ ∘ f) = f` for `f` and `h` into the same object |
| `IsomorphismMonic`, `IsomorphismEpic` | an isomorphism is monic and epic: `h ∘ f = h ∘ g`, or `f ∘ h = g ∘ h`, gives `f = g` |

## Identity and composite functors

The identity functor and the composite of two functors are normalized
off the carriers of their source, so that they lie in the functor sets;
a composite of normalized maps is normalized only on the source, so the
normalization is done again.

| member | statement |
|---|---|
| `IdentityFunctorDef`, `FunctorComposeDef` | `identity_functor(C)`; `functor_compose(C, G, F)`, `G` after `F` normalized off the carriers of `C` |
| `IdentityFunctorApply`, `FunctorComposeApply` | on the objects and morphisms of `C` the identity functor is the identity, and `functor_compose(C, G, F)` is `G` after `F` |
| `IdentityFunctorSet` | the identity functor is a normalized functor: the identity maps, normalized |
| `FunctorComposeSet` | the normalized composite of two functors is a normalized functor: the composite maps, normalized |
| `IdentityFunctorFunctor`, `FunctorComposeFunctor` | the identity functor and the normalized composite of two functors are functors |

The conventions every proof here follows are `library/proofs/README.md`;
the rules are `library/chapter_constitution.md`.
