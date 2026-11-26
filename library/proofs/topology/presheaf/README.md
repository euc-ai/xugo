# presheaf — presheaves and sheaves on a topological space, their germs and stalks

A presheaf on the topological space `T` assigns to each open set `U` its
sections `F(U)` and restricts a section over `U` to an open `V ⊆ U`:
`presheaf(T, F, res)`. A sheaf is a presheaf whose sections are local and
glue. The sections of every open set live in one type, so a germ — the
class of a pair `(U, s)` under agreement near a point — and the stalk of
germs at a point have fixed types, and so does every construction on
them. A cover of `U` is a family of open sets whose union is `U`, and the
sections to glue are indexed by the open sets themselves. Compatible operations on
sections act on germs: `GermConstant`, `GermUnaryOperation`, and
`GermBinaryOperation` treat nullary, unary, and binary operations.
The source and target presheaves of an operation may have different
section types; scalar action is one example. `GermOperation` is the
same-presheaf binary specialization.

Every germ has a representative inside a prescribed neighbourhood
(`GermRepresentativeWithin`). The chapter's `CommonRepresentatives`
proof helper repeats this step for a finite list of germs, restricting
earlier representatives as the neighbourhood shrinks. It returns the
sections, their memberships, and their germ equalities over the final
neighbourhood, retaining each input's presheaf and section type.
Operation compatibility then moves an equation to those sections;
closure rules and the section equation complete its proof. Constants
are evaluated on the final neighbourhood. `GermActionDistributive`
uses this process for a scalar germ and two vector germs. The germ
induction principles provide the same-neighbourhood form for properties
of one, two, or three germs from a single presheaf.

## The structures

| member | statement |
|---|---|
| `Presheaf` | `presheaf(T, F, res)` ⇔ `is_topology(T)`, restriction lands in `F(V)`, restricting to `U` changes nothing, restricting twice is restricting once |
| `Topology`, `RestrictIn`, `RestrictSelf`, `RestrictTwice` | the four axioms |
| `Sheaf` | `sheaf(T, F, res)` ⇔ a presheaf whose sections are local and glue on every open cover |
| `SheafPresheaf`, `Locality`, `Gluing` | the three axioms |

## Presheaves as functors

`presheaf_functor(F, res)` is the functor record whose object map is
`U ↦ F(U)` and whose arrow map uses `res(U, V)`, normalized with `junk`
outside `F(U)`. This record is intended for the reverse-inclusion category
of opens: an arrow from `U` to `V` represents `V ⊆ U`, so its direction agrees
with restriction.
This records the section carriers explicitly, and imposes no condition
on a restriction map outside its source carrier.

The presheaf axioms are exactly the functor laws for this record, together
with `is_topology(T)`. That topology condition remains explicit: reverse
inclusion defines a preorder category on any family `T`. Normalization
turns equality of restrictions on their section carriers into equality
of the arrow representatives.

| member | statement |
|---|---|
| `PresheafFunctorDef` | sections and normalized restrictions, assembled into a functor record |
| `PresheafIffFunctor` | `presheaf(T, F, res)` ⇔ `is_topology(T)` and `presheaf_functor(F, res)` is a functor from the reverse-inclusion category on `T` to `set_category` |

## Comparison on a basis

The two sheaves may have different point and section types.

| member | statement |
|---|---|
| `BijectionOnBase` | a map of sections over a continuous map `f`, from `G` over `V` to `F` over the preimage of `V`, that commutes with restriction and is bijective over each basic open is bijective over every open |

## Germs and stalks

At a point `x`, the representative carrier is
`Cₓ = {(U, s) | U ∈ T ∧ x ∈ U ∧ s ∈ F(U)}`.
`StalkQuotient` identifies the stalk with its quotient by germ membership.
Under the presheaf laws, germ membership defines an equivalence on this
set. `GermClass`
identifies a lawful representative's germ with its carrier class.
`GermEq` is the general `relations/equivalence.ClassOnEqIff` law read
at that equivalence, followed by the meaning of membership in a germ.
The guard on the source representative matters: no condition is imposed
on a restriction map at an invalid source pair.

| member | statement |
|---|---|
| `SheafGermDef` | `sheaf_germ(x, U, s)` = the pairs agreeing with `(U, s)` near `x` |
| `StalkDef` | `stalk(x)` = the germs at `x` |
| `InGerm` | `(V, t) ∈ sheaf_germ(T, F, res, x, U, s)` ⇔ `V` is open, holds `x`, carries `t`, and `(V, t)` agrees with `(U, s)` near `x` |
| `GermOwn` | `(U, s) ∈ sheaf_germ(x, U, s)` |
| `AgreeNearTrans` | agreeing near `x` is transitive: two agreements restrict to the intersection of their neighbourhoods |
| `GermEquivalence` | germ membership is an equivalence on the pairs `(U, s)` with `U ∈ T`, `x ∈ U`, and `s ∈ F(U)` |
| `GermClass` | a lawful representative’s germ is its equivalence class inside `Cₓ` |
| `StalkQuotient` | the stalk is the quotient of `Cₓ` by germ membership |
| `GermEq` | two germs are equal ⇔ their sections agree near `x` |
| `GermRestrict` | a restriction has the germ of the section it restricts |
| `GermConstant` | sections compatible with restriction give the same germ on every neighbourhood |
| `GermUnaryOperation` | a restriction-compatible operation between two presheaves acts on germs by representatives |
| `GermBinaryOperation` | a restriction-compatible binary operation between three presheaves acts on germs by representatives |
| `GermActionDistributive` | section-level scalar distributivity transfers to germs when addition and scalar action agree with their section operations |
| `GermOperation` | an operation on sections that keeps to the sections and commutes with restriction acts on germs by representatives: the union of the germs of its values on representatives is the germ of `op(W, s, t)` |
| `InStalk` | `g ∈ stalk(x)` ⇔ `g` is the germ of a section over an open neighbourhood of `x` |
| `GermInStalk` | the germ of a section over an open neighbourhood of `x` lies in the stalk |
| `GermRepresentativeWithin` | every germ at `x` has a section representative on an open neighbourhood contained in any prescribed open neighbourhood of `x` |
| `GermInduction`, `GermInduction3`, `GermInduction2` | a property of one, three or two germs at `x` holds once it holds of the germs of sections over one open neighbourhood of `x` |
| `GermsDetermineSection` | on a sheaf, sections with the same germs everywhere are equal |

## Stalk maps

A continuous map f with section maps ψ(V) : Y(V) → X(f⁻¹V) compatible with restriction induces a map on stalks: a germ at f(x) goes to the union of the germs at x of the images of its representatives over their preimages, and that union is one germ.

| member | statement |
|---|---|
| `StalkMapDef` | unite the image germs of all representatives |
| `StalkMapGerm` | the map on a germ is the germ of the image section |
