# locally_ringed_space — presheaves of rings, rings of germs, locally ringed spaces and their morphisms

A presheaf of rings assigns a ring record `F(U)` to each open set and a
restriction map to each inclusion: `presheaf_of_rings(T, F, res)`, with
`F : set(A) → ring_ops(B)`. Its underlying presheaf has section sets
`F(U).carrier`. Restrictions are homomorphisms between these records;
applying this condition to the identity restriction supplies each section
ring. A sheaf of rings adds locality and gluing, and
`SheafPresheafOfRings` supplies its underlying ring presheaf.

For a point in the underlying space, the stalk of a ring presheaf is a
ring. The operation lemmas move germ operations to section operations,
and `StalkRing` transfers the ring equations after choosing common
representatives. This construction uses the presheaf and homomorphism
laws. A locally ringed space is a sheaf of rings whose stalk ring at
every point is local.
An isomorphism of locally ringed spaces, between spaces with points of
two types and sections of two types, is a homeomorphism with a ring
isomorphism of sections over every open set, compatible with the
restrictions.

## Ring presheaves and their stalks

| member | statement |
|---|---|
| `PresheafOfRings` | `presheaf_of_rings(…)` ⇔ a presheaf whose restrictions are ring homomorphisms |
| `Presheaf`, `PresheafRestrictHomomorphism` | the two presheaf-of-rings axioms |
| `SheafPresheafOfRings` | every sheaf of rings is a presheaf of rings |
| `SheafOfRings` | `sheaf_of_rings(…)` ⇔ a sheaf whose restrictions are ring homomorphisms |
| `Sheaf`, `RestrictHomomorphism` | the two axioms |
| `StalkAddDef`, `StalkMulDef`, `StalkNegDef`, `StalkSubDef`, `StalkZeroDef`, `StalkOneDef` | the operations on germs |
| `StalkRingDef` | `stalk_ring(T, F, res, x)` holds the germ operations and their carrier in one ring record |
| `SectionRing` | the sections of a ring presheaf over an open set form a ring |
| `GermAdd`, `GermMul`, `GermNeg` | the sum, product and negation of germs of sections over `W` are the germs of the sum, product and negation in `F(W)` |
| `GermZero`, `GermOne` | the zero and one germs are those of `F(W).zero` and `F(W).one` over every open neighbourhood `W` of `x` |
| `StalkRing` | the stalk of a ring presheaf at `x ∈ ⋃T` is a ring |
| `GermHomomorphism` | taking germs at `x` is a ring homomorphism from the sections over a neighbourhood of `x` to the stalk |
| `CoefficientGermHomomorphism` | for a ring homomorphism `α` from `R` to the sections over the whole space, `a ↦` the germ of `α(a)` at `x` is a ring homomorphism from `R` to the stalk |

## Locally ringed spaces and isomorphisms

| member | statement |
|---|---|
| `LocallyRingedSpace` | `locally_ringed_space(…)` ⇔ a sheaf of rings with local stalks |
| `RingedSheaf`, `StalkLocal` | the two axioms |
| `LrsIsomorphismDef` | `lrs_isomorphism(…, φ, ψ)` ⇔ `φ` a homeomorphism, `ψ(V)` a ring isomorphism over every open `V`, compatible with restriction |

## Morphisms

A morphism has a continuous point map f and contravariant ring homomorphisms ψ(V) on sections, compatible with restrictions. Its stalk map preserves nonunits on the incoming stalk carrier. The point map is the structure subject; ψ is a component of its bundle. The stalk map itself, and its value on a germ, are the presheaf chapter's (`stalk_map`, `StalkMapGerm`); StalkMapHomomorphism makes it a ring homomorphism on a sheaf of rings, so locality can be proved before the morphism structure is assembled.

| member | statement |
|---|---|
| `StalkMapHomomorphism` | compatible section homomorphisms induce stalk homomorphisms |
| `LrsMorphism` | endpoint LRS structures, continuity, section homomorphisms, restriction compatibility and stalk locality |
| `MorphismSource`, `MorphismTarget`, `MorphismContinuous`, `MorphismSections`, `MorphismRestrict`, `MorphismLocal` | the six defining projections |
| `MorphismCompose` | a composite of morphisms is a morphism — card |
| `IsomorphismMorphism` | an isomorphism between LRS endpoints is a morphism — card |
| `MorphismInverseIsomorphism` | morphisms inverse on points and on sections make f, with f.ψ, an isomorphism |

IsomorphismMorphism explicitly assumes LRS endpoints because lrs_isomorphism itself asserts only the homeomorphism and section-isomorphism conditions. All inverse equations constrain points and valid sections on their carriers.

## Units

A section is a unit exactly when its germs are: a unit germ comes from a section that is a unit on some smaller neighbourhood, those neighbourhoods make the unit locus open, and on a sheaf the local inverses glue.

| member | statement |
|---|---|
| `GermUnitIffRestrictUnit` | for a presheaf of rings, a germ is a unit exactly when its section is a unit on some smaller neighbourhood |
| `UnitLocusOpen` | for a presheaf of rings, the points where a section's germ is a unit form an open set |
| `UnitIffGermsUnit` | a section of a sheaf of rings is a unit exactly when all its germs are units |

GermUnitIffRestrictUnit and UnitLocusOpen need only a presheaf of rings. UnitIffGermsUnit needs a sheaf of rings: the local inverses are glued, and their product with the section is checked to be one by locality. All three allow the empty open.
