# structure_sheaf — the structure sheaf of the prime spectrum, its sections and stalks

A section of the structure sheaf over an open `U` of the spectrum is a
function from the primes to fractions — at each `p ∈ U` a fraction of the
local ring at `p` — that is locally a single fraction `a / b`,
`locally_fraction(R, U, p, s)` at each `p ∈ U`, and `∅` outside `U`:
`structure_sections(R, U)`. Every section over every open set
is of one type, `set(A) → set(prod(A, A))`; the fractions at two primes are
classes of one type in two rings of fractions that are two sets of
classes, so the rings at two primes are never compared as types. The
ring operations on the sections over `U` are pointwise, each in the ring
of fractions at its prime, and `∅` outside `U`, so they depend on `U`.

The sheaf tuple `spec_sheaf(R)` contains the Zariski topology, the
record-valued section family `spec_section_ops(R)` and restriction.

The chapter describes the affine half of the theory of schemes.
The coefficient section `fraction_section(R, U, a, R.one)`, the fraction
`a / 1` over `U`, makes the sections over `D(f)` a
localization at the powers of `f` (`SectionsAtBasicOpen`). Its germ
makes the stalk at `p` a localization at the complement of `p`
(`StalkAtPrime`). These statements use `is_localization_on` with the
section and stalk ring records; they specify the map from
the original ring as well as the target ring. `GlobalSections` states
that the coefficient-section map over the whole spectrum is a ring
isomorphism.

## The definitions

| member | statement |
|---|---|
| `FractionSectionDef` | `fraction_section(R, U, a, b)` = the fraction `a / b` as a section over `U`: its class at each prime of `U`, ∅ elsewhere |
| `LocallyFractionDef` | `locally_fraction(R, U, p, s)` ⇔ on an open neighborhood `V ⊆ U` of `p`, `s` is `a / b` with `b` outside every prime of `V` |
| `StructureSectionsDef` | `structure_sections(R, U)` = the functions ∅ outside `U` and `locally_fraction` at every point of `U` |
| `StructureRestrictDef` | `structure_restrict(U, V, s)` = `s` on `V`, ∅ elsewhere |
| `StructureAddDef`, `StructureMulDef`, `StructureNegDef`, `StructureSubDef`, `StructureZeroDef`, `StructureOneDef` | the pointwise operations over `U` |
| `SpecSectionOps` | `spec_section_ops(R, U)` is the ring record of sections over `U` |
| `SpecStalkOps` | `spec_stalk_ops(R, p)` is the ring record of germs at `p` |

## The sheaf of rings

| member | statement |
|---|---|
| `ZariskiPointPrime` | a point of an open set of the spectrum is a prime ideal |
| `StructureRestrictIn` | restricting a section to a smaller open set gives a section |
| `StructureSectionValue` | a section's value at a point lies in the localization there |
| `ConstantFractionSection` | `fraction_section(R, U, a, b)` is a section on an open set where `b` avoids every prime |
| `StructureSectionLocalFraction` | near each point a section is a fraction `a / b` on an open neighbourhood, with `b` in the multiplicative complement of every point there |
| `StructureSectionsCommonNeighborhood` | two sections are fractions `a / b` and `c / d` on one neighborhood of a common point, with the common denominator `b * d` outside every point of it |
| `StructureSectionAddIn`, `StructureSectionMulIn`, `StructureSectionNegIn` | sections are closed under the pointwise ring operations |
| `SpectrumLocalizationRing` | the fractions at a prime form a commutative ring |
| `StructureSectionRing` | sections over an open set form a commutative ring |
| `StructurePresheaf` | sections and restriction form a presheaf |
| `StructureSectionsLocality` | sections over `U` agreeing on a cover of `U` are equal |
| `StructureSectionsGluing` | compatible sections on a cover of `U` glue to a structure section over `U` |
| `StructureRestrictionHomomorphism` | restriction to a smaller open set is a ring homomorphism |
| `StructureSheafOfRings` | the sections form a sheaf of rings on the spectrum |

## The localizations

| member | statement |
|---|---|
| `CoefficientSectionHomomorphism` | the coefficient-section map is a ring homomorphism on every open set |
| `BasicOpenCoefficientKernel` | a coefficient vanishing on `D(h)` is killed by a power of `h` |
| `BasicOpenSectionKernel` | a section on `D(f)` vanishing on `D(f) ∩ D(h)` is killed on `D(f)` by a power of `h` |
| `BasicOpenSectionRepresentation` | a section on `D(f)` becomes a coefficient section after multiplication by a power of `f` |
| `SectionsAtBasicOpen` | the coefficient sections make the sections over `D(f)` a localization at the powers of `f` |
| `GlobalSections` | the coefficient-section map identifies the ring with its global sections |
| `StalkAtPrime` | the coefficient germs make the stalk at `p` a localization at `R.carrier ∖ p` |
| `SpecLocallyRinged` | the spectrum is a locally ringed space |
