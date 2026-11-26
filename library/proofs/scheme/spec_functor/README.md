# spec_functor — contraction on spectra and pullback of regular sections

A ring homomorphism R → S gives a locally ringed space morphism from
Spec S to Spec R. Its point map contracts prime ideals: it is
`preimage_on(R, φ)`, the preimage cut to the source ring. Its section map
applies the ring homomorphism to the numerator and denominator of each
local fraction and is empty outside the carrier-restricted preimage.
The composition and identity equations are stated on space points and
valid sections; values of the total maps outside these carriers are free.

## The maps and their laws

| member | statement |
|---|---|
| `SpecSectionMapDef` | pointwise fraction maps on the preimage, empty elsewhere |
| `SpecPointMapExtensional` | maps agreeing on the carrier induce the same map on spectrum points |
| `SpecSectionMapExtensional` | maps agreeing on the carrier induce the same map on valid sections |
| `PreimagePrime` | the contraction `preimage_on(R, φ, q)` of a prime ideal along a ring homomorphism is prime |
| `SpecMapContinuous` | the point map is continuous and the preimage of D(a) is D(φ(a)) |
| `SpecSectionIn` | the image of a regular section is a regular section — card |
| `SpecSectionHomomorphism` | the section maps are ring homomorphisms — card |
| `SpecSectionRestrict` | section maps commute with restrictions |
| `SpecStalkLocal` | the induced stalk map preserves nonunits on its stalk carrier — card |
| `SpecMorphism` | the two maps define a locally ringed space morphism — card |
| `SpecCompose` | the point and section equations for composition — card |
| `SpecIdentity` | the identity of R fixes each point of Spec R and each regular section |
| `SpecIsomorphism` | a ring isomorphism induces an isomorphism of locally ringed spectra in the reverse direction |

The extensionality laws read only the source carrier. For sections,
each section value at a point of its domain is a fraction class,
and every representative has both coordinates in that carrier. Agreement
there therefore suffices for the fraction maps. The point law identifies
their preimage guards, and both section maps are empty
outside those guards.

The carrier inverse of a ring isomorphism induces the inverse spectrum
morphism. Carrier extensionality turns the two ring composites into the
identity on points and sections. This theorem uses the stated morphism,
composition and identity laws and the locally ringed space inverse criterion.

## Basic open spectra

| member | statement |
|---|---|
| `BasicOpenAffine` | the restriction of Spec R to D(f) is isomorphic to the spectrum of the localization at the powers of f — card |

BasicOpenAffine identifies the restriction to D(f) with the spectrum of the localization at the powers of f. The point correspondence is extension and contraction of primes. SectionsAtBasicOpen and LocalizationAtProduct give the section rings the same localization interface, and LocalizationIsomorphism compares them uniquely on coefficients. LocalizationHomomorphismExtensional gives compatibility with restrictions. The section and stalk interfaces use their ring records.
