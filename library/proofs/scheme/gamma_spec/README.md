# gamma_spec — maps to a spectrum and homomorphisms on global sections

For a locally ringed space X and a commutative ring R, a morphism X → Spec R gives a homomorphism R → Γ(X). Conversely a ring homomorphism determines a prime at each point from the nonunits of its stalk and a section by its germs on local fraction neighbourhoods. The two constructions are inverse on carrier points and valid sections. Naturality is outside this chapter.

The section definition uses Hilbert choice. Its specification includes membership in the section carrier; the inverse germ is also chosen with stalk membership and its product equation. For an arbitrary section, the chosen section is read through AdjunctSectionGerm, whose existence is glued on the pullback of each neighbourhood W on which the local fraction represents the section. AdjunctionLeft needs neither: for the global coefficient section, α(a) itself meets the specification, so the proof reads the choice in specAdjunctSectionDef directly.

| member | statement |
|---|---|
| GlobalSectionHomDef | compose the global fraction section `fraction_section(R, prime_spectrum(R), a, R.one)` with the morphism section map |
| specAdjunctPointDef | elements whose global germs are nonunits form the assigned subset |
| specAdjunctSectionDef | choose the section specified by every local fraction |
| GlobalSectionHom | the forward construction is a ring homomorphism — card |
| AdjunctPointPrime | the point assigned to x is prime: the contraction of the stalk's maximal ideal along α followed by taking germs |
| AdjunctPointInSpectrum | the point assigned to x lies in Spec R |
| AdjunctPointContinuous | the point map is continuous, and the preimage of D(a) is the unit locus of α(a) |
| AdjunctSectionExists | local quotients glue on pullbacks of their representation neighbourhoods — card |
| AdjunctSectionGerm | the chosen section belongs to the section carrier and satisfies its specification — card |
| AdjunctSectionHomomorphism, AdjunctSectionRestrict | the section maps preserve ring operations and restrictions — cards |
| AdjunctStalkLocal, AdjunctMorphism | the stalk maps are local and the construction is an LRS morphism — cards |
| AdjunctionLeft | the section assignment recovers the original ring homomorphism on its carrier |
| AdjunctionRight | a locally ringed-space morphism is recovered from its map on global sections — card |
| AffineMorphisms, AffineMorphismsInverse | recover the ring map of an affine morphism, and recover a ring map from its Spec morphism — cards |

The affine recovery map uses `inverse_on` on the ring carrier and the global fraction map `b ↦ fraction_section(S, prime_spectrum(S), b, S.one)` to recover the unique element whose global section is the given one. The first affine card includes its ring-homomorphism property and the point and section equations. The second states recovery of the original ring map on its carrier. These equations express the hom-set correspondence without a Hom type or a categorical equivalence object.
