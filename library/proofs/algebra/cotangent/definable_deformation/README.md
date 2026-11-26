# definable_deformation — marked extension codes and definable algebra deformations

A marked square-zero extension is represented on N × S by its additive,
multiplicative and base-structure defects (alpha, beta, rho). The code
ring has fixed inclusion n ↦ (n,0), projection to S and structure map
r ↦ (rho(r),f(r)). Every array is normalized off its carrier. The unit is
(-beta(1,1),1); the chosen section preserves zero but need not preserve one.

Valid codes form a closed additive subgroup of a countable product of
discrete coefficient groups. Changes of section are normalized functions
h with h(0)=0. Their actual coboundary image is Polishable; it is never
replaced by its closure. This gives Exal its Polish cover and realizes its
classes as actual marked extensions, including countable ring codes on num.

The conormal comparison uses the reduced subgroup h(x_0)=0. The full
standard conormal model splits off a contractible copy of N; continuous
reduction identifies the quotient covers. Using all functions S→N as
changes of section would violate the fixed inclusion at zero.

`operations.go` supplies coefficient pushforward,
algebra pullback and continuous additive lifts of localization. Such a
localization lift uses fixed fraction representatives; independently
chosen lifts are not asserted to compose strictly. The cover chapter
therefore records actual extension maps at every intersection.

`deformations.go` imposes rho|ker(R→R0)=iota. The result is a closed affine
coset, empty exactly when the existing AQ obstruction is nonzero. Its
difference group is the inflated R0-extension code group; gauge kernels
are normalized R0-derivations. Flatness requires the separate hypotheses
of algebra_deformation.DeformationIffFlat.

The finite-presentation model records conormal maps on finitely many
relations, with boundaries from finitely many generator values. Finite
coefficients make the code and boundary spaces compact. The dyadic
polynomial example has $x_k = 2x_{k+1}$, zero augmentation and Der tower
(Z,×2); its phantom classes are modeled by Z_2/Z and realized by codes.
The general phantom comparison is in [definable_andre_quillen](../definable_andre_quillen/README.md).

All theorem entries below are unfilled cards. Definitions introduce only
structures and explicit maps; no proof session or theorem fill is included.

## Members

| Member | Status | Statement and purpose |
|---|---|---|
| `FactorSetCodesClosed` | card | Expand the explicit ring and marking axioms. — card |
| `FactorSetCoboundaryContinuous` | card | Changing the split extension section by a zero-preserving h gives the displayed coboundary. — card |
| `FactorSetCodesPolishCover` | card | The ambient countable discrete products and the closed gauge subgroup are Polish. — card |
| `FactorSetShear` | card | Expand additivity, multiplication and the structure map of the shear. — card |
| `FactorSetIsoIffBoundary` | card | Every marked isomorphism is a unique normalized shear on the carrier. — card |
| `factorSetExtractDef` | definition | Read additive, multiplicative and base-map defects through the inverse of the fixed inclusion. |
| `FactorSetRealization` | card | Each extension element has a unique kernel component relative to the section. — card |
| `factorSetClassDef` | definition | The code quotient class maps to the existing AQ degree-one class. |
| `FactorSetAQDefinableIso` | card | The homeomorphic model uses h(x_0)=0. — card |
| `reducedConormalCodesDef` | definition | Conormal maps that vanish at the zero generator. |
| `conormalFactorSetDef` | definition | Evaluate a conormal map on the additive, multiplicative and base-ring relations, with zero off their carriers. |
| `FactorSetConormalAgreement` | card | The three relation families generate the standard presentation kernel. — card |
| `leastExtensionSectionDef` | definition | The least preimage on natural-number ring codes, overridden at zero to preserve the fixed marking. |
| `countableExtensionTopologyDef` | definition | The pointwise discrete topology on the carrier predicate, ring operation tables and marking tables of extensions on num. |
| `CountableRingCodeExtraction` | card | Near a fixed valid code each least preimage is certified by finitely many tests below its value. — card |
| `CountableRingCodeClassification` | card | Both extracted codes realize their marked extensions; FactorSetIsoIffBoundary gives the equivalence. — card |
| `FactorSetAmbientDef` | definition | Three normalized function spaces for additive defect, multiplicative defect and structure defect, with pointwise addition. |
| `FactorSetTopologyDef` | definition | The topology of pointwise discrete coefficient values on all three defect arrays. |
| `factorSetRingDef` | definition | The ring operations of a zero-preserving section. |
| `FactorSetExtensionDef` | definition | The fixed markings are n ↦ (n,0), projection to S, and r ↦ (rho(r),f(r)). |
| `FactorSetCodesDef` | definition | Valid normalized defects are exactly the arrays for which the explicit operations and fixed markings form a square-zero extension. |
| `FactorSetGaugeDef` | definition | Zero-preserving, off-carrier-normalized changes of section. |
| `FactorSetCoboundaryDef` | definition | The three components are h(s)+h(t)-h(s+t), s*h(t)+t*h(s)-h(st), and -h(f(r)). |
| `factorSetGroupDef` | definition | The additive group record of valid factor sets. |
| `FactorSetBoundariesDef` | definition | Actual coboundaries, with no closure. |
| `DeformationCodesDef` | definition | Codes whose structure defect restricts to the prescribed map on the thickening ideal. |
| `deformationCodeKernelDef` | definition | The subgroup of codes whose base structure map factors through R0. |
| `DeformationCodesCoset` | card | The rho conditions are closed affine coordinate equations. — card |
| `DeformationKernelIsReducedBase` | card | Inflate rho along the surjection p. — card |
| `DeformationCodesNonemptyIffObstruction` | card | Use DeformationObstruction and extract a code from the resulting marked extension along a zero-preserving section. — card |
| `DeformationCodeAutomorphisms` | card | The zero additive and multiplicative defects are additivity and the Leibniz rule; the zero rho defect forces vanishing on g(R0) because p is onto. — card |
| `ExalCountableOrContinuum` | card | Read PolishCoverCountableIffOpen on FactorSetCodesPolishCover. — card |
| `ExalClosedBoundaryPolish` | card | Apply ClosedCoverQuotientPolish to the actual boundary subgroup. — card |
| `FiniteCoefficientExalCompact` | card | All coefficient factors are finite discrete compact spaces. — card |
| `dyadicPolynomialUnionDef` | definition | An increasing union of polynomial integer rings whose variable at stage k is twice the next variable, with the zero augmentation. |
| `DyadicPolynomialUnionExists` | card | Construct the injective direct limit of Z[x] under x↦2x, or the subring Z+x Z[1/2][x] in Q[x], and enumerate its countable carrier. — card |
| `DyadicPhantomExtensions` | card | Every displayed class splits at every polynomial stage. — card |
| `DyadicDerivationTower` | card | The degree-zero AQ cocycle is the normalized derivation, and a derivation of Z[x_k] with zero-augmentation coefficients is uniquely determined by its value on x_k. — card |
| `finiteConormalCodesDef` | definition | Conormal maps recorded only on the specified relation generators, normalized outside them. |
| `finiteConormalBoundariesDef` | definition | The image of the finite generator-value space N^X under relation evaluation of the free derivation. |
| `FinitePresentationExalModel` | card | The relation generators need not be independent and the quotient need not be finitely generated. — card |
| `ExalCoefficientCodesContinuous` | card | Postcompose defects with the coefficient map. — card |
| `ExalPullbackCodesContinuous` | card | Precompose the two defect arrays by g in both variables, retaining rho. — card |
| `LocalizedCodeContinuous` | card | This is a continuous additive lift for each localization arrow. — card |
