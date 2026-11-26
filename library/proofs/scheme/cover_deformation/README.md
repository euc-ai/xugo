# cover_deformation — countable affine intersection data and definable deformation obstructions

The objects are affine-cover data: rings and modules at every finite
nonempty set of chart indices, with principal localization arrows and
strict identity and composition. Extensions and deformations are local
marked objects with gluing data. Constructing a glued scheme and proving
independence of arbitrary covers are outside this chapter.

`definitions.go` describes actual extensions and marked maps at every
intersection. `codes.go` represents these by local factor sets $z_\sigma$
and arrow functions $\eta_{\sigma,\tau}$. The map on extension elements is
(n,s) ↦ (nu(n)+eta(s),g(s)). Its strict composition is the linear equation
$\eta_{\sigma,\upsilon} = \nu_{\tau,\upsilon} \eta_{\sigma,\tau} + \eta_{\tau,\upsilon} g_{\sigma,\tau}$. This avoids assuming that independent
choices of sections for localized codes compose strictly.

Derivations extend uniquely by the existing quotient rule. Their
normalized pointwise groups are closed Polish groups and their restrictions
are continuous. The finite-intersection Cech complex is the ordered-tuple
variant in [cech_cohomology](../../topology/cech_cohomology/README.md).
AQ cohomology classes also form a strict restriction diagram: standard
resolution maps compose strictly on carriers, and the localization right
map is inverted uniquely on cohomology. Pointwise dual standard complexes
alone do not give a strict covariant restriction diagram: the natural
algebra-map transpose goes in the opposite direction. For A → B with a
coefficient map N_A → N_B, the natural diagram is

$$
K(A,N_A) \to K(A,N_B) \leftarrow K(B,N_B).
$$

The right arrow is a quasi-isomorphism for localization, not necessarily
an isomorphism in each degree. For Z → Z[1/2] with coefficients Z[1/2],
the degree-zero functional supported at the generator named 1/2 is
nonzero but pulls back to zero. This example already lies in a common
ambient field. On cohomology the unique inverse gives restriction;
coefficient naturality and strict composition give its presheaf laws.
Separate local resolution comparisons do not supply compatible cochain
inverses. No additional cochain strictification is assumed here.

The local-to-global exact sequence is

$$
0 \to H^1(\operatorname{Der}) \to \operatorname{Exal} \to H^0(T^1) \to H^2(\operatorname{Der}).
$$

Comparison codes retain individual actual maps without composition.
Their six path defects around a triangle give d2. Comparison codes modulo
locally split codes provide a Polish cover of H0(T1), whose sections need
not be Polish quotient groups. The exact-sequence lifts are split gluing,
inclusion of compositional codes, and the explicit triple defect.

A base thickening gives three obstruction stages: the compatible local
T2 class, a choice-independent matching class in H1(T1), and finally a
class in H2(Der)/image(d2). A specified compatible local family glues
exactly when its unquotiented triple class vanishes. When deformations
exist, their classes form an $\operatorname{Exal}_{R_0}$ torsor; each nonempty fiber over a
fixed local family is an H1(Der) torsor. Smooth local charts remove T1 and
T2 but do not by themselves remove the H2(Der) obstruction. Both earlier
obstructions have Borel lifts to arrays of actual local AQ cocycles.

The two-chart interface specializes to the existing
[biaffine_deformation](../biaffine_deformation/README.md) marked objects.
The infinite nodal chain uses an initial affine-line chart and countably
many K[x,y]/(xy) node charts, with reciprocal Laurent overlaps. Its local
smoothing parameters form a full infinite product. The projective-plane
calibration has three standard ratio charts: triple cochains are nonzero,
although H2 of its tangent derivation sheaf vanishes by its specific
Laurent computation. These are cover data, without a new scheme-gluing layer.

Polish coefficients, noninjective algebra colimits, completions,
cover-independence, and formal moduli stacks are not asserted. All theorem
entries below are unfilled cards.

## Members

| Member | Status | Statement and purpose |
|---|---|---|
| `biaffineCoverRingsDef` | definition | Chart zero, repeated chart one, and their overlap, read inside the old overlap ring. |
| `biaffineCoverModulesDef` | definition | The old chart modules and their common localized span. |
| `biaffineCoverDenominatorsDef` | definition | Identity arrows invert one; the two chart-to-overlap arrows invert the prescribed biaffine denominators. |
| `BiaffineCoverDatum` | card | The existing chart-localization and span-localization theorems give every nonidentity arrow. — card |
| `biaffineCoverGluingDef` | definition | Both localizations map isomorphically to the coded overlap extension; compose the first map with the inverse of the second. |
| `BiaffineCoverSpecialization` | card | The two actual maps to the overlap are localizations by CoverExtensionMapsLocalize, so their comparison is the old marked biaffine gluing isomorphism. — card |
| `BiaffineExtensionCoverRealization` | card | Together with CoverExtensionIsoIffBoundary this identifies the new marked code classification with the existing biaffine classification; changing lifts is allowed by the old isomorphism predicate. — card |
| `coverArrowsDef` | definition | All inclusion arrows between finite nonempty intersections. |
| `coverCodeAmbientDef` | definition | Pointwise addition on local defects and arrow shears, with explicit normalization at inactive intersections and scalar coordinates. |
| `coverCodeTopologyDef` | definition | Countable products of local defect arrays and normalized arrow functions. |
| `coverCodeExtensionsDef` | definition | The local marked extension encoded by the local factor set. |
| `coverCodeMapsDef` | definition | Actual maps on extension elements. |
| `coverComparisonCodesDef` | definition | Local codes and actual marked maps on individual arrows, without composition equations. |
| `coverExtensionCodesDef` | definition | Impose the linear strict-composition equations on actual extension maps. |
| `coverGaugeGroupDef` | definition | The countable product of zero-preserving normalized section changes. |
| `coverGaugeTopologyDef` | definition | Product of the closed zero-preserving gauge groups. |
| `coverCoboundaryDef` | definition | Local section coboundaries and the conjugation shear nu(gamma_source)-gamma_target after g. |
| `coverBoundariesDef` | definition | The image of simultaneous changes of coordinates, not its closure. |
| `coverDatumDef` | definition | Countably indexed affine intersection data with principal localization arrows and strictly compatible ring and module maps. |
| `coverExtensionDef` | definition | An actual extension at every finite intersection, with marked maps and strict composition. |
| `coverExtensionIsoDef` | definition | Objectwise marked isomorphisms commuting with every intersection map. |
| `CoverExtensionMapsLocalize` | card | Thus actual intersection diagrams recover the usual localized gluing data without imposing artificial strictness on section choices. — card |
| `coverDeformationDatumDef` | definition | A square-zero base thickening, a cover over its reduction, and compatible coefficient maps from the thickening ideal. |
| `coverDeformationComparisonsDef` | definition | Impose the prescribed rho values on the thickening ideal at every intersection. |
| `coverDeformationCodesDef` | definition | Impose the prescribed rho values on the thickening ideal at every intersection. |
| `coverLocalDeformationsDef` | definition | Independent local deformation codes; there are no overlap maps or compatibility assumptions. |
| `coverInflateDef` | definition | Inflate only the rho component along the base surjection; arrow shears and other defects are unchanged. |
| `CoverDeformationCodesCoset` | card | The local affine rho equations are closed. — card |
| `CoverDeformationsTorsor` | card | Translate by the fixed deformation, use the inflation isomorphism onto the difference subgroup, and pass to actual boundary subgroups. — card |
| `coverLocalObstructionDef` | definition | The local algebra deformation obstructions as a degree-zero Cech class. |
| `CoverLocalObstruction` | card | Naturality of the transitivity connecting map makes the local obstruction classes compatible. — card |
| `coverMatchingCochainDef` | definition | The unique reduced-base torsor difference between the two localized local deformations on each ordered pair. |
| `coverMatchingObstructionDef` | definition | Choose independent local deformation codes and take the class of their matching cochain. |
| `CoverMatchingObstruction` | card | The torsor difference telescopes on triples. — card |
| `CoverThirdObstruction` | card | The choice-independent third obstruction lives in H2(Der) modulo image(d2). — card |
| `SmoothCoverDeformationObstruction` | card | Vanishing T2 removes the first obstruction and vanishing T1 removes the matching obstruction and the image of d2. — card |
| `nodalChainCoverDef` | definition | An affine line at the left end and countably many node charts K[x,y]/(xy), adjacent branches glued by reciprocal coordinates; nonadjacent overlaps are empty. |
| `NodalChainCoverExists` | card | Use the displayed node and affine-line rings, Laurent overlaps on adjacent charts and the zero ring elsewhere. — card |
| `NodalChainAQCalibration` | card | Every finite collection of chart indices misses a node with nonzero T1, so the chart datum is genuinely infinite. — card |
| `projectivePlaneCoverDef` | definition | The three polynomial standard charts of projective two-space, localized at the omitted homogeneous coordinate ratios and glued by their ratio identities. |
| `ProjectivePlaneCoverExists` | card | Take the degree-zero parts of the homogeneous localizations of K[X0,X1,X2], one for each nonempty subset of the three coordinates, and transport their countable carriers to num. — card |
| `ProjectivePlaneTripleCalibration` | card | The triple cocycle equation is genuinely tested even though this particular smooth cover has vanishing final obstruction group. — card |
| `coverRepeatedDef` | definition | Strictly repeated chart data indexed by a retraction of num onto a finite set. |
| `TwoChartCoverExact` | card | FiniteRepeatedCoverVanishing kills H2(Der); CoverExtensionExactSequence then makes the local-class map onto. — card |
| `CoverExalCountableOrContinuum` | card | Apply the common Polish-cover countability and Baire dichotomy to the actual extension code cover. — card |
| `coverThickeningTopologyDef` | definition | The pointwise topology on compatible thickening-ideal coefficient maps; values off the ideal and inactive intersections are zero. |
| `CoverLocalObstructionBorelLift` | card | The target is a product of actual AQ cocycle groups. — card |
| `CoverMatchingObstructionBorelLift` | card | The second lift is defined on the Borel locus where the first obstruction vanishes. — card |
| `CoverDeformationGluingFiber` | card | The full torsor is under cover Exal over R0; after fixing a compatible local family, each nonempty gluing fiber is a torsor under H1(Der). — card |
| `CoverExtensionCodesRealize` | card | Expand the explicit map formula. — card |
| `CoverExtensionCodesClosed` | card | The local factor-set equations, actual-map equations and composition equations are finite-coordinate homogeneous linear equations in z and eta. — card |
| `CoverCoboundaryContinuous` | card | Conjugate the split extension diagram by the simultaneous zero-preserving shears. — card |
| `CoverExtensionCodesPolishCover` | card | Finite nonempty subsets of num and their arrows are countable. — card |
| `CoverExtensionIsoIffBoundary` | card | Objectwise marked isomorphisms are normalized shears. — card |
| `CoverExtensionExtraction` | card | Extract each local factor set. — card |
| `localizedDerivationDef` | definition | The existing quotient-rule derivation, normalized to zero off the localization carrier. |
| `coverDerivationModuleDef` | definition | Normalized derivations form an R-module by the chart structure map. |
| `coverDerivationRestrictionDef` | definition | Postcompose coefficients and uniquely extend across the localization. |
| `coverDerivationTopologyDef` | definition | Ambient pointwise topologies; intersect with the derivation carrier when making a Polish group. |
| `DerivationLocalizationUnique` | card | The quotient rule determines d(s/a^k), proves independence of representatives and supplies the unique extension. — card |
| `DerivationPresheaf` | card | Uniqueness of derivation localization proves identity, composition and linearity of restriction. — card |
| `DerivationPresheafPolish` | card | Derivation equations are closed finite-coordinate conditions. — card |
| `coverAQModuleDef` | definition | AQ cohomology read as an R-module; no Polish quotient topology is imposed. |
| `coverAQRestrictionDef` | definition | The named localization restriction on AQ classes. |
| `AQPresheaf` | card | This is an algebraic diagram. — card |
| `coverPathDefectDef` | definition | The difference of the two actual maps from sigma to upsilon, uniquely extended as a derivation on the terminal intersection. |
| `coverTripleDefectDef` | definition | The six path defects around a triangle. |
| `coverLocalClassDef` | definition | The compatible singleton extension classes, read as a degree-zero Cech class. |
| `coverLocalKernelDef` | definition | Comparison data with locally split classes; arrow comparison choices remain in the kernel. |
| `coverD2Def` | definition | Choose concrete comparison data for the given compatible local classes and take its triple-defect class. |
| `coverAnchorDef` | definition | The least chart index of a finite nonempty intersection. |
| `coverGlueCodeDef` | definition | Glue split local extensions using the cocycle between the least index of each intersection and that of its parent. |
| `CoverTripleDefectCocycle` | card | Each path defect is a derivation; compare the four compositions around a quadruple intersection to obtain the alternating cocycle identity. — card |
| `CoverLocalClasses` | card | The assertion is algebraic and does not assume the quotient groups are Polish. — card |
| `CoverD2WellDefined` | card | Choose local marked isomorphisms between the two representatives. — card |
| `CoverExtensionExactSequence` | card | This is 0→H1(Der)→Exal→H0(T1)→H2(Der); no surjectivity of the last map is asserted. — card |
| `CoverLocalClassesPolishCover` | card | The witness-rich source is a cover for H0(T1). — card |
| `CoverSequenceDefinable` | card | The three lifts are the explicit split gluing map, inclusion of strictly compositional codes into comparison codes, and the six-term triple defect. — card |
| `CoverExtensionAutomorphisms` | card | The kernel of the simultaneous gauge action consists of derivations compatible with all restrictions. — card |
