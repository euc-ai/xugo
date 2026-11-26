// obstruction.go — the deformations of a curve held by two charts over a
// thickening R → R₀ with square-zero kernel J, the curve over R₀ through
// g and the coefficients a lattice pair M with a map ι from J into
// H⁰(M). The obstruction comes in two levels. The local one is the pair
// of the charts' obstructions ∂¹(ξ) in D²(A₀/R₀, M₀) × D²(A₁/R₀, M₁): it
// vanishes exactly when each chart has a deformation. Then the chart
// deformations localize to deformations of the overlap, whose classes
// differ by the left map's image of one δ in D¹(A₀₁/R₀, M₀₁); the class
// of δ modulo the restrictions of the charts' D¹ is the gluing
// obstruction, which does not depend on the chart deformations and
// vanishes exactly when the curve has a deformation. The deformations,
// when there are any, move in two layers: their chart classes by the
// compatible pairs of classes over R₀, and on each fibre by regluing,
// freely modulo Der(A₀, M₀) + Der(A₁, M₁). With both charts smooth both
// obstructions vanish and the deformations are an H¹(𝒟⁰)-torsor.

package biaffine_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/algebra_deformation"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_examples"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/square_zero_classification"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/transitivity"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/quotient_group"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/square_zero_extension"
	"github.com/euc-ai/xugo/library/proofs/scheme/lattice_pair"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements over a thickening
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The derivations over the thickening
// ---------------------------------------------------------------------------

// ThickeningDerivationsAgree — when f maps R onto R₀, the derivations of
// the overlap over R through g ∘ f are those over R₀ through g, and so is
// the derivation pair.
var ThickeningDerivationsAgree = thickeningDerivationsAgreeThm{family.Add(registry.ProofEntry{
	Name: "ThickeningDerivationsAgree",
	Key:  "prop_95afc8f91c766179",
	Reading: "f onto is load-bearing: a derivation over R kills g(f(a)) for every a, " +
		"which is every g(b) only when every b is some f(a). It lets a statement about a " +
		"biaffine extension over the base R — its automorphisms (BiaffineAutomorphisms), its " +
		"regluings (ExalSequence) — be read with H⁰ and H¹ of the derivation pair over R₀.",
	Deps: []registry.EntryLike{
		biaffineOverlapDerivationsDef,
		biaffineDerivationPairDef,
		partial_derivative.DerivationOn,
		ring_homomorphism.RingHomomorphism,
		ring_homomorphism.MapIn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)).",
		Hypotheses: []string{
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"ring_homomorphism(R₀, A₀₁, g)",
		},
		Conclusion: "biaffine_overlap_derivations(R, λa:A. g(f(a)), A₀₁, V, M) = " +
			"biaffine_overlap_derivations(R₀, g, A₀₁, V, M) ∧ " +
			"biaffine_derivation_pair(R, λa:A. g(f(a)), A₀₁, A₀, A₁, V, M) = " +
			"biaffine_derivation_pair(R₀, g, A₀₁, A₀, A₁, V, M)",
	},
		"the two records have the same operations, so it is the carriers "+
			"(biaffineOverlapDerivationsDef): g ∘ f is a ring map from R as both are (RingHomomorphism, "+
			"MapIn), and the clause d(g(f(a))) = zero for every a in R is the clause d(g(b)) = zero for "+
			"every b in R₀, f being onto (DerivationOn); the pairs follow (biaffineDerivationPairDef)"),
})}

// ---------------------------------------------------------------------------
// The local obstruction
// ---------------------------------------------------------------------------

// LocalDeformationsExistIff — each chart has a deformation exactly when
// the local obstruction vanishes; a deformation of one chart kills that
// chart's component.
var LocalDeformationsExistIff = localDeformationsExistIffThm{family.Add(registry.ProofEntry{
	Name: "LocalDeformationsExistIff",
	Key:  "prop_91660d5755a197d6",
	Reading: "The two charts are independent here: nothing about the overlap enters " +
		"the first level. The existence is stated at the realizations' type set(prod(U, " +
		"D)), where every class has an extension; the vanishing holds of a deformation on " +
		"any type. ι lands in H⁰(M) = M₀ ∩ M₁, so it is a coefficient map for each chart.",
	Deps: []registry.EntryLike{
		biaffineLocalObstructionDef,
		algebra_deformation.DeformationObstruction,
		algebra_deformation.AlgebraDeformationObstructionDef,
		lattice_pair.LatticePairDef,
		module_homomorphism.ModuleHomomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀ι:(A → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, A₀₁, g)",
			"image(g, R₀.carrier) ⊆ A₀ ∩ A₁",
			"module_homomorphism(R₀, " +
				"    thickening_kernel(R, R₀, f), " +
				"    restrict_module(scalar_restriction(g, V), fst(M) ∩ snd(M)), " +
				"    ι)",
		},
		Conclusion: "((∃E₀:square_zero_ops(A, C, set(prod(U, D)), D). " +
			"        algebra_deformation(R, R₀, f, restrict_ring(A₀₁, A₀), g, «wg3Module0», ι, E₀)) ∧ " +
			"    (∃E₁:square_zero_ops(A, C, set(prod(U, D)), D). " +
			"        algebra_deformation(R, R₀, f, restrict_ring(A₀₁, A₁), g, «wg3Module1», ι, E₁)) ⇔ " +
			"    «wg3LocalObstruction» = «wg3LocalZero») ∧ " +
			"(∀E₀:square_zero_ops(A, C, I, D). " +
			"    algebra_deformation(R, R₀, f, restrict_ring(A₀₁, A₀), g, «wg3Module0», ι, E₀) ⇒ " +
			"    fst(«wg3LocalObstruction») = «wg3SecondZero0») ∧ " +
			"(∀E₁:square_zero_ops(A, C, H, D). " +
			"    algebra_deformation(R, R₀, f, restrict_ring(A₀₁, A₁), g, «wg3Module1», ι, E₁) ⇒ " +
			"    snd(«wg3LocalObstruction») = «wg3SecondZero1»)",
	},
		"each chart with its module and ι is the situation of DeformationObstruction: g is a ring "+
			"map into the chart, the chart module a module over it (LatticePairDef), and ι linear "+
			"into H⁰(M) is linear into each chart module, which holds H⁰(M) with the same operations "+
			"(ModuleHomomorphismDef). DeformationObstruction at each chart gives each component, and "+
			"the pair is the zero pair exactly when both are (biaffineLocalObstructionDef)"),
})}

// ---------------------------------------------------------------------------
// The gluing obstruction
// ---------------------------------------------------------------------------

// LocalizedLiftsSameImage — for classes ζ₀, ζ₁ of deformations of the two
// charts, their restrictions to the overlap both go to the overlap's
// thickening class under the right map, and their difference is the left
// map's image of exactly one δ in D^1(A₀₁/R₀, M₀₁).
var LocalizedLiftsSameImage = localizedLiftsSameImageThm{family.Add(registry.ProofEntry{
	Name: "LocalizedLiftsSameImage",
	Key:  "prop_f23fee084de26b6f",
	Reading: "The restriction of the class of a chart deformation is the class of its " +
		"localization (SquareZeroLocalizationClass), a deformation of the overlap with the " +
		"same ι (DeformationLocalizes), so its right-map image is the overlap's thickening " +
		"class. The difference then lies in the kernel of the right map, the left map's image " +
		"by exactness, and f onto makes the left map injective (RestrictionMapInjective): δ " +
		"is unique. A deformation class is the class of a chart deformation, its realization " +
		"(DeformationIffPullbackClass, RightMapIsPullback, ExtensionRealizeClass).",
	Deps: []registry.EntryLike{
		algebra_deformation.DeformationIffPullbackClass,
		algebra_deformation.RightMapIsPullback,
		algebra_deformation.DeformationLocalizes,
		algebra_deformation.SquareZeroLocalizationClass,
		algebra_deformation.RestrictionMapInjective,
		square_zero_classification.ExtensionRealizeClass,
		transitivity.CotangentCohomologyTransitivity,
		lattice_pair.BiaffineChartLocalization,
		square_zero_extension.SpanIsModuleLocalization,
		module_homomorphism.ExactAtDef,
		cotangent_complex.CotangentCohomologyModuleOn,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀ι:(A → D). " +
			"∀ζ₀ ζ₁:set(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, A₀₁, g)",
			"image(g, R₀.carrier) ⊆ A₀ ∩ A₁",
			"module_homomorphism(R₀, " +
				"    thickening_kernel(R, R₀, f), " +
				"    restrict_module(scalar_restriction(g, V), fst(M) ∩ snd(M)), " +
				"    ι)",
			"ζ₀ ∈ " +
				"cotangent_cohomology(R, " +
				"    restrict_ring(A₀₁, A₀), " +
				"    λa:A. g(f(a)), " +
				"    restrict_ring(A₀₁, A₀), " +
				"    λc:C. c, " +
				"    «wg3Module0», " +
				"    1).carrier",
			"co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₀), g, «wg3Module0», 1, ζ₀) = " +
				"thickening_class(R, R₀, f, «wg3OverReduced»(fst(M)), ι)",
			"ζ₁ ∈ " +
				"cotangent_cohomology(R, " +
				"    restrict_ring(A₀₁, A₁), " +
				"    λa:A. g(f(a)), " +
				"    restrict_ring(A₀₁, A₁), " +
				"    λc:C. c, " +
				"    «wg3Module1», " +
				"    1).carrier",
			"co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₁), g, «wg3Module1», 1, ζ₁) = " +
				"thickening_class(R, R₀, f, «wg3OverReduced»(snd(M)), ι)",
		},
		Conclusion: "«wg3OverlapRight»(«wg3ThickeningRestriction0»(ζ₀)) = «wg3OverlapThickeningClass» ∧ " +
			"«wg3OverlapRight»(«wg3ThickeningRestriction1»(ζ₁)) = «wg3OverlapThickeningClass» ∧ " +
			"(∃δ:set(U → D). " +
			"    δ ∈ «wg3OverlapOverReduced».carrier ∧ " +
			"    «wg3OverlapOverThickening».add(«wg3ThickeningRestriction0»(ζ₀), " +
			"        «wg3OverlapOverThickening».neg(«wg3ThickeningRestriction1»(ζ₁))) = " +
			"    «wg3OverlapLeft»(δ) ∧ " +
			"    (∀δ':set(U → D). " +
			"        δ' ∈ «wg3OverlapOverReduced».carrier ∧ " +
			"        «wg3OverlapOverThickening».add(«wg3ThickeningRestriction0»(ζ₀), " +
			"            «wg3OverlapOverThickening».neg(«wg3ThickeningRestriction1»(ζ₁))) = " +
			"        «wg3OverlapLeft»(δ') ⇒ " +
			"        δ' = δ))",
		Abbrev: Abbrev{
			{Name: "wg3OverlapOverReduced", Text: "cotangent_cohomology(R₀, " +
				"    A₀₁, " +
				"    g, " +
				"    A₀₁, " +
				"    λc:C. c, " +
				"    «wg3Overlap», " +
				"    1)"},
			{Name: "wg3OverlapOverThickening", Text: "cotangent_cohomology(R, " +
				"    A₀₁, " +
				"    λa:A. g(f(a)), " +
				"    A₀₁, " +
				"    λc:C. c, " +
				"    «wg3Overlap», " +
				"    1)"},
			{Name: "wg3OverlapRight", Text: "co_transitivity_right_map(R, R₀, f, A₀₁, g, «wg3Overlap», 1)"},
			{Name: "wg3OverlapLeft", Text: "co_transitivity_left_map(R, R₀, f, A₀₁, g, «wg3Overlap», 1)"},
			{Name: "wg3OverlapThickeningClass", Text: "thickening_class(R, " +
				"    R₀, " +
				"    f, " +
				"    «wg3OverReduced»(lattice_pair_ambient(A₀₁, V, M)), " +
				"    ι)"},
		},
	},
		"realize ζ₀ (ExtensionRealizeClass): its realization is a deformation of chart 0 "+
			"(DeformationIffPullbackClass, RightMapIsPullback), localized at a lift of t a "+
			"deformation of A₀₁ with coefficients (M₀₁, ι) (DeformationLocalizes, in place by "+
			"BiaffineChartLocalization and SpanIsModuleLocalization) whose class is the restriction "+
			"of ζ₀ (SquareZeroLocalizationClass); its right-map image is the overlap's thickening "+
			"class (DeformationIffPullbackClass, RightMapIsPullback at A₀₁). The same at chart 1. "+
			"The right map is a homomorphism (CotangentCohomologyModuleOn), so it kills the "+
			"difference, which exactness at D¹(A₀₁/R, M₀₁) (CotangentCohomologyTransitivity, "+
			"ExactAtDef) makes the left map's image of some δ, unique by RestrictionMapInjective"),
})}

// GluingObstructionWellDefined — the gluing obstruction is a class of the
// gluing cokernel, and the same for any two pairs of deformation classes
// of the charts.
var GluingObstructionWellDefined = gluingObstructionWellDefinedThm{family.Add(registry.ProofEntry{
	Name: "GluingObstructionWellDefined",
	Key:  "prop_1f4788ff0e1e2d28",
	Reading: "Two deformation classes of a chart differ by the left map's image of one η " +
		"(DeformationsTorsor), and restriction carries ζ + i*(η) to res(ζ) + i*(res(η)) " +
		"(RestrictionCompatibleTorsor); so changing the chart deformations moves δ by res₀(η₀) − " +
		"res₁(η₁), a member of the sum of the images the cokernel divides by. The obstruction is " +
		"thus a class of the curve and ι alone, once the local obstruction vanishes. The coset " +
		"lies in the cokernel only because δ exists: with ζ₀ and ζ₁ deformation classes, the " +
		"difference of their restrictions is in the left map's image (LocalizedLiftsSameImage).",
	Deps: []registry.EntryLike{
		biaffineGluingObstructionDef,
		biaffineGluingCokernelDef,
		LocalizedLiftsSameImage,
		algebra_deformation.DeformationsTorsor,
		algebra_deformation.RestrictionMapInjective,
		cotangent_examples.RestrictionCompatibleTorsor,
		cotangent_examples.CotangentCohomologyRestrictionHom,
		quotient_group.InLeftCosets,
		quotient_group.InSetMul,
		submodule.QuotientModuleDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀ι:(A → D). " +
			"∀ζ₀ ζ_0' ζ₁ ζ_1':set(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, A₀₁, g)",
			"image(g, R₀.carrier) ⊆ A₀ ∩ A₁",
			"module_homomorphism(R₀, " +
				"    thickening_kernel(R, R₀, f), " +
				"    restrict_module(scalar_restriction(g, V), fst(M) ∩ snd(M)), " +
				"    ι)",
			"ζ₀ ∈ " +
				"cotangent_cohomology(R, " +
				"    restrict_ring(A₀₁, A₀), " +
				"    λa:A. g(f(a)), " +
				"    restrict_ring(A₀₁, A₀), " +
				"    λc:C. c, " +
				"    «wg3Module0», " +
				"    1).carrier",
			"co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₀), g, «wg3Module0», 1, ζ₀) = " +
				"thickening_class(R, R₀, f, «wg3OverReduced»(fst(M)), ι)",
			"ζ_0' ∈ " +
				"cotangent_cohomology(R, " +
				"    restrict_ring(A₀₁, A₀), " +
				"    λa:A. g(f(a)), " +
				"    restrict_ring(A₀₁, A₀), " +
				"    λc:C. c, " +
				"    «wg3Module0», " +
				"    1).carrier",
			"co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₀), g, «wg3Module0», 1, ζ_0') = " +
				"thickening_class(R, R₀, f, «wg3OverReduced»(fst(M)), ι)",
			"ζ₁ ∈ " +
				"cotangent_cohomology(R, " +
				"    restrict_ring(A₀₁, A₁), " +
				"    λa:A. g(f(a)), " +
				"    restrict_ring(A₀₁, A₁), " +
				"    λc:C. c, " +
				"    «wg3Module1», " +
				"    1).carrier",
			"co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₁), g, «wg3Module1», 1, ζ₁) = " +
				"thickening_class(R, R₀, f, «wg3OverReduced»(snd(M)), ι)",
			"ζ_1' ∈ " +
				"cotangent_cohomology(R, " +
				"    restrict_ring(A₀₁, A₁), " +
				"    λa:A. g(f(a)), " +
				"    restrict_ring(A₀₁, A₁), " +
				"    λc:C. c, " +
				"    «wg3Module1», " +
				"    1).carrier",
			"co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₁), g, «wg3Module1», 1, ζ_1') = " +
				"thickening_class(R, R₀, f, «wg3OverReduced»(snd(M)), ι)",
		},
		Conclusion: "«wg3GluingObstruction»(ζ₀, ζ₁) ∈ «wg3Cokernel».carrier ∧ " +
			"«wg3GluingObstruction»(ζ₀, ζ₁) = «wg3GluingObstruction»(ζ_0', ζ_1')",
	},
		"δ for (ζ₀, ζ₁) is the one of LocalizedLiftsSameImage, inverse_on picking it "+
			"(biaffineGluingObstructionDef), so its coset lies in the cokernel (InLeftCosets, "+
			"QuotientModuleDef). ζ₀' = ζ₀ + i*(η₀) and ζ₁' = ζ₁ + i*(η₁) (DeformationsTorsor); "+
			"restricting, res(ζ₀') − res(ζ₁') = res(ζ₀) − res(ζ₁) + i*(res₀(η₀) − res₁(η₁)) "+
			"over the overlap (RestrictionCompatibleTorsor, CotangentCohomologyRestrictionHom), "+
			"so δ' = δ + res₀(η₀) − res₁(η₁) by injectivity of the left map "+
			"(RestrictionMapInjective), and the cosets agree (InSetMul)"),
})}

// GluingObstructionZeroIffLift — for deformation classes of the two
// charts, the gluing obstruction vanishes exactly when some deformation
// classes of the charts have one restriction to the overlap, and exactly
// when the curve has a deformation.
var GluingObstructionZeroIffLift = gluingObstructionZeroIffLiftThm{family.Add(registry.ProofEntry{
	Name: "GluingObstructionZeroIffLift",
	Key:  "prop_8aad630f37de8b7c",
	Reading: "δ ∈ res₀(D¹(A₀)) + res₁(D¹(A₁)) means the chart deformations can be moved, by those " +
		"two classes, until their localizations have one class; then they are isomorphic and glue " +
		"(LocalClassOnto). The deformation is asserted on the realizations' type; a deformation on any " +
		"type gives compatible classes (LocalClassLandsInKernel over R), and the obstruction vanishes.",
	Deps: []registry.EntryLike{
		GluingObstructionWellDefined,
		LocalizedLiftsSameImage,
		LocalClassOnto,
		LocalClassLandsInKernel,
		BiaffineDeformationDef,
		biaffineGluingObstructionDef,
		algebra_deformation.DeformationsTorsor,
		algebra_deformation.DeformationIffPullbackClass,
		algebra_deformation.RightMapIsPullback,
		algebra_deformation.RestrictionMapInjective,
		cotangent_examples.RestrictionCompatibleTorsor,
		square_zero_classification.ExtensionRealizeClass,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀ι:(A → D). " +
			"∀ζ₀ ζ₁:set(U → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, A₀₁, g)",
			"image(g, R₀.carrier) ⊆ A₀ ∩ A₁",
			"module_homomorphism(R₀, " +
				"    thickening_kernel(R, R₀, f), " +
				"    restrict_module(scalar_restriction(g, V), fst(M) ∩ snd(M)), " +
				"    ι)",
			"ζ₀ ∈ " +
				"cotangent_cohomology(R, " +
				"    restrict_ring(A₀₁, A₀), " +
				"    λa:A. g(f(a)), " +
				"    restrict_ring(A₀₁, A₀), " +
				"    λc:C. c, " +
				"    «wg3Module0», " +
				"    1).carrier",
			"co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₀), g, «wg3Module0», 1, ζ₀) = " +
				"thickening_class(R, R₀, f, «wg3OverReduced»(fst(M)), ι)",
			"ζ₁ ∈ " +
				"cotangent_cohomology(R, " +
				"    restrict_ring(A₀₁, A₁), " +
				"    λa:A. g(f(a)), " +
				"    restrict_ring(A₀₁, A₁), " +
				"    λc:C. c, " +
				"    «wg3Module1», " +
				"    1).carrier",
			"co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₁), g, «wg3Module1», 1, ζ₁) = " +
				"thickening_class(R, R₀, f, «wg3OverReduced»(snd(M)), ι)",
		},
		Conclusion: "(«wg3GluingObstruction»(ζ₀, ζ₁) = «wg3Cokernel».zero ⇔ " +
			"    ∃ζ_0' ζ_1':set(U → D). " +
			"        ζ_0' ∈ " +
			"        cotangent_cohomology(R, " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λa:A. g(f(a)), " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λc:C. c, " +
			"            «wg3Module0», " +
			"            1).carrier ∧ " +
			"        co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₀), g, «wg3Module0», 1, ζ_0') = " +
			"        thickening_class(R, R₀, f, «wg3OverReduced»(fst(M)), ι) ∧ " +
			"        ζ_1' ∈ " +
			"        cotangent_cohomology(R, " +
			"            restrict_ring(A₀₁, A₁), " +
			"            λa:A. g(f(a)), " +
			"            restrict_ring(A₀₁, A₁), " +
			"            λc:C. c, " +
			"            «wg3Module1», " +
			"            1).carrier ∧ " +
			"        co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₁), g, «wg3Module1», 1, ζ_1') = " +
			"        thickening_class(R, R₀, f, «wg3OverReduced»(snd(M)), ι) ∧ " +
			"        «wg3ThickeningRestriction0»(ζ_0') = «wg3ThickeningRestriction1»(ζ_1')) ∧ " +
			"(«wg3GluingObstruction»(ζ₀, ζ₁) = «wg3Cokernel».zero ⇔ " +
			"    ∃E₀:square_zero_ops(A, C, set(prod(U, D)), D). " +
			"    ∃t₀:set(prod(U, D)). " +
			"    ∃E₁:square_zero_ops(A, C, set(prod(U, D)), D). " +
			"    ∃t₁:set(prod(U, D)). " +
			"    ∃φ:(set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"            set(prod(set(prod(U, D)), set(prod(U, D))))). " +
			"        biaffine_deformation(R, R₀, f, g, A₀₁, A₀, A₁, t, s, V, M, ι, E₀, t₀, E₁, t₁, φ))",
	},
		"⇒: the zero of the cokernel is the sum of the images, so δ = res₀(a) + res₁(b); ζ₀ − i*(a) "+
			"and ζ₁ + i*(b) are deformation classes (DeformationsTorsor) whose restrictions differ by "+
			"i*(δ − res₀(a) − res₁(b)) = zero (RestrictionCompatibleTorsor). ⇐: for compatible "+
			"deformation classes δ is zero (RestrictionMapInjective), and the obstruction does not "+
			"depend on the classes (GluingObstructionWellDefined). Compatible deformation classes glue: "+
			"their realizations are chart deformations (ExtensionRealizeClass, "+
			"DeformationIffPullbackClass, RightMapIsPullback) with lifts of t and s, and LocalClassOnto "+
			"over R through g ∘ f gives the gluing (BiaffineDeformationDef). A deformation's chart "+
			"classes are compatible over R (LocalClassLandsInKernel) deformation classes"),
})}

// ---------------------------------------------------------------------------
// The theorem
// ---------------------------------------------------------------------------

// BiaffineDeformationTheorem — the obstruction in two levels: a
// deformation of the curve kills the local obstruction and every gluing
// obstruction; when the local obstruction vanishes the charts have
// deformation classes, and any of them with vanishing gluing obstruction
// gives a deformation of the curve.
var BiaffineDeformationTheorem = biaffineDeformationTheoremThm{family.Add(registry.ProofEntry{
	Name: "BiaffineDeformationTheorem",
	Key:  "prop_acb048c2e9931729",
	Reading: "The second level is defined only once the first vanishes: the gluing " +
		"obstruction is read at deformation classes of the charts, which exist exactly then " +
		"(LocalDeformationsExistIff), and it does not depend on which " +
		"(GluingObstructionWellDefined). Neither level implies the other: a chart can fail " +
		"to deform, and two deformable charts can fail to glue when D¹ of the overlap is not " +
		"reached by the charts'. Both vanish for smooth charts (SmoothChartsUnobstructed).",
	Deps: []registry.EntryLike{
		LocalDeformationsExistIff,
		GluingObstructionWellDefined,
		GluingObstructionZeroIffLift,
		LocalClassLandsInKernel,
		BiaffineDeformationDef,
		algebra_deformation.DeformationIffPullbackClass,
		algebra_deformation.RightMapIsPullback,
		square_zero_classification.ExtensionRealizeClass,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀ι:(A → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, A₀₁, g)",
			"image(g, R₀.carrier) ⊆ A₀ ∩ A₁",
			"module_homomorphism(R₀, " +
				"    thickening_kernel(R, R₀, f), " +
				"    restrict_module(scalar_restriction(g, V), fst(M) ∩ snd(M)), " +
				"    ι)",
		},
		Conclusion: "(∀E₀:square_zero_ops(A, C, I, D). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, C, H, D). " +
			"∀t₁:H. " +
			"∀φ:(set(prod(I, I)) → set(prod(H, H))). " +
			"    «wg3Deformation»(E₀, t₀, E₁, t₁, φ) ⇒ " +
			"    «wg3LocalObstruction» = «wg3LocalZero» ∧ " +
			"    (∀ζ₀ ζ₁:set(U → D). " +
			"        ζ₀ ∈ " +
			"        cotangent_cohomology(R, " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λa:A. g(f(a)), " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λc:C. c, " +
			"            «wg3Module0», " +
			"            1).carrier ∧ " +
			"        co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₀), g, «wg3Module0», 1, ζ₀) = " +
			"        thickening_class(R, R₀, f, «wg3OverReduced»(fst(M)), ι) ∧ " +
			"        ζ₁ ∈ " +
			"        cotangent_cohomology(R, " +
			"            restrict_ring(A₀₁, A₁), " +
			"            λa:A. g(f(a)), " +
			"            restrict_ring(A₀₁, A₁), " +
			"            λc:C. c, " +
			"            «wg3Module1», " +
			"            1).carrier ∧ " +
			"        co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₁), g, «wg3Module1», 1, ζ₁) = " +
			"        thickening_class(R, R₀, f, «wg3OverReduced»(snd(M)), ι) ⇒ " +
			"        «wg3GluingObstruction»(ζ₀, ζ₁) = «wg3Cokernel».zero)) ∧ " +
			"(«wg3LocalObstruction» = «wg3LocalZero» ⇒ " +
			"    (∃ζ₀ ζ₁:set(U → D). " +
			"        ζ₀ ∈ " +
			"        cotangent_cohomology(R, " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λa:A. g(f(a)), " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λc:C. c, " +
			"            «wg3Module0», " +
			"            1).carrier ∧ " +
			"        co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₀), g, «wg3Module0», 1, ζ₀) = " +
			"        thickening_class(R, R₀, f, «wg3OverReduced»(fst(M)), ι) ∧ " +
			"        ζ₁ ∈ " +
			"        cotangent_cohomology(R, " +
			"            restrict_ring(A₀₁, A₁), " +
			"            λa:A. g(f(a)), " +
			"            restrict_ring(A₀₁, A₁), " +
			"            λc:C. c, " +
			"            «wg3Module1», " +
			"            1).carrier ∧ " +
			"        co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₁), g, «wg3Module1», 1, ζ₁) = " +
			"        thickening_class(R, R₀, f, «wg3OverReduced»(snd(M)), ι)) ∧ " +
			"    (∀ζ₀ ζ₁:set(U → D). " +
			"        ζ₀ ∈ " +
			"        cotangent_cohomology(R, " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λa:A. g(f(a)), " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λc:C. c, " +
			"            «wg3Module0», " +
			"            1).carrier ∧ " +
			"        co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₀), g, «wg3Module0», 1, ζ₀) = " +
			"        thickening_class(R, R₀, f, «wg3OverReduced»(fst(M)), ι) ∧ " +
			"        ζ₁ ∈ " +
			"        cotangent_cohomology(R, " +
			"            restrict_ring(A₀₁, A₁), " +
			"            λa:A. g(f(a)), " +
			"            restrict_ring(A₀₁, A₁), " +
			"            λc:C. c, " +
			"            «wg3Module1», " +
			"            1).carrier ∧ " +
			"        co_transitivity_right_map(R, R₀, f, restrict_ring(A₀₁, A₁), g, «wg3Module1», 1, ζ₁) = " +
			"        thickening_class(R, R₀, f, «wg3OverReduced»(snd(M)), ι) ∧ " +
			"        «wg3GluingObstruction»(ζ₀, ζ₁) = «wg3Cokernel».zero ⇒ " +
			"        ∃E₀:square_zero_ops(A, C, set(prod(U, D)), D). " +
			"        ∃t₀:set(prod(U, D)). " +
			"        ∃E₁:square_zero_ops(A, C, set(prod(U, D)), D). " +
			"        ∃t₁:set(prod(U, D)). " +
			"        ∃φ:(set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"                set(prod(set(prod(U, D)), set(prod(U, D))))). " +
			"            biaffine_deformation(R, R₀, f, g, A₀₁, A₀, A₁, t, s, V, M, ι, E₀, t₀, E₁, t₁, φ)))",
	},
		"a deformation's charts are deformations (BiaffineDeformationDef), so the local "+
			"obstruction vanishes (LocalDeformationsExistIff); its chart classes are compatible "+
			"deformation classes (LocalClassLandsInKernel, DeformationIffPullbackClass, "+
			"RightMapIsPullback), so their gluing obstruction vanishes (GluingObstructionZeroIffLift), "+
			"and so does every other's (GluingObstructionWellDefined). Conversely the local "+
			"obstruction vanishing gives chart deformations, whose classes are deformation classes "+
			"(LocalDeformationsExistIff), and GluingObstructionZeroIffLift gives the deformation"),
})}

// CokernelZeroLocalObstructionSuffices — when the gluing cokernel is zero,
// the curve has a deformation as soon as the local obstruction vanishes.
var CokernelZeroLocalObstructionSuffices = cokernelZeroLocalObstructionSufficesThm{family.Add(registry.ProofEntry{
	Name: "CokernelZeroLocalObstructionSuffices",
	Key:  "prop_4c9bd855de68a0bc",
	Reading: "The cokernel is zero when the restrictions of the charts' D¹ fill D¹(A₀₁/R₀, M₀₁), " +
		"in particular when that vanishes, as it does when a chart is smooth over R₀. Then the " +
		"gluing obstruction, a class of the cokernel, is its zero whatever the deformation classes.",
	Deps: []registry.EntryLike{BiaffineDeformationTheorem, GluingObstructionWellDefined},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀ι:(A → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, A₀₁, g)",
			"image(g, R₀.carrier) ⊆ A₀ ∩ A₁",
			"module_homomorphism(R₀, " +
				"    thickening_kernel(R, R₀, f), " +
				"    restrict_module(scalar_restriction(g, V), fst(M) ∩ snd(M)), " +
				"    ι)",
			"biaffine_gluing_cokernel⟨U:U⟩(R₀, g, A₀₁, A₀, A₁, V, M).carrier = {«wg3Cokernel».zero}",
			"«wg3LocalObstruction» = «wg3LocalZero»",
		},
		Conclusion: "∃E₀:square_zero_ops(A, C, set(prod(U, D)), D). " +
			"∃t₀:set(prod(U, D)). " +
			"∃E₁:square_zero_ops(A, C, set(prod(U, D)), D). " +
			"∃t₁:set(prod(U, D)). " +
			"∃φ:(set(prod(set(prod(U, D)), set(prod(U, D)))) → set(prod(set(prod(U, D)), set(prod(U, D))))). " +
			"    biaffine_deformation(R, R₀, f, g, A₀₁, A₀, A₁, t, s, V, M, ι, E₀, t₀, E₁, t₁, φ)",
	},
		"BiaffineDeformationTheorem gives deformation classes of both charts; their "+
			"gluing obstruction is a class of the cokernel (GluingObstructionWellDefined), "+
			"its only class the zero, so BiaffineDeformationTheorem gives the deformation"),
})}

// ---------------------------------------------------------------------------
// The deformations as a torsor
// ---------------------------------------------------------------------------

// BiaffineDeformationsTorsor — given one deformation D of the curve over
// the thickening R → R₀, the deformations are the Baer sums of D with the
// biaffine extensions over R₀ read over R: each such sum is a
// deformation, every deformation is isomorphic to one, and two sums are
// isomorphic exactly when the extensions over R₀ are.
var BiaffineDeformationsTorsor = biaffineDeformationsTorsorThm{family.Add(registry.ProofEntry{
	Name: "BiaffineDeformationsTorsor",
	Key:  "prop_a057a1057aa25008",
	Reading: "The isomorphism classes of deformations, when there are any, are a torsor under " +
		"Exal over R₀ (BiaffineExalGroupOn at the base R₀ through g), acting by the Baer sum. An " +
		"extension over R₀ is read over R with its structure maps after f, its rings, inclusions, " +
		"projections and gluing unchanged; its structure maps are then zero on J, which is why " +
		"the sum keeps the deformation condition. f onto is load-bearing twice: the Baer sum of a " +
		"deformation with the negation of another has its structure maps zero on J, so they " +
		"factor through R₀, which is the transitivity; and an isomorphism over R of two " +
		"extensions read through f is one over R₀, which is the freeness. Read in its two layers, " +
		"the chart classes and the regluings, the torsor is BiaffineDeformationsTorsorLayers.",
	Deps: []registry.EntryLike{
		BiaffineBaerSumIsExtension,
		BiaffineExalGroupOn,
		BiaffineExalSumClass,
		BiaffineExalNegClass,
		BiaffineExalClassEqIff,
		BiaffineDeformationDef,
		BiaffineExtensionDef,
		BiaffineIsomorphismDef,
		biaffineBaerGluingDef,
		algebra_deformation.DeformationBaerSum,
		algebra_deformation.AlgebraDeformationDef,
		square_zero_extension.BaerSumIsomorphism,
		square_zero_extension.BaerSumLocalizes,
		square_zero_extension.SquareZeroIsomorphismDef,
		square_zero_extension.SquareZeroLocalizationDef,
		ring_homomorphism.RingHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀ι:(A → D). " +
			"∀E₀:square_zero_ops(A, C, I, D). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, C, H, D). " +
			"∀t₁:H. " +
			"∀φ:(set(prod(I, I)) → set(prod(H, H))).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, A₀₁, g)",
			"image(g, R₀.carrier) ⊆ A₀ ∩ A₁",
			"module_homomorphism(R₀, " +
				"    thickening_kernel(R, R₀, f), " +
				"    restrict_module(scalar_restriction(g, V), fst(M) ∩ snd(M)), " +
				"    ι)",
			"«wg3Deformation»(E₀, t₀, E₁, t₁, φ)",
		},
		Conclusion: "(∀E_0':square_zero_ops(B, C, G, D). " +
			"∀t_0':G. " +
			"∀E_1':square_zero_ops(B, C, F, D). " +
			"∀t_1':F. " +
			"∀φ':(set(prod(G, G)) → set(prod(F, F))). " +
			"    «wg3ReducedExtension»(E_0', t_0', E_1', t_1', φ') ⇒ " +
			"    «wg3Deformation»(square_zero_baer_sum(«wg3Module0», " +
			"            E₀, " +
			"            mk_square_zero(E_0'.ring, " +
			"                λa:A. E_0'.structure(f(a)), " +
			"                E_0'.inclusion, " +
			"                E_0'.projection)), " +
			"        ideal_quotient_projection(square_zero_fiber_product(E₀, " +
			"                mk_square_zero(E_0'.ring, " +
			"                    λa:A. E_0'.structure(f(a)), " +
			"                    E_0'.inclusion, " +
			"                    E_0'.projection)), " +
			"            image(λm:D. " +
			"                    (E₀.inclusion(m), " +
			"                        mk_square_zero(E_0'.ring, " +
			"                            λa:A. E_0'.structure(f(a)), " +
			"                            E_0'.inclusion, " +
			"                            E_0'.projection).ring.neg(mk_square_zero(E_0'.ring, " +
			"                                λa:A. E_0'.structure(f(a)), " +
			"                                E_0'.inclusion, " +
			"                                E_0'.projection).inclusion(m))), " +
			"                «wg3Module0».carrier), " +
			"            (t₀, t_0')), " +
			"        square_zero_baer_sum(«wg3Module1», " +
			"            E₁, " +
			"            mk_square_zero(E_1'.ring, " +
			"                λa:A. E_1'.structure(f(a)), " +
			"                E_1'.inclusion, " +
			"                E_1'.projection)), " +
			"        ideal_quotient_projection(square_zero_fiber_product(E₁, " +
			"                mk_square_zero(E_1'.ring, " +
			"                    λa:A. E_1'.structure(f(a)), " +
			"                    E_1'.inclusion, " +
			"                    E_1'.projection)), " +
			"            image(λm:D. " +
			"                    (E₁.inclusion(m), " +
			"                        mk_square_zero(E_1'.ring, " +
			"                            λa:A. E_1'.structure(f(a)), " +
			"                            E_1'.inclusion, " +
			"                            E_1'.projection).ring.neg(mk_square_zero(E_1'.ring, " +
			"                                λa:A. E_1'.structure(f(a)), " +
			"                                E_1'.inclusion, " +
			"                                E_1'.projection).inclusion(m))), " +
			"                «wg3Module1».carrier), " +
			"            (t₁, t_1')), " +
			"        biaffine_baer_gluing(A₀₁, " +
			"            V, " +
			"            M, " +
			"            E₀, " +
			"            t₀, " +
			"            E₁, " +
			"            t₁, " +
			"            φ, " +
			"            mk_square_zero(E_0'.ring, " +
			"                λa:A. E_0'.structure(f(a)), " +
			"                E_0'.inclusion, " +
			"                E_0'.projection), " +
			"            t_0', " +
			"            mk_square_zero(E_1'.ring, " +
			"                λa:A. E_1'.structure(f(a)), " +
			"                E_1'.inclusion, " +
			"                E_1'.projection), " +
			"            t_1', " +
			"            φ'))) ∧ " +
			"(∀E_0':square_zero_ops(A, C, G, D). " +
			"∀t_0':G. " +
			"∀E_1':square_zero_ops(A, C, F, D). " +
			"∀t_1':F. " +
			"∀φ':(set(prod(G, G)) → set(prod(F, F))). " +
			"    «wg3Deformation»(E_0', t_0', E_1', t_1', φ') ⇒ " +
			"    ∃X₀:square_zero_ops(B, C, set(prod(U, D)), D). " +
			"    ∃u₀:set(prod(U, D)). " +
			"    ∃X₁:square_zero_ops(B, C, set(prod(U, D)), D). " +
			"    ∃u₁:set(prod(U, D)). " +
			"    ∃χ:(set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"            set(prod(set(prod(U, D)), set(prod(U, D))))). " +
			"        «wg3ReducedExtension»(X₀, u₀, X₁, u₁, χ) ∧ " +
			"        (∃ψ₀:(set(prod(I, set(prod(U, D)))) → G). ∃ψ₁:(set(prod(H, set(prod(U, D)))) → F). " +
			"            biaffine_isomorphism(R, " +
			"                A₀₁, " +
			"                V, " +
			"                M, " +
			"                square_zero_baer_sum(«wg3Module0», " +
			"                    E₀, " +
			"                    mk_square_zero(X₀.ring, " +
			"                        λa:A. X₀.structure(f(a)), " +
			"                        X₀.inclusion, " +
			"                        X₀.projection)), " +
			"                ideal_quotient_projection(square_zero_fiber_product(E₀, " +
			"                        mk_square_zero(X₀.ring, " +
			"                            λa:A. X₀.structure(f(a)), " +
			"                            X₀.inclusion, " +
			"                            X₀.projection)), " +
			"                    image(λm:D. " +
			"                            (E₀.inclusion(m), " +
			"                                mk_square_zero(X₀.ring, " +
			"                                    λa:A. X₀.structure(f(a)), " +
			"                                    X₀.inclusion, " +
			"                                    X₀.projection).ring.neg(mk_square_zero(X₀.ring, " +
			"                                        λa:A. X₀.structure(f(a)), " +
			"                                        X₀.inclusion, " +
			"                                        X₀.projection).inclusion(m))), " +
			"                        «wg3Module0».carrier), " +
			"                    (t₀, u₀)), " +
			"                square_zero_baer_sum(«wg3Module1», " +
			"                    E₁, " +
			"                    mk_square_zero(X₁.ring, " +
			"                        λa:A. X₁.structure(f(a)), " +
			"                        X₁.inclusion, " +
			"                        X₁.projection)), " +
			"                ideal_quotient_projection(square_zero_fiber_product(E₁, " +
			"                        mk_square_zero(X₁.ring, " +
			"                            λa:A. X₁.structure(f(a)), " +
			"                            X₁.inclusion, " +
			"                            X₁.projection)), " +
			"                    image(λm:D. " +
			"                            (E₁.inclusion(m), " +
			"                                mk_square_zero(X₁.ring, " +
			"                                    λa:A. X₁.structure(f(a)), " +
			"                                    X₁.inclusion, " +
			"                                    X₁.projection).ring.neg(mk_square_zero(X₁.ring, " +
			"                                        λa:A. X₁.structure(f(a)), " +
			"                                        X₁.inclusion, " +
			"                                        X₁.projection).inclusion(m))), " +
			"                        «wg3Module1».carrier), " +
			"                    (t₁, u₁)), " +
			"                biaffine_baer_gluing(A₀₁, " +
			"                    V, " +
			"                    M, " +
			"                    E₀, " +
			"                    t₀, " +
			"                    E₁, " +
			"                    t₁, " +
			"                    φ, " +
			"                    mk_square_zero(X₀.ring, " +
			"                        λa:A. X₀.structure(f(a)), " +
			"                        X₀.inclusion, " +
			"                        X₀.projection), " +
			"                    u₀, " +
			"                    mk_square_zero(X₁.ring, " +
			"                        λa:A. X₁.structure(f(a)), " +
			"                        X₁.inclusion, " +
			"                        X₁.projection), " +
			"                    u₁, " +
			"                    χ), " +
			"                E_0', " +
			"                t_0', " +
			"                E_1', " +
			"                t_1', " +
			"                φ', " +
			"                ψ₀, " +
			"                ψ₁))) ∧ " +
			"(∀E_0':square_zero_ops(B, C, G, D). " +
			"∀t_0':G. " +
			"∀E_1':square_zero_ops(B, C, F, D). " +
			"∀t_1':F. " +
			"∀φ':(set(prod(G, G)) → set(prod(F, F))). " +
			"∀E_0'':square_zero_ops(B, C, E, D). " +
			"∀t_0'':E. " +
			"∀E_1'':square_zero_ops(B, C, Z, D). " +
			"∀t_1'':Z. " +
			"∀φ'':(set(prod(E, E)) → set(prod(Z, Z))). " +
			"    «wg3ReducedExtension»(E_0', t_0', E_1', t_1', φ') ∧ " +
			"    «wg3ReducedExtension»(E_0'', t_0'', E_1'', t_1'', φ'') ⇒ " +
			"    ((∃ψ₀:(set(prod(I, G)) → set(prod(I, E))). ∃ψ₁:(set(prod(H, F)) → set(prod(H, Z))). " +
			"            biaffine_isomorphism(R, " +
			"                A₀₁, " +
			"                V, " +
			"                M, " +
			"                square_zero_baer_sum(«wg3Module0», " +
			"                    E₀, " +
			"                    mk_square_zero(E_0'.ring, " +
			"                        λa:A. E_0'.structure(f(a)), " +
			"                        E_0'.inclusion, " +
			"                        E_0'.projection)), " +
			"                ideal_quotient_projection(square_zero_fiber_product(E₀, " +
			"                        mk_square_zero(E_0'.ring, " +
			"                            λa:A. E_0'.structure(f(a)), " +
			"                            E_0'.inclusion, " +
			"                            E_0'.projection)), " +
			"                    image(λm:D. " +
			"                            (E₀.inclusion(m), " +
			"                                mk_square_zero(E_0'.ring, " +
			"                                    λa:A. E_0'.structure(f(a)), " +
			"                                    E_0'.inclusion, " +
			"                                    E_0'.projection).ring.neg(mk_square_zero(E_0'.ring, " +
			"                                        λa:A. E_0'.structure(f(a)), " +
			"                                        E_0'.inclusion, " +
			"                                        E_0'.projection).inclusion(m))), " +
			"                        «wg3Module0».carrier), " +
			"                    (t₀, t_0')), " +
			"                square_zero_baer_sum(«wg3Module1», " +
			"                    E₁, " +
			"                    mk_square_zero(E_1'.ring, " +
			"                        λa:A. E_1'.structure(f(a)), " +
			"                        E_1'.inclusion, " +
			"                        E_1'.projection)), " +
			"                ideal_quotient_projection(square_zero_fiber_product(E₁, " +
			"                        mk_square_zero(E_1'.ring, " +
			"                            λa:A. E_1'.structure(f(a)), " +
			"                            E_1'.inclusion, " +
			"                            E_1'.projection)), " +
			"                    image(λm:D. " +
			"                            (E₁.inclusion(m), " +
			"                                mk_square_zero(E_1'.ring, " +
			"                                    λa:A. E_1'.structure(f(a)), " +
			"                                    E_1'.inclusion, " +
			"                                    E_1'.projection).ring.neg(mk_square_zero(E_1'.ring, " +
			"                                        λa:A. E_1'.structure(f(a)), " +
			"                                        E_1'.inclusion, " +
			"                                        E_1'.projection).inclusion(m))), " +
			"                        «wg3Module1».carrier), " +
			"                    (t₁, t_1')), " +
			"                biaffine_baer_gluing(A₀₁, " +
			"                    V, " +
			"                    M, " +
			"                    E₀, " +
			"                    t₀, " +
			"                    E₁, " +
			"                    t₁, " +
			"                    φ, " +
			"                    mk_square_zero(E_0'.ring, " +
			"                        λa:A. E_0'.structure(f(a)), " +
			"                        E_0'.inclusion, " +
			"                        E_0'.projection), " +
			"                    t_0', " +
			"                    mk_square_zero(E_1'.ring, " +
			"                        λa:A. E_1'.structure(f(a)), " +
			"                        E_1'.inclusion, " +
			"                        E_1'.projection), " +
			"                    t_1', " +
			"                    φ'), " +
			"                square_zero_baer_sum(«wg3Module0», " +
			"                    E₀, " +
			"                    mk_square_zero(E_0''.ring, " +
			"                        λa:A. E_0''.structure(f(a)), " +
			"                        E_0''.inclusion, " +
			"                        E_0''.projection)), " +
			"                ideal_quotient_projection(square_zero_fiber_product(E₀, " +
			"                        mk_square_zero(E_0''.ring, " +
			"                            λa:A. E_0''.structure(f(a)), " +
			"                            E_0''.inclusion, " +
			"                            E_0''.projection)), " +
			"                    image(λm:D. " +
			"                            (E₀.inclusion(m), " +
			"                                mk_square_zero(E_0''.ring, " +
			"                                    λa:A. E_0''.structure(f(a)), " +
			"                                    E_0''.inclusion, " +
			"                                    E_0''.projection).ring.neg(mk_square_zero(E_0''.ring, " +
			"                                        λa:A. E_0''.structure(f(a)), " +
			"                                        E_0''.inclusion, " +
			"                                        E_0''.projection).inclusion(m))), " +
			"                        «wg3Module0».carrier), " +
			"                    (t₀, t_0'')), " +
			"                square_zero_baer_sum(«wg3Module1», " +
			"                    E₁, " +
			"                    mk_square_zero(E_1''.ring, " +
			"                        λa:A. E_1''.structure(f(a)), " +
			"                        E_1''.inclusion, " +
			"                        E_1''.projection)), " +
			"                ideal_quotient_projection(square_zero_fiber_product(E₁, " +
			"                        mk_square_zero(E_1''.ring, " +
			"                            λa:A. E_1''.structure(f(a)), " +
			"                            E_1''.inclusion, " +
			"                            E_1''.projection)), " +
			"                    image(λm:D. " +
			"                            (E₁.inclusion(m), " +
			"                                mk_square_zero(E_1''.ring, " +
			"                                    λa:A. E_1''.structure(f(a)), " +
			"                                    E_1''.inclusion, " +
			"                                    E_1''.projection).ring.neg(mk_square_zero(E_1''.ring, " +
			"                                        λa:A. E_1''.structure(f(a)), " +
			"                                        E_1''.inclusion, " +
			"                                        E_1''.projection).inclusion(m))), " +
			"                        «wg3Module1».carrier), " +
			"                    (t₁, t_1'')), " +
			"                biaffine_baer_gluing(A₀₁, " +
			"                    V, " +
			"                    M, " +
			"                    E₀, " +
			"                    t₀, " +
			"                    E₁, " +
			"                    t₁, " +
			"                    φ, " +
			"                    mk_square_zero(E_0''.ring, " +
			"                        λa:A. E_0''.structure(f(a)), " +
			"                        E_0''.inclusion, " +
			"                        E_0''.projection), " +
			"                    t_0'', " +
			"                    mk_square_zero(E_1''.ring, " +
			"                        λa:A. E_1''.structure(f(a)), " +
			"                        E_1''.inclusion, " +
			"                        E_1''.projection), " +
			"                    t_1'', " +
			"                    φ''), " +
			"                ψ₀, " +
			"                ψ₁)) ⇔ " +
			"        ∃χ₀:(G → E). ∃χ₁:(F → Z). " +
			"            biaffine_isomorphism(R₀, " +
			"                A₀₁, " +
			"                V, " +
			"                M, " +
			"                E_0', " +
			"                t_0', " +
			"                E_1', " +
			"                t_1', " +
			"                φ', " +
			"                E_0'', " +
			"                t_0'', " +
			"                E_1'', " +
			"                t_1'', " +
			"                φ'', " +
			"                χ₀, " +
			"                χ₁)))",
		Abbrev: Abbrev{
			{Name: "wg3ReducedExtension", Text: "biaffine_extension(R₀, g, A₀₁, A₀, A₁, t, s, V, M)"},
		},
	},
		"the sum: the extension over R₀ read over R is a biaffine extension over R through g ∘ f, its "+
			"structure maps after the ring map f and its gluing unchanged (BiaffineExtensionDef, "+
			"RingHomomorphism, SquareZeroLocalizationDef), so the Baer sum is one "+
			"(BiaffineBaerSumIsExtension at the base R), and its charts are deformations, DeformationBaerSum "+
			"at each chart with ι linear into each chart module as LocalDeformationsExistIff reads it "+
			"(AlgebraDeformationDef, BiaffineDeformationDef). Transitivity: for a deformation D', the Baer "+
			"sum of D' with the negation of D is a biaffine extension over R whose chart structure maps "+
			"vanish on J, [(k'(j), k(j))] = [(i'(ι(j)), i(ι(j)))] being an antidiagonal pair of D' and the "+
			"negated D; f onto, they factor through R₀, an extension over R₀ read over R, isomorphic to one "+
			"on the realizations' type (BiaffineExalClassEqIff over R₀), and the sum of D with it is "+
			"isomorphic to D' by the group laws over R (BiaffineExalGroupOn, BiaffineExalSumClass, "+
			"BiaffineExalNegClass, BaerSumIsomorphism). Freeness: ⇐ is the sum respecting isomorphisms, one "+
			"over R₀ being one over R of the extensions read through f (BiaffineExalSumClass, "+
			"BiaffineIsomorphismDef); ⇒ cancels D in the group over R (BiaffineExalGroupOn, "+
			"BiaffineExalClassEqIff), and an isomorphism over R of the extensions read through f is over R₀, "+
			"every member of R₀ being some f(a) (SquareZeroIsomorphismDef)"),
})}

// BiaffineDeformationsTorsorLayers — given one deformation of the curve,
// the deformations move in two layers: the chart classes of another are
// those of the first moved by exactly one compatible pair (η₀, η₁) over
// R₀, and every compatible pair moves them to some deformation; a gluing
// moved by a derivation of the overlap over R₀ is again a deformation,
// another deformation with the same chart classes is one of these
// regluings up to isomorphism, and two regluings are isomorphic exactly
// when the derivations differ by fst(𝒟⁰) + snd(𝒟⁰).
var BiaffineDeformationsTorsorLayers = biaffineDeformationsTorsorLayersThm{family.Add(registry.ProofEntry{
	Name: "BiaffineDeformationsTorsorLayers",
	Key:  "prop_9bb5024d3eec9792",
	Reading: "The isomorphism classes of deformations are a torsor under Exal_{R₀} of the " +
		"curve with coefficients M, an extension 0 → H¹(𝒟⁰) → Exal → compatible classes → 0 " +
		"(ExalSequenceExact over R₀). BiaffineDeformationsTorsor states the action by the Baer " +
		"sum; here it is read in the sequence's two layers: the compatible classes act on the " +
		"chart classes, through the left maps, freely and transitively, and H¹(𝒟⁰) acts on each " +
		"fibre by regluing. f onto makes the left maps injective, hence the uniqueness of (η₀, " +
		"η₁), and makes derivations over R and over R₀ the same (ThickeningDerivationsAgree).",
	Deps: []registry.EntryLike{
		ExalSequence,
		ThickeningDerivationsAgree,
		LocalClassOnto,
		LocalClassLandsInKernel,
		BiaffineDeformationDef,
		biaffineRegluingDef,
		BiaffineIsomorphismDef,
		algebra_deformation.DeformationsTorsor,
		algebra_deformation.DeformationLocalizes,
		algebra_deformation.RestrictionMapInjective,
		cotangent_examples.RestrictionCompatibleTorsor,
		square_zero_classification.ExtensionRealizeClass,
		square_zero_extension.SquareZeroIsomorphismDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀ι:(A → D). " +
			"∀E₀:square_zero_ops(A, C, I, D). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, C, H, D). " +
			"∀t₁:H. " +
			"∀φ:(set(prod(I, I)) → set(prod(H, H))).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₀), 𝕌⟨A:U⟩)",
			"cotangent_universe(restrict_ring(A₀₁, A₁), 𝕌⟨A:U⟩)",
			"cotangent_universe(A₀₁, 𝕌⟨A:U⟩)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, A₀₁, g)",
			"image(g, R₀.carrier) ⊆ A₀ ∩ A₁",
			"module_homomorphism(R₀, " +
				"    thickening_kernel(R, R₀, f), " +
				"    restrict_module(scalar_restriction(g, V), fst(M) ∩ snd(M)), " +
				"    ι)",
			"«wg3Deformation»(E₀, t₀, E₁, t₁, φ)",
		},
		Conclusion: "(∀E_0':square_zero_ops(A, C, G, D). " +
			"∀t_0':G. " +
			"∀E_1':square_zero_ops(A, C, F, D). " +
			"∀t_1':F. " +
			"∀φ':(set(prod(G, G)) → set(prod(F, F))). " +
			"    «wg3Deformation»(E_0', t_0', E_1', t_1', φ') ⇒ " +
			"    ∃η₀ η₁:set(U → D). " +
			"        (η₀, η₁) ∈ «wg3ReducedCompatible».carrier ∧ " +
			"        square_zero_class⟨U:U⟩(R, restrict_ring(A₀₁, A₀), λa:A. g(f(a)), «wg3Module0», E_0') = " +
			"        cotangent_cohomology(R, " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λa:A. g(f(a)), " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λc:C. c, " +
			"            «wg3Module0», " +
			"            1).add( " +
			"            square_zero_class⟨U:U⟩(R, restrict_ring(A₀₁, A₀), λa:A. g(f(a)), «wg3Module0», E₀), " +
			"            co_transitivity_left_map(R, " +
			"                R₀, " +
			"                f, " +
			"                restrict_ring(A₀₁, A₀), " +
			"                g, " +
			"                «wg3Module0», " +
			"                1, " +
			"                η₀)) ∧ " +
			"        square_zero_class⟨U:U⟩(R, restrict_ring(A₀₁, A₁), λa:A. g(f(a)), «wg3Module1», E_1') = " +
			"        cotangent_cohomology(R, " +
			"            restrict_ring(A₀₁, A₁), " +
			"            λa:A. g(f(a)), " +
			"            restrict_ring(A₀₁, A₁), " +
			"            λc:C. c, " +
			"            «wg3Module1», " +
			"            1).add( " +
			"            square_zero_class⟨U:U⟩(R, restrict_ring(A₀₁, A₁), λa:A. g(f(a)), «wg3Module1», E₁), " +
			"            co_transitivity_left_map(R, " +
			"                R₀, " +
			"                f, " +
			"                restrict_ring(A₀₁, A₁), " +
			"                g, " +
			"                «wg3Module1», " +
			"                1, " +
			"                η₁)) ∧ " +
			"        (∀η_0' η_1':set(U → D). " +
			"            (η_0', η_1') ∈ «wg3ReducedCompatible».carrier ∧ " +
			"            square_zero_class⟨U:U⟩(R, " +
			"                restrict_ring(A₀₁, A₀), " +
			"                λa:A. g(f(a)), " +
			"                «wg3Module0», " +
			"                E_0') = " +
			"            cotangent_cohomology(R, " +
			"                restrict_ring(A₀₁, A₀), " +
			"                λa:A. g(f(a)), " +
			"                restrict_ring(A₀₁, A₀), " +
			"                λc:C. c, " +
			"                «wg3Module0», " +
			"                1).add(square_zero_class⟨U:U⟩(R, " +
			"                    restrict_ring(A₀₁, A₀), " +
			"                    λa:A. g(f(a)), " +
			"                    «wg3Module0», " +
			"                    E₀), " +
			"                co_transitivity_left_map(R, " +
			"                    R₀, " +
			"                    f, " +
			"                    restrict_ring(A₀₁, A₀), " +
			"                    g, " +
			"                    «wg3Module0», " +
			"                    1, " +
			"                    η_0')) ∧ " +
			"            square_zero_class⟨U:U⟩(R, " +
			"                restrict_ring(A₀₁, A₁), " +
			"                λa:A. g(f(a)), " +
			"                «wg3Module1», " +
			"                E_1') = " +
			"            cotangent_cohomology(R, " +
			"                restrict_ring(A₀₁, A₁), " +
			"                λa:A. g(f(a)), " +
			"                restrict_ring(A₀₁, A₁), " +
			"                λc:C. c, " +
			"                «wg3Module1», " +
			"                1).add(square_zero_class⟨U:U⟩(R, " +
			"                    restrict_ring(A₀₁, A₁), " +
			"                    λa:A. g(f(a)), " +
			"                    «wg3Module1», " +
			"                    E₁), " +
			"                co_transitivity_left_map(R, " +
			"                    R₀, " +
			"                    f, " +
			"                    restrict_ring(A₀₁, A₁), " +
			"                    g, " +
			"                    «wg3Module1», " +
			"                    1, " +
			"                    η_1')) ⇒ " +
			"            η_0' = η₀ ∧ η_1' = η₁)) ∧ " +
			"(∀η₀ η₁:set(U → D). " +
			"    (η₀, η₁) ∈ «wg3ReducedCompatible».carrier ⇒ " +
			"    ∃E_0':square_zero_ops(A, C, set(prod(U, D)), D). " +
			"    ∃t_0':set(prod(U, D)). " +
			"    ∃E_1':square_zero_ops(A, C, set(prod(U, D)), D). " +
			"    ∃t_1':set(prod(U, D)). " +
			"    ∃φ':(set(prod(set(prod(U, D)), set(prod(U, D)))) → " +
			"            set(prod(set(prod(U, D)), set(prod(U, D))))). " +
			"        «wg3Deformation»(E_0', t_0', E_1', t_1', φ') ∧ " +
			"        square_zero_class⟨U:U⟩(R, restrict_ring(A₀₁, A₀), λa:A. g(f(a)), «wg3Module0», E_0') = " +
			"        cotangent_cohomology(R, " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λa:A. g(f(a)), " +
			"            restrict_ring(A₀₁, A₀), " +
			"            λc:C. c, " +
			"            «wg3Module0», " +
			"            1).add( " +
			"            square_zero_class⟨U:U⟩(R, restrict_ring(A₀₁, A₀), λa:A. g(f(a)), «wg3Module0», E₀), " +
			"            co_transitivity_left_map(R, " +
			"                R₀, " +
			"                f, " +
			"                restrict_ring(A₀₁, A₀), " +
			"                g, " +
			"                «wg3Module0», " +
			"                1, " +
			"                η₀)) ∧ " +
			"        square_zero_class⟨U:U⟩(R, restrict_ring(A₀₁, A₁), λa:A. g(f(a)), «wg3Module1», E_1') = " +
			"        cotangent_cohomology(R, " +
			"            restrict_ring(A₀₁, A₁), " +
			"            λa:A. g(f(a)), " +
			"            restrict_ring(A₀₁, A₁), " +
			"            λc:C. c, " +
			"            «wg3Module1», " +
			"            1).add( " +
			"            square_zero_class⟨U:U⟩(R, restrict_ring(A₀₁, A₁), λa:A. g(f(a)), «wg3Module1», E₁), " +
			"            co_transitivity_left_map(R, " +
			"                R₀, " +
			"                f, " +
			"                restrict_ring(A₀₁, A₁), " +
			"                g, " +
			"                «wg3Module1», " +
			"                1, " +
			"                η₁))) ∧ " +
			"(∀d:(C → D). " +
			"    d ∈ «wg3ReducedDerivations».carrier ⇒ " +
			"    «wg3Deformation»(E₀, t₀, E₁, t₁, biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d))) ∧ " +
			"(∀E_0':square_zero_ops(A, C, G, D). " +
			"∀t_0':G. " +
			"∀E_1':square_zero_ops(A, C, F, D). " +
			"∀t_1':F. " +
			"∀φ':(set(prod(G, G)) → set(prod(F, F))). " +
			"    «wg3Deformation»(E_0', t_0', E_1', t_1', φ') ∧ " +
			"    square_zero_class⟨U:U⟩(R, restrict_ring(A₀₁, A₀), λa:A. g(f(a)), «wg3Module0», E_0') = " +
			"    square_zero_class⟨U:U⟩(R, restrict_ring(A₀₁, A₀), λa:A. g(f(a)), «wg3Module0», E₀) ∧ " +
			"    square_zero_class⟨U:U⟩(R, restrict_ring(A₀₁, A₁), λa:A. g(f(a)), «wg3Module1», E_1') = " +
			"    square_zero_class⟨U:U⟩(R, restrict_ring(A₀₁, A₁), λa:A. g(f(a)), «wg3Module1», E₁) ⇒ " +
			"    ∃d:(C → D). " +
			"        d ∈ «wg3ReducedDerivations».carrier ∧ " +
			"        (∃ψ₀:(I → G). ∃ψ₁:(H → F). " +
			"            biaffine_isomorphism(R, " +
			"                A₀₁, " +
			"                V, " +
			"                M, " +
			"                E₀, " +
			"                t₀, " +
			"                E₁, " +
			"                t₁, " +
			"                biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d), " +
			"                E_0', " +
			"                t_0', " +
			"                E_1', " +
			"                t_1', " +
			"                φ', " +
			"                ψ₀, " +
			"                ψ₁))) ∧ " +
			"(∀d d':(C → D). " +
			"    d ∈ «wg3ReducedDerivations».carrier ∧ d' ∈ «wg3ReducedDerivations».carrier ⇒ " +
			"    ((∃ψ₀:(I → I). ∃ψ₁:(H → H). " +
			"            biaffine_isomorphism(R, " +
			"                A₀₁, " +
			"                V, " +
			"                M, " +
			"                E₀, " +
			"                t₀, " +
			"                E₁, " +
			"                t₁, " +
			"                biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d), " +
			"                E₀, " +
			"                t₀, " +
			"                E₁, " +
			"                t₁, " +
			"                biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d'), " +
			"                ψ₀, " +
			"                ψ₁)) ⇔ " +
			"        «wg3ReducedDerivations».add(d, «wg3ReducedDerivations».neg(d')) ∈ " +
			"        set_mul(«wg3ReducedDerivations».add, fst(«wg3ReducedPair»), snd(«wg3ReducedPair»))))",
		Abbrev: Abbrev{
			{Name: "wg3ReducedCompatible", Text: "biaffine_compatible_classes(R₀, g, A₀₁, A₀, A₁, V, M)"},
			{Name: "wg3ReducedDerivations", Text: "biaffine_overlap_derivations(R₀, g, A₀₁, V, M)"},
			{Name: "wg3ReducedPair", Text: "biaffine_derivation_pair(R₀, g, A₀₁, A₀, A₁, V, M)"},
		},
	},
		"chart classes: E₀' and E₀ are deformations of chart 0, so their classes differ by "+
			"i*(η₀) for exactly one η₀ (DeformationsTorsor), and the same at chart 1. Both gluings "+
			"make the restrictions over R agree (LocalClassLandsInKernel over R), and restriction "+
			"carries ζ + i*(η) to res(ζ) + i*(res(η)) (RestrictionCompatibleTorsor), so i*(res₀(η₀)) "+
			"= i*(res₁(η₁)) over the overlap and res₀(η₀) = res₁(η₁) by injectivity "+
			"(RestrictionMapInjective): (η₀, η₁) is compatible over R₀. Conversely the realizations "+
			"of the moved classes are chart deformations (DeformationsTorsor, ExtensionRealizeClass) "+
			"with compatible restrictions, glued by LocalClassOnto (BiaffineDeformationDef). "+
			"Regluing: ExalSequence over R, with the derivations over R those over R₀ "+
			"(ThickeningDerivationsAgree); a moved gluing keeps the chart deformations, so it is a "+
			"deformation, and an isomorphism over R of the chart deformations keeps them deformations"),
})}

// SmoothChartsUnobstructed — when both charts have no D¹ and no D² over
// R₀ with any coefficients, both obstructions vanish, the compatible
// classes and the gluing cokernel are zero, the curve has a deformation,
// and its deformations are an H¹(𝒟⁰)-torsor under regluing.
var SmoothChartsUnobstructed = smoothChartsUnobstructedThm{family.Add(registry.ProofEntry{
	Name: "SmoothChartsUnobstructed",
	Key:  "prop_889713ed15a88e04",
	Reading: "Smoothness is asked as the vanishing of D¹ and D² of each chart with every " +
		"coefficients on the type D, which is what it gives (a smooth algebra has its cotangent " +
		"complex a projective module in degree 0); D¹(A₀₁/R₀, M₀₁) vanishes with it, the overlap " +
		"being a localization of a chart (LocalizationRightMapIsomorphism), so the cokernel is " +
		"zero. The automorphisms of a deformation are H⁰(𝒟⁰) with no smoothness at all " +
		"(BiaffineAutomorphisms, ThickeningDerivationsAgree); a smooth curve over R₀ thus has " +
		"deformations, any two related by a class of H¹(𝒟⁰), each with automorphisms H⁰(𝒟⁰). That " +
		"vanishing uses the hypothesis at the coefficients M₀₁ read over chart 0: D¹(A₀₁/R₀, M₀₁) " +
		"is D¹(A₀/R₀, M₀₁) (LocalizationRightMapIsomorphism, CohomologyCoefficientRestriction).",
	Deps: []registry.EntryLike{
		BiaffineDeformationTheorem,
		BiaffineDeformationsTorsorLayers,
		CokernelZeroLocalObstructionSuffices,
		LocalDeformationsExistIff,
		ClassModulesOverSubring,
		cotangent_examples.LocalizationRightMapIsomorphism,
		algebra_deformation.CohomologyCoefficientRestriction,
		lattice_pair.BiaffineChartLocalization,
		lattice_pair.AmbientContains,
		biaffineCompatibleClassesDef,
		biaffineGluingCokernelDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀g:(B → C). " +
			"∀A₀₁:ring_ops(C). " +
			"∀A₀ A₁:set(C). " +
			"∀t s:C. " +
			"∀V:module_ops(C, D). " +
			"∀M:prod(set(D), set(D)). " +
			"∀ι:(A → D).",
		Hypotheses: []string{
			"cotangent_universe⟨A:A, U:U⟩(R, 𝕌)",
			"cotangent_universe⟨A:B, U:U⟩(R₀, 𝕌)",
			"cotangent_universe⟨A:C, U:U⟩(restrict_ring(A₀₁, A₀), 𝕌)",
			"cotangent_universe⟨A:C, U:U⟩(restrict_ring(A₀₁, A₁), 𝕌)",
			"cotangent_universe⟨A:C, U:U⟩(A₀₁, 𝕌)",
			"biaffine(A₀₁, A₀, A₁, t, s)",
			"lattice_pair(A₀₁, A₀, A₁, V, M)",
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    x * y = R.zero",
			"ring_homomorphism(R₀, A₀₁, g)",
			"image(g, R₀.carrier) ⊆ A₀ ∩ A₁",
			"module_homomorphism(R₀, thickening_kernel(R, R₀, f), «wg3OverReduced»(fst(M) ∩ snd(M)), ι)",
			"∀N:module_ops(C, D). " +
				"    module_on(restrict_ring(A₀₁, A₀), N) ⇒ " +
				"    cotangent_cohomology(R₀, " +
				"        restrict_ring(A₀₁, A₀), " +
				"        g, " +
				"        restrict_ring(A₀₁, A₀), " +
				"        λc:C. c, " +
				"        N, " +
				"        1).carrier = " +
				"    insert(cotangent_cohomology(R₀, " +
				"            restrict_ring(A₀₁, A₀), " +
				"            g, " +
				"            restrict_ring(A₀₁, A₀), " +
				"            λc:C. c, " +
				"            N, " +
				"            1).zero, " +
				"        ∅⟨A:(U → D) → bool⟩) ∧ " +
				"    cotangent_cohomology(R₀, " +
				"        restrict_ring(A₀₁, A₀), " +
				"        g, " +
				"        restrict_ring(A₀₁, A₀), " +
				"        λc:C. c, " +
				"        N, " +
				"        2).carrier = " +
				"    insert(cotangent_cohomology(R₀, " +
				"            restrict_ring(A₀₁, A₀), " +
				"            g, " +
				"            restrict_ring(A₀₁, A₀), " +
				"            λc:C. c, " +
				"            N, " +
				"            2).zero, " +
				"        ∅⟨A:(U → D) → bool⟩)",
			"∀N:module_ops(C, D). " +
				"    module_on(restrict_ring(A₀₁, A₁), N) ⇒ " +
				"    cotangent_cohomology(R₀, " +
				"        restrict_ring(A₀₁, A₁), " +
				"        g, " +
				"        restrict_ring(A₀₁, A₁), " +
				"        λc:C. c, " +
				"        N, " +
				"        1).carrier = " +
				"    insert(cotangent_cohomology(R₀, " +
				"            restrict_ring(A₀₁, A₁), " +
				"            g, " +
				"            restrict_ring(A₀₁, A₁), " +
				"            λc:C. c, " +
				"            N, " +
				"            1).zero, " +
				"        ∅⟨A:(U → D) → bool⟩) ∧ " +
				"    cotangent_cohomology(R₀, " +
				"        restrict_ring(A₀₁, A₁), " +
				"        g, " +
				"        restrict_ring(A₀₁, A₁), " +
				"        λc:C. c, " +
				"        N, " +
				"        2).carrier = " +
				"    insert(cotangent_cohomology(R₀, " +
				"            restrict_ring(A₀₁, A₁), " +
				"            g, " +
				"            restrict_ring(A₀₁, A₁), " +
				"            λc:C. c, " +
				"            N, " +
				"            2).zero, " +
				"        ∅⟨A:(U → D) → bool⟩)",
		},
		Conclusion: "«wg3LocalObstruction» = " +
			"(cotangent_cohomology(R₀, " +
			"        restrict_ring(A₀₁, A₀), " +
			"        g, " +
			"        restrict_ring(A₀₁, A₀), " +
			"        λc:C. c, " +
			"        «wg3Module0», " +
			"        2).zero, " +
			"    cotangent_cohomology(R₀, " +
			"        restrict_ring(A₀₁, A₁), " +
			"        g, " +
			"        restrict_ring(A₀₁, A₁), " +
			"        λc:C. c, " +
			"        «wg3Module1», " +
			"        2).zero) ∧ " +
			"biaffine_compatible_classes(R₀, g, A₀₁, A₀, A₁, V, M).carrier = " +
			"insert(biaffine_compatible_classes(R₀, g, A₀₁, A₀, A₁, V, M).zero, " +
			"    ∅⟨A:prod((U → D) → bool, (U → D) → bool)⟩) ∧ " +
			"biaffine_gluing_cokernel(R₀, g, A₀₁, A₀, A₁, V, M).carrier = " +
			"insert(biaffine_gluing_cokernel(R₀, g, A₀₁, A₀, A₁, V, M).zero, ∅⟨A:((U → D) → bool) → bool⟩) ∧ " +
			"(∃E₀:square_zero_ops(A, C, prod(U, D) → bool, D). " +
			"∃t₀:set(prod(U, D)). " +
			"∃E₁:square_zero_ops(A, C, prod(U, D) → bool, D). " +
			"∃t₁:set(prod(U, D)). " +
			"∃φ:((prod(prod(U, D) → bool, prod(U, D) → bool) → bool) → " +
			"        prod(prod(U, D) → bool, prod(U, D) → bool) → " +
			"        bool). " +
			"    biaffine_deformation(R, R₀, f, g, A₀₁, A₀, A₁, t, s, V, M, ι, E₀, t₀, E₁, t₁, φ)) ∧ " +
			"(∀E₀:square_zero_ops(A, C, I, D). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, C, H, D). " +
			"∀t₁:H. " +
			"∀φ:((prod(I, I) → bool) → prod(H, H) → bool). " +
			"∀E_0':square_zero_ops(A, C, G, D). " +
			"∀t_0':G. " +
			"∀E_1':square_zero_ops(A, C, F, D). " +
			"∀t_1':F. " +
			"∀φ':((prod(G, G) → bool) → prod(F, F) → bool). " +
			"    biaffine_deformation(R, R₀, f, g, A₀₁, A₀, A₁, t, s, V, M, ι, E₀, t₀, E₁, t₁, φ) ∧ " +
			"    biaffine_deformation(R, R₀, f, g, A₀₁, A₀, A₁, t, s, V, M, ι, E_0', t_0', E_1', t_1', φ') ⇒ " +
			"    ∃d:(C → D). " +
			"        d ∈ biaffine_overlap_derivations(R₀, g, A₀₁, V, M).carrier ∧ " +
			"        (∃ψ₀:(I → G). ∃ψ₁:(H → F). " +
			"            biaffine_isomorphism(R, " +
			"                A₀₁, " +
			"                V, " +
			"                M, " +
			"                E₀, " +
			"                t₀, " +
			"                E₁, " +
			"                t₁, " +
			"                biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d), " +
			"                E_0', " +
			"                t_0', " +
			"                E_1', " +
			"                t_1', " +
			"                φ', " +
			"                ψ₀, " +
			"                ψ₁))) ∧ " +
			"(∀E₀:square_zero_ops(A, C, I, D). " +
			"∀t₀:I. " +
			"∀E₁:square_zero_ops(A, C, H, D). " +
			"∀t₁:H. " +
			"∀φ:((prod(I, I) → bool) → prod(H, H) → bool). " +
			"∀d d':(C → D). " +
			"    biaffine_deformation(R, R₀, f, g, A₀₁, A₀, A₁, t, s, V, M, ι, E₀, t₀, E₁, t₁, φ) ∧ " +
			"    d ∈ biaffine_overlap_derivations(R₀, g, A₀₁, V, M).carrier ∧ " +
			"    d' ∈ biaffine_overlap_derivations(R₀, g, A₀₁, V, M).carrier ⇒ " +
			"    biaffine_deformation(R, " +
			"        R₀, " +
			"        f, " +
			"        g, " +
			"        A₀₁, " +
			"        A₀, " +
			"        A₁, " +
			"        t, " +
			"        s, " +
			"        V, " +
			"        M, " +
			"        ι, " +
			"        E₀, " +
			"        t₀, " +
			"        E₁, " +
			"        t₁, " +
			"        biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d)) ∧ " +
			"    ((∃ψ₀:(I → I). ∃ψ₁:(H → H). " +
			"            biaffine_isomorphism(R, " +
			"                A₀₁, " +
			"                V, " +
			"                M, " +
			"                E₀, " +
			"                t₀, " +
			"                E₁, " +
			"                t₁, " +
			"                biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d), " +
			"                E₀, " +
			"                t₀, " +
			"                E₁, " +
			"                t₁, " +
			"                biaffine_regluing(A₀₁, V, M, E₀, t₀, φ, d'), " +
			"                ψ₀, " +
			"                ψ₁)) ⇔ " +
			"        biaffine_overlap_derivations(R₀, g, A₀₁, V, M).add(d, " +
			"            biaffine_overlap_derivations(R₀, g, A₀₁, V, M).neg(d')) ∈ " +
			"        set_mul(biaffine_overlap_derivations(R₀, g, A₀₁, V, M).add, " +
			"            fst(biaffine_derivation_pair(R₀, g, A₀₁, A₀, A₁, V, M)), " +
			"            snd(biaffine_derivation_pair(R₀, g, A₀₁, A₀, A₁, V, M)))))",
	},
		"D² of each chart with its module is zero, so the local obstruction is the zero pair "+
			"(LocalDeformationsExistIff, biaffineLocalObstructionDef); D¹ of each chart is zero, "+
			"so the compatible classes are the zero pair alone (biaffineCompatibleClassesDef, "+
			"ClassModulesOverSubring for the zero). D¹(A₀₁/R₀, M₀₁) is D¹(A₀/R₀, M₀₁) through "+
			"the right map of R₀ → A₀ → A₀₁ (LocalizationRightMapIsomorphism at "+
			"BiaffineChartLocalization, CohomologyCoefficientRestriction), zero by hypothesis "+
			"with M₀₁ read over chart 0 (AmbientContains), so the cokernel is its one class "+
			"(biaffineGluingCokernelDef). CokernelZeroLocalObstructionSuffices gives a "+
			"deformation; for two, the compatible pair of BiaffineDeformationsTorsorLayers is "+
			"zero, so their chart classes agree and its regluing layer gives the rest"),
})}
