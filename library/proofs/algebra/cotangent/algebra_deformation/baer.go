// baer.go — the Baer sum read through the classes. The class of the Baer
// sum of two extensions is the sum of their classes in D^1(S/R, N). The
// left map of the cohomology sequence of R → S → T sends the class of an
// extension over S to the class of the same extension read over R. So
// the Baer sum of a deformation with an extension over R₀, read over R,
// is again a deformation, its class moved by the left map's image of the
// extension's class, and two deformations differ by the Baer sum with the
// realization of the class between them.

package algebra_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cohomology_one"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/square_zero_classification"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/standard_resolution"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/transitivity"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/chain_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/square_zero_extension"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// The spelling of the statements
// ---------------------------------------------------------------------------

// ---------------------------------------------------------------------------
// The class of a Baer sum
// ---------------------------------------------------------------------------

// BaerSumClass — in a universe for R and S, the class of the Baer sum of
// two square-zero extensions of S by N over R is the sum of their classes
// in D^1(S/R, N).
var BaerSumClass = baerSumClassThm{family.Add(registry.ProofEntry{
	Name: "BaerSumClass",
	Key:  "prop_c97d50fc57a6e63b",
	Reading: "The sum is that of the module D^1(S/R, N), the coset of the sum of two cocycles. " +
		"Lifts s and s' of the standard presentation to E and E' give the lift u ↦ [(s(u), s'(u))] to " +
		"the Baer sum, which reads γ_s + γ_{s'}: on the kernel [(i(γ_s(x)), i'(γ_{s'}(x)))] is the " +
		"inclusion of the sum. With BaerSumSplitUnit, BaerSumInverse and ExtensionIsoIffSameClass, " +
		"the classes of the extensions under the Baer sum are the group D^1(S/R, N).",
	Deps: []registry.EntryLike{
		square_zero_extension.BaerSumIsExtension,
		square_zero_extension.SquareZeroBaerSumDef,
		square_zero_extension.SquareZeroFiberProductDef,
		square_zero_extension.SquareZeroLiftDef,
		square_zero_extension.ExtractConormalDef,
		square_zero_classification.StandardExtensionLiftExists,
		square_zero_classification.ExtensionClassWellDefined,
		cohomology_one.ConormalToCocycleDef,
		cohomology_one.ConormalClassDef,
		cotangent_complex.CotangentCohomologyDef,
		chain_complex.CohomologyModuleDef,
		submodule.QuotientModuleDef,
		quotient_ring.IdealQuotientProjection,
		functions.InjectiveOnDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀E':square_zero_ops(A, B, I, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"square_zero_extension(R, S, f, N, E)",
			"square_zero_extension(R, S, f, N, E')",
		},
		Conclusion: "square_zero_class⟨U:U⟩(R, S, f, N, square_zero_baer_sum(N, E, E')) = " +
			"cotangent_cohomology(R, S, f, S, λy:B. y, N, 1).add(square_zero_class(R, S, f, N, E), " +
			"    square_zero_class(R, S, f, N, E'))",
	},
		"let s and s' be lifts of the standard presentation's augmentation to E and E' "+
			"(StandardExtensionLiftExists). u ↦ [(s(u), s'(u))] is a lift to the Baer sum: (s(u), s'(u)) "+
			"lies in the fiber product, both projections being ε(u), and the coset map is a ring map over "+
			"R (BaerSumIsExtension, IdealQuotientProjection, SquareZeroLiftDef). On the kernel of ε, "+
			"[(i(γ_s(x)), i'(γ_{s'}(x)))] = [(i(γ_s(x) + γ_{s'}(x)), 0)] (BaerSumIsExtension's last "+
			"conjunct), so the lift reads γ_s + γ_{s'} (ExtractConormalDef, InjectiveOnDef); off the "+
			"kernel both are N.zero. The class is the coset of C(γ_s + γ_{s'}) = C(γ_s) + C(γ_{s'}), the "+
			"cocycle map being linear (ConormalToCocycleDef, ConormalClassDef), the sum of the two cosets "+
			"(ExtensionClassWellDefined, CotangentCohomologyDef, CohomologyModuleDef, QuotientModuleDef)"),
})}

// LeftMapIsRestrictionOfScalars — in a universe for the three rings, an
// extension E of T by N over S read over R through f is an extension
// over R, and the left map D^1(T/S, N) → D^1(T/R, N) of the cohomology
// sequence sends the class of E to its class.
var LeftMapIsRestrictionOfScalars = leftMapIsRestrictionOfScalarsThm{family.Add(registry.ProofEntry{
	Name: "LeftMapIsRestrictionOfScalars",
	Key:  "prop_c72d1ff5babf684a",
	Reading: "The companion of RightMapIsPullback: the left map forgets that the extension is " +
		"an algebra over S and keeps it as one over R, its structure map after f. In degree 1 it " +
		"is precomposition with the change of coefficients R[T] → S[T] of the standard " +
		"presentations, the identity on the tags of T's elements and f on the constants " +
		"(standard_base_change). Over a thickening it is how D^1(T/R₀, M) acts on the " +
		"deformations: an extension over R₀ read over R has its structure map zero on the kernel J.",
	Deps: []registry.EntryLike{
		transitivity.CoTransitivityLeftMapDef,
		standard_resolution.StandardBaseChangeDef,
		standard_resolution.StandardBaseChangeAugmentation,
		standard_resolution.StandardBaseChangeMap,
		square_zero_classification.StandardExtensionLiftExists,
		square_zero_classification.ExtensionClassWellDefined,
		square_zero_extension.SquareZeroExtension,
		square_zero_extension.SquareZeroLiftDef,
		square_zero_extension.ExtractConormalDef,
		cohomology_one.ConormalToCocycleDef,
		cohomology_one.ConormalClassDef,
		chain_complex.CohomologyMapDef,
		ring_homomorphism.RingHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀E:square_zero_ops(B, C, I, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"square_zero_extension(S, T, g, N, E)",
		},
		Conclusion: "«overT»( " +
			"    mk_square_zero(E.ring, λa:A. E.structure(f(a)), E.inclusion, E.projection)) ∧ " +
			"«leftMap»(square_zero_class⟨U:U⟩(S, T, g, N, E)) = " +
			"«classT»(mk_square_zero(E.ring, λa:A. E.structure(f(a)), E.inclusion, E.projection))",
	},
		"E read over R is an extension: k ∘ f is a ring map from R, and p ∘ k ∘ f = g ∘ f "+
			"(SquareZeroExtension, RingHomomorphism). A lift s of the augmentation of T's standard "+
			"presentation over S to E (StandardExtensionLiftExists) followed by the change of "+
			"coefficients β from the presentation over R is a lift of the presentation over R to E "+
			"read over R, β covering the augmentations and carrying the constant a to the constant "+
			"f(a) (StandardBaseChangeDef, StandardBaseChangeAugmentation, StandardBaseChangeMap, "+
			"SquareZeroLiftDef); it reads γ_s ∘ β on the kernel (ExtractConormalDef). C_R(γ_s ∘ β) "+
			"is the transposed Jacobian of β applied to C_S(γ_s), the cochain map the left map is "+
			"induced by (CoTransitivityLeftMapDef, ConormalToCocycleDef), so both sides are the "+
			"coset of that cochain (ExtensionClassWellDefined, ConormalClassDef, CohomologyMapDef)"),
})}

// ---------------------------------------------------------------------------
// Deformations moved by a Baer sum
// ---------------------------------------------------------------------------

// DeformationBaerSum — in a universe for the three rings, the Baer sum of
// a deformation E of T with an extension X of T by M over R₀, read over
// R, is a deformation whose class is that of E plus the left map's image
// of the class of X; and any two deformations E and E' are related so:
// E' is isomorphic to the Baer sum of E with the realization of the one
// class η between them.
var DeformationBaerSum = deformationBaerSumThm{family.Add(registry.ProofEntry{
	Name: "DeformationBaerSum",
	Key:  "prop_29223f0529f41604",
	Reading: "X read over R has its structure map zero on J, f(j) being R₀.zero, so the sum's " +
		"structure map at j is [(k(j), 0)] = [(i(ι(j)), 0)], the inclusion of ι(j): the deformation " +
		"condition survives the sum. This is DeformationsTorsor read through extensions: D^1(T/R₀, " +
		"M) acts on the deformations by the Baer sum with the extensions over R₀, through the left " +
		"map (LeftMapIsRestrictionOfScalars). The realization exists at set(prod(U, D)), the type " +
		"of the realizations, and η is the one DeformationsTorsor gives, unique since f is onto.",
	Deps: []registry.EntryLike{
		AlgebraDeformationDef,
		ThickeningKernelDef,
		DeformationsTorsor,
		BaerSumClass,
		LeftMapIsRestrictionOfScalars,
		square_zero_extension.BaerSumIsExtension,
		square_zero_extension.SquareZeroBaerSumDef,
		square_zero_classification.ExtensionRealizeClass,
		square_zero_classification.ExtensionIsoIffSameClass,
		square_zero_classification.SquareZeroRealizationDef,
		ring_homomorphism.RingKernelDef,
		ring_homomorphism.AdditiveHomomorphism,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀M:module_ops(C, D). " +
			"∀ι:(A → D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(R₀, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, T, g)",
			"module_on(T, M)",
			"module_homomorphism(R₀, thickening_kernel(R, R₀, f), scalar_restriction(g, M), ι)",
		},
		Conclusion: "(∀E:square_zero_ops(A, C, I, D). ∀X:square_zero_ops(B, C, F, D). " +
			"    «deformation»(E) ∧ square_zero_extension(R₀, T, g, M, X) ⇒ " +
			"    «deformation»(square_zero_baer_sum(M, " +
			"            E, " +
			"            mk_square_zero(X.ring, λa:A. X.structure(f(a)), X.inclusion, X.projection))) ∧ " +
			"    square_zero_class⟨U:U⟩(R, " +
			"        T, " +
			"        λa:A. g(f(a)), " +
			"        M, " +
			"        square_zero_baer_sum(M, " +
			"            E, " +
			"            mk_square_zero(X.ring, λa:A. X.structure(f(a)), X.inclusion, X.projection))) = " +
			"    «deformationTR»(1).add(«classOfT»(E), " +
			"        «deformationLeft»(square_zero_class(R₀, T, g, M, X)))) ∧ " +
			"(∀E:square_zero_ops(A, C, I, D). ∀E':square_zero_ops(A, C, G, D). " +
			"    «deformation»(E) ∧ «deformation»(E') ⇒ " +
			"    ∃η:set(U → D). " +
			"        η ∈ «deformationTReduced»(1).carrier ∧ " +
			"        «classOfT»(E') = «deformationTR»(1).add(«classOfT»(E), «deformationLeft»(η)) ∧ " +
			"        (∃φ:(set(prod(I, set(prod(U, D)))) → G). " +
			"            square_zero_isomorphism(R, " +
			"                M, " +
			"                square_zero_baer_sum(M, " +
			"                    E, " +
			"                    mk_square_zero(square_zero_realization(R₀, T, g, M, η).ring, " +
			"                        λa:A. square_zero_realization(R₀, T, g, M, η).structure(f(a)), " +
			"                        square_zero_realization(R₀, T, g, M, η).inclusion, " +
			"                        square_zero_realization(R₀, T, g, M, η).projection)), " +
			"                E', " +
			"                φ)))",
	},
		"X read over R is an extension of T by M over R (LeftMapIsRestrictionOfScalars), so the "+
			"Baer sum is one (BaerSumIsExtension); for j in J, f(j) = R₀.zero and X's structure map "+
			"keeps zero, so the sum's structure map at j is [(k(j), X.ring.zero)] = [(i(ι(j)), 0)], the "+
			"inclusion of ι(j) (SquareZeroBaerSumDef, AlgebraDeformationDef, RingKernelDef, "+
			"AdditiveHomomorphism): a deformation. Its class is the sum of the two (BaerSumClass), the "+
			"class of X read over R the left map's image of X's (LeftMapIsRestrictionOfScalars). For "+
			"two deformations DeformationsTorsor gives η; its realization is an extension over R₀ with "+
			"class η (ExtensionRealizeClass, SquareZeroRealizationDef), so by the first part the sum is "+
			"a deformation with class class(E) + i*(η) = class(E'), and ExtensionIsoIffSameClass gives φ"),
})}
