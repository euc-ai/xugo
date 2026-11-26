// localization.go — square-zero extensions and deformations localized at
// a lift. An extension E of S by N localized at a lift t' of t is an
// extension of S[1/t] by N[1/t] (algebra/ring/square_zero_extension), and
// its class is the restriction of E's class to S[1/t]: the right map of
// R → S → S[1/t] sends it to the class of the pullback, which is E pushed
// along N → N[1/t]. A deformation of T over R, localized, is a
// deformation of T[1/t] with coefficients M[1/t].

package algebra_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_examples"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/square_zero_classification"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/transitivity"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_localization"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/square_zero_extension"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// SquareZeroLocalizationClass — in a universe for R, S and S', the class
// of an extension E of S by N over R localized at a lift t' of t is the
// restriction of the class of E to the localization S' of S, its
// coefficients carried into the localization N' of N.
var SquareZeroLocalizationClass = squareZeroLocalizationClassThm{family.Add(registry.ProofEntry{
	Name: "SquareZeroLocalizationClass",
	Key:  "prop_833e3fac66b1606e",
	Reading: "This is how a class on a chart is read on the overlap: localizing the extension " +
		"and restricting its class agree, so the restriction is the localization of extensions " +
		"read in D^1. The restriction is the coefficient map along ν followed by the inverse of " +
		"the right map of R → S → S', a bijection on the classes because S' is a localization " +
		"(LocalizationRightMapIsomorphism); the localization of E is an extension of S' whatever " +
		"lift t' is chosen, and two lifts give one class (SquareZeroLocalizationIndependent). S' " +
		"and N' are any localizations, the fraction model or in place.",
	Deps: []registry.EntryLike{
		square_zero_extension.SquareZeroLocalizationIsExtension,
		square_zero_extension.SquareZeroIsomorphismDef,
		RightMapIsPullback,
		PullbackIsExtension,
		PushoutIsExtension,
		PushoutClassIsCoefficientMap,
		CohomologyCoefficientRestriction,
		SquareZeroPullbackDef,
		SquareZeroPushoutDef,
		square_zero_classification.ExtensionClassWellDefined,
		cotangent_examples.LocalizationRightMapIsomorphism,
		cotangent_examples.CotangentCohomologyRestrictionHom,
		transitivity.CotangentCohomologyRestrictionDef,
		ring_localization.IsModuleLocalizationOnDef,
		ring_localization.ToFractionHomomorphism,
		functions.InverseOnLeft,
		module_homomorphism.ModuleIsomorphismDef,
		square_zero_extension.SquareZeroExtension,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀E:square_zero_ops(A, B, C, D). " +
			"∀t:B. " +
			"∀t':C. " +
			"∀S':ring_ops(F). " +
			"∀ρ:(B → F). " +
			"∀N':module_ops(F, G). " +
			"∀ν:(D → G).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(S', 𝕌⟨A:U⟩)",
			"square_zero_extension(R, S, f, N, E)",
			"t' ∈ E.ring.carrier",
			"E.projection(t') = t",
			"is_localization_on(S, monoid_powers(S.mul, S.one, t), S', ρ)",
			"is_module_localization_on(S, monoid_powers(S.mul, S.one, t), S', ρ, N, N', ν)",
		},
		Conclusion: "square_zero_class⟨U:U⟩(R, " +
			"    S', " +
			"    λa:A. ρ(f(a)), " +
			"    N', " +
			"    square_zero_localization(N, S', ρ, N', ν, E, t')) = " +
			"cotangent_cohomology_restriction(R, S, f, S', ρ, N', ν, 1, square_zero_class(R, S, f, N, E))",
	},
		"let L be the localization, an extension of S' by N' over R "+
			"(SquareZeroLocalizationIsExtension). The right map of R → S → S' sends the class of L to the "+
			"class of its pullback ρ*L along ρ (RightMapIsPullback, CohomologyCoefficientRestriction). "+
			"[(e, m)] ↦ (p(e), e/1 + L.inclusion(m)) is an isomorphism from the pushout ν_*E onto ρ*L "+
			"over R, the identity on N' and over S: it kills the relations (i(n), −ν(n)), i(n)/1 being "+
			"L.inclusion(ν(n)) (SquareZeroLocalizationIsExtension's last conjunct at v = one), e ↦ e/1 is "+
			"a ring map (ToFractionHomomorphism), and a map of extensions of S by one module over the "+
			"identity is bijective (SquareZeroPushoutDef, SquareZeroPullbackDef, PushoutIsExtension, "+
			"PullbackIsExtension, SquareZeroIsomorphismDef). So the class of ρ*L is that of ν_*E "+
			"(ExtensionClassWellDefined), the coefficient image of E's class "+
			"(PushoutClassIsCoefficientMap, CohomologyCoefficientRestriction). The right map is injective "+
			"on the classes of D^1(S'/R, N') (LocalizationRightMapIsomorphism, ModuleIsomorphismDef) and "+
			"L's class is one of them, so it is the inverse_on of the coefficient image (InverseOnLeft, "+
			"CotangentCohomologyRestrictionDef, CotangentCohomologyRestrictionHom)"),
})}

// DeformationLocalizes — a deformation E of T over R, localized at a
// lift t' of t, is a deformation of the localization T' of T at the
// powers of t, with coefficients the localization M' of M and the map ν ∘ ι
// from the kernel J; T' is an algebra over R₀ through ρ ∘ g and ν ∘ ι is
// linear over R₀.
var DeformationLocalizes = deformationLocalizesThm{family.Add(registry.ProofEntry{
	Name: "DeformationLocalizes",
	Key:  "prop_7ff3fd8ff8e4c700",
	Reading: "The deformation condition E.structure(j) = i(ι(j)) on J localizes term by term: " +
		"j/1 is the image of i(ι(j))/1, which is the localized inclusion of ν(ι(j)). With M = J " +
		"⊗_{R₀} T and ι(j) = j ⊗ 1, M' = J ⊗_{R₀} T' and ν ∘ ι is j ↦ j ⊗ 1 again, so a flat " +
		"deformation localizes to a flat deformation. The first two conjuncts are what the situation " +
		"asks of T' and (M', ν ∘ ι), so the obstruction and the torsor of T' are read with them.",
	Deps: []registry.EntryLike{
		AlgebraDeformationDef,
		square_zero_extension.SquareZeroLocalizationIsExtension,
		square_zero_extension.SquareZeroLocalizationDef,
		ring_localization.IsLocalizationOnDef,
		ring_localization.IsModuleLocalizationOnDef,
		ring_homomorphism.RingHomomorphism,
		module_homomorphism.ModuleHomomorphismDef,
		module_homomorphism.HomCompose,
		module_homomorphism.HomIn,
		ring_homomorphism.RingKernelDef,
	},
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀R₀:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀M:module_ops(C, D). " +
			"∀ι:(A → D). " +
			"∀E:square_zero_ops(A, C, I, D). " +
			"∀t:C. " +
			"∀t':I. " +
			"∀T':ring_ops(F). " +
			"∀ρ:(C → F). " +
			"∀M':module_ops(F, G). " +
			"∀ν:(D → G).",
		Hypotheses: []string{
			"ring_homomorphism(R, R₀, f)",
			"image(f, R.carrier) = R₀.carrier",
			"∀x y:A. " +
				"    x ∈ ring_kernel(R₀.zero, R.carrier, f) ∧ y ∈ ring_kernel(R₀.zero, R.carrier, f) ⇒ " +
				"    R.mul(x, y) = R.zero",
			"ring_homomorphism(R₀, T, g)",
			"module_on(T, M)",
			"module_homomorphism(R₀, thickening_kernel(R, R₀, f), scalar_restriction(g, M), ι)",
			"«deformation»(E)",
			"t' ∈ E.ring.carrier",
			"E.projection(t') = t",
			"is_localization_on(T, monoid_powers(T.mul, T.one, t), T', ρ)",
			"is_module_localization_on(T, monoid_powers(T.mul, T.one, t), T', ρ, M, M', ν)",
		},
		Conclusion: "ring_homomorphism(R₀, T', λb:B. ρ(g(b))) ∧ " +
			"module_homomorphism(R₀, " +
			"    thickening_kernel(R, R₀, f), " +
			"    scalar_restriction(λb:B. ρ(g(b)), M'), " +
			"    λa:A. ν(ι(a))) ∧ " +
			"algebra_deformation(R, " +
			"    R₀, " +
			"    f, " +
			"    T', " +
			"    λb:B. ρ(g(b)), " +
			"    M', " +
			"    λa:A. ν(ι(a)), " +
			"    square_zero_localization(M, T', ρ, M', ν, E, t'))",
	},
		"ρ ∘ g is a ring map, ρ one by IsLocalizationOnDef (RingHomomorphism); ν ∘ ι is linear over R₀, "+
			"ι linear into M over R₀ through g and ν into M' over T through ρ (IsModuleLocalizationOnDef, "+
			"HomCompose, ModuleHomomorphismDef). Unfold AlgebraDeformationDef: the localization is an "+
			"extension of T' by M' over R through ρ ∘ g ∘ f (SquareZeroLocalizationIsExtension at the base "+
			"R, E an extension of T over R through g ∘ f). For j in J (RingKernelDef) the structure map "+
			"reads E.structure(j)/1 = i(ι(j))/1, E being a deformation (SquareZeroLocalizationDef), and "+
			"ι(j) lies in M (HomIn), so the last conjunct of SquareZeroLocalizationIsExtension at v = one, "+
			"ρ(one) • ν(ι(j)) = ν(ι(j)), makes it the inclusion of ν(ι(j))"),
})}
