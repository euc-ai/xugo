package definable_deformation

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/algebra_deformation"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var ExalCoefficientCodesContinuous = exalCoefficientCodesContinuousThm{family.Add(registry.ProofEntry{
	Name: "ExalCoefficientCodesContinuous",
	Key:  "prop_c35b57491226092",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:ring_ops(B). " +
				"∀f:(A → B). " +
				"∀N:module_ops(B, D). " +
				"∀M:module_ops(B, F). " +
				"∀v:(D → F).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"module_on(S, N)",
				"module_on(S, M)",
				"module_homomorphism(S, N, M, v)",
			},
			Conclusion: "group_homomorphism(factor_set_group(R, S, f, N), " +
				"    factor_set_group(R, S, f, M), " +
				"    λz:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
				"        (λp:prod(B, B). COND(p ∈ set_cross(S.carrier, S.carrier), v(fst(z, p)), M.zero), " +
				"        (λp:prod(B, B). COND(p ∈ set_cross(S.carrier, S.carrier), v(fst(snd(z), p)), M.zero), " +
				"        λr:A. COND(r ∈ R.carrier, v(snd(snd(z), r)), M.zero)))) ∧ " +
				"continuous_map(subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
				"    subtopology(factor_set_topology(R, S, M), factor_set_codes(R, S, f, M)), " +
				"    λz:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
				"        (λp:prod(B, B). COND(p ∈ set_cross(S.carrier, S.carrier), v(fst(z, p)), M.zero), " +
				"        (λp:prod(B, B). COND(p ∈ set_cross(S.carrier, S.carrier), v(fst(snd(z), p)), M.zero), " +
				"        λr:A. COND(r ∈ R.carrier, v(snd(snd(z), r)), M.zero)))) ∧ " +
				"image(λz:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
				"        (λp:prod(B, B). COND(p ∈ set_cross(S.carrier, S.carrier), v(fst(z, p)), M.zero), " +
				"        (λp:prod(B, B). COND(p ∈ set_cross(S.carrier, S.carrier), v(fst(snd(z), p)), M.zero), " +
				"        λr:A. COND(r ∈ R.carrier, v(snd(snd(z), r)), M.zero))), " +
				"    factor_set_boundaries(R, S, f, N)) ⊆ " +
				"factor_set_boundaries(R, S, f, M)",
		},
		"Postcompose defects with the coefficient map. Pushout of the canonical section "+
			"proves agreement with pushout classes; the formula reads one coordinate."),
	Deps: []registry.EntryLike{
		FactorSetRealization,
		FactorSetCoboundaryDef,
		algebra_deformation.PushoutClassIsCoefficientMap,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "Postcompose defects with the coefficient map. Pushout of the canonical " +
		"section proves agreement with pushout classes; the formula reads one coordinate.",
})}

var ExalPullbackCodesContinuous = exalPullbackCodesContinuousThm{family.Add(registry.ProofEntry{
	Name: "ExalPullbackCodesContinuous",
	Key:  "prop_68d044bfd79f117c",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:ring_ops(B). " +
				"∀f:(A → B). " +
				"∀N:module_ops(B, D). " +
				"∀S₁:ring_ops(F). " +
				"∀f₁:(A → F). " +
				"∀g:(F → B).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"module_on(S, N)",
				"ring_homomorphism(R, S₁, f₁)",
				"ring_homomorphism(S₁, S, g)",
				"∀r:A. r ∈ R.carrier ⇒ g(f₁(r)) = f(r)",
			},
			Conclusion: "group_homomorphism(factor_set_group(R, S, f, N), " +
				"    factor_set_group(R, S₁, f₁, scalar_restriction(g, N)), " +
				"    λz:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
				"        (λp:prod(F, F). " +
				"            COND(p ∈ set_cross(S₁.carrier, S₁.carrier), " +
				"                fst(z, (g(fst(p)), g(snd(p)))), " +
				"                N.zero), " +
				"        (λp:prod(F, F). " +
				"            COND(p ∈ set_cross(S₁.carrier, S₁.carrier), " +
				"                fst(snd(z), (g(fst(p)), g(snd(p)))), " +
				"                N.zero), " +
				"        snd(snd(z))))) ∧ " +
				"continuous_map(subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
				"    subtopology(factor_set_topology(R, S₁, scalar_restriction(g, N)), " +
				"        factor_set_codes(R, S₁, f₁, scalar_restriction(g, N))), " +
				"    λz:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
				"        (λp:prod(F, F). " +
				"            COND(p ∈ set_cross(S₁.carrier, S₁.carrier), " +
				"                fst(z, (g(fst(p)), g(snd(p)))), " +
				"                N.zero), " +
				"        (λp:prod(F, F). " +
				"            COND(p ∈ set_cross(S₁.carrier, S₁.carrier), " +
				"                fst(snd(z), (g(fst(p)), g(snd(p)))), " +
				"                N.zero), " +
				"        snd(snd(z))))) ∧ " +
				"image(λz:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
				"        (λp:prod(F, F). " +
				"            COND(p ∈ set_cross(S₁.carrier, S₁.carrier), " +
				"                fst(z, (g(fst(p)), g(snd(p)))), " +
				"                N.zero), " +
				"        (λp:prod(F, F). " +
				"            COND(p ∈ set_cross(S₁.carrier, S₁.carrier), " +
				"                fst(snd(z), (g(fst(p)), g(snd(p)))), " +
				"                N.zero), " +
				"        snd(snd(z)))), " +
				"    factor_set_boundaries(R, S, f, N)) ⊆ " +
				"factor_set_boundaries(R, S₁, f₁, scalar_restriction(g, N))",
		},
		"Precompose the two defect arrays by g in both variables, retaining rho. The "+
			"pullback section yields this formula and RightMapIsPullback identifies its class."),
	Deps: []registry.EntryLike{
		FactorSetRealization,
		FactorSetCoboundaryDef,
		algebra_deformation.RightMapIsPullback,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "Precompose the two defect arrays by g in both variables, retaining rho. " +
		"The pullback section yields this formula and RightMapIsPullback identifies its class.",
})}

var LocalizedCodeContinuous = localizedCodeContinuousThm{family.Add(registry.ProofEntry{
	Name: "LocalizedCodeContinuous",
	Key:  "prop_a8dbfb5a72a1b690",
	Build: family.Card(
		Statement{
			Binders: "∀R:ring_ops(A). " +
				"∀S:ring_ops(B). " +
				"∀f:(A → B). " +
				"∀N:module_ops(B, D). " +
				"∀t:B. " +
				"∀S₁:ring_ops(F). " +
				"∀g:(B → F). " +
				"∀M:module_ops(F, G). " +
				"∀v:(D → G).",
			Hypotheses: []string{
				"ring_homomorphism(R, S, f)",
				"module_on(S, N)",
				"countable(R.carrier)",
				"countable(S.carrier)",
				"countable(N.carrier)",
				"cotangent_universe(R, 𝕌⟨A:U⟩)",
				"cotangent_universe(S, 𝕌⟨A:U⟩)",
				"cotangent_universe(S₁, 𝕌⟨A:U⟩)",
				"t ∈ S.carrier",
				"is_localization_on(S, monoid_powers(S.mul, S.one, t), S₁, g)",
				"is_module_localization_on(S, monoid_powers(S.mul, S.one, t), S₁, g, N, M, v)",
			},
			Conclusion: "∃L:(prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)) → " +
				"        prod(prod(F, F) → G, prod(prod(F, F) → G, A → G))). " +
				"    group_homomorphism(factor_set_group(R, S, f, N), " +
				"        factor_set_group(R, S₁, λr:A. g(f(r)), M), " +
				"        L) ∧ " +
				"    continuous_map(subtopology(factor_set_topology(R, S, N), factor_set_codes(R, S, f, N)), " +
				"        subtopology(factor_set_topology(R, S₁, M), factor_set_codes(R, S₁, λr:A. g(f(r)), M)), " +
				"        L) ∧ " +
				"    (∀z:prod(prod(B, B) → D, prod(prod(B, B) → D, A → D)). " +
				"        z ∈ factor_set_codes(R, S, f, N) ⇒ " +
				"        square_zero_class⟨U:U⟩(R, " +
				"            S₁, " +
				"            λr:A. g(f(r)), " +
				"            M, " +
				"            factor_set_extension(S₁, λr:A. g(f(r)), M, L(z))) = " +
				"        cotangent_cohomology_restriction(R, " +
				"            S, " +
				"            f, " +
				"            S₁, " +
				"            g, " +
				"            M, " +
				"            v, " +
				"            1, " +
				"            square_zero_class(R, S, f, N, factor_set_extension(S, f, N, z))))",
		},
		"Choose once a fraction representation of each target scalar, using a fixed "+
			"enumeration, and choose zero at zero. Lift these fractions at the canonical lift "+
			"of t and extract defects. Each target coordinate is a finite linear expression "+
			"in the original defects; SquareZeroLocalizationClass identifies the class."),
	Deps: []registry.EntryLike{
		FactorSetRealization,
		algebra_deformation.SquareZeroLocalizationClass,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "This is a continuous additive lift for each localization arrow. No strict " +
		"compatibility between independently chosen lifts for composite arrows is asserted.",
})}
