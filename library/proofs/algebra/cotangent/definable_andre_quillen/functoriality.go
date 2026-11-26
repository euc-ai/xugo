package definable_andre_quillen

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_examples"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/transitivity"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/polish_cohomology"
	"github.com/euc-ai/xugo/library/proofs/topology/polish_space"
	"github.com/euc-ai/xugo/library/registry"
)

var AQAlgebraMapContinuous = aQAlgebraMapContinuousThm{family.Add(registry.ProofEntry{
	Name: "AQAlgebraMapContinuous",
	Key:  "prop_7f0cf0785932f644",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
		},
		Conclusion: "continuous_map(dual_pointwise_topologies(N, standard_names(R, T), n), " +
			"    dual_pointwise_topologies(N, standard_names(R, S), n), " +
			"    λw:(U → D). " +
			"        free_algebra_jacobian_transpose(universe_embedding(R), " +
			"            universe_embedding(R), " +
			"            R, " +
			"            R, " +
			"            standard_names(R, S, n), " +
			"            standard_names(R, T, n), " +
			"            standard_map(R, S, T, g, n), " +
			"            λu:U. standard_to_base(R, T, λa:A. g(f(a)), n, u), " +
			"            N, " +
			"            w))",
	},
		"The map in CotangentMapsDualAgreement is the transpose of the actual cotangent "+
			"chain map. At each output name the image of its basis vector has finite support, "+
			"so FiniteCoordinateContinuous applies to the normalized degree carriers."),
	Deps: []registry.EntryLike{
		cotangent_complex.CotangentMapsDualAgreement,
		cotangent_complex.CotangentFunctorialMap,
		polish_space.FiniteCoordinateContinuous,
	},
	Reading: "Continuity in the pointwise discrete topologies does not " +
		"require countability. Inactive coordinates are zero, and the " +
		"finite support depends on the output name, not on the input cochain.",
})}

var AQAlgebraMapDefinable = aQAlgebraMapDefinableThm{family.Add(registry.ProofEntry{
	Name: "AQAlgebraMapDefinable",
	Key:  "prop_7ab8dd1bbf1fcb",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(T, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"countable(R.carrier)",
			"countable(S.carrier)",
			"countable(T.carrier)",
			"countable(N.carrier)",
		},
		Conclusion: "cohomology_borel_map(cotangent_cochain⟨U:U⟩(R, T, λa:A. g(f(a)), T, λc:C. c, N), " +
			"    dual_pointwise_topologies(N, standard_names(R, T)), " +
			"    n, " +
			"    cotangent_cochain(R, S, f, T, g, N), " +
			"    dual_pointwise_topologies(N, standard_names(R, S)), " +
			"    n, " +
			"    co_transitivity_right_map(R, S, f, T, g, N, n))",
	},
		"AQScalarPolishModel gives both complexes and AQAlgebraMapContinuous gives "+
			"the degreewise continuity. CotangentMapsDualAgreement supplies the cochain "+
			"map, and CohomologyDefinableFunctor applies to the named right map."),
	Deps: []registry.EntryLike{
		AQScalarPolishModel,
		AQAlgebraMapContinuous,
		cotangent_complex.CotangentMapsDualAgreement,
		polish_cohomology.CohomologyDefinableFunctor,
		transitivity.CoTransitivityRightMapDef,
	},
	Reading: "The right map is contravariant in the algebra: it takes D^n(T/R,N) to " +
		"D^n(S/R,N). Both complexes have scalars T, so no change of quotient carrier is hidden.",
})}

var AQLocalizationDefinable = aQLocalizationDefinableThm{family.Add(registry.ProofEntry{
	Name: "AQLocalizationDefinable",
	Key:  "prop_e6e3805d051df4bb",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀t:B. " +
			"∀S':ring_ops(C). " +
			"∀ρ:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(S', 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"t ∈ S.carrier",
			"is_localization_on(S, monoid_powers(S.mul, S.one, t), S', ρ)",
			"module_on(S', N)",
			"countable(R.carrier)",
			"countable(S.carrier)",
			"countable(S'.carrier)",
			"countable(N.carrier)",
		},
		Conclusion: "cohomology_borel_iso(cotangent_cochain⟨U:U⟩(R, S', λa:A. ρ(f(a)), S', λc:C. c, N), " +
			"    dual_pointwise_topologies(N, standard_names(R, S')), " +
			"    n, " +
			"    cotangent_cochain(R, S, f, S', ρ, N), " +
			"    dual_pointwise_topologies(N, standard_names(R, S)), " +
			"    n, " +
			"    co_transitivity_right_map(R, S, f, S', ρ, N, n))",
	},
		"The continuous cochain map of AQAlgebraMapContinuous induces the isomorphism "+
			"of LocalizationRightMapIsomorphism. With AQScalarPolishModel on both sides, "+
			"ContinuousQuasiIsoDefinableIso supplies a Borel lift of its inverse."),
	Deps: []registry.EntryLike{
		AQAlgebraMapContinuous,
		AQScalarPolishModel,
		cotangent_complex.CotangentMapsDualAgreement,
		cotangent_examples.LocalizationRightMapIsomorphism,
		polish_cohomology.ContinuousQuasiIsoDefinableIso,
	},
	Reading: "This is the right map from the localization back to S, with coefficients already " +
		"over the localization. Its inverse lift is Borel; no continuous section is asserted.",
})}

var AQRestrictionDefinable = aQRestrictionDefinableThm{family.Add(registry.ProofEntry{
	Name: "AQRestrictionDefinable",
	Key:  "prop_f1876762dcb5189d",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀N:module_ops(B, D). " +
			"∀t:B. " +
			"∀S':ring_ops(C). " +
			"∀ρ:(B → C). " +
			"∀N':module_ops(C, E). " +
			"∀ν:(D → E). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"cotangent_universe(S', 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"t ∈ S.carrier",
			"is_localization_on(S, monoid_powers(S.mul, S.one, t), S', ρ)",
			"module_on(S, N)",
			"module_on(S', N')",
			"module_homomorphism(S, N, scalar_restriction(ρ, N'), ν)",
			"countable(R.carrier)",
			"countable(S.carrier)",
			"countable(S'.carrier)",
			"countable(N.carrier)",
			"countable(N'.carrier)",
		},
		Conclusion: "borel_cover_map(cocycle_group(«source», n), " +
			"    cocycle_topology(«source», dual_pointwise_topologies(N, standard_names(R, S)), n), " +
			"    coboundaries(«source», n), " +
			"    cocycle_group(«target», n), " +
			"    cocycle_topology(«target», dual_pointwise_topologies(N', standard_names(R, S')), n), " +
			"    coboundaries(«target», n), " +
			"    cotangent_cohomology_restriction(R, S, f, S', ρ, N', ν, n))",
		Abbrev: Abbrev{
			{Name: "source", Text: "cotangent_cochain⟨U:U⟩(R, S, f, S, λy:B. y, N)"},
			{Name: "target", Text: "cotangent_cochain⟨U:U⟩(R, S', λa:A. ρ(f(a)), S', λc:C. c, N')"},
		},
	},
		"AndreQuillenCoefficientMapContinuous applied to N' restricted along ρ gives a "+
			"continuous coefficient lift. Compose it with the Borel inverse supplied by "+
			"AQLocalizationDefinable; CotangentCohomologyRestrictionHom identifies the "+
			"composite with the existing restriction and supplies its additive homomorphism law."),
	Deps: []registry.EntryLike{
		AndreQuillenCoefficientMapContinuous,
		AQLocalizationDefinable,
		cotangent_examples.CotangentCohomologyRestrictionHom,
		transitivity.CotangentCohomologyRestrictionDef,
	},
	Reading: "The source scalars are S and the target scalars S', so the " +
		"statement uses borel_cover_map of their additive groups. The coefficient " +
		"map need only be S-linear; N' need not itself be the localization of N.",
})}
