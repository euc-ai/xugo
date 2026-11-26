package sobolev_section

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	"github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	"github.com/euc-ai/xugo/library/proofs/analysis/torus_sobolev"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var LocalizationExists = localizationExistsThm{family.Add(registry.ProofEntry{
	Name: "LocalizationExists",
	Key:  "prop_e40085976d68d622",
	Deps: []registry.EntryLike{
		smooth_manifold.PartitionOfUnity,
		smooth_manifold.PartitionOfUnityDef,
		smooth_manifold.AtlasDef,
		smooth_manifold.AtlasMemberCompatible,
		smooth_manifold.ChartRestrict,
		smooth_manifold.CompatibleChartDef,
		vec_smooth.SmoothMapCompose,
		vec_smooth.LinearSmoothMap,
		continuous.HomeomorphismCompose,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
			Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)"},
			Conclusion: "∃D:sobolev_localization(A). sobolev_localization_on(n, T, 𝒜, D)",
		},
		"Around each point restrict a compatible atlas chart to a small ball and rescale it affinely "+
			"into torus_small_box — the filler's promotion: a compatible chart restricted to an open "+
			"subdomain and post-composed with a Euclidean diffeomorphism of its image stays compatible "+
			"(ChartRestrict, CompatibleChartDef, SmoothMapCompose, LinearSmoothMap, HomeomorphismCompose). "+
			"PartitionOfUnity over K = ⋃T and these chart domains gives finitely many smooth weights, each "+
			"supported in one domain, summing to one on ⋃T (PartitionOfUnityDef). Choose a chart for each "+
			"weight and set the partition entries to zero at and past the count."),
})}

var FiniteRankSequenceNorm = finiteRankSequenceNormThm{family.Add(registry.ProofEntry{
	Name: "FiniteRankSequenceNorm",
	Key:  "prop_cb2e664b0b7f77ea",
	Deps: []registry.EntryLike{sequence_hilbert.NormSquaredFiniteSup},
	Build: family.Card(
		Statement{
			Binders:    "∀n r N:num. ∀s:int. ∀u:(prod(num, prod(num, num → int)) → complex).",
			Hypotheses: []string{"u ∈ (localization_sequence_module(n, r, N, s)).carrier"},
			Conclusion: "real_pow(localization_sequence_norm(n, r, N, s, u), 2) = " +
				"real_sum({i:num | i < N}, " +
				"    λi:num. " +
				"        real_sum({j:num | j < r}, " +
				"            λj:num. real_pow(sobolev_norm(n, s, λk:(num → int). u((i, (j, k)))), 2)))",
		},
		"A finite sum over chart and fibre indices commutes with the nonnegative finite-frequency sum."),
})}

var SmoothLocalization = smoothLocalizationThm{family.Add(registry.ProofEntry{
	Name: "SmoothLocalization",
	Key:  "prop_295e811413390dac",
	Deps: []registry.EntryLike{
		torus_sobolev.PeriodizedZeroExtensionSmooth,
		torus_sobolev.RapidIffAllSobolev,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀s:int. " +
				"∀f:(A → num → complex).",
			Hypotheses: []string{
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
				"smooth_projected_section(n, r, T, 𝒜, P, f)",
			},
			Conclusion: "localize_section(n, r, D, f) ∈ (section_sobolev_module(n, r, T, 𝒜, P, D, s)).carrier",
		},
		"Each cutoff component extends smoothly by zero and periodically; its Fourier sequence "+
			"is rapidly decreasing and hence belongs to every integer-order weighted space."),
})}

var SectionHilbert = sectionHilbertThm{family.Add(registry.ProofEntry{
	Name: "SectionHilbert",
	Reading: "The vectors are normalized frequency arrays in the closure of the localized " +
		"smooth image. This statement does not give pointwise representatives at low or " +
		"negative regularity. Empty bases and zero projections give the zero Hilbert space.",
	Key: "prop_bb3a610e8b87330c",
	Deps: []registry.EntryLike{
		SmoothLocalization,
		sequence_hilbert.WeightedHilbert,
		hilbert_space.ClosedSubspace,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀s:int.",
			Hypotheses: []string{
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
			},
			Conclusion: "complex_hilbert_space(section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
				"    localization_sequence_inner(n, r, D.count, s))",
		},
		"Smooth localized sections form a vector subspace of a finite-component "+
			"weighted Hilbert space; its closure is a closed Hilbert subspace."),
})}

var SectionSmoothDense = sectionSmoothDenseThm{family.Add(registry.ProofEntry{
	Name: "SectionSmoothDense",
	Key:  "prop_853e22495d644bc0",
	Deps: []registry.EntryLike{SectionHilbert},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀s:int. " +
				"∀u:(prod(num, prod(num, num → int)) → complex). " +
				"∀ε:real.",
			Hypotheses: []string{"&0 < ε",
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
				"u ∈ (section_sobolev_module(n, r, T, 𝒜, P, D, s)).carrier",
			},
			Conclusion: "∃f:(A → num → complex). " +
				"    smooth_projected_section(n, r, T, 𝒜, P, f) ∧ " +
				"    localization_sequence_norm(n, " +
				"        r, " +
				"        D.count, " +
				"        s, " +
				"        λz:prod(num, prod(num, num → int)). u(z) - localize_section(n, r, D, f, z)) < " +
				"    ε",
		},
		"Membership in the closure means every norm ball meets the localized smooth section subspace."),
})}

var SectionNormEquivalence = sectionNormEquivalenceThm{family.Add(registry.ProofEntry{
	Name: "SectionNormEquivalence",
	Key:  "prop_515154d4225ab5b9",
	Deps: []registry.EntryLike{
		torus_sobolev.LocalPullback,
		torus_sobolev.SmoothMultiplier,
		FiniteRankSequenceNorm,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀s:int. " +
				"∀E:sobolev_localization(A).",
			Hypotheses: []string{
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
				"sobolev_localization_on(n, T, 𝒜, E)",
			},
			Conclusion: "∃C:real. " +
				"    &0 < C ∧ " +
				"    ∀f:(A → num → complex). " +
				"        smooth_projected_section(n, r, T, 𝒜, P, f) ⇒ " +
				"        localization_sequence_norm(n, r, E.count, s, localize_section(n, r, E, f)) ≤ " +
				"        C * localization_sequence_norm(n, r, D.count, s, localize_section(n, r, D, f))",
		},
		"Insert the source partition into each target chart. Every overlap is a compactly supported "+
			"change of coordinates, and the finite sum of local pullback bounds gives the norm comparison."),
})}

var SectionCoordinateIsomorphism = sectionCoordinateIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "SectionCoordinateIsomorphism",
	Key:  "prop_56d9337e78350808",
	Deps: []registry.EntryLike{SectionNormEquivalence, SectionSmoothDense, SectionHilbert},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀s:int. " +
				"∀E:sobolev_localization(A).",
			Hypotheses: []string{
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
				"sobolev_localization_on(n, T, 𝒜, E)",
			},
			Conclusion: "bounded_operator(section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
				"    localization_sequence_norm(n, r, D.count, s), " +
				"    section_sobolev_module(n, r, T, 𝒜, P, E, s), " +
				"    localization_sequence_norm(n, r, E.count, s), " +
				"    section_coordinate_change(n, r, T, 𝒜, P, D, E, s)) ∧ " +
				"(∀f:(A → num → complex). " +
				"    smooth_projected_section(n, r, T, 𝒜, P, f) ⇒ " +
				"    section_coordinate_change(n, r, T, 𝒜, P, D, E, s)(localize_section(n, r, D, f)) = " +
				"    localize_section(n, r, E, f)) ∧ " +
				"(∀u:(prod(num, prod(num, num → int)) → complex). " +
				"    u ∈ (section_sobolev_module(n, r, T, 𝒜, P, D, s)).carrier ⇒ " +
				"    section_coordinate_change(n, r, T, 𝒜, P, E, D, s)( " +
				"        section_coordinate_change(n, r, T, 𝒜, P, D, E, s)(u)) = " +
				"    u)",
		},
		"The two norm comparisons extend the identity on smooth sections "+
			"in both directions; density makes their composites the identity."),
})}

var SectionOrderInclusion = sectionOrderInclusionThm{family.Add(registry.ProofEntry{
	Name: "SectionOrderInclusion",
	Key:  "prop_92172c89b1007afb",
	Deps: []registry.EntryLike{
		torus_sobolev.SobolevInclusion,
		SectionSmoothDense,
		FiniteRankSequenceNorm,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀s:int. " +
				"∀t:int.",
			Hypotheses: []string{
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
				"s ≤ t",
			},
			Conclusion: "bounded_operator(section_sobolev_module(n, r, T, 𝒜, P, D, t), " +
				"    localization_sequence_norm(n, r, D.count, t), " +
				"    section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
				"    localization_sequence_norm(n, r, D.count, s), " +
				"    λu:(prod(num, prod(num, num → int)) → complex). u)",
		},
		"The ambient sequence inclusion is bounded and sends "+
			"the dense smooth image into the weaker closed subspace."),
})}

var SectionRellich = sectionRellichThm{family.Add(registry.ProofEntry{
	Name: "SectionRellich",
	Key:  "prop_470badb71b768eef",
	Deps: []registry.EntryLike{
		torus_sobolev.Rellich,
		SectionOrderInclusion,
		SectionHilbert,
		FiniteRankSequenceNorm,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀s:int. " +
				"∀t:int.",
			Hypotheses: []string{
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
				"s < t",
			},
			Conclusion: "compact_operator(section_sobolev_module(n, r, T, 𝒜, P, D, t), " +
				"    localization_sequence_norm(n, r, D.count, t), " +
				"    section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
				"    localization_sequence_norm(n, r, D.count, s), " +
				"    λu:(prod(num, prod(num, num → int)) → complex). u)",
		},
		"Finite chart and fibre sums of torus Rellich inclusions are compact; restriction to "+
			"the closed section subspaces and the order-inclusion theorem give the global result."),
})}

var SectionSobolevEmbedding = sectionSobolevEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "SectionSobolevEmbedding",
	Reading: "Uniqueness is pointwise because k is nonnegative and the partition " +
		"sums to one on the manifold. Zero values outside the base carrier and " +
		"beyond the ambient fibre dimension are part of the section predicate.",
	Key:  "prop_f4d76510bcd2568d",
	Deps: []registry.EntryLike{torus_sobolev.SobolevEmbedding, SectionSmoothDense},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀s:int. " +
				"∀k:num. " +
				"∀u:(prod(num, prod(num, num → int)) → complex).",
			Hypotheses: []string{
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
				"int_of_num(n + 2 * k) < int_of_num(2) * s",
				"u ∈ (section_sobolev_module(n, r, T, 𝒜, P, D, s)).carrier",
			},
			Conclusion: "∃!f:(A → num → complex). " +
				"    projected_section_class(n, r, T, 𝒜, P, k, f) ∧ localize_section(n, r, D, f) = u",
		},
		"Apply finite-component Sobolev embedding in each chart, pass the projection and "+
			"overlap identities to the uniform limits, then reassemble with the partition."),
})}

var SectionSmoothRegularity = sectionSmoothRegularityThm{family.Add(registry.ProofEntry{
	Name: "SectionSmoothRegularity",
	Key:  "prop_885d49f79da7db59",
	Deps: []registry.EntryLike{SectionSobolevEmbedding, SmoothLocalization},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀u:(prod(num, prod(num, num → int)) → complex).",
			Hypotheses: []string{
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
			},
			Conclusion: "(∀s:int. u ∈ (section_sobolev_module(n, r, T, 𝒜, P, D, s)).carrier) ⇔ " +
				"∃f:(A → num → complex). " +
				"    smooth_projected_section(n, r, T, 𝒜, P, f) ∧ localize_section(n, r, D, f) = u",
		},
		"All orders supply arbitrarily many derivatives of the same compatible local "+
			"realization; conversely smooth localizations have rapid Fourier decay."),
})}

var SectionSmoothMultiplier = sectionSmoothMultiplierThm{family.Add(registry.ProofEntry{
	Name: "SectionSmoothMultiplier",
	Key:  "prop_4c4a0e23c7c15baf",
	Deps: []registry.EntryLike{torus_sobolev.SmoothMultiplier, SectionSmoothDense, SectionHilbert},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀s:int. " +
				"∀a:(A → complex).",
			Hypotheses: []string{
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
				"smooth_manifold_function⟨n⟩(T, 𝒜, λx:A. re(a(x)))",
				"smooth_manifold_function⟨n⟩(T, 𝒜, λx:A. im(a(x)))",
			},
			Conclusion: "bounded_operator(section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
				"    localization_sequence_norm(n, r, D.count, s), " +
				"    section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
				"    localization_sequence_norm(n, r, D.count, s), " +
				"    section_sobolev_multiply(n, r, T, 𝒜, P, D, s, a)) ∧ " +
				"(∀f:(A → num → complex). " +
				"    smooth_projected_section(n, r, T, 𝒜, P, f) ⇒ " +
				"    section_sobolev_multiply(n, r, T, 𝒜, P, D, s, a, localize_section(n, r, D, f)) = " +
				"    localize_section(n, r, D, λx:A. λj:num. a(x) * f(x, j)))",
		},
		"Cut off the scalar function in each chart and apply the torus multiplier "+
			"bound; extend by density. This includes every smooth partition cutoff."),
})}

var SectionBundleIsomorphism = sectionBundleIsomorphismThm{family.Add(registry.ProofEntry{
	Name: "SectionBundleIsomorphism",
	Key:  "prop_21d262c83dcbf1bd",
	Deps: []registry.EntryLike{torus_sobolev.SmoothMultiplier, SectionSmoothDense, SectionHilbert},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀s:int. " +
				"∀t:num. " +
				"∀Q B C:(A → num → num → complex).",
			Hypotheses: []string{
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
				"smooth_projection_bundle(n, t, T, 𝒜, Q)",
				"smooth_projection_map(n, r, t, T, 𝒜, P, Q, B)",
				"smooth_projection_map(n, t, r, T, 𝒜, Q, P, C)",
				"∀x:A. ∀i j:num. " +
					"    x ∈ ⋃T ∧ i < r ∧ j < r ⇒ " +
					"    module_sum(complex_add, " +
					"        complex_of_real(&0), " +
					"        {l:num | l < t}, " +
					"        λl:num. C(x, i, l) * B(x, l, j)) = " +
					"    P(x, i, j)",
				"∀x:A. ∀i j:num. " +
					"    x ∈ ⋃T ∧ i < t ∧ j < t ⇒ " +
					"    module_sum(complex_add, " +
					"        complex_of_real(&0), " +
					"        {l:num | l < r}, " +
					"        λl:num. B(x, i, l) * C(x, l, j)) = " +
					"    Q(x, i, j)",
			},
			Conclusion: "∃L R:((prod(num, prod(num, num → int)) → complex) → " +
				"        prod(num, prod(num, num → int)) → " +
				"        complex). " +
				"    bounded_operator(section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
				"        localization_sequence_norm(n, r, D.count, s), " +
				"        section_sobolev_module(n, t, T, 𝒜, Q, D, s), " +
				"        localization_sequence_norm(n, t, D.count, s), " +
				"        L) ∧ " +
				"    bounded_operator(section_sobolev_module(n, t, T, 𝒜, Q, D, s), " +
				"        localization_sequence_norm(n, t, D.count, s), " +
				"        section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
				"        localization_sequence_norm(n, r, D.count, s), " +
				"        R) ∧ " +
				"    (∀f:(A → num → complex). " +
				"        smooth_projected_section(n, r, T, 𝒜, P, f) ⇒ " +
				"        L(localize_section(n, r, D, f)) = " +
				"        localize_section(n, t, D, section_matrix_action(r, t, B, f))) ∧ " +
				"    (∀f:(A → num → complex). " +
				"        smooth_projected_section(n, t, T, 𝒜, Q, f) ⇒ " +
				"        R(localize_section(n, t, D, f)) = " +
				"        localize_section(n, r, D, section_matrix_action(t, r, C, f))) ∧ " +
				"    (∀u:(prod(num, prod(num, num → int)) → complex). " +
				"        u ∈ (section_sobolev_module(n, r, T, 𝒜, P, D, s)).carrier ⇒ R(L(u)) = u) ∧ " +
				"    (∀u:(prod(num, prod(num, num → int)) → complex). " +
				"        u ∈ (section_sobolev_module(n, t, T, 𝒜, Q, D, s)).carrier ⇒ L(R(u)) = u)",
		},
		"Each finite matrix entry acts as a smooth local multiplier. The pointwise "+
			"inverse identities extend by density, so different projection presentations "+
			"of an identified bundle give boundedly isomorphic Sobolev spaces."),
})}

var ComponentFourierDense = componentFourierDenseThm{family.Add(registry.ProofEntry{
	Name: "ComponentFourierDense",
	Key:  "prop_fc0da54932cb016e",
	Deps: []registry.EntryLike{sequence_hilbert.FiniteSupportDense, FiniteRankSequenceNorm},
	Build: family.Card(
		Statement{
			Binders:    "∀n r:num. ∀s:int. ∀u:(prod(num, prod(num, num → int)) → complex). ∀ε:real.",
			Hypotheses: []string{"&0 < ε", "u ∈ (localization_sequence_module(n, r, 1, s)).carrier"},
			Conclusion: "∃f:((num → real) → num → complex). " +
				"    torus_component_smooth(n, r, f) ∧ " +
				"    localization_sequence_norm(n, " +
				"        r, " +
				"        1, " +
				"        s, " +
				"        λz:prod(num, prod(num, num → int)). u(z) - torus_component_code(n, r, f, z)) < " +
				"    ε",
		},
		"Truncate the finitely many component sequences and synthesize their finite "+
			"Fourier series; the finite-component norm identity combines the errors."),
})}

var SectionChartExtension = sectionChartExtensionThm{family.Add(registry.ProofEntry{
	Name: "SectionChartExtension",
	Reading: "The source contains arbitrary local vector-valued Sobolev sequences, " +
		"including negative orders. The extension is fixed by its action on dense smooth " +
		"data; compact chart support makes the cutoff and zero extension compatible.",
	Key: "prop_3b59e2838c68dc0b",
	Deps: []registry.EntryLike{
		torus_sobolev.LocalPullback,
		torus_sobolev.SmoothMultiplier,
		ComponentFourierDense,
		SectionHilbert,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀s:int. " +
				"∀c:prod(set(A), A → num → real). " +
				"∀χ:(A → real).",
			Hypotheses: []string{
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
				"compatible_chart⟨n⟩(T, 𝒜, c)",
				"image(snd(c), fst(c)) ⊆ torus_small_box(n)",
				"smooth_manifold_function⟨n⟩(T, 𝒜, χ)",
				"compact_in(T, function_support(T, &0, χ))",
				"function_support(T, &0, χ) ⊆ fst(c)",
			},
			Conclusion: "bounded_operator(localization_sequence_module(n, r, 1, s), " +
				"    localization_sequence_norm(n, r, 1, s), " +
				"    section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
				"    localization_sequence_norm(n, r, D.count, s), " +
				"    section_chart_extension(n, r, T, 𝒜, P, D, s, c, χ)) ∧ " +
				"(∀f:((num → real) → num → complex). " +
				"    torus_component_smooth(n, r, f) ⇒ " +
				"    section_chart_extension(n, r, T, 𝒜, P, D, s, c, χ)(torus_component_code(n, r, f)) = " +
				"    localize_section(n, r, D, chart_extension_seed(r, P, c, χ, f)))",
		},
		"Cut off and project a smooth local vector function, then extend it by zero in the "+
			"chart. Finite overlap pullback and smooth matrix-multiplier bounds give a bound at "+
			"every integer order, so density extends the map to arbitrary local Sobolev data."),
})}

var SectionChartRestriction = sectionChartRestrictionThm{family.Add(registry.ProofEntry{
	Name: "SectionChartRestriction",
	Key:  "prop_848e3891b9a2efbc",
	Deps: []registry.EntryLike{
		torus_sobolev.LocalPullback,
		torus_sobolev.SmoothMultiplier,
		SectionSmoothDense,
		sequence_hilbert.WeightedHilbert,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀s:int. " +
				"∀c:prod(set(A), A → num → real). " +
				"∀χ:(A → real).",
			Hypotheses: []string{
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
				"compatible_chart⟨n⟩(T, 𝒜, c)",
				"image(snd(c), fst(c)) ⊆ torus_small_box(n)",
				"smooth_manifold_function⟨n⟩(T, 𝒜, χ)",
				"compact_in(T, function_support(T, &0, χ))",
				"function_support(T, &0, χ) ⊆ fst(c)",
			},
			Conclusion: "bounded_operator(section_sobolev_module(n, r, T, 𝒜, P, D, s), " +
				"    localization_sequence_norm(n, r, D.count, s), " +
				"    localization_sequence_module(n, r, 1, s), " +
				"    localization_sequence_norm(n, r, 1, s), " +
				"    section_chart_restriction(n, r, T, 𝒜, P, D, s, c, χ)) ∧ " +
				"(∀f:(A → num → complex). " +
				"    smooth_projected_section(n, r, T, 𝒜, P, f) ⇒ " +
				"    section_chart_restriction(n, r, T, 𝒜, P, D, s, c, χ)(localize_section(n, r, D, f)) = " +
				"    localize_section(n, r, sobolev_localization_data(1, λi:num. c, λi:num. χ), f))",
		},
		"Insert the global partition into the cutoff chart expression and bound each overlap "+
			"pullback. Extend the resulting local Fourier data from the dense smooth global sections."),
})}

var SectionCoordinateOrderCompatible = sectionCoordinateOrderCompatibleThm{family.Add(registry.ProofEntry{
	Name: "SectionCoordinateOrderCompatible",
	Key:  "prop_f799c84d58653b3d",
	Deps: []registry.EntryLike{
		SectionCoordinateIsomorphism,
		SectionOrderInclusion,
		SectionSmoothDense,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. " +
				"∀T:set(set(A)). " +
				"∀𝒜:set(prod(set(A), A → num → real)). " +
				"∀P:(A → num → num → complex). " +
				"∀D:sobolev_localization(A). " +
				"∀s:int. " +
				"∀E:sobolev_localization(A). " +
				"∀t:int. " +
				"∀u:(prod(num, prod(num, num → int)) → complex).",
			Hypotheses: []string{
				"smooth_projection_bundle(n, r, T, 𝒜, P)",
				"sobolev_localization_on(n, T, 𝒜, D)",
				"sobolev_localization_on(n, T, 𝒜, E)",
				"s ≤ t",
				"u ∈ (section_sobolev_module(n, r, T, 𝒜, P, D, t)).carrier",
			},
			Conclusion: "section_coordinate_change(n, r, T, 𝒜, P, D, E, s, u) = " +
				"section_coordinate_change(n, r, T, 𝒜, P, D, E, t, u)",
		},
		"Both coordinate changes agree on the common dense smooth "+
			"subspace and are continuous into the weaker target order."),
})}
