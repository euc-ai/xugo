package torus_sobolev

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/analysis/bounded_operator"
	"github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	"github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	"github.com/euc-ai/xugo/library/proofs/analysis/torus_fourier"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var PeetreInequality = peetreInequalityThm{family.Add(registry.ProofEntry{
	Name: "PeetreInequality",
	Key:  "prop_2c2fa9563af015b8",
	Reading: "The order s is any integer; the constant and the order on the second factor " +
		"use |s|, so the estimate moves a weight across a convolution in either direction.",
	Build: family.Card(
		"∀n:num. ∀s:int. ∀k l:(num → int). "+
			"    sobolev_weight(n, s, λj:num. k(j) + l(j)) ≤ "+
			"    real_zpow(&2, int_abs(s)) * sobolev_weight(n, int_abs(s), k) * sobolev_weight(n, s, l)",
		"For s ≥ 0 raise 1 + |k + l|² ≤ 1 + 2|k|² + 2|l|² ≤ 2(1 + |k|²)(1 + |l|²) to the power s. "+
			"For s < 0 apply the same inequality to l = (k + l) + (−k), which has |−k| = |k|, and invert."),
})}

var SobolevHilbert = sobolevHilbertThm{family.Add(registry.ProofEntry{
	Name: "SobolevHilbert",
	Key:  "prop_7ab6f7184e107b63",
	Deps: []registry.EntryLike{sequence_hilbert.WeightedHilbert},
	Build: family.Card(
		"∀n:num. ∀s:int. complex_hilbert_space(sobolev_module(n, s), sobolev_inner(n, s))",
		"The Sobolev weight is strictly positive at every active "+
			"frequency, so weighted-sequence completeness applies."),
})}

var SobolevInclusion = sobolevInclusionThm{family.Add(registry.ProofEntry{
	Name: "SobolevInclusion",
	Key:  "prop_90f254299a559c6d",
	Deps: []registry.EntryLike{sequence_hilbert.NormSquaredFiniteSup, SobolevHilbert},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀s t:int.",
			Hypotheses: []string{"s ≤ t"},
			Conclusion: "bounded_operator(sobolev_module(n, t), " +
				"    sobolev_norm(n, t), " +
				"    sobolev_module(n, s), " +
				"    sobolev_norm(n, s), " +
				"    λu:((num → int) → complex). u) ∧ " +
				"(∀u:((num → int) → complex). " +
				"    u ∈ (sobolev_module(n, t)).carrier ⇒ sobolev_norm(n, s, u) ≤ sobolev_norm(n, t, u))",
		},
		"The base of every weight is at least one, so lowering "+
			"the exponent decreases every finite squared subsum."),
})}

var FrequencyProjectionFiniteRank = frequencyProjectionFiniteRankThm{family.Add(registry.ProofEntry{
	Name: "FrequencyProjectionFiniteRank",
	Key:  "prop_cdfa99c642d991dd",
	Deps: []registry.EntryLike{
		torus_fourier.FrequencyBlocksFinite,
		SobolevHilbert,
		sequence_hilbert.NormSquaredFiniteSup,
		module_dimension.FiniteDimensionalSpanning,
	},
	Build: family.Card(
		"∀n:num. ∀s t:int. ∀R:real. "+
			"    bounded_operator(sobolev_module(n, t), "+
			"        sobolev_norm(n, t), "+
			"        sobolev_module(n, s), "+
			"        sobolev_norm(n, s), "+
			"        sequence_truncate(fourier_block(n, R))) ∧ "+
			"    finite_rank_operator(sobolev_module(n, t), "+
			"        sobolev_module(n, s), "+
			"        sequence_truncate(fourier_block(n, R)))",
		"A finite frequency block has a finite coordinate basis, "+
			"and each of its weighted coordinate evaluations is bounded."),
})}

var RellichTailEstimate = rellichTailEstimateThm{family.Add(registry.ProofEntry{
	Name: "RellichTailEstimate",
	Key:  "prop_6614a4c48c6357cf",
	Deps: []registry.EntryLike{sequence_hilbert.NormSquaredFiniteSup},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀s t:int. ∀R:real. ∀u:((num → int) → complex).",
			Hypotheses: []string{"s < t", "&0 ≤ R", "u ∈ (sobolev_module(n, t)).carrier"},
			Conclusion: "real_pow( " +
				"    sobolev_norm(n, s, λk:(num → int). u(k) - sequence_truncate(fourier_block(n, R), u, k)), " +
				"    2) ≤ " +
				"real_zpow(&1 + real_pow(R, 2), s - t) * real_pow(sobolev_norm(n, t, u), 2)",
		},
		"Outside the retained block, the ratio of the two squared weights is "+
			"bounded by the displayed negative power; take suprema of finite subsums."),
})}

var Rellich = rellichThm{family.Add(registry.ProofEntry{
	Name: "Rellich",
	Key:  "prop_2a5e7e419aa5f6a9",
	Deps: []registry.EntryLike{
		FrequencyProjectionFiniteRank,
		RellichTailEstimate,
		SobolevHilbert,
		bounded_operator.FiniteRankCompact,
		bounded_operator.CompactNormLimit,
		SobolevInclusion,
		hilbert_space.InnerProductNorm,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀s t:int.",
			Hypotheses: []string{"s < t"},
			Conclusion: "compact_operator(sobolev_module(n, t), " +
				"    sobolev_norm(n, t), " +
				"    sobolev_module(n, s), " +
				"    sobolev_norm(n, s), " +
				"    λu:((num → int) → complex). u)",
		},
		"The finite-frequency projections converge to the "+
			"inclusion in operator norm by the tail estimate."),
})}

var RapidIffAllSobolev = rapidIffAllSobolevThm{family.Add(registry.ProofEntry{
	Name: "RapidIffAllSobolev",
	Key:  "prop_ed98fc332611e834",
	Deps: []registry.EntryLike{torus_fourier.LatticeSummable, sequence_hilbert.NormSquaredFiniteSup},
	Build: family.Card(
		"∀n:num. ∀u:((num → int) → complex). "+
			"    rapid_sequence(n, u) ⇔ ∀s:int. u ∈ (sobolev_module(n, s)).carrier",
		"Rapid decay and lattice counting give every weighted square sum; a single "+
			"coordinate is bounded by each Sobolev norm, giving every rapid-decay bound."),
})}

var SmoothDense = smoothDenseThm{family.Add(registry.ProofEntry{
	Name: "SmoothDense",
	Key:  "prop_92e6d5737bffbaed",
	Deps: []registry.EntryLike{sequence_hilbert.FiniteSupportDense, torus_fourier.RapidSynthesis},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀s:int. ∀u:((num → int) → complex). ∀ε:real.",
			Hypotheses: []string{"&0 < ε", "u ∈ (sobolev_module(n, s)).carrier"},
			Conclusion: "∃f:((num → real) → complex). " +
				"    torus_smooth(n, f) ∧ " +
				"    sobolev_norm(n, s, λk:(num → int). u(k) - torus_coefficients(n, f, k)) < ε",
		},
		"Finite-support sequences are dense and synthesize to trigonometric polynomials."),
})}

var SobolevEmbedding = sobolevEmbeddingThm{family.Add(registry.ProofEntry{
	Name: "SobolevEmbedding",
	Reading: "The strict inequality is s > n/2 + r. One finite order " +
		"supplies C^r regularity, not smoothness; smooth realization requires " +
		"membership in all integer orders. Dimension zero is included.",
	Key: "prop_1390c232e90355f4",
	Deps: []registry.EntryLike{
		torus_fourier.SummableSynthesis,
		torus_fourier.LatticeSummable,
		sequence_hilbert.NormSquaredFiniteSup,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. ∀s:int. ∀u:((num → int) → complex).",
			Hypotheses: []string{
				"int_of_num(n + 2 * r) < int_of_num(2) * s",
				"u ∈ (sobolev_module(n, s)).carrier",
			},
			Conclusion: "torus_class(n, r, torus_synthesis(n, u)) ∧ " +
				"torus_coefficients(n, torus_synthesis(n, u)) = u",
		},
		"Weighted Cauchy–Schwarz and summability beyond half the "+
			"dimension give uniform convergence through r derivatives."),
})}

var SmoothIffAllOrders = smoothIffAllOrdersThm{family.Add(registry.ProofEntry{
	Name: "SmoothIffAllOrders",
	Key:  "prop_9c72a52226429379",
	Deps: []registry.EntryLike{
		RapidIffAllSobolev,
		torus_fourier.RapidSynthesis,
		torus_fourier.SmoothCoefficientsRapid,
	},
	Build: family.Card(
		"∀n:num. ∀u:((num → int) → complex). "+
			"    (∀s:int. u ∈ (sobolev_module(n, s)).carrier) ⇔ "+
			"    ∃f:((num → real) → complex). torus_smooth(n, f) ∧ torus_coefficients(n, f) = u",
		"Use the rapid-sequence characterization and the smooth Fourier bijection."),
})}

var SmoothMultiplier = smoothMultiplierThm{family.Add(registry.ProofEntry{
	Name: "SmoothMultiplier",
	Key:  "prop_d38578756b22c1a6",
	Deps: []registry.EntryLike{
		torus_fourier.SmoothCoefficientsRapid,
		PeetreInequality,
		SobolevHilbert,
		torus_fourier.LatticeSummable,
		sequence_hilbert.NormSquaredFiniteSup,
		sequence_hilbert.SumAbsolute,
		sequence_hilbert.SumLinear,
		sequence_hilbert.SumIterated,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀s:int. ∀a:((num → real) → complex).",
			Hypotheses: []string{"torus_smooth(n, a)"},
			Conclusion: "bounded_operator(sobolev_module(n, s), " +
				"    sobolev_norm(n, s), " +
				"    sobolev_module(n, s), " +
				"    sobolev_norm(n, s), " +
				"    sobolev_multiply(n, a)) ∧ " +
				"bounded_op_norm(sobolev_module(n, s), " +
				"    sobolev_norm(n, s), " +
				"    sobolev_norm(n, s), " +
				"    sobolev_multiply(n, a)) ≤ " +
				"sobolev_multiplier_bound(n, s, a)",
		},
		"A polynomial weight inequality and the weighted ℓ¹ norm of the rapidly decreasing "+
			"coefficient sequence give the convolution bound, for positive and negative integer orders."),
})}

var MultiplierRealization = multiplierRealizationThm{family.Add(registry.ProofEntry{
	Name: "MultiplierRealization",
	Key:  "prop_288360aea18fd543",
	Deps: []registry.EntryLike{
		torus_fourier.SmoothFourierInversion,
		PeetreInequality,
		torus_fourier.SmoothCoefficientsRapid,
		torus_fourier.RapidSynthesis,
		torus_fourier.LatticeSummable,
		sequence_hilbert.SumIterated,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀a f:((num → real) → complex).",
			Hypotheses: []string{"torus_smooth(n, a)", "torus_smooth(n, f)"},
			Conclusion: "sobolev_multiply(n, a, torus_coefficients(n, f)) = " +
				"torus_coefficients(n, λx:(num → real). a(x) * f(x))",
		},
		"Multiply the absolutely convergent Fourier series, "+
			"regroup by total frequency and use uniqueness."),
})}

var DerivativeOrder = derivativeOrderThm{family.Add(registry.ProofEntry{
	Name: "DerivativeOrder",
	Key:  "prop_71b74d69a6629833",
	Deps: []registry.EntryLike{SobolevHilbert, sequence_hilbert.NormSquaredFiniteSup},
	Build: family.Card(
		Statement{
			Binders:    "∀n j:num. ∀s:int.",
			Hypotheses: []string{"j < n"},
			Conclusion: "bounded_operator(sobolev_module(n, s), " +
				"    sobolev_norm(n, s), " +
				"    sobolev_module(n, s - int_of_num(1)), " +
				"    sobolev_norm(n, s - int_of_num(1)), " +
				"    frequency_derivative(n, j)) ∧ " +
				"(∀u:((num → int) → complex). " +
				"    u ∈ (sobolev_module(n, s)).carrier ⇒ " +
				"    sobolev_norm(n, s - int_of_num(1), frequency_derivative(n, j, u)) ≤ sobolev_norm(n, s, u))",
		},
		"The square of each coordinate frequency is at most one plus the squared frequency length."),
})}

var LocalPullback = localPullbackThm{family.Add(registry.ProofEntry{
	Name: "LocalPullback",
	Reading: "The cutoff has compact support strictly inside the source coordinate domain, and " +
		"both domains lie in a half-period box. Bounds on derivatives and inverse Jacobian are needed " +
		"only near that compact support; no uniform bound over an arbitrary open domain is assumed.",
	Key: "prop_17d96d2689e2cd95",
	Deps: []registry.EntryLike{
		SmoothDense,
		SmoothMultiplier,
		SobolevHilbert,
		PeriodizedZeroExtensionSmooth,
		RapidIffAllSobolev,
		torus_fourier.SmoothFourierInversion,
		torus_fourier.SmoothCoefficientsRapid,
		torus_fourier.SmoothParseval,
		torus_fourier.CoefficientDerivative,
		bounded_operator.BoundedExtension,
		hilbert_space.InnerProductNorm,
		vec_smooth.SmoothMul,
		vec_smooth.SmoothCompose,
		vec_smooth.PartialDerivativeChain,
		vec_integral.ChangeOfVariables,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀s:int. " +
				"∀U V:set(num → real). " +
				"∀φ:((num → real) → num → real). " +
				"∀χ:((num → real) → real).",
			Hypotheses: []string{
				"U ∈ euclidean_topology(n)",
				"V ∈ euclidean_topology(n)",
				"U ⊆ torus_small_box(n)",
				"V ⊆ torus_small_box(n)",
				"vec_diffeomorphic_map⟨n⟩(U, V, φ)",
				"vec_smooth_on⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, χ)",
				"compact_in(euclidean_topology(n), function_support(euclidean_topology(n), &0, χ))",
				"function_support(euclidean_topology(n), &0, χ) ⊆ U",
			},
			Conclusion: "bounded_operator(sobolev_module(n, s), " +
				"    sobolev_norm(n, s), " +
				"    sobolev_module(n, s), " +
				"    sobolev_norm(n, s), " +
				"    sobolev_local_pullback(n, s, U, φ, χ)) ∧ " +
				"(∀f:((num → real) → complex). " +
				"    torus_smooth(n, f) ⇒ " +
				"    sobolev_local_pullback(n, s, U, φ, χ, torus_coefficients(n, f)) = " +
				"    torus_coefficients(n, local_pullback_seed(n, U, φ, χ, f)))",
		},
		"For nonnegative orders use the chain rule, change of variables and "+
			"compact-support bounds; for negative orders use duality, with the "+
			"inverse Jacobian density. Extend uniquely from the dense smooth subspace."),
})}

var LocalPullbackOrderCompatible = localPullbackOrderCompatibleThm{family.Add(registry.ProofEntry{
	Name: "LocalPullbackOrderCompatible",
	Key:  "prop_165d9f158c6e8ae6",
	Deps: []registry.EntryLike{
		LocalPullback,
		SmoothDense,
		SobolevInclusion,
		SobolevHilbert,
		hilbert_space.InnerProductNorm,
		bounded_operator.BoundedAgreeDense,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀s:int. " +
				"∀U V:set(num → real). " +
				"∀φ:((num → real) → num → real). " +
				"∀χ:((num → real) → real). " +
				"∀t:int. " +
				"∀u:((num → int) → complex).",
			Hypotheses: []string{
				"U ∈ euclidean_topology(n)",
				"V ∈ euclidean_topology(n)",
				"U ⊆ torus_small_box(n)",
				"V ⊆ torus_small_box(n)",
				"vec_diffeomorphic_map⟨n⟩(U, V, φ)",
				"vec_smooth_on⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, χ)",
				"compact_in(euclidean_topology(n), function_support(euclidean_topology(n), &0, χ))",
				"function_support(euclidean_topology(n), &0, χ) ⊆ U",
				"s ≤ t",
				"u ∈ (sobolev_module(n, t)).carrier",
			},
			Conclusion: "sobolev_local_pullback(n, s, U, φ, χ, u) = sobolev_local_pullback(n, t, U, φ, χ, u)",
		},
		"Both extensions agree on smooth sequences and are continuous into the weaker Sobolev space."),
})}

var DifferentialOperatorOrder = differentialOperatorOrderThm{family.Add(registry.ProofEntry{
	Name: "DifferentialOperatorOrder",
	Key:  "prop_31378facbc8fc864",
	Deps: []registry.EntryLike{
		DerivativeOrder,
		SmoothMultiplier,
		SobolevInclusion,
		SobolevHilbert,
		hilbert_space.InnerProductNorm,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n N m:num. " +
				"∀s:int. " +
				"∀r:(num → num). " +
				"∀j:(num → num → num). " +
				"∀a:(num → (num → real) → complex).",
			Hypotheses: []string{
				"∀i:num. i < N ⇒ r(i) ≤ m ∧ torus_smooth(n, a(i)) ∧ (∀l:num. l < r(i) ⇒ j(i, l) < n)",
			},
			Conclusion: "bounded_operator(sobolev_module(n, s), " +
				"    sobolev_norm(n, s), " +
				"    sobolev_module(n, s - int_of_num(m)), " +
				"    sobolev_norm(n, s - int_of_num(m)), " +
				"    sobolev_differential_operator(n, N, r, j, a))",
		},
		"Iterate the first-derivative bound, multiply by each smooth coefficient, "+
			"and sum the finitely many terms into the weakest target order."),
})}

var CutoffZeroExtension = cutoffZeroExtensionThm{family.Add(registry.ProofEntry{
	Name: "CutoffZeroExtension",
	Key:  "prop_baad92521e324ba0",
	Deps: []registry.EntryLike{
		SmoothDense,
		SmoothMultiplier,
		PeriodizedZeroExtensionSmooth,
		MultiplierRealization,
		SobolevHilbert,
		hilbert_space.InnerProductNorm,
		complete_metric.ClosureIffSequential,
		vec_smooth.SmoothMul,
		sequence_hilbert.FiniteSum,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. " +
				"∀s:int. " +
				"∀U:set(num → real). " +
				"∀χ:((num → real) → real). " +
				"∀u:((num → int) → complex).",
			Hypotheses: []string{
				"U ∈ euclidean_topology(n)",
				"U ⊆ torus_small_box(n)",
				"vec_smooth_on⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, χ)",
				"compact_in(euclidean_topology(n), function_support(euclidean_topology(n), &0, χ))",
				"function_support(euclidean_topology(n), &0, χ) ⊆ U",
				"u ∈ (sobolev_module(n, s)).carrier",
			},
			Conclusion: "sobolev_multiply(n, " +
				"    torus_periodize(n, λx:(num → real). complex_of_real(χ(x))), " +
				"    u) ∈ " +
				"local_sobolev_carrier(n, s, U)",
		},
		"Approximate u by smooth sequences, multiply by the compactly supported cutoff "+
			"and periodize the zero extensions; multiplier boundedness passes to the limit."),
})}

var PeriodizedZeroExtensionSmooth = periodizedZeroExtensionSmoothThm{family.Add(registry.ProofEntry{
	Name: "PeriodizedZeroExtensionSmooth",
	Key:  "prop_e36fce57deec8302",
	Deps: []registry.EntryLike{
		sequence_hilbert.FiniteSum,
		vec_smooth.SmoothCompose,
		vec_smooth.SmoothLocal,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. ∀U:set(num → real). ∀g:((num → real) → complex).",
			Hypotheses: []string{
				"U ∈ euclidean_topology(n)",
				"U ⊆ torus_small_box(n)",
				"vec_smooth_on⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, λx:(num → real). re(g(x)))",
				"vec_smooth_on⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, λx:(num → real). im(g(x)))",
				"compact_in(euclidean_topology(n), " +
					"    function_support(euclidean_topology(n), complex_of_real(&0), g))",
				"function_support(euclidean_topology(n), complex_of_real(&0), g) ⊆ U",
			},
			Conclusion: "torus_smooth(n, torus_periodize(n, g)) ∧ " +
				"(∀x:(num → real). x ∈ torus_small_box(n) ⇒ torus_periodize(n, g, x) = g(x))",
		},
		"The compact support leaves a collar on which the zero extension vanishes; its "+
			"periodic translates are locally finite and disjoint inside the half-period cube."),
})}
