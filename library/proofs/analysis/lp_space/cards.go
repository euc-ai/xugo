package lp_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_homomorphism"
	"github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	"github.com/euc-ai/xugo/library/proofs/measure/almost_everywhere_function"
	"github.com/euc-ai/xugo/library/proofs/measure/complex_measure_integral"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/measure/measure_space"
	"github.com/euc-ai/xugo/library/proofs/measure/nonneg_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_convex"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/registry"
)

var LpSeminorm = lpSeminormThm{family.Add(registry.ProofEntry{
	Name: "LpSeminorm",
	Reading: "1 ≤ p is load-bearing: at p = 0 the zero function " +
		"has seminorm one, and Minkowski fails for 0 < p < 1.",
	Deps: []registry.EntryLike{
		LpHolder,
		real_convex.Young,
		nonneg_integral.IntegralZeroIffAE,
		almost_everywhere_function.MeasurableFunctionModule,
	},
	Key: "prop_2867f2f66aac9467",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p:real.",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "&1 ≤ p"},
		Conclusion: "submodule(complex_ring, " +
			"    measurable_function_module(Ω, S), " +
			"    lp_functions(Ω, S, μ, p)) ∧ " +
			"complex_seminorm(lp_function_module(Ω, S, μ, p), lp_seminorm(Ω, S, μ, p)) ∧ " +
			"seminorm_kernel(lp_function_module(Ω, S, μ, p), lp_seminorm(Ω, S, μ, p)) = " +
			"null_functions(Ω, S, μ)",
	},
		"Integrate Young’s inequality to obtain Hölder and Minkowski, treating p=1 "+
			"directly by the triangle inequality. The zero-integral criterion identifies the "+
			"kernel, and every measurable null function belongs to each p-integrable carrier."),
})}

var FastCauchyLimit = fastCauchyLimitThm{family.Add(registry.ProofEntry{
	Name: "FastCauchyLimit",
	Deps: []registry.EntryLike{
		LpSeminorm,
		nonneg_integral.Markov,
		nonneg_integral.SubSigmaIntegral,
		integral_convergence.FatouAE,
		measure_space.AECountable,
	},
	Key: "prop_e53a992d9784e540",
	Reading: "The limit is genuinely G-measurable, even when G is incomplete. It is " +
		"constructed on a G-measurable convergence set and is zero on its G-measurable " +
		"complement. The limit is G-measurable without completeness because it is set to " +
		"zero on the G-measurable divergence set. Almost everywhere here is with respect to S.",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀p:real. " +
			"∀G:set(set(A)). " +
			"∀f:(num → A → complex).",
		Hypotheses: []string{
			"measure_on(Ω, S, μ)",
			"&1 ≤ p",
			"sigma_algebra_on(Ω, G)",
			"G ⊆ S",
			"∀n:num. f(n) ∈ lp_functions(Ω, S, μ, p) ∧ complex_measurable(Ω, G, f(n))",
			"metric_cauchy(lp_function_module(Ω, S, μ, p).carrier, " +
				"    norm_distance(lp_function_module(Ω, S, μ, p), lp_seminorm(Ω, S, μ, p)), " +
				"    f)",
		},
		Conclusion: "∃g:(A → complex). ∃σ:(num → num). " +
			"    g ∈ lp_functions(Ω, S, μ, p) ∧ " +
			"    complex_measurable(Ω, G, g) ∧ " +
			"    (∀n:num. σ(n) < σ(n + 1)) ∧ " +
			"    measure_ae(Ω, S, μ, λx:A. real_converges_to(λn:num. |f(σ(n), x) - g(x)|, &0)) ∧ " +
			"    real_converges_to(λn:num. lp_seminorm(Ω, S, μ, p, λx:A. f(n, x) - g(x)), &0)",
	},
		"Choose a subsequence whose successive p-seminorm differences are summable. Minkowski "+
			"and Fatou make the sum of their absolute differences finite a.e.; its convergence set "+
			"is G-measurable, so set the limit to zero on the remaining G-null set and outside Ω. "+
			"Fatou bounds the p-distance tails, and the Cauchy condition recovers the whole sequence."),
})}

var LpBanach = lpBanachThm{family.Add(registry.ProofEntry{
	Name: "LpBanach",
	Deps: []registry.EntryLike{LpSeminorm, FastCauchyLimit, hilbert_space.SeminormQuotientComplete},
	Key:  "prop_9bea7e5cf033a979",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p:real.",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "&1 ≤ p"},
		Conclusion: "complex_banach_space(lp_module(Ω, S, μ, p), lp_norm(Ω, S, μ, p)) ∧ " +
			"lp_module(Ω, S, μ, p).carrier ⊆ ae_module(Ω, S, μ).carrier",
	},
		"Combine the function-layer seminorm and Cauchy-limit theorems with SeminormQuotientComplete. "+
			"The quotient uses exactly the ambient null submodule, so its cosets are L0 cosets."),
})}

var LpNormClass = lpNormClassThm{family.Add(registry.ProofEntry{
	Name: "LpNormClass",
	Deps: []registry.EntryLike{
		LpSeminorm,
		hilbert_space.SeminormQuotientNormed,
		equivalence.InducedMapClass,
	},
	Key: "prop_30b3317826c998ff",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀p:real. " +
			"∀f:(A → complex).",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "&1 ≤ p", "f ∈ lp_functions(Ω, S, μ, p)"},
		Conclusion: "ae_class(Ω, S, μ, f) ∈ lp_module(Ω, S, μ, p).carrier ∧ " +
			"lp_norm(Ω, S, μ, p, ae_class(Ω, S, μ, f)) = lp_seminorm(Ω, S, μ, p, f)",
	},
		"The representative is already zero off the carrier. Evaluate the "+
			"induced seminorm on its coset using the quotient-norm theorem."),
})}

var LpMeasurableClosed = lpMeasurableClosedThm{family.Add(registry.ProofEntry{
	Name: "LpMeasurableClosed",
	Deps: []registry.EntryLike{
		FastCauchyLimit,
		LpBanach,
		almost_everywhere_function.SubSigmaClassEmbedding,
		complete_metric.ClosedIffSequential,
		LpMeasurableRepresentative,
	},
	Key: "prop_e53243ca49441211",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀p:real. " +
			"∀G:set(set(A)).",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "&1 ≤ p", "sigma_algebra_on(Ω, G)", "G ⊆ S"},
		Conclusion: "submodule(complex_ring, " +
			"    lp_module(Ω, S, μ, p), " +
			"    lp_measurable_subspace(Ω, S, μ, G, p)) ∧ " +
			"closed_in(norm_topology(lp_module(Ω, S, μ, p), lp_norm(Ω, S, μ, p)), " +
			"    lp_measurable_subspace(Ω, S, μ, G, p))",
	},
		"Quotient inclusion gives linearity. For sequential closedness choose "+
			"G-measurable representatives and apply FastCauchyLimit with that "+
			"same G; uniqueness of a metric limit identifies the ambient limit."),
})}

var LpMeasurableRepresentative = lpMeasurableRepresentativeThm{family.Add(registry.ProofEntry{
	Name: "LpMeasurableRepresentative",
	Reading: "lp_functions(Ω, G, μ, p) reads the G-lower integral, which " +
		"equals the S-integral only for G-measurable integrands (SubSigmaIntegral).",
	Deps: []registry.EntryLike{
		almost_everywhere_function.SubSigmaClassEmbedding,
		nonneg_integral.SubSigmaIntegral,
	},
	Key: "prop_102ad029ecbd4fb7",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀p:real. " +
			"∀G:set(set(A)). " +
			"∀Q:set(A → complex).",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "&1 ≤ p", "sigma_algebra_on(Ω, G)", "G ⊆ S"},
		Conclusion: "Q ∈ lp_measurable_subspace(Ω, S, μ, G, p) ⇔ " +
			"∃f:(A → complex). " +
			"    f ∈ lp_functions(Ω, S, μ, p) ∧ complex_measurable(Ω, G, f) ∧ Q = ae_class(Ω, S, μ, f)",
	},
		"Read the quotient inclusion on a G-measurable coset. Sub-sigma "+
			"integral invariance identifies p-integrability in G and S."),
})}

var IntegralOnClasses = integralOnClassesThm{family.Add(registry.ProofEntry{
	Name: "IntegralOnClasses",
	Deps: []registry.EntryLike{
		complex_measure_integral.ComplexIntegralLinear,
		complex_measure_integral.ComplexIntegralAE,
		complex_measure_integral.ComplexIntegralBound,
		module_homomorphism.InducedMapHom,
		LpSeminorm,
	},
	Key: "prop_e63666936129d1fb",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real).",
		Hypotheses: []string{"measure_on(Ω, S, μ)"},
		Conclusion: "module_homomorphism(complex_ring, " +
			"    lp_module(Ω, S, μ, &1), " +
			"    regular_module(complex_ring), " +
			"    lp_integral(Ω, S, μ)) ∧ " +
			"(∀f:(A → complex). " +
			"    f ∈ lp_functions(Ω, S, μ, &1) ⇒ " +
			"    lp_integral(Ω, S, μ, ae_class(Ω, S, μ, f)) = complex_measure_integral(Ω, S, μ, f)) ∧ " +
			"(∀Q:set(A → complex). " +
			"    Q ∈ lp_module(Ω, S, μ, &1).carrier ⇒ |lp_integral(Ω, S, μ, Q)| ≤ lp_norm(Ω, S, μ, &1, Q))",
	},
		"Complex integral linearity makes a homomorphism on the integrable function module. It kills "+
			"null functions, so InducedMapHom descends it and the integral modulus bound descends as well."),
})}

var SimpleDenseInLp = simpleDenseInLpThm{family.Add(registry.ProofEntry{
	Name: "SimpleDenseInLp",
	Deps: []registry.EntryLike{integral_convergence.DominatedConvergenceAE},
	Key:  "prop_d66f9dac05ab8119",
	Build: family.Card(Statement{
		Binders: "∀Ω:set(A). " +
			"∀S:set(set(A)). " +
			"∀μ:(set(A) → extended_nonneg_real). " +
			"∀p:real. " +
			"∀f:(A → complex). " +
			"∀ε:real.",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "&1 ≤ p", "f ∈ lp_functions(Ω, S, μ, p)", "&0 < ε"},
		Conclusion: "∃s:(A → complex). " +
			"    s ∈ lp_functions(Ω, S, μ, p) ∧ " +
			"    finite(image(s, Ω)) ∧ " +
			"    lp_seminorm(Ω, S, μ, p, λx:A. f(x) - s(x)) < ε",
	},
		"Truncate the function and discretize its real and imaginary parts, choosing "+
			"finite-measure support from integrability when the ambient measure is "+
			"infinite. Dominated convergence of the pth-power errors gives the estimate."),
})}

var LpNested = lpNestedThm{family.Add(registry.ProofEntry{
	Name: "LpNested",
	Reading: "Finiteness of μ is needed for the inclusion and for the bound, since " +
		"extended_to_real reads infinity as zero. At p = q the factor is one even when μ(Ω) = 0.",
	Deps: []registry.EntryLike{LpHolder, LpNormClass},
	Key:  "prop_44eb9c852296bf4e",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p q:real.",
		Hypotheses: []string{"finite_measure_on(Ω, S, μ)", "&1 ≤ p", "p ≤ q"},
		Conclusion: "lp_module(Ω, S, μ, q).carrier ⊆ lp_module(Ω, S, μ, p).carrier ∧ " +
			"(∀Q:set(A → complex). " +
			"    Q ∈ lp_module(Ω, S, μ, q).carrier ⇒ " +
			"    lp_norm(Ω, S, μ, p, Q) ≤ " +
			"    real_rpow(extended_to_real(μ(Ω)), real_inv(p) - real_inv(q)) * lp_norm(Ω, S, μ, q, Q))",
	},
		"For p<q apply Hölder to |f|^p and the indicator of Ω (the constant one is not "+
			"in lp_functions unless Ω = 𝕌), with exponents q/p and q/(q−p). Handle p=q and "+
			"zero total mass separately, then read the same cosets in both quotient carriers."),
})}

var LInfinitySeminorm = lInfinitySeminormThm{family.Add(registry.ProofEntry{
	Name: "LInfinitySeminorm",
	Reading: "When μ(Ω) = 0 or Ω = ∅, every function has " +
		"essential supremum zero and L-infinity is the zero space.",
	Deps: []registry.EntryLike{
		measure_space.AECountable,
		almost_everywhere_function.MeasurableFunctionModule,
	},
	Key: "prop_4c717f6f9726d65e",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real).",
		Hypotheses: []string{"measure_on(Ω, S, μ)"},
		Conclusion: "complex_seminorm(linfinity_function_module(Ω, S, μ), " +
			"    λf:(A → complex). extended_to_real(essential_sup(Ω, S, μ, f))) ∧ " +
			"seminorm_kernel(linfinity_function_module(Ω, S, μ), " +
			"    λf:(A → complex). extended_to_real(essential_sup(Ω, S, μ, f))) = " +
			"null_functions(Ω, S, μ) ∧ " +
			"(∀f:(num → A → complex). " +
			"    metric_cauchy(linfinity_function_module(Ω, S, μ).carrier, " +
			"        norm_distance(linfinity_function_module(Ω, S, μ), " +
			"            λg:(A → complex). extended_to_real(essential_sup(Ω, S, μ, g))), " +
			"        f) ⇒ " +
			"    ∃g:(A → complex). " +
			"        g ∈ linfinity_functions(Ω, S, μ) ∧ " +
			"        real_converges_to( " +
			"            λn:num. extended_to_real(essential_sup(Ω, S, μ, λx:A. f(n, x) - g(x))), &0))",
	},
		"Essential bounds give the seminorm laws and identify its null kernel. Combine "+
			"countably many null exceptions for a rapidly Cauchy subsequence, take its uniform "+
			"limit off that measurable null set, and recover convergence of the full sequence."),
})}

var LInfinityBanach = lInfinityBanachThm{family.Add(registry.ProofEntry{
	Name: "LInfinityBanach",
	Deps: []registry.EntryLike{LInfinitySeminorm, hilbert_space.SeminormQuotientComplete},
	Key:  "prop_ca850cbc5b296410",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real).",
		Hypotheses: []string{"measure_on(Ω, S, μ)"},
		Conclusion: "complex_banach_space(linfinity_module(Ω, S, μ), linfinity_norm(Ω, S, μ)) ∧ " +
			"linfinity_module(Ω, S, μ).carrier ⊆ ae_module(Ω, S, μ).carrier",
	},
		"Apply the universal seminorm quotient completeness theorem to the "+
			"essential-supremum seminorm and its function-layer completeness."),
})}

var LInfinityToLp = lInfinityToLpThm{family.Add(registry.ProofEntry{
	Name:    "LInfinityToLp",
	Reading: "Finiteness of μ is load-bearing, since extended_to_real reads infinity as zero.",
	Deps:    []registry.EntryLike{LInfinitySeminorm, LpNormClass},
	Key:     "prop_d7d348a530bc0669",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p:real.",
		Hypotheses: []string{"finite_measure_on(Ω, S, μ)", "&1 ≤ p"},
		Conclusion: "linfinity_module(Ω, S, μ).carrier ⊆ lp_module(Ω, S, μ, p).carrier ∧ " +
			"(∀Q:set(A → complex). " +
			"    Q ∈ linfinity_module(Ω, S, μ).carrier ⇒ " +
			"    lp_norm(Ω, S, μ, p, Q) ≤ " +
			"    real_rpow(extended_to_real(μ(Ω)), real_inv(p)) * linfinity_norm(Ω, S, μ, Q))",
	},
		"Integrate the pth power of an essential bound and take pth roots. Approach "+
			"the essential supremum by finite bounds and include the zero-mass case."),
})}

var LpRealSubmodule = lpRealSubmoduleThm{family.Add(registry.ProofEntry{
	Name: "LpRealSubmodule",
	Deps: []registry.EntryLike{hom_module.RestrictScalarsModuleOn, LpSeminorm},
	Key:  "prop_f4c9f97bb5666b84",
	Build: family.Card(Statement{
		Binders:    "∀Ω:set(A). ∀S:set(set(A)). ∀μ:(set(A) → extended_nonneg_real). ∀p:real.",
		Hypotheses: []string{"measure_on(Ω, S, μ)", "&1 ≤ p"},
		Conclusion: "module_on(real_ring, lp_real_module(Ω, S, μ, p))",
	},
		"Real representatives are preserved by addition and real scalar multiplication. "+
			"Restrict scalars along complex_of_real and take the corresponding real submodule."),
})}
