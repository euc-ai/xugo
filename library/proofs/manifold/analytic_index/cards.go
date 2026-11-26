package analytic_index

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/analysis/fredholm"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_cotangent"
	"github.com/euc-ai/xugo/library/proofs/manifold/pseudo_differential"
	"github.com/euc-ai/xugo/library/proofs/manifold/riemannian"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_projection_bundle"
	"github.com/euc-ai/xugo/library/proofs/manifold/sobolev_section"
	"github.com/euc-ai/xugo/library/proofs/topology/k_compact_support"
	"github.com/euc-ai/xugo/library/proofs/topology/projection_bundle"
	"github.com/euc-ai/xugo/library/registry"
)

var SymbolExtensionExists = symbolExtensionExistsThm{family.Add(registry.ProofEntry{
	Name: "SymbolExtensionExists",
	Key:  "prop_c2a22848a953cfad",
	Deps: []registry.EntryLike{
		smooth_projection_bundle.SmoothBundleContinuous,
		manifold_cotangent.CotangentManifold,
		manifold_cotangent.ProjectionSmooth,
		manifold_cotangent.CoordinateReconstruction,
		manifold_cotangent.MetricIdentification,
		riemannian.CompactMetricExists,
		projection_bundle.PullbackBundle,
		smooth_manifold.FunctionContinuous,
	},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀m:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex).",
		Hypotheses: []string{"compact_in(T, ⋃T)", "ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, m, σ)"},
		Conclusion: "∃τ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"    ps_symbol_extension(n, r, q, T, 𝒜, P, Q, σ, τ) ∧ " +
			"    kc_triple(cotangent_topology(n, T, 𝒜), " +
			"        (projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"                λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"                (r, P)), " +
			"            (projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"                    λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"                    (q, Q)), " +
			"                τ)))",
	},
		"Multiply σ by a smooth cutoff on the cotangent manifold that vanishes near the zero "+
			"section and equals one off a compact K: the product equals σ off K, is smooth and "+
			"so continuous (CoordinateReconstruction, FunctionContinuous), and is invertible off "+
			"K by ellipticity. The pulled-back bundles are continuous (SmoothBundleContinuous, "+
			"ProjectionSmooth, PullbackBundle) over ⋃cotangent_topology, the cotangent bundle "+
			"(CotangentManifold). The cutoff is the filler's promotion: over a compact base a "+
			"Riemannian metric (CompactMetricExists) carried to T*M by MetricIdentification has "+
			"compact closed disk bundles, and a radial bump of its norm is the cutoff."),
})}

var SymbolExtensionIndependent = symbolExtensionIndependentThm{family.Add(registry.ProofEntry{
	Name: "SymbolExtensionIndependent",
	Key:  "prop_15e8f9fdbc5e1fb0",
	Deps: []registry.EntryLike{SymbolExtensionExists},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀m:int. " +
			"∀σ τ υ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex).",
		Hypotheses: []string{
			"compact_in(T, ⋃T)",
			"ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, m, σ)",
			"ps_symbol_extension(n, r, q, T, 𝒜, P, Q, σ, τ)",
			"ps_symbol_extension(n, r, q, T, 𝒜, P, Q, σ, υ)",
		},
		Conclusion: "kc_class(cotangent_topology(n, T, 𝒜), " +
			"    (projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"            λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"            (r, P)), " +
			"        (projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"                λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"                (q, Q)), " +
			"            τ))) = " +
			"kc_class(cotangent_topology(n, T, 𝒜), " +
			"    (projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"            λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"            (r, P)), " +
			"        (projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"                λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"                (q, Q)), " +
			"            υ))) ∧ " +
			"kc_class(cotangent_topology(n, T, 𝒜), " +
			"    (projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"            λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"            (r, P)), " +
			"        (projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"                λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"                (q, Q)), " +
			"            τ))) = " +
			"ps_symbol_class(n, r, q, T, 𝒜, P, Q, σ)",
	},
		"Both extensions agree with the homogeneous symbol outside the union of two compact "+
			"sets, so their straight-line homotopy has uniformly compact singular support."),
})}

var SymbolClassRealization = symbolClassRealizationThm{family.Add(registry.ProofEntry{
	Name: "SymbolClassRealization",
	Key:  "prop_19fe6fde3bacfa28",
	Deps: []registry.EntryLike{
		pseudo_differential.SymbolRealization,
		smooth_projection_bundle.SmoothBundleContinuous,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀a:set(prod(prod(num, " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"            prod(prod(num, " +
			"                    prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex), " +
			"                prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex))).",
		Hypotheses: []string{
			"smooth_manifold⟨n⟩(T, 𝒜)",
			"compact_in(T, ⋃T)",
			"a ∈ (kc_group(cotangent_topology(n, T, 𝒜))).carrier",
		},
		Conclusion: "∃r q:num. " +
			"∃P Q:(A → num → num → complex). " +
			"∃σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∃D:((A → num → complex) → A → num → complex). " +
			"    pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, int_of_num(0), σ, D) ∧ " +
			"    ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, int_of_num(0), σ) ∧ " +
			"    ps_symbol_class(n, r, q, T, 𝒜, P, Q, σ) = a",
	},
		"Compress the compact singular support into a disk, identify its bundles with pullbacks "+
			"from the zero section, smooth the projection and bundle-map data, and radially extend "+
			"the sphere map to a homogeneous symbol. Local quantization realizes it."),
})}

var IndexSobolevIndependent = indexSobolevIndependentThm{family.Add(registry.ProofEntry{
	Name: "IndexSobolevIndependent",
	Key:  "prop_bcaf897b301078a7",
	Deps: []registry.EntryLike{
		pseudo_differential.EllipticRegularity,
		pseudo_differential.PrincipalSymbolAdjoint,
	},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L:sobolev_localization(A). " +
			"∀m s t:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀D:((A → num → complex) → A → num → complex).",
		Hypotheses: []string{
			"pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, m, σ, D)",
			"ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, m, σ)",
			"sobolev_localization_on(n, T, 𝒜, L)",
		},
		Conclusion: "ps_operator_index(n, r, q, T, 𝒜, P, Q, L, m, s, D) = " +
			"ps_operator_index(n, r, q, T, 𝒜, P, Q, L, m, t, D)",
	},
		"Elliptic regularity identifies the kernels with the smooth kernel, "+
			"while the cokernels pair with the smooth kernel of the formal "+
			"adjoint. These finite dimensions do not depend on the Sobolev order."),
})}

var IndexLocalizationIndependent = indexLocalizationIndependentThm{family.Add(registry.ProofEntry{
	Name: "IndexLocalizationIndependent",
	Key:  "prop_cc0e669576f74f71",
	Deps: []registry.EntryLike{sobolev_section.SectionCoordinateIsomorphism},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L H:sobolev_localization(A). " +
			"∀m s:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀D:((A → num → complex) → A → num → complex).",
		Hypotheses: []string{
			"pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, m, σ, D)",
			"ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, m, σ)",
			"sobolev_localization_on(n, T, 𝒜, L)",
			"sobolev_localization_on(n, T, 𝒜, H)",
		},
		Conclusion: "ps_operator_index(n, r, q, T, 𝒜, P, Q, L, m, s, D) = " +
			"ps_operator_index(n, r, q, T, 𝒜, P, Q, H, m, s, D)",
	},
		"Canonical bounded coordinate isomorphisms conjugate the two "+
			"realizations; their kernels and cokernels have the same dimensions."),
})}

var IndexSameSymbol = indexSameSymbolThm{family.Add(registry.ProofEntry{
	Name: "IndexSameSymbol",
	Key:  "prop_1247ce4da2a96540",
	Deps: []registry.EntryLike{
		pseudo_differential.SamePrincipalLowerOrder,
		pseudo_differential.NegativeOrderCompact,
		fredholm.CompactPerturbation,
	},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L:sobolev_localization(A). " +
			"∀m s:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀D E:((A → num → complex) → A → num → complex).",
		Hypotheses: []string{
			"pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, m, σ, D)",
			"ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, m, σ)",
			"sobolev_localization_on(n, T, 𝒜, L)",
			"pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, m, σ, E)",
		},
		Conclusion: "ps_operator_index(n, r, q, T, 𝒜, P, Q, L, m, s, D) = " +
			"ps_operator_index(n, r, q, T, 𝒜, P, Q, L, m, s, E)",
	},
		"The difference lowers order by one and is compact in the common Sobolev "+
			"realization; Fredholm index is invariant under compact perturbation."),
})}

var IndexClassIndependent = indexClassIndependentThm{family.Add(registry.ProofEntry{
	Name: "IndexClassIndependent",
	Key:  "prop_a106240164885d53",
	Deps: []registry.EntryLike{
		IndexSameSymbol,
		IndexLocalizationIndependent,
		k_compact_support.Equivalence,
		pseudo_differential.EllipticFredholm,
		fredholm.FredholmOpenIndexLocallyConstant,
		fredholm.IndexDirectSum,
	},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀v w:num. " +
			"∀F G:(A → num → num → complex). " +
			"∀L H:sobolev_localization(A). " +
			"∀σ τ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀D E:((A → num → complex) → A → num → complex).",
		Hypotheses: []string{
			"sobolev_localization_on(n, T, 𝒜, L)",
			"sobolev_localization_on(n, T, 𝒜, H)",
			"pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, int_of_num(0), σ, D)",
			"ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, int_of_num(0), σ)",
			"pseudo_differential_operator(n, v, w, T, 𝒜, F, G, int_of_num(0), τ, E)",
			"ps_elliptic_symbol(n, v, w, T, 𝒜, F, G, int_of_num(0), τ)",
			"ps_symbol_class(n, r, q, T, 𝒜, P, Q, σ) = ps_symbol_class(n, v, w, T, 𝒜, F, G, τ)",
		},
		Conclusion: "ps_operator_index(n, r, q, T, 𝒜, P, Q, L, int_of_num(0), int_of_num(0), D) = " +
			"ps_operator_index(n, v, w, T, 𝒜, F, G, H, int_of_num(0), int_of_num(0), E)",
	},
		"Follow the generators of the relative triple relation. Smooth uniformly supported "+
			"homotopies, quantize continuously in operator norm, use local constancy, additivity and the "+
			"zero index of degenerate triples; stable projection isomorphisms give bounded conjugacies."),
})}

var AnalyticIndexOnOperators = analyticIndexOnOperatorsThm{family.Add(registry.ProofEntry{
	Name: "AnalyticIndexOnOperators",
	Key:  "prop_2ce5fc06913c400d",
	Deps: []registry.EntryLike{IndexClassIndependent},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L:sobolev_localization(A). " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀D:((A → num → complex) → A → num → complex).",
		Hypotheses: []string{
			"sobolev_localization_on(n, T, 𝒜, L)",
			"pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, int_of_num(0), σ, D)",
			"ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, int_of_num(0), σ)",
		},
		Conclusion: "analytic_index(n, T, 𝒜, ps_symbol_class(n, r, q, T, 𝒜, P, Q, σ)) = " +
			"ps_operator_index(n, r, q, T, 𝒜, P, Q, L, int_of_num(0), int_of_num(0), D)",
	}, "Every choice in the definition has the same integer by class independence."),
})}

var AnalyticIndexHomomorphism = analyticIndexHomomorphismThm{family.Add(registry.ProofEntry{
	Name: "AnalyticIndexHomomorphism",
	Key:  "prop_bee5924a53ed6fc1",
	Deps: []registry.EntryLike{
		SymbolClassRealization,
		AnalyticIndexOnOperators,
		fredholm.IndexDirectSum,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀T:set(set(A)). ∀𝒜:set(prod(set(A), A → num → real)).",
		Hypotheses: []string{"smooth_manifold⟨n⟩(T, 𝒜)", "compact_in(T, ⋃T)"},
		Conclusion: "group_homomorphism(kc_group(cotangent_topology(n, T, 𝒜)), " +
			"    additive_group(int_ring), " +
			"    analytic_index(n, T, 𝒜))",
	},
		"Direct sum of elliptic realizations realizes the sum of symbol "+
			"triples and adds Fredholm indices; every class has a realization."),
})}

var OrderReduction = orderReductionThm{family.Add(registry.ProofEntry{
	Name: "OrderReduction",
	Key:  "prop_e6140486210ebd62",
	Deps: []registry.EntryLike{
		AnalyticIndexOnOperators,
		IndexSobolevIndependent,
		pseudo_differential.PrincipalSymbolCompose,
		pseudo_differential.EllipticParametrixModuloCompact,
	},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L:sobolev_localization(A). " +
			"∀m s:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀D:((A → num → complex) → A → num → complex).",
		Hypotheses: []string{
			"pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, m, σ, D)",
			"ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, m, σ)",
			"sobolev_localization_on(n, T, 𝒜, L)",
		},
		Conclusion: "analytic_index(n, T, 𝒜, ps_symbol_class(n, r, q, T, 𝒜, P, Q, σ)) = " +
			"ps_operator_index(n, r, q, T, 𝒜, P, Q, L, m, s, D)",
	},
		"Construct an invertible elliptic order-reducing operator using a positive elliptic operator "+
			"on the projected bundle. Its inverse and zero index are proved before composition; the "+
			"positive scalar rescaling of the symbol preserves its compact-support class."),
})}
