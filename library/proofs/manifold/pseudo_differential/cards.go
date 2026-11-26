package pseudo_differential

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/analysis/bounded_operator"
	"github.com/euc-ai/xugo/library/proofs/analysis/fredholm"
	"github.com/euc-ai/xugo/library/proofs/analysis/torus_fourier"
	"github.com/euc-ai/xugo/library/proofs/analysis/torus_pseudo_differential"
	"github.com/euc-ai/xugo/library/proofs/manifold/manifold_cotangent"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_manifold"
	"github.com/euc-ai/xugo/library/proofs/manifold/smooth_projection_bundle"
	"github.com/euc-ai/xugo/library/proofs/manifold/sobolev_section"
	"github.com/euc-ai/xugo/library/proofs/real/real_zpow"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var PseudoDifferentialBounded = pseudoDifferentialBoundedThm{family.Add(registry.ProofEntry{
	Name: "PseudoDifferentialBounded",
	Key:  "prop_e6169d1532e07e18",
	Deps: []registry.EntryLike{
		torus_pseudo_differential.PseudoDifferentialBounded,
		sobolev_section.SectionNormEquivalence,
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
			"sobolev_localization_on(n, T, 𝒜, L)",
		},
		Conclusion: "bounded_operator(section_sobolev_module(n, r, T, 𝒜, P, L, s), " +
			"    localization_sequence_norm(n, r, L.count, s), " +
			"    section_sobolev_module(n, q, T, 𝒜, Q, L, s - m), " +
			"    localization_sequence_norm(n, q, L.count, s - m), " +
			"    ps_realization(n, r, q, T, 𝒜, P, Q, L, m, s, D))",
	},
		"Finite chart restriction, torus symbol bounds and chart extension "+
			"give the global Sobolev bound. Norm equivalence transfers it to any "+
			"localization; the smoothing remainder is bounded at these orders."),
})}

var RealizationOnSmooth = realizationOnSmoothThm{family.Add(registry.ProofEntry{
	Name: "RealizationOnSmooth",
	Key:  "prop_4ae5423b7f936e13",
	Deps: []registry.EntryLike{PseudoDifferentialBounded},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L:sobolev_localization(A). " +
			"∀m s:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀D:((A → num → complex) → A → num → complex). " +
			"∀f:(A → num → complex).",
		Hypotheses: []string{
			"pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, m, σ, D)",
			"sobolev_localization_on(n, T, 𝒜, L)",
			"smooth_projected_section(n, r, T, 𝒜, P, f)",
		},
		Conclusion: "ps_realization(n, r, q, T, 𝒜, P, Q, L, m, s, D, localize_section(n, r, L, f)) = " +
			"localize_section(n, q, L, D(f))",
	}, "The unique bounded extension agrees on the dense localized smooth image."),
})}

var FirstOrderPseudoDifferential = firstOrderPseudoDifferentialThm{family.Add(registry.ProofEntry{
	Name: "FirstOrderPseudoDifferential",
	Key:  "prop_26634280a1fc821f",
	Deps: []registry.EntryLike{
		torus_pseudo_differential.FirstOrderQuantization,
		sobolev_section.LocalizationExists,
	},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀D:((A → num → complex) → A → num → complex). " +
			"∀C:(prod(set(A), A → num → real) → num → A → num → num → complex). " +
			"∀B:(prod(set(A), A → num → real) → A → num → num → complex).",
		Hypotheses: []string{
			"compact_in(T, ⋃T)",
			"ps_principal_symbol(n, r, q, T, 𝒜, P, Q, int_of_num(1), σ)",
			"∀f:(A → num → complex). " +
				"    smooth_projected_section(n, r, T, 𝒜, P, f) ⇒ smooth_projected_section(n, q, T, 𝒜, Q, D(f))",
			"∀c:prod(set(A), A → num → real). ∀h i j:num. " +
				"    compatible_chart⟨n⟩(T, 𝒜, c) ⇒ " +
				"    vec_smooth_on⟨n⟩(image(snd(c), fst(c)), " +
				"        λy:(num → real). re(C(c, h, inverse_on(fst(c), snd(c), y), i, j))) ∧ " +
				"    vec_smooth_on⟨n⟩(image(snd(c), fst(c)), " +
				"        λy:(num → real). im(C(c, h, inverse_on(fst(c), snd(c), y), i, j))) ∧ " +
				"    vec_smooth_on⟨n⟩(image(snd(c), fst(c)), " +
				"        λy:(num → real). re(B(c, inverse_on(fst(c), snd(c), y), i, j))) ∧ " +
				"    vec_smooth_on⟨n⟩(image(snd(c), fst(c)), " +
				"        λy:(num → real). im(B(c, inverse_on(fst(c), snd(c), y), i, j)))",
			"∀c:prod(set(A), A → num → real). ∀f:(A → num → complex). ∀x:A. ∀i:num. " +
				"    compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
				"    x ∈ fst(c) ∧ " +
				"    smooth_projected_section(n, r, T, 𝒜, P, f) ∧ " +
				"    i < q ⇒ " +
				"    D(f, x, i) = " +
				"    module_sum(complex_add, " +
				"        &0, " +
				"        {j:num | j < r}, " +
				"        λj:num. " +
				"            module_sum(complex_add, " +
				"                &0, " +
				"                {h:num | h < n}, " +
				"                λh:num. " +
				"                    C(c, h, x, i, j) * " +
				"                    complex(partial_derivative( " +
				"                            λy:(num → real). re(f(inverse_on(fst(c), snd(c), y), j)), " +
				"                            h, " +
				"                            snd(c, x)), " +
				"                        partial_derivative( " +
				"                            λy:(num → real). im(f(inverse_on(fst(c), snd(c), y), j)), " +
				"                            h, " +
				"                            snd(c, x)))) + " +
				"            B(c, x, i, j) * f(x, j))",
			"∀c:prod(set(A), A → num → real). ∀x:A. ∀u:(num → real). ∀i j:num. " +
				"    compatible_chart⟨n⟩(T, 𝒜, c) ∧ " +
				"    x ∈ fst(c) ∧ " +
				"    vec⟨n⟩(&0, u) ∧ " +
				"    u ≠ (λh:num. &0) ∧ " +
				"    i < q ∧ " +
				"    j < r ⇒ " +
				"    σ((x, cotangent_from_chart(n, T, 𝒜, c, x, u)), i, j) = " +
				"    complex_i * module_sum(complex_add, &0, {h:num | h < n}, λh:num. C(c, h, x, i, j) * &u(h))",
		},
		Conclusion: "pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, int_of_num(1), σ, D)",
	},
		"Take any localization and smooth cutoffs equal to one near each partition support. "+
			"In each chart the full symbol is the cutoff times the zero-order matrix plus the "+
			"coefficients against i times the frequency, periodized; it is a first-order torus "+
			"symbol whose principal part is the localized principal symbol. First-order "+
			"quantization reproduces D on the cutoff section where the partition weight is "+
			"positive, so the partition sum is D itself and the smoothing remainder is zero."),
})}

var SymbolRealization = symbolRealizationThm{family.Add(registry.ProofEntry{
	Name: "SymbolRealization",
	Key:  "prop_27ba878df02e0c5b",
	Deps: []registry.EntryLike{torus_pseudo_differential.SymbolRealization},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀m:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex).",
		Hypotheses: []string{"compact_in(T, ⋃T)", "ps_principal_symbol(n, r, q, T, 𝒜, P, Q, m, σ)"},
		Conclusion: "∃D:((A → num → complex) → A → num → complex). " +
			"    pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, m, σ, D)",
	},
		"Choose finite small charts and cutoffs equal to one near the partition "+
			"supports; cut off each local homogeneous symbol near the zero covariable "+
			"and quantize. The resulting finite sum has the prescribed principal symbol."),
})}

var NegativeOrderCompact = negativeOrderCompactThm{family.Add(registry.ProofEntry{
	Name: "NegativeOrderCompact",
	Key:  "prop_30429d4cf7ba83f0",
	Deps: []registry.EntryLike{
		PseudoDifferentialBounded,
		torus_pseudo_differential.NegativeOrderCompact,
		sobolev_section.SectionRellich,
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
			"sobolev_localization_on(n, T, 𝒜, L)",
			"m < int_of_num(0)",
		},
		Conclusion: "compact_operator(section_sobolev_module(n, r, T, 𝒜, P, L, s), " +
			"    localization_sequence_norm(n, r, L.count, s), " +
			"    section_sobolev_module(n, q, T, 𝒜, Q, L, s), " +
			"    localization_sequence_norm(n, q, L.count, s), " +
			"    ps_realization(n, r, q, T, 𝒜, P, Q, L, m, s, D))",
	}, "The mapping property gains positive order and the global Rellich inclusion is compact."),
})}

var EllipticFredholm = ellipticFredholmThm{family.Add(registry.ProofEntry{
	Name: "EllipticFredholm",
	Key:  "prop_a627a4d0f42bbe30",
	Deps: []registry.EntryLike{EllipticParametrixModuloCompact, fredholm.Atkinson},
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
			"sobolev_localization_on(n, T, 𝒜, L)",
			"ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, m, σ)",
		},
		Conclusion: "fredholm_operator(section_sobolev_module(n, r, T, 𝒜, P, L, s), " +
			"    localization_sequence_inner(n, r, L.count, s), " +
			"    section_sobolev_module(n, q, T, 𝒜, Q, L, s - m), " +
			"    localization_sequence_inner(n, q, L.count, s - m), " +
			"    ps_realization(n, r, q, T, 𝒜, P, Q, L, m, s, D))",
	},
		"Quantize the inverse homogeneous symbol. Both compositions have identity "+
			"principal symbol, so their errors lower order and are compact; apply Atkinson."),
})}

var PrincipalSymbolCompose = principalSymbolComposeThm{family.Add(registry.ProofEntry{
	Name: "PrincipalSymbolCompose",
	Key:  "prop_259f869b947f4045",
	Deps: []registry.EntryLike{
		torus_pseudo_differential.PrincipalSymbolCompose,
		torus_pseudo_differential.CoordinateChange,
		torus_pseudo_differential.Pseudolocality,
		torus_pseudo_differential.QuantizationSmooth,
		torus_pseudo_differential.FirstOrderQuantization,
		torus_pseudo_differential.PseudoDifferentialBounded,
		sobolev_section.SectionChartRestriction,
		sobolev_section.SectionChartExtension,
		sobolev_section.SectionNormEquivalence,
	},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀v:num. " +
			"∀S:(A → num → num → complex). " +
			"∀m l:int. " +
			"∀σ τ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀D E:((A → num → complex) → A → num → complex).",
		Hypotheses: []string{
			"pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, m, σ, D)",
			"pseudo_differential_operator(n, q, v, T, 𝒜, Q, S, l, τ, E)",
		},
		Conclusion: "pseudo_differential_operator(n, " +
			"    r, " +
			"    v, " +
			"    T, " +
			"    𝒜, " +
			"    P, " +
			"    S, " +
			"    m + l, " +
			"    λp:prod(A, prod(set(A), A → num → real) → num → real). λi:num. λj:num. " +
			"        module_sum(complex_add, " +
			"            complex_of_real(&0), " +
			"            {k:num | k < q}, " +
			"            λk:num. τ(p, i, k) * σ(p, k, j)), " +
			"    λf:(A → num → complex). E(D(f)))",
	},
		"Insert finite chart cutoffs, transform covariables by the inverse transpose derivative "+
			"(torus_pseudo_differential.CoordinateChange), read the multipliers between the two "+
			"quantizations as order-0 quantizations (FirstOrderQuantization at c = 0), and apply the "+
			"local composition expansion (torus_pseudo_differential.PrincipalSymbolCompose). "+
			"Off-diagonal terms, between cutoffs of disjoint support, improve all orders "+
			"(torus_pseudo_differential.Pseudolocality), and the principal chart terms multiply. E's "+
			"representation reads D(f) as a smooth section (QuantizationSmooth through the charts); "+
			"the cross terms with the smoothing remainders are bounded by PseudoDifferentialBounded "+
			"through SectionChartRestriction and SectionChartExtension, and SectionNormEquivalence "+
			"moves the bounds between the localizations of D, E and the composite."),
})}

var PrincipalSymbolAdjoint = principalSymbolAdjointThm{family.Add(registry.ProofEntry{
	Name: "PrincipalSymbolAdjoint",
	Key:  "prop_ce4213a055571bf0",
	Deps: []registry.EntryLike{
		torus_fourier.SmoothParseval,
		torus_fourier.FourierCompleteness,
		torus_pseudo_differential.PrincipalSymbolCompose,
		torus_pseudo_differential.FirstOrderQuantization,
		torus_pseudo_differential.CoordinateChange,
		torus_pseudo_differential.Pseudolocality,
		sobolev_section.SectionHilbert,
		sobolev_section.SectionNormEquivalence,
		sobolev_section.SectionSmoothRegularity,
		smooth_manifold.FunctionReciprocal,
		bounded_operator.RieszRepresentation,
	},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L:sobolev_localization(A). " +
			"∀m:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀D:((A → num → complex) → A → num → complex).",
		Hypotheses: []string{
			"pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, m, σ, D)",
			"sobolev_localization_on(n, T, 𝒜, L)",
		},
		Conclusion: "pseudo_differential_operator(n, " +
			"    q, " +
			"    r, " +
			"    T, " +
			"    𝒜, " +
			"    Q, " +
			"    P, " +
			"    m, " +
			"    λp:prod(A, prod(set(A), A → num → real) → num → real). λi:num. λj:num. " +
			"        complex_conj(σ(p, j, i)), " +
			"    ps_formal_adjoint(n, r, q, T, 𝒜, P, Q, L, D))",
	},
		"By SmoothParseval the order-0 localization inner product integrates the ambient Hermitian "+
			"fibre product against the smooth positive density Σ_l φ_l² dy_l of L's partition and "+
			"charts, and it separates smooth sections (SectionHilbert, FourierCompleteness), so the "+
			"ε-chosen adjoint is any adjoint one exhibits. In D's own localization take the adjoint of "+
			"each chart quantization, absorb density ratios and cutoffs as order-zero multipliers "+
			"(FirstOrderQuantization, PrincipalSymbolCompose), and re-localize the result into "+
			"OperatorDef's form, partition outside and cutoff inside, by CoordinateChange and "+
			"Pseudolocality; the symbol is the conjugate transpose because P and Q are Hermitian. The "+
			"filler promotes two steps: the torus adjoint of a principal pair, with symbol conj ∘ h, and "+
			"the adjoint of a smoothing operator, smoothing through the duality of orders s and −s under "+
			"the order-0 pairing (RieszRepresentation, SectionSmoothRegularity, SectionNormEquivalence)."),
	Reading: "The order-0 pairing has density Σ_l φ_l² dy_l, positive because " +
		"the localization's partition sums to 1. The ε-chosen adjoint is fixed only " +
		"on ⋃T and in components below r; the rest goes into the smoothing remainder.",
})}

var SamePrincipalLowerOrder = samePrincipalLowerOrderThm{family.Add(registry.ProofEntry{
	Name: "SamePrincipalLowerOrder",
	Key:  "prop_6f9929dfc2c31c23",
	Deps: []registry.EntryLike{
		torus_pseudo_differential.CoordinateChange,
		torus_pseudo_differential.Pseudolocality,
		torus_pseudo_differential.PseudoDifferentialBounded,
		torus_pseudo_differential.PrincipalPairDef,
		sobolev_section.SectionChartRestriction,
		sobolev_section.SectionChartExtension,
		sobolev_section.SectionNormEquivalence,
		sobolev_section.SectionSmoothDense,
		sobolev_section.SectionHilbert,
		bounded_operator.BoundedExtension,
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
			"pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, m, σ, E)",
			"sobolev_localization_on(n, T, 𝒜, L)",
		},
		Conclusion: "bounded_operator(section_sobolev_module(n, r, T, 𝒜, P, L, s), " +
			"    localization_sequence_norm(n, r, L.count, s), " +
			"    section_sobolev_module(n, q, T, 𝒜, Q, L, s - m + int_of_num(1)), " +
			"    localization_sequence_norm(n, q, L.count, s - m + int_of_num(1)), " +
			"    ps_realization(n, " +
			"        r, " +
			"        q, " +
			"        T, " +
			"        𝒜, " +
			"        P, " +
			"        Q, " +
			"        L, " +
			"        m - int_of_num(1), " +
			"        s, " +
			"        λf:(A → num → complex). λx:A. λi:num. D(f, x, i) - E(f, x, i)))",
	},
		"D and E come in their own localizations: insert D's partition into E, carry each "+
			"chart term of E into the matching chart of D by CoordinateChange, and drop the pieces "+
			"off the supports by Pseudolocality. In each chart the two symbols are then principal "+
			"pairs with the same ps_local_principal, so they differ by a torus symbol of order m−1 "+
			"— the filler's promotion, read off PrincipalPairDef. Torus PseudoDifferentialBounded "+
			"at order m−1 with SectionChartRestriction and SectionChartExtension bounds the "+
			"difference from order s to s−m+1, SectionNormEquivalence moves that bound and both "+
			"smoothing remainders to L, and BoundedExtension over the dense smooth sections gives "+
			"the realization; the remainder need not have a further homogeneous leading term."),
	Reading: "Two principal pairs with the same homogeneous part differ by " +
		"a symbol of order m − 1 even when their radial cutoffs differ, the " +
		"difference of cutoffs times the symbol being compactly supported in ξ.",
})}

var InverseSymbol = inverseSymbolThm{family.Add(registry.ProofEntry{
	Name: "InverseSymbol",
	Key:  "prop_cb1d2b57d690ac1",
	Deps: []registry.EntryLike{
		manifold_cotangent.CotangentManifold,
		manifold_cotangent.CoordinateCovector,
		real_zpow.ZpowNeg,
		vec_smooth.SmoothCompose,
		smooth_projection_bundle.SmoothNormalizedInverse,
	},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀m:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex).",
		Hypotheses: []string{"ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, m, σ)"},
		Conclusion: "∃τ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"    ps_elliptic_symbol(n, q, r, T, 𝒜, Q, P, -m, τ) ∧ " +
			"    (∀p:prod(A, prod(set(A), A → num → real) → num → real). " +
			"        p ∈ cotangent_punctured(n, T, 𝒜) ⇒ " +
			"        projection_inverse_on({p}, " +
			"            projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"                λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"                (r, P)), " +
			"            projection_pullback(cotangent_topology(n, T, 𝒜), " +
			"                λp:prod(A, prod(set(A), A → num → real) → num → real). fst(p), " +
			"                (q, Q)), " +
			"            σ, " +
			"            τ))",
	},
		"Over a punctured covector p the pulled-back projections read P(fst(p)) and Q(fst(p)), "+
			"since ⋃cotangent_topology is the cotangent bundle (CotangentManifold). Take τ(p) the "+
			"normalized inverse of σ(p), the one inverse V with P V Q = V, and zero off the punctured "+
			"bundle; its uniqueness gives the projection laws and homogeneity of order −m, "+
			"cotangent_scale fixing fst(p) (ZpowNeg). Chart parameters with nonzero frequency are "+
			"punctured (CoordinateCovector), σ and P, Q after ps_base are smooth there (SmoothCompose), "+
			"and SmoothNormalizedInverse makes τ smooth; σ witnesses the ellipticity of τ."),
	Reading: "τ is forced to be the unique normalized inverse, PτQ = τ; its " +
		"uniqueness and its homogeneity of order −m use only that P and Q are " +
		"idempotent, Hermitian symmetry entering only through SmoothNormalizedInverse.",
})}

var EllipticParametrixModuloCompact = ellipticParametrixModuloCompactThm{family.Add(registry.ProofEntry{
	Name: "EllipticParametrixModuloCompact",
	Key:  "prop_22dfd7b44d5591cc",
	Deps: []registry.EntryLike{
		InverseSymbol,
		SymbolRealization,
		PrincipalSymbolCompose,
		SamePrincipalLowerOrder,
		NegativeOrderCompact,
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
			"sobolev_localization_on(n, T, 𝒜, L)",
			"ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, m, σ)",
		},
		Conclusion: "∃τ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∃E:((A → num → complex) → A → num → complex). " +
			"    pseudo_differential_operator(n, q, r, T, 𝒜, Q, P, -m, τ, E) ∧ " +
			"    fredholm_parametrix(section_sobolev_module(n, r, T, 𝒜, P, L, s), " +
			"        localization_sequence_inner(n, r, L.count, s), " +
			"        section_sobolev_module(n, q, T, 𝒜, Q, L, s - m), " +
			"        localization_sequence_inner(n, q, L.count, s - m), " +
			"        ps_realization(n, r, q, T, 𝒜, P, Q, L, m, s, D), " +
			"        ps_realization(n, q, r, T, 𝒜, Q, P, L, -m, s - m, E))",
	},
		"Quantize the inverse homogeneous symbol. Composition and the identity "+
			"symbol leave negative-order errors, whose Sobolev realizations are compact."),
})}

var EllipticKernelSmooth = ellipticKernelSmoothThm{family.Add(registry.ProofEntry{
	Name: "EllipticKernelSmooth",
	Key:  "prop_7838537decb4e28a",
	Deps: []registry.EntryLike{
		EllipticParametrixModuloCompact,
		RealizationOnSmooth,
		sobolev_section.SectionSmoothRegularity,
	},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L:sobolev_localization(A). " +
			"∀m s:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀D:((A → num → complex) → A → num → complex). " +
			"∀u:(prod(num, prod(num, num → int)) → complex).",
		Hypotheses: []string{
			"pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, m, σ, D)",
			"sobolev_localization_on(n, T, 𝒜, L)",
			"ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, m, σ)",
			"u ∈ (section_sobolev_module(n, r, T, 𝒜, P, L, s)).carrier",
			"ps_realization(n, r, q, T, 𝒜, P, Q, L, m, s, D, u) = " +
				"(λz:prod(num, prod(num, num → int)). complex_of_real(&0))",
		},
		Conclusion: "∃f:(A → num → complex). " +
			"    smooth_projected_section(n, r, T, 𝒜, P, f) ∧ " +
			"    localize_section(n, r, L, f) = u ∧ " +
			"    D(f) = (λx:A. λi:num. complex_of_real(&0))",
	},
		"The parametrix identity raises the regularity of a kernel vector by one. "+
			"Iterate to every integer order and apply the global smooth-regularity theorem."),
})}

var EllipticRegularity = ellipticRegularityThm{family.Add(registry.ProofEntry{
	Name: "EllipticRegularity",
	Key:  "prop_31e14a81fe147f60",
	Deps: []registry.EntryLike{EllipticParametrixModuloCompact},
	Build: family.Card(Statement{
		Binders: "∀n r q:num. " +
			"∀T:set(set(A)). " +
			"∀𝒜:set(prod(set(A), A → num → real)). " +
			"∀P Q:(A → num → num → complex). " +
			"∀L:sobolev_localization(A). " +
			"∀m s:int. " +
			"∀σ:(prod(A, prod(set(A), A → num → real) → num → real) → num → num → complex). " +
			"∀D:((A → num → complex) → A → num → complex). " +
			"∀t:int. " +
			"∀u:(prod(num, prod(num, num → int)) → complex).",
		Hypotheses: []string{
			"pseudo_differential_operator(n, r, q, T, 𝒜, P, Q, m, σ, D)",
			"sobolev_localization_on(n, T, 𝒜, L)",
			"ps_elliptic_symbol(n, r, q, T, 𝒜, P, Q, m, σ)",
			"u ∈ (section_sobolev_module(n, r, T, 𝒜, P, L, s)).carrier",
			"ps_realization(n, r, q, T, 𝒜, P, Q, L, m, s, D, u) ∈ " +
				"(section_sobolev_module(n, q, T, 𝒜, Q, L, t)).carrier",
		},
		Conclusion: "u ∈ (section_sobolev_module(n, r, T, 𝒜, P, L, t + m)).carrier",
	},
		"Apply the order −m parametrix and repeatedly gain "+
			"one order from its remainder until reaching t+m."),
})}
