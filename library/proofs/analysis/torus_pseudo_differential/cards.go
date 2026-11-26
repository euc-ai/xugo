package torus_pseudo_differential

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/analysis/bounded_operator"
	"github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	"github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	"github.com/euc-ai/xugo/library/proofs/analysis/torus_fourier"
	"github.com/euc-ai/xugo/library/proofs/analysis/torus_sobolev"
	"github.com/euc-ai/xugo/library/proofs/real/real_uniform_convergence"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var QuantizationSmooth = quantizationSmoothThm{family.Add(registry.ProofEntry{
	Name: "QuantizationSmooth",
	Key:  "prop_c0fdb8fee7b695b8",
	Deps: []registry.EntryLike{
		torus_fourier.SmoothCoefficientsRapid,
		torus_fourier.LatticeSummable,
		sequence_hilbert.SumAbsolute,
		vec_smooth.PartialDerivativeMul,
		real_uniform_convergence.UniformLimitDerivative,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀m:int. ∀a:((num → real) → complex). ∀f:((num → real) → complex).",
		Hypotheses: []string{"torus_symbol(n, m, a)", "torus_smooth(n, f)"},
		Conclusion: "torus_smooth(n, torus_quantize(n, a, torus_coefficients(n, f)))",
	},
		"Rapid Fourier decay dominates polynomial symbol growth after every "+
			"derivative; uniform absolute convergence permits termwise differentiation."),
})}

var FirstOrderQuantization = firstOrderQuantizationThm{family.Add(registry.ProofEntry{
	Name: "FirstOrderQuantization",
	Key:  "prop_ab1f34fc821fd978",
	Deps: []registry.EntryLike{
		torus_fourier.SmoothFourierInversion,
		torus_fourier.CoefficientDerivative,
		torus_fourier.SmoothCoefficientsRapid,
		torus_fourier.ClassPartial,
		torus_fourier.LatticeSummable,
		sequence_hilbert.SumAbsolute,
		sequence_hilbert.SumLinear,
		sequence_hilbert.SumUnique,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀b:((num → real) → complex). " +
			"∀c:(num → (num → real) → complex). " +
			"∀f:((num → real) → complex). " +
			"∀x:(num → real).",
		Hypotheses: []string{"torus_smooth(n, f)", "vec⟨n⟩(&0, x)"},
		Conclusion: "torus_quantize(n, " +
			"    λz:(num → real). " +
			"        b(ps_base(n, z)) + " +
			"        module_sum(complex_add, " +
			"            &0, " +
			"            {h:num | h < n}, " +
			"            λh:num. c(h, ps_base(n, z)) * complex_i * &ps_frequency(n, z, h)), " +
			"    torus_coefficients(n, f), " +
			"    x) = " +
			"b(x) * f(x) + " +
			"module_sum(complex_add, &0, {h:num | h < n}, λh:num. c(h, x) * torus_partial(n, h, f, x))",
	},
		"At a lattice point the symbol is b(x) plus the sum of c_h(x) i k_h. Rapid decay of "+
			"the coefficients of f splits the quantization into finitely many absolutely summable "+
			"series; Fourier inversion sums the first to f(x), and the derivative rule identifies "+
			"i k_h times the coefficients of f with those of the h-th partial derivative."),
})}

var PseudoDifferentialBounded = pseudoDifferentialBoundedThm{family.Add(registry.ProofEntry{
	Name: "PseudoDifferentialBounded",
	Key:  "prop_fb1b84c4b6e57980",
	Reading: "The realization is chosen by ε against three clauses; this card states all three " +
		"at it, which is the existence the choice needs. Off the source Sobolev space it is zero.",
	Deps: []registry.EntryLike{
		QuantizationSmooth,
		torus_fourier.CoefficientDerivative,
		torus_fourier.SmoothCoefficientsRapid,
		torus_fourier.TorusIntegralBound,
		torus_sobolev.SmoothDense,
		torus_sobolev.SobolevHilbert,
		torus_sobolev.RapidIffAllSobolev,
		torus_sobolev.PeetreInequality,
		sequence_hilbert.NormSquaredFiniteSup,
		sequence_hilbert.SumIterated,
		bounded_operator.BoundedExtension,
		hilbert_space.InnerProductNorm,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀m s:int. ∀a:((num → real) → complex).",
		Hypotheses: []string{"torus_symbol(n, m, a)"},
		Conclusion: "bounded_operator(sobolev_module(n, s), " +
			"    sobolev_norm(n, s), " +
			"    sobolev_module(n, s - m), " +
			"    sobolev_norm(n, s - m), " +
			"    torus_ps_realization(n, m, s, a)) ∧ " +
			"(∀u:((num → int) → complex). " +
			"    u ∉ (sobolev_module(n, s)).carrier ⇒ " +
			"    torus_ps_realization(n, m, s, a, u) = (λk:(num → int). complex_of_real(&0))) ∧ " +
			"(∀f:((num → real) → complex). " +
			"    torus_smooth(n, f) ⇒ " +
			"    torus_ps_realization(n, m, s, a, torus_coefficients(n, f)) = " +
			"    torus_coefficients(n, torus_quantize(n, a, torus_coefficients(n, f))))",
	},
		"Exhibit an operator meeting the three clauses; the choice then names one. Expand the "+
			"symbol in Fourier coefficients in the base variable: divided by ⟨ξ⟩^m they decay "+
			"faster than any power of the base frequency, uniformly in the covariable ξ; Peetre's "+
			"inequality and a weighted convolution estimate bound the quantization from the "+
			"smooth Fourier sequences, dense in the source space, into the target space. Extend "+
			"the bounded map from that dense subspace and set it to zero off the source space."),
})}

var PrincipalSymbolCompose = principalSymbolComposeThm{family.Add(registry.ProofEntry{
	Name: "PrincipalSymbolCompose",
	Key:  "prop_3e213725c7d545dc",
	Deps: []registry.EntryLike{
		QuantizationSmooth,
		torus_fourier.SmoothFourierInversion,
		torus_fourier.SmoothCoefficientsRapid,
		torus_fourier.CoefficientDerivative,
		torus_sobolev.PeetreInequality,
		sequence_hilbert.SumIterated,
		vec_smooth.Hadamard,
		vec_smooth.PartialDerivativeUnderIntegral,
		vec_smooth.SmoothMul,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀m l:int. ∀a b h k:((num → real) → complex).",
		Hypotheses: []string{"torus_principal_pair(n, m, a, h)", "torus_principal_pair(n, l, b, k)"},
		Conclusion: "∃c:((num → real) → complex). " +
			"    torus_principal_pair(n, m + l, c, λz:(num → real). h(z) * k(z)) ∧ " +
			"    (∀f:((num → real) → complex). " +
			"        torus_smooth(n, f) ⇒ " +
			"        torus_quantize(n, c, torus_coefficients(n, f)) = " +
			"        torus_quantize(n, " +
			"            a, " +
			"            torus_coefficients(n, torus_quantize(n, b, torus_coefficients(n, f)))))",
	},
		"Taylor expansion in the continuous covariable gives the product as leading term and a "+
			"remainder of order at most m+l−1; the periodic Fourier sum controls all derivatives."),
})}

var SymbolRealization = symbolRealizationThm{family.Add(registry.ProofEntry{
	Name: "SymbolRealization",
	Key:  "prop_7e69e3732617040e",
	Deps: []registry.EntryLike{
		vec_smooth.BumpFunction,
		vec_smooth.SmoothLocal,
		vec_smooth.SmoothMul,
		vec_smooth.SmoothCompose,
		vec_smooth.PartialDerivativeChain,
		euclidean_topology.BoxCompact,
		real_valued.ContinuousCompactMinimum,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀m:int. ∀h:((num → real) → complex).",
		Hypotheses: []string{"torus_homogeneous_symbol(n, m, h)"},
		Conclusion: "∃a:((num → real) → complex). torus_principal_pair(n, m, a, h)",
	},
		"Multiply the homogeneous symbol by a smooth radial cutoff; compactness in "+
			"the periodic base and unit covariable sphere gives every symbol estimate."),
})}

var NegativeOrderCompact = negativeOrderCompactThm{family.Add(registry.ProofEntry{
	Name: "NegativeOrderCompact",
	Key:  "prop_fefb001d0a08a667",
	Deps: []registry.EntryLike{
		PseudoDifferentialBounded,
		torus_sobolev.Rellich,
		torus_sobolev.SobolevHilbert,
		bounded_operator.CompactIdeal,
		hilbert_space.InnerProductNorm,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀m s:int. ∀a:((num → real) → complex).",
		Hypotheses: []string{"torus_symbol(n, m, a)", "m < int_of_num(0)"},
		Conclusion: "compact_operator(sobolev_module(n, s), " +
			"    sobolev_norm(n, s), " +
			"    sobolev_module(n, s), " +
			"    sobolev_norm(n, s), " +
			"    torus_ps_realization(n, m, s, a))",
	},
		"The operator gains positive Sobolev order and then factors through the compact order inclusion."),
})}

// Pseudolocality — a quantization between periodic cutoffs with disjoint supports is smoothing.
var Pseudolocality = pseudolocalityThm{family.Add(registry.ProofEntry{
	Name: "Pseudolocality",
	Key:  "prop_42ad04facb1305c6",
	Deps: []registry.EntryLike{
		torus_fourier.SmoothCoefficientsRapid,
		torus_fourier.LatticeSummable,
		sequence_hilbert.SumAbsolute,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀m:int. ∀a χ ω:((num → real) → complex). ∀s t:int.",
		Hypotheses: []string{
			"torus_symbol(n, m, a)",
			"torus_smooth(n, χ)",
			"torus_smooth(n, ω)",
			"function_support(euclidean_topology(n), complex_of_real(&0), χ) ∩ " +
				"function_support(euclidean_topology(n), complex_of_real(&0), ω) = " +
				"∅",
		},
		Conclusion: "∃C:real. " +
			"    &0 ≤ C ∧ " +
			"    ∀f:((num → real) → complex). " +
			"        torus_smooth(n, f) ⇒ " +
			"        sobolev_norm(n, " +
			"            t, " +
			"            torus_coefficients(n, " +
			"                λx:(num → real). " +
			"                    χ(x) * " +
			"                    torus_quantize(n, " +
			"                        a, " +
			"                        torus_coefficients(n, λy:(num → real). ω(y) * f(y)), " +
			"                        x))) ≤ " +
			"        C * sobolev_norm(n, s, torus_coefficients(n, f))",
	},
		"The kernel Σ_k a(x, k) e^{ik·(x−y)} is smooth off the periodic diagonal: multiplying it "+
			"by (e^{i(x_j − y_j)} − 1)^N turns it into N-fold frequency differences of a, which gain "+
			"N orders by the derivative bounds of SymbolDef, and on the product of the two disjoint "+
			"periodic supports one such factor is bounded away from zero. A smooth periodic kernel "+
			"maps every Sobolev order into every other (SmoothCoefficientsRapid, LatticeSummable)."),
	Reading: "The supports are taken in ℝⁿ, but the cutoffs are periodic, so disjointness " +
		"there is disjointness on the torus. For n ≥ 2 no single coordinate factor stays away " +
		"from zero on the product of the supports; the sum of the n factors does.",
})}

// CoordinateChange — a cut-off quantization conjugated by a diffeomorphism of the small box is
// a quantization whose principal part is the transported one.
var CoordinateChange = coordinateChangeThm{family.Add(registry.ProofEntry{
	Name: "CoordinateChange",
	Key:  "prop_c086af71f0834db3",
	Deps: []registry.EntryLike{
		Pseudolocality,
		torus_sobolev.LocalPullback,
		vec_smooth.DiffeomorphismInverse,
		vec_smooth.SmoothLocal,
		vec_smooth.Hadamard,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. " +
			"∀m:int. " +
			"∀U V:set(num → real). " +
			"∀κ:((num → real) → num → real). " +
			"∀χ ω:((num → real) → real). " +
			"∀a h:((num → real) → complex).",
		Hypotheses: []string{
			"U ∈ euclidean_topology(n)",
			"V ∈ euclidean_topology(n)",
			"U ⊆ torus_small_box(n)",
			"V ⊆ torus_small_box(n)",
			"vec_diffeomorphic_map⟨n⟩(U, V, κ)",
			"vec_smooth_on⟨n⟩({x:num → real | vec⟨n⟩(&0, x)}, χ)",
			"compact_in(euclidean_topology(n), function_support(euclidean_topology(n), &0, χ))",
			"function_support(euclidean_topology(n), &0, χ) ⊆ U",
			"vec_smooth_on⟨n⟩({y:num → real | vec⟨n⟩(&0, y)}, ω)",
			"compact_in(euclidean_topology(n), function_support(euclidean_topology(n), &0, ω))",
			"function_support(euclidean_topology(n), &0, ω) ⊆ V",
			"torus_principal_pair(n, m, a, h)",
		},
		Conclusion: "∃b:((num → real) → complex). " +
			"    torus_principal_pair(n, " +
			"        m, " +
			"        b, " +
			"        λz:(num → real). " +
			"            COND(vec⟨2 * n⟩(&0, z), " +
			"                torus_periodize(n, " +
			"                    λx:(num → real). " +
			"                        COND(x ∈ U, " +
			"                            complex_of_real(χ(x) * ω(κ(x))) * " +
			"                            h(ps_join(n, " +
			"                                    κ(x), " +
			"                                    λi:num. " +
			"                                        Σ_{j<n} vec_jacobian_matrix⟨n, n⟩(inverse_on(U, κ), κ(x), j, i) * " +
			"                                        ps_frequency(n, z, j))), " +
			"                            complex_of_real(&0)), " +
			"                    ps_base(n, z)), " +
			"                complex_of_real(&0))) ∧ " +
			"    (∀s t:int. ∃C:real. " +
			"        &0 ≤ C ∧ " +
			"        ∀f:((num → real) → complex). " +
			"            torus_smooth(n, f) ⇒ " +
			"            sobolev_norm(n, " +
			"                t, " +
			"                λk:(num → int). " +
			"                    torus_coefficients(n, " +
			"                        local_pullback_seed(n, " +
			"                            U, " +
			"                            κ, " +
			"                            χ, " +
			"                            torus_quantize(n, " +
			"                                a, " +
			"                                torus_coefficients(n, " +
			"                                    local_pullback_seed(n, V, inverse_on(U, κ), ω, f)))), " +
			"                        k) - " +
			"                    torus_coefficients(n, torus_quantize(n, b, torus_coefficients(n, f)), k)) ≤ " +
			"            C * sobolev_norm(n, s, torus_coefficients(n, f)))",
	},
		"Kuranishi's change of variables. The conjugated operator f ↦ χ·[a(ω·f∘κ⁻¹)]∘κ has a kernel "+
			"singular only on the diagonal over U; its symbol b(x, ξ), the operator applied to e^{iξ·} "+
			"and divided by it, taken over the box and periodized in x, satisfies the symbol bounds. "+
			"κ(x) − κ(y) = A(x, y)(x − y) with A(x, y) = ∫₀¹ Dκ(y + t(x − y)) dt jointly smooth where "+
			"the segment lies in U, a parametric form of vec_smooth.Hadamard (whose base point is fixed "+
			"and whose set is convex) that is the filler's promotion; a Taylor expansion of a in the "+
			"covariable at the transposed derivative of κ⁻¹ — the transport cotangent_from_chart "+
			"performs — leaves an order m − 1 remainder; Pseudolocality removes the kernel away from "+
			"the diagonal and LocalPullback bounds the two pullbacks, the inner one along inverse_on(U, "+
			"κ), which on V is the smooth inverse DiffeomorphismInverse gives (vec_smooth.SmoothLocal)."),
	Reading: "No Jacobian determinant enters the transported symbol, because " +
		"the operator is a pullback conjugation, not a change of measure. " +
		"inverse_on(U, κ) is read only on V, where it is the smooth inverse.",
})}
