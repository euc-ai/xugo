package torus_fourier

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_power_series"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_uniform_convergence"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/real_valued"
	"github.com/euc-ai/xugo/library/proofs/vector/euclidean_topology"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var TorusIntegralCongruence = torusIntegralCongruenceThm{family.Add(registry.ProofEntry{
	Name: "TorusIntegralCongruence",
	Key:  "prop_a547834bf759490c",
	Deps: []registry.EntryLike{real_integral.IntegralCongruence},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀f g:((num → real) → complex).",
			Hypotheses: []string{"∀x:(num → real). vec⟨n⟩(&0, x) ⇒ f(x) = g(x)"},
			Conclusion: "torus_integral(n, f) = torus_integral(n, g)",
		},
		"Induct on n. Every point at which the iterated integral evaluates its integrand is an "+
			"n-vector, and an n-vector extended by a last coordinate is an (n+1)-vector; at each "+
			"level the one-dimensional integrals agree by congruence of the real and imaginary parts."),
})}

var TorusIntegralLinear = torusIntegralLinearThm{family.Add(registry.ProofEntry{
	Name: "TorusIntegralLinear",
	Key:  "prop_1a1e3134baa5c589",
	Reading: "Continuity is what the iterated definition needs: it makes every slice integral " +
		"continuous in the outer coordinate, so each one-dimensional integral exists and is linear.",
	Deps: []registry.EntryLike{
		TorusIntegralCongruence,
		complete_metric.HeineCantor,
		euclidean_topology.BoxCompact,
		path_integral.ComplexContinuousIntegrable,
		path_integral.ComplexHasIntegralAdd,
		path_integral.ComplexHasIntegralScale,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀f g:((num → real) → complex). ∀c:complex.",
			Hypotheses: []string{"torus_class(n, 0, f)", "torus_class(n, 0, g)"},
			Conclusion: "torus_integral(n, λx:(num → real). c * f(x) + g(x)) = " +
				"c * torus_integral(n, f) + torus_integral(n, g)",
		},
		"Prove by induction on n, for every continuous integrand, that the slice integral "+
			"t ↦ torus_integral(n, f(ext(·, t))) is continuous: f is uniformly continuous on "+
			"the compact period cube. A slice is not zero off the n-vectors, so zero it there "+
			"first (TorusIntegralCongruence keeps its integral) before the induction reads it "+
			"as a function of class 0. Continuous slices are integrable on [0, 2π], and the "+
			"one-dimensional complex integral is linear on integrable functions."),
})}

var TorusIntegralBound = torusIntegralBoundThm{family.Add(registry.ProofEntry{
	Name: "TorusIntegralBound",
	Key:  "prop_f4e54bc5dbab01d",
	Deps: []registry.EntryLike{TorusIntegralLinear, path_integral.ComplexHasIntegralBound},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. ∀f:((num → real) → complex). ∀B:real.",
			Hypotheses: []string{
				"torus_class(n, 0, f)",
				"∀x:(num → real). vec⟨n⟩(&0, x) ⇒ |f(x)| ≤ B",
			},
			Conclusion: "|torus_integral(n, f)| ≤ B",
		},
		"Induct on n with the slice continuity behind TorusIntegralLinear. Each "+
			"level bounds the inner integral by B, and the normalized one-dimensional "+
			"integral of a function bounded by B over [0, 2π] has modulus at most B."),
})}

var LatticeSummable = latticeSummableThm{family.Add(registry.ProofEntry{
	Name: "LatticeSummable",
	Key:  "prop_a400affd6b49336d",
	Reading: "The threshold is sharp: at 2σ = n the sum over the lattice diverges " +
		"logarithmically. In dimension zero the lattice is one point and every σ works.",
	Build: family.Card(
		Statement{
			Binders:    "∀n σ:num.",
			Hypotheses: []string{"n < 2 * σ"},
			Conclusion: "∃C:real. ∀F:set(num → int). " +
				"    finite(F) ∧ F ⊆ fourier_lattice(n) ⇒ " +
				"    real_sum(F, λk:(num → int). real_inv(real_pow(&1 + frequency_length_squared(n, k), σ))) ≤ C",
		},
		"Group the frequencies by the dyadic shells 4^j ≤ 1 + |k|² < 4^(j+1). Shell j lies in the "+
			"box of side 2^(j+2), so it holds at most 2^((j+2)n) points, each term at most 4^(−jσ). "+
			"The shells contribute O(2^(j(n − 2σ))), a convergent geometric series since n < 2σ."),
})}

var SummableSynthesis = summableSynthesisThm{family.Add(registry.ProofEntry{
	Name: "SummableSynthesis",
	Key:  "prop_46f2832cdb976ee2",
	Deps: []registry.EntryLike{
		CharacterOrthogonality,
		TorusIntegralLinear,
		TorusIntegralBound,
		FrequencyBlocksFinite,
		sequence_hilbert.SumAbsolute,
		sequence_hilbert.SumLinear,
		real_uniform_convergence.UniformLimitDerivative,
		real_valued.UniformLimitContinuous,
		vec_smooth.PartialDerivativeValue,
	},
	Reading: "The weight is ⟨k⟩^r with ⟨k⟩ = √(1 + |k|²), one power per derivative: " +
		"that is what makes the Sobolev embedding sharp after one Cauchy–Schwarz step.",
	Build: family.Card(
		Statement{
			Binders: "∀n r:num. ∀u:((num → int) → complex).",
			Hypotheses: []string{
				"∀k:(num → int). k ∉ fourier_lattice(n) ⇒ u(k) = complex_of_real(&0)",
				"∃C:real. ∀F:set(num → int). " +
					"    finite(F) ∧ F ⊆ fourier_lattice(n) ⇒ " +
					"    real_sum(F, " +
					"        λk:(num → int). real_pow(real_sqrt(&1 + frequency_length_squared(n, k)), r) * |u(k)|) ≤ " +
					"    C",
			},
			Conclusion: "torus_class(n, r, torus_synthesis(n, u)) ∧ " +
				"torus_coefficients(n, torus_synthesis(n, u)) = u",
		},
		"Each character is smooth and periodic, and a derivative of order at most r multiplies "+
			"it by a monomial in the coordinates of k bounded by ⟨k⟩^r. So every differentiated "+
			"series is dominated by the summable weights and converges uniformly along the frequency "+
			"blocks; uniform limits keep continuity and commute with each derivative. Termwise "+
			"integration against the conjugate characters and their orthogonality recover u."),
})}

var ClassPartial = classPartialThm{family.Add(registry.ProofEntry{
	Name: "ClassPartial",
	Key:  "prop_75c85a86be093000",
	Deps: []registry.EntryLike{vec_smooth.PartialDerivativeValue},
	Build: family.Card(
		Statement{
			Binders:    "∀n r j:num. ∀f:((num → real) → complex).",
			Hypotheses: []string{"j < n", "torus_class(n, r + 1, f)"},
			Conclusion: "torus_class(n, r, torus_partial(n, j, f))",
		},
		"On the n-vectors the real and imaginary parts of the derivative are the partial derivatives "+
			"of those of f, which are of class r. Translating by a period commutes with differentiating "+
			"in coordinate j < n, and the derivative is zero off the n-vectors by definition."),
})}

var FrequencyBlocksFinite = frequencyBlocksFiniteThm{family.Add(registry.ProofEntry{
	Name: "FrequencyBlocksFinite",
	Key:  "prop_4a66a1e373b1803",
	Build: family.Card(
		"∀n:num. ∀R:real. finite(fourier_block(n, R))",
		"Every active integer coordinate is bounded by the radius, so "+
			"the block lies in a finite product of finite integer intervals."),
})}

var CharacterOrthogonality = characterOrthogonalityThm{family.Add(registry.ProofEntry{
	Name: "CharacterOrthogonality",
	Key:  "prop_709676280c4236a8",
	Deps: []registry.EntryLike{
		path_integral.CircleCharacterIntegral,
		TorusIntegralCongruence,
		TorusIntegralLinear,
		complex_power_series.ExpAdd,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀k l:(num → int).",
			Hypotheses: []string{"k ∈ fourier_lattice(n)", "l ∈ fourier_lattice(n)"},
			Conclusion: "torus_integral(n, " +
				"    λx:(num → real). torus_character(n, k, x) * complex_conj(torus_character(n, l, x))) = " +
				"COND(k = l, complex_of_real(&1), complex_of_real(&0))",
		},
		"Integrate coordinate by coordinate; a nonzero integer frequency has zero "+
			"one-period integral. In dimension zero the single character has integral one."),
})}

var CoefficientDerivative = coefficientDerivativeThm{family.Add(registry.ProofEntry{
	Name: "CoefficientDerivative",
	Key:  "prop_40251ab496cfba4e",
	Deps: []registry.EntryLike{
		TorusIntegralCongruence,
		TorusIntegralLinear,
		vec_smooth.PartialDerivativeMul,
		vec_smooth.PartialDerivativeValue,
		real_integral.IntegrationByParts,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n j:num. ∀f:((num → real) → complex). ∀k:(num → int).",
			Hypotheses: []string{"j < n", "torus_smooth(n, f)", "k ∈ fourier_lattice(n)"},
			Conclusion: "torus_coefficients(n, torus_partial(n, j, f), k) = " +
				"complex_i * complex_of_real(real_of_int(k(j))) * torus_coefficients(n, f, k)",
		},
		"Integrate by parts in coordinate j; periodicity cancels the boundary "+
			"term and the negative exponent gives the positive i k multiplier."),
})}

var SmoothCoefficientsRapid = smoothCoefficientsRapidThm{family.Add(registry.ProofEntry{
	Name: "SmoothCoefficientsRapid",
	Key:  "prop_99490bb30206f665",
	Deps: []registry.EntryLike{
		CoefficientDerivative,
		ClassPartial,
		TorusIntegralBound,
		euclidean_topology.BoxCompact,
		real_valued.ContinuousCompactMinimum,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀f:((num → real) → complex).",
			Hypotheses: []string{"torus_smooth(n, f)"},
			Conclusion: "rapid_sequence(n, torus_coefficients(n, f))",
		},
		"Repeated integration by parts transfers powers of the "+
			"frequency to bounded derivatives on a fundamental cube."),
})}

var CircleCompleteness = circleCompletenessThm{family.Add(registry.ProofEntry{
	Name: "CircleCompleteness",
	Key:  "prop_45fac50f495f18f",
	Deps: []registry.EntryLike{
		TrigonometricApproximation,
		TorusIntegralLinear,
		TorusIntegralBound,
		real_integral.NonnegIntegralZeroVanishes,
	},
	Build: family.Card(
		Statement{
			Binders: "∀f:((num → real) → complex).",
			Hypotheses: []string{
				"torus_class(1, 0, f)",
				"∀k:(num → int). k ∈ fourier_lattice(1) ⇒ torus_coefficients(1, f, k) = complex_of_real(&0)",
			},
			Conclusion: "f = (λx:(num → real). complex_of_real(&0))",
		},
		"The Fejér means converge uniformly to a continuous periodic "+
			"function; all means vanish if all Fourier coefficients vanish."),
})}

var FourierCompleteness = fourierCompletenessThm{family.Add(registry.ProofEntry{
	Name: "FourierCompleteness",
	Key:  "prop_81da2d4e6e0bc557",
	Deps: []registry.EntryLike{
		CircleCompleteness,
		TorusIntegralCongruence,
		TorusIntegralLinear,
		complex_power_series.ExpAdd,
	},
	Build: family.Card(
		Statement{
			Binders: "∀n:num. ∀f:((num → real) → complex).",
			Hypotheses: []string{
				"torus_class(n, 0, f)",
				"∀k:(num → int). k ∈ fourier_lattice(n) ⇒ torus_coefficients(n, f, k) = complex_of_real(&0)",
			},
			Conclusion: "f = (λx:(num → real). complex_of_real(&0))",
		},
		"Apply one-dimensional uniqueness to a coordinate at a time, with the remaining Fourier "+
			"coefficients as parameters. Each slice x ↦ f(ext(x, t)) is re-zeroed off the (n−1)-vector "+
			"carrier by a COND before torus_class, the induction hypothesis or CircleCompleteness reads it."),
})}

var RapidSynthesis = rapidSynthesisThm{family.Add(registry.ProofEntry{
	Name: "RapidSynthesis",
	Key:  "prop_845cfec93afa574f",
	Deps: []registry.EntryLike{SummableSynthesis, LatticeSummable},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀u:((num → int) → complex).",
			Hypotheses: []string{"rapid_sequence(n, u)"},
			Conclusion: "torus_smooth(n, torus_synthesis(n, u)) ∧ " +
				"torus_coefficients(n, torus_synthesis(n, u)) = u",
		},
		"Lattice summability gives uniform convergence after every derivative; "+
			"termwise integration and character orthogonality recover the coefficients."),
})}

var SmoothFourierInversion = smoothFourierInversionThm{family.Add(registry.ProofEntry{
	Name: "SmoothFourierInversion",
	Key:  "prop_65c72501b9a054e1",
	Deps: []registry.EntryLike{
		SmoothCoefficientsRapid,
		RapidSynthesis,
		FourierCompleteness,
		TorusIntegralLinear,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀f:((num → real) → complex).",
			Hypotheses: []string{"torus_smooth(n, f)"},
			Conclusion: "torus_synthesis(n, torus_coefficients(n, f)) = f",
		},
		"The synthesized smooth function has the same coefficients as "+
			"f; continuous Fourier uniqueness identifies the functions."),
})}

var UniformFourierConvergence = uniformFourierConvergenceThm{family.Add(registry.ProofEntry{
	Name: "UniformFourierConvergence",
	Key:  "prop_c8022759767d0fac",
	Deps: []registry.EntryLike{
		LatticeSummable,
		FrequencyBlocksFinite,
		sequence_hilbert.SumAbsolute,
		sequence_hilbert.SumLinear,
		sequence_hilbert.FiniteSum,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀u:((num → int) → complex). ∀ε:real.",
			Hypotheses: []string{"&0 < ε", "rapid_sequence(n, u)"},
			Conclusion: "∃R:real. " +
				"    &0 ≤ R ∧ " +
				"    ∀S:real. " +
				"        R ≤ S ⇒ " +
				"        ∀x:(num → real). " +
				"            vec⟨n⟩(&0, x) ⇒ " +
				"            |torus_synthesis(n, sequence_truncate(fourier_block(n, S), u), x) - " +
				"            torus_synthesis(n, u, x)| < " +
				"            ε",
		},
		"Rapid decay bounds the absolute tail uniformly in the base point."),
})}

var SmoothParseval = smoothParsevalThm{family.Add(registry.ProofEntry{
	Name: "SmoothParseval",
	Key:  "prop_88828ecc5648ab74",
	Deps: []registry.EntryLike{
		SmoothFourierInversion,
		UniformFourierConvergence,
		CharacterOrthogonality,
		SmoothCoefficientsRapid,
		LatticeSummable,
		FrequencyBlocksFinite,
		TorusIntegralLinear,
		TorusIntegralBound,
		sequence_hilbert.InnerProductSum,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀f g:((num → real) → complex).",
			Hypotheses: []string{"torus_smooth(n, f)", "torus_smooth(n, g)"},
			Conclusion: "weighted_sequence_inner(fourier_lattice(n), " +
				"    λk:(num → int). &1, " +
				"    torus_coefficients(n, f), " +
				"    torus_coefficients(n, g)) = " +
				"torus_integral(n, λx:(num → real). f(x) * complex_conj(g(x)))",
		},
		"Pass the finite polynomial orthogonality identity to uniformly convergent Fourier series."),
})}

var TrigonometricApproximation = trigonometricApproximationThm{family.Add(registry.ProofEntry{
	Name: "TrigonometricApproximation",
	Key:  "prop_566314f9d36ce8ee",
	Deps: []registry.EntryLike{
		CharacterOrthogonality,
		path_integral.CircleCharacterIntegral,
		TorusIntegralLinear,
		TorusIntegralBound,
		complete_metric.HeineCantor,
		euclidean_topology.BoxCompact,
		sequence_hilbert.FiniteSum,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀n:num. ∀f:((num → real) → complex). ∀ε:real.",
			Hypotheses: []string{"&0 < ε", "torus_class(n, 0, f)"},
			Conclusion: "∃g:((num → real) → complex). " +
				"    torus_polynomial(n, g) ∧ ∀x:(num → real). vec⟨n⟩(&0, x) ⇒ |f(x) - g(x)| < ε",
		},
		"The product Fejér kernels are positive approximate identities; uniform "+
			"continuity on the compact period cube controls their convolution."),
})}
