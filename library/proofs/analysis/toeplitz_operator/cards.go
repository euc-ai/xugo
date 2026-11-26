package toeplitz_operator

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/analysis/bounded_operator"
	"github.com/euc-ai/xugo/library/proofs/analysis/fredholm"
	"github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	"github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	"github.com/euc-ai/xugo/library/proofs/analysis/torus_fourier"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_power_series"
	"github.com/euc-ai/xugo/library/proofs/complex/path_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_trigonometry"
	"github.com/euc-ai/xugo/library/proofs/topology/covering_space"
	"github.com/euc-ai/xugo/library/proofs/vector/circle"
	"github.com/euc-ai/xugo/library/registry"
)

var CircleApproximation = circleApproximationThm{family.Add(registry.ProofEntry{
	Name: "CircleApproximation",
	Key:  "prop_e85325b1809b7d45",
	Deps: []registry.EntryLike{torus_fourier.TrigonometricApproximation},
	Build: family.Card(
		Statement{
			Binders:    "∀f:(real → complex). ∀ε:real.",
			Hypotheses: []string{"&0 < ε", "circle_symbol(f)"},
			Conclusion: "∃g:(real → complex). " +
				"    circle_polynomial(g) ∧ circle_symbol_norm(λt:real. f(t) - g(t)) < ε",
		},
		"Read f as the continuous periodic function x ↦ f(x(0)) on the one-dimensional torus, "+
			"zero off the 1-vectors, and approximate it within ε/2 by a trigonometric polynomial "+
			"there. Its frequencies are integer multiples of the first coordinate, so restricted "+
			"to the first coordinate it is a circle polynomial, within ε/2 of f on [0, 2π]."),
})}

var ToeplitzBounded = toeplitzBoundedThm{family.Add(registry.ProofEntry{
	Name: "ToeplitzBounded",
	Key:  "prop_c6e9662f4455da6e",
	Deps: []registry.EntryLike{
		sequence_hilbert.FiniteSupportDense,
		CircleApproximation,
		path_integral.CircleCharacterIntegral,
		sequence_hilbert.WeightedHilbert,
		sequence_hilbert.NormSquaredFiniteSup,
		sequence_hilbert.SumReindex,
		hilbert_space.InnerProductNorm,
		bounded_operator.BoundedExtension,
		bounded_operator.OperatorNormBound,
		path_integral.ComplexHasIntegralBound,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀f:(real → complex).",
			Hypotheses: []string{"circle_symbol(f)"},
			Conclusion: "bounded_operator(hardy_sequence_module, " +
				"    hardy_sequence_norm, " +
				"    hardy_sequence_module, " +
				"    hardy_sequence_norm, " +
				"    toeplitz_operator(f)) ∧ " +
				"bounded_op_norm(hardy_sequence_module, " +
				"    hardy_sequence_norm, " +
				"    hardy_sequence_norm, " +
				"    toeplitz_operator(f)) ≤ " +
				"circle_symbol_norm(f) ∧ " +
				"(∀u:(num → complex). " +
				"    finite({j:num | u(j) ≠ complex_of_real(&0)}) ⇒ " +
				"    ∀m:num. " +
				"        toeplitz_operator(f, u, m) = " +
				"        module_sum(complex_add, " +
				"            complex_of_real(&0), " +
				"            {j:num | u(j) ≠ complex_of_real(&0)}, " +
				"            λj:num. circle_coefficient(f, int_of_num(m) - int_of_num(j)) * u(j)))",
		},
		"For trigonometric symbols use Parseval and projection to nonnegative frequencies; "+
			"uniformly approximate continuous symbols, then extend from finite-support vectors."),
})}

var ToeplitzNormContinuity = toeplitzNormContinuityThm{family.Add(registry.ProofEntry{
	Name: "ToeplitzNormContinuity",
	Key:  "prop_136fdc56f9703cfe",
	Deps: []registry.EntryLike{
		ToeplitzBounded,
		sequence_hilbert.FiniteSupportDense,
		sequence_hilbert.WeightedHilbert,
		hilbert_space.InnerProductNorm,
		bounded_operator.BoundedAgreeDense,
		bounded_operator.OperatorNormBound,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀f g:(real → complex).",
			Hypotheses: []string{"circle_symbol(f)", "circle_symbol(g)"},
			Conclusion: "bounded_op_norm(hardy_sequence_module, " +
				"    hardy_sequence_norm, " +
				"    hardy_sequence_norm, " +
				"    λu:(num → complex). λj:num. toeplitz_operator(f, u, j) - toeplitz_operator(g, u, j)) ≤ " +
				"circle_symbol_norm(λt:real. f(t) - g(t))",
		},
		"Linearity on finite-support vectors passes to the bounded "+
			"extensions; apply the symbol-norm bound to f minus g."),
})}

var PolynomialSemicommutator = polynomialSemicommutatorThm{family.Add(registry.ProofEntry{
	Name: "PolynomialSemicommutator",
	Key:  "prop_f9e1ae193f99bb56",
	Deps: []registry.EntryLike{
		ToeplitzBounded,
		path_integral.CircleCharacterIntegral,
		sequence_hilbert.FiniteSupportDense,
		bounded_operator.BoundedAgreeDense,
		hilbert_space.FiniteDimensionalClosed,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀f g:(real → complex).",
			Hypotheses: []string{"circle_polynomial(f)", "circle_polynomial(g)"},
			Conclusion: "finite_rank_operator(hardy_sequence_module, " +
				"    hardy_sequence_module, " +
				"    λu:(num → complex). λj:num. " +
				"        toeplitz_operator(f, toeplitz_operator(g, u), j) - " +
				"        toeplitz_operator(λt:real. f(t) * g(t), u, j))",
		},
		"Finite-band Laurent multiplication loses only finitely "+
			"many coordinates at the nonnegative-frequency boundary."),
})}

var CompactSemicommutator = compactSemicommutatorThm{family.Add(registry.ProofEntry{
	Name: "CompactSemicommutator",
	Key:  "prop_1482e1dcc8839a0d",
	Deps: []registry.EntryLike{
		PolynomialSemicommutator,
		ToeplitzNormContinuity,
		bounded_operator.CompactNormLimit,
		bounded_operator.FiniteRankCompact,
		CircleApproximation,
		ToeplitzBounded,
		sequence_hilbert.WeightedHilbert,
		hilbert_space.InnerProductNorm,
		bounded_operator.OperatorNormBound,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀f g:(real → complex).",
			Hypotheses: []string{"circle_symbol(f)", "circle_symbol(g)"},
			Conclusion: "compact_operator(hardy_sequence_module, " +
				"    hardy_sequence_norm, " +
				"    hardy_sequence_module, " +
				"    hardy_sequence_norm, " +
				"    λu:(num → complex). λj:num. " +
				"        toeplitz_operator(f, toeplitz_operator(g, u), j) - " +
				"        toeplitz_operator(λt:real. f(t) * g(t), u, j))",
		},
		"Uniform trigonometric approximation gives operator-norm limits of finite-rank semicommutators."),
})}

var NonvanishingFredholm = nonvanishingFredholmThm{family.Add(registry.ProofEntry{
	Name: "NonvanishingFredholm",
	Reading: "Continuity and periodicity give a positive lower bound on the modulus " +
		"over a period, hence a continuous reciprocal symbol. Piecewise smoothness is " +
		"needed only when identifying the index with the integral winding number.",
	Key: "prop_85985b67f3269f20",
	Deps: []registry.EntryLike{
		CompactSemicommutator,
		fredholm.Atkinson,
		ToeplitzBounded,
		sequence_hilbert.WeightedHilbert,
		bounded_operator.BoundedAgreeDense,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀f:(real → complex).",
			Hypotheses: []string{"circle_symbol(f)", "∀t:real. f(t) ≠ complex_of_real(&0)"},
			Conclusion: "fredholm_operator(hardy_sequence_module, " +
				"    hardy_sequence_inner, " +
				"    hardy_sequence_module, " +
				"    hardy_sequence_inner, " +
				"    toeplitz_operator(f))",
		},
		"The reciprocal symbol is continuous, and its Toeplitz operator "+
			"is a two-sided inverse modulo the compact semicommutators."),
})}

var ShiftIndex = shiftIndexThm{family.Add(registry.ProofEntry{
	Name: "ShiftIndex",
	Key:  "prop_7d25ffa336a8e5b",
	Deps: []registry.EntryLike{
		ToeplitzBounded,
		path_integral.CircleCharacterIntegral,
		sequence_hilbert.WeightedHilbert,
		sequence_hilbert.SumReindex,
		sequence_hilbert.NormSquaredFiniteSup,
		bounded_operator.BoundedAgreeDense,
	},
	Build: family.Card(
		"fredholm_operator(hardy_sequence_module, "+
			"    hardy_sequence_inner, "+
			"    hardy_sequence_module, "+
			"    hardy_sequence_inner, "+
			"    unilateral_shift) ∧ "+
			"fredholm_index(hardy_sequence_module, "+
			"    hardy_sequence_module, "+
			"    hardy_sequence_inner, "+
			"    unilateral_shift) = "+
			"-int_of_num(1) ∧ "+
			"(∀u:(num → complex). "+
			"    u ∈ hardy_sequence_module.carrier ⇒ "+
			"    toeplitz_operator(λt:real. complex_exp(complex_i * complex_of_real(t)), u) = "+
			"    unilateral_shift(u))",
		"The shift has zero kernel and range the sequences with zeroth "+
			"coordinate zero, whose orthogonal complement is one dimensional."),
})}

var LoopWindingInteger = loopWindingIntegerThm{family.Add(registry.ProofEntry{
	Name: "LoopWindingInteger",
	Key:  "prop_fe702b06e40b7fab",
	Deps: []registry.EntryLike{
		path_integral.ComplexNewtonLeibnizOffFinite,
		path_integral.PathIntegrable,
		path_integral.PathDerivativeCompose,
		real_integral.IntegralDerivative,
		complex_power_series.ExpDerivative,
		real_trigonometry.CosOneSinZeroIff,
	},
	Build: family.Card(
		Statement{
			Binders: "∀f d:(real → complex).",
			Hypotheses: []string{
				"circle_symbol(f)",
				"piecewise_smooth_path(f, d, &0, &2 * pi)",
				"∀t:real. f(t) ≠ complex_of_real(&0)",
			},
			Conclusion: "complex_of_real(real_of_int(circle_winding_number(f, d))) = " +
				"winding_index(f, d, &0, &2 * pi, complex_of_real(&0))",
		},
		"Lift the argument continuously along the interval and integrate its piecewise derivative; "+
			"endpoint agreement makes the total argument increment an integer multiple of 2π."),
})}

var SymbolHomotopyToPower = symbolHomotopyToPowerThm{family.Add(registry.ProofEntry{
	Name: "SymbolHomotopyToPower",
	Key:  "prop_90c5e62b2869012d",
	Deps: []registry.EntryLike{
		LoopWindingInteger,
		covering_space.PathLifting,
		circle.CircleCovering,
		real_continuous.ExtremeValueMax,
	},
	Build: family.Card(
		Statement{
			Binders: "∀f d:(real → complex).",
			Hypotheses: []string{
				"circle_symbol(f)",
				"piecewise_smooth_path(f, d, &0, &2 * pi)",
				"∀t:real. f(t) ≠ complex_of_real(&0)",
			},
			Conclusion: "∃F:(real → real → complex). " +
				"    circle_symbol_homotopy(F) ∧ " +
				"    F(&0) = f ∧ " +
				"    F(&1) = " +
				"    (λt:real. " +
				"        complex_exp(complex_i * complex_of_real(real_of_int(circle_winding_number(f, d)) * t)))",
		},
		"Remove the positive modulus and contract the periodic part "+
			"of a lifted argument, leaving only its integer winding slope."),
})}

var ToeplitzIndex = toeplitzIndexThm{family.Add(registry.ProofEntry{
	Name: "ToeplitzIndex",
	Key:  "prop_9e9744f5bf071968",
	Deps: []registry.EntryLike{
		NonvanishingFredholm,
		SymbolHomotopyToPower,
		ToeplitzNormContinuity,
		ShiftIndex,
		fredholm.IndexHomotopy,
		fredholm.IndexComposition,
		CompactSemicommutator,
		ToeplitzBounded,
		fredholm.CompactPerturbation,
	},
	Reading: "The supplied d is constrained by piecewise_smooth_path, so it is " +
		"the velocity away from finitely many break points. The index sign is kernel " +
		"dimension minus cokernel dimension; exp(it) has winding +1 and index −1.",
	Build: family.Card(
		Statement{
			Binders: "∀f d:(real → complex).",
			Hypotheses: []string{
				"circle_symbol(f)",
				"piecewise_smooth_path(f, d, &0, &2 * pi)",
				"∀t:real. f(t) ≠ complex_of_real(&0)",
			},
			Conclusion: "fredholm_operator(hardy_sequence_module, " +
				"    hardy_sequence_inner, " +
				"    hardy_sequence_module, " +
				"    hardy_sequence_inner, " +
				"    toeplitz_operator(f)) ∧ " +
				"fredholm_index(hardy_sequence_module, " +
				"    hardy_sequence_module, " +
				"    hardy_sequence_inner, " +
				"    toeplitz_operator(f)) = " +
				"-circle_winding_number(f, d)",
		},
		"The nonvanishing-symbol homotopy gives a Fredholm operator-norm homotopy to an integer power of "+
			"the shift symbol; composition additivity and the shift calculation give the negative winding."),
})}
