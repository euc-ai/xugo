package definable_andre_quillen

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/cotangent/cotangent_complex"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/free_complex_duality"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/polish_cohomology"
	"github.com/euc-ai/xugo/library/registry"
)

var PolynomialResolutionDualPolish = polynomialResolutionDualPolishThm{family.Add(registry.ProofEntry{
	Name: "PolynomialResolutionDualPolish",
	Key:  "prop_ae4c3b562f9abf65",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X:(num → set(U)). " +
			"∀d s:(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀ε:(U → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"polynomial_resolution(R, X, d, s, S, f, ε)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"countable(N.carrier)",
			"∀n:num. countable(X(n))",
		},
		Conclusion: "polish_cochain_complex(T, «dual», dual_pointwise_topologies(N, X)) ∧ " +
			"(∀n:num. cohomology_cover(«dual», dual_pointwise_topologies(N, X), n))",
		Abbrev: Abbrev{
			{Name: "dual", Text: "free_dual_complex(T, " +
				"    N, " +
				"    differential_complex(R, X, d, T, λu:U. g(ε(u)), regular_module(T)), " +
				"    X, " +
				"    λn:num. λa:(U → C). a, " +
				"    λn:num. λa:(U → C). a)"},
		},
	},
		"DifferentialScalarBased supplies the name basis of the scalar differential "+
			"complex. Apply CountableBasedDualPolish and CohomologyHasPolishCover; the "+
			"standard resolution recovers the usual AQ model through CotangentDualAgreement."),
	Deps: []registry.EntryLike{
		cotangent_complex.DifferentialScalarBased,
		polish_cohomology.CountableBasedDualPolish,
		polish_cohomology.CohomologyHasPolishCover,
		cotangent_complex.CotangentDualAgreement,
	},
	Reading: "The coefficients and the name sets are countable; the ring and the host " +
		"type need not be. Coboundaries are the actual image, without taking its closure.",
})}

var ResolutionComparisonDefinableIso = resolutionComparisonDefinableIsoThm{family.Add(registry.ProofEntry{
	Name: "ResolutionComparisonDefinableIso",
	Key:  "prop_4b00c883e573e0dd",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀X Y:(num → set(U)). " +
			"∀d s d' s':(num → num → U → U). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀ε ε':(U → B). " +
			"∀F:(num → U → U). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D). " +
			"∀n:num.",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"polynomial_resolution(R, X, d, s, S, f, ε)",
			"polynomial_resolution(R, Y, d', s', S, f, ε')",
			"simplicial_algebra_map(R, X, d, s, Y, d', s', F)",
			"∀u:U. u ∈ universe_algebra(R, X(0)) ⇒ ε'(F(0, u)) = ε(u)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"countable(N.carrier)",
			"∀k:num. countable(X(k)) ∧ countable(Y(k))",
		},
		Conclusion: "polish_cochain_map(T, " +
			"    «targetDual», " +
			"    dual_pointwise_topologies(N, Y), " +
			"    «sourceDual», " +
			"    dual_pointwise_topologies(N, X), " +
			"    «transpose») ∧ " +
			"cohomology_borel_iso(«targetDual», " +
			"    dual_pointwise_topologies(N, Y), " +
			"    n, " +
			"    «sourceDual», " +
			"    dual_pointwise_topologies(N, X), " +
			"    n, " +
			"    cohomology_map(«sourceDual», «transpose», n))",
		Abbrev: Abbrev{
			{Name: "sourceDual", Text: "free_dual_complex(T, " +
				"    N, " +
				"    differential_complex(R, X, d, T, λu:U. g(ε(u)), regular_module(T)), " +
				"    X, " +
				"    λk:num. λa:(U → C). a, " +
				"    λk:num. λa:(U → C). a)"},
			{Name: "targetDual", Text: "free_dual_complex(T, " +
				"    N, " +
				"    differential_complex(R, Y, d', T, λu:U. g(ε'(u)), regular_module(T)), " +
				"    Y, " +
				"    λk:num. λa:(U → C). a, " +
				"    λk:num. λa:(U → C). a)"},
			{Name: "transpose", Text: "free_dual_map(T, " +
				"    N, " +
				"    X, " +
				"    λk:num. λa:(U → C). a, " +
				"    λk:num. λa:(U → C). a, " +
				"    differential_map(R, X, Y, d', λu:U. g(ε'(u)), F, regular_module(T)))"},
		},
	},
		"ResolutionMapChainHomotopyEquivalence supplies an inverse comparison over the "+
			"identity. DifferentialScalarBased, BasedDualMapContinuous and "+
			"FreeDualHomotopyEquivalence transpose it to a continuous cochain homotopy "+
			"equivalence; HomotopyEquivalenceDefinableIso gives the Borel inverse on cohomology."),
	Deps: []registry.EntryLike{
		PolynomialResolutionDualPolish,
		cotangent_complex.DifferentialScalarBased,
		cotangent_complex.ResolutionMapChainHomotopyEquivalence,
		polish_cohomology.BasedDualMapContinuous,
		free_complex_duality.FreeDualHomotopyEquivalence,
		polish_cohomology.HomotopyEquivalenceDefinableIso,
	},
	Reading: "The specified simplicial map must cover the identity of S. The transpose " +
		"runs from Y to X; the homotopies are algebraic and need not be continuous.",
})}

var AQScalarPolishModel = aQScalarPolishModelThm{family.Add(registry.ProofEntry{
	Name: "AQScalarPolishModel",
	Key:  "prop_a3c90e6276adbd4b",
	Build: family.Card(Statement{
		Binders: "∀R:ring_ops(A). " +
			"∀S:ring_ops(B). " +
			"∀f:(A → B). " +
			"∀T:ring_ops(C). " +
			"∀g:(B → C). " +
			"∀N:module_ops(C, D).",
		Hypotheses: []string{
			"cotangent_universe(R, 𝕌⟨A:U⟩)",
			"cotangent_universe(S, 𝕌⟨A:U⟩)",
			"ring_homomorphism(R, S, f)",
			"ring_homomorphism(S, T, g)",
			"module_on(T, N)",
			"countable(R.carrier)",
			"countable(S.carrier)",
			"countable(N.carrier)",
		},
		Conclusion: "polish_cochain_complex(T, " +
			"    cotangent_cochain⟨U:U⟩(R, S, f, T, g, N), " +
			"    dual_pointwise_topologies(N, standard_names(R, S)))",
	},
		"Apply CountableBasedDualPolish to CotangentScalarBased using "+
			"StandardNamesCountable. CotangentDualAgreement identifies the degree carriers, "+
			"operations and differentials on the carriers with the existing cotangent cochains."),
	Deps: []registry.EntryLike{
		StandardNamesCountable,
		cotangent_complex.CotangentScalarBased,
		cotangent_complex.CotangentDualAgreement,
		polish_cohomology.CountableBasedDualPolish,
	},
	Reading: "Coefficients live over T while names come from S over R. T need " +
		"not be countable; the two host-capacity hypotheses are stated explicitly.",
})}
