package hilbert_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/registry"
)

var CauchySchwarz = cauchySchwarzThm{family.Add(registry.ProofEntry{
	Name: "CauchySchwarz",
	Key:  "prop_f930f6e2ac37e79",
	Reading: "Only the semidefinite laws are assumed, so the inequality also holds " +
		"for a form with null vectors, which it then makes orthogonal to everything.",
	Build: family.Card(
		SemiInnerDef.Statement(Statement{
			Binders:    "∀x y:A.",
			Hypotheses: []string{"x ∈ M.carrier", "y ∈ M.carrier"},
			Conclusion: "|p(x, y)| ≤ hilbert_norm(p, x) * hilbert_norm(p, y)",
		}),
		"For every complex t the real part of p(x − t y, x − t y) is nonnegative. Take t a "+
			"unit multiple of a real s that turns the cross term into −2s|p(x, y)|; the resulting "+
			"real quadratic in s is nonnegative, so its discriminant is not positive. A zero "+
			"leading coefficient forces p(x, y) = 0 by the same quadratic, now linear in s."),
})}

var InnerProductNorm = innerProductNormThm{family.Add(registry.ProofEntry{
	Name: "InnerProductNorm",
	Key:  "prop_1135bb003995f661",
	Deps: []registry.EntryLike{CauchySchwarz},
	Build: family.Card(
		InnerProductSpace.Statement("complex_normed_space(M, hilbert_norm(p))"),
		"Cauchy–Schwarz supplies the triangle inequality; "+
			"positivity and homogeneity give the other norm axioms."),
})}

var ClosedSubspace = closedSubspaceThm{family.Add(registry.ProofEntry{
	Name: "ClosedSubspace",
	Key:  "prop_85c79e073ae2325a",
	Deps: []registry.EntryLike{NormMetric, InnerProductNorm, complete_metric.ClosedComplete},
	Build: family.Card(
		HilbertSpace.Statement(Statement{
			Binders: "∀S:set(A).",
			Hypotheses: []string{
				"submodule(complex_ring, M, S)",
				"closed_in(norm_topology(M, hilbert_norm(p)), S)",
			},
			Conclusion: "complex_hilbert_space(restrict_module(M, S), p)",
		}),
		"A Cauchy sequence in the subspace converges in the ambient "+
			"Hilbert space, and closedness keeps its limit in the subspace."),
})}

var OrthogonalDecomposition = orthogonalDecompositionThm{family.Add(registry.ProofEntry{
	Name: "OrthogonalDecomposition",
	Key:  "prop_1bbcc1ebf6fdb9e1",
	Deps: []registry.EntryLike{ClosedSubspace, InnerProductNorm},
	Build: family.Card(
		HilbertSpace.Statement(Statement{
			Binders: "∀S:set(A). ∀x:A.",
			Hypotheses: []string{
				"submodule(complex_ring, M, S)",
				"closed_in(norm_topology(M, hilbert_norm(p)), S)",
				"x ∈ M.carrier",
			},
			Conclusion: "hilbert_projection(M, p, S, x) ∈ S ∧ " +
				"M.add(x, M.neg(hilbert_projection(M, p, S, x))) ∈ hilbert_complement(M, p, S)",
		}),
		"A minimizing sequence for the distance to S is Cauchy by the parallelogram "+
			"identity; its limit is the unique perpendicular decomposition."),
})}

var ProjectionLinearContraction = projectionLinearContractionThm{family.Add(registry.ProofEntry{
	Name: "ProjectionLinearContraction",
	Key:  "prop_74f2cad567afc5cc",
	Deps: []registry.EntryLike{OrthogonalDecomposition},
	Build: family.Card(
		HilbertSpace.Statement(Statement{
			Binders: "∀S:set(A).",
			Hypotheses: []string{
				"submodule(complex_ring, M, S)",
				"closed_in(norm_topology(M, hilbert_norm(p)), S)",
			},
			Conclusion: "module_homomorphism(complex_ring, M, M, hilbert_projection(M, p, S)) ∧ " +
				"(∀x:A. x ∈ M.carrier ⇒ hilbert_norm(p, hilbert_projection(M, p, S, x)) ≤ hilbert_norm(p, x))",
		}),
		"Uniqueness of orthogonal decomposition gives "+
			"linearity; Pythagoras gives the contraction estimate."),
})}

var OrthogonalComplementClosed = orthogonalComplementClosedThm{family.Add(registry.ProofEntry{
	Name: "OrthogonalComplementClosed",
	Key:  "prop_fb91589fe95c713a",
	Deps: []registry.EntryLike{CauchySchwarz},
	Build: family.Card(
		InnerProductSpace.Statement(Statement{
			Binders:    "∀S:set(A).",
			Hypotheses: []string{"S ⊆ M.carrier"},
			Conclusion: "submodule(complex_ring, M, hilbert_complement(M, p, S)) ∧ " +
				"closed_in(norm_topology(M, hilbert_norm(p)), hilbert_complement(M, p, S))",
		}),
		"The complement is the intersection of kernels of continuous inner-product functionals."),
})}

var FiniteDimensionalHeineBorel = finiteDimensionalHeineBorelThm{family.Add(registry.ProofEntry{
	Name: "FiniteDimensionalHeineBorel",
	Key:  "prop_ad631fbb6b8948f3",
	Deps: []registry.EntryLike{NormMetric, complete_metric.SequentialImpCompact},
	Reading: "The finite-dimensional submodule E carries S; M itself may " +
		"be infinite dimensional, and S is closed and bounded in the norm of M.",
	Build: family.Card(
		NormedSpace.Statement(Statement{
			Binders: "∀E S:set(A). ∀B:real.",
			Hypotheses: []string{
				"submodule(complex_ring, M, E)",
				"finite_dimensional(complex_ring, restrict_module(M, E))",
				"S ⊆ E",
				"closed_in(norm_topology(M, v), S)",
				"∀x:A. x ∈ S ⇒ v(x) ≤ B",
			},
			Conclusion: "compact_in(norm_topology(M, v), S)",
		}),
		"Write the vectors of E in a finite basis. The norm is at most a constant times the "+
			"largest coordinate modulus, and on the compact coordinate unit sphere it is bounded "+
			"below, so the coordinates of a bounded sequence in S are bounded. Bolzano–Weierstrass "+
			"in each coordinate gives a subsequence converging in the norm, and closedness keeps "+
			"its limit in S; sequential compactness in the metric space is compactness."),
})}

var FiniteDimensionalClosed = finiteDimensionalClosedThm{family.Add(registry.ProofEntry{
	Name: "FiniteDimensionalClosed",
	Key:  "prop_7747cdd7fdb667b3",
	Deps: []registry.EntryLike{FiniteDimensionalComplete, NormMetric, complete_metric.CompleteClosed},
	Build: family.Card(
		NormedSpace.Statement(Statement{
			Binders: "∀S:set(A).",
			Hypotheses: []string{
				"submodule(complex_ring, M, S)",
				"finite_dimensional(complex_ring, restrict_module(M, S))",
			},
			Conclusion: "closed_in(norm_topology(M, v), S)",
		}),
		"Compare the norm on a finite basis with the Euclidean coordinate "+
			"norm; a convergent coordinate sequence stays in its span."),
})}

var FiniteDimensionalComplete = finiteDimensionalCompleteThm{family.Add(registry.ProofEntry{
	Name: "FiniteDimensionalComplete",
	Key:  "prop_9c66683f96b5b106",
	Deps: []registry.EntryLike{FiniteDimensionalHeineBorel, NormMetric},
	Build: family.Card(
		NormedSpace.Statement(Statement{
			Binders:    "",
			Hypotheses: []string{"finite_dimensional(complex_ring, M)"},
			Conclusion: "complex_banach_space(M, v)",
		}),
		"A finite basis identifies the space with finite dimensional "+
			"complex Euclidean space with an equivalent norm."),
})}

var ProductHilbert = productHilbertThm{family.Add(registry.ProofEntry{
	Name: "ProductHilbert",
	Key:  "prop_df45625c4da34bbe",
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀N:module_ops(complex, B). " +
				"∀p:(A → A → complex). " +
				"∀q:(B → B → complex).",
			Hypotheses: []string{"complex_hilbert_space(M, p)", "complex_hilbert_space(N, q)"},
			Conclusion: "complex_hilbert_space(product_module(M, N), direct_sum_inner(p, q))",
		},
		"The product norm squared is the sum of the two norm squares; completeness follows componentwise."),
})}
