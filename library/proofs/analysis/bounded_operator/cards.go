package bounded_operator

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/hom_module"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	"github.com/euc-ai/xugo/library/proofs/topology/compact"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/proofs/topology/continuous"
	"github.com/euc-ai/xugo/library/proofs/topology/metric_space"
	"github.com/euc-ai/xugo/library/proofs/topology/product_topology"
	"github.com/euc-ai/xugo/library/registry"
)

var OperatorNormBound = operatorNormBoundThm{family.Add(registry.ProofEntry{
	Name: "OperatorNormBound",
	Key:  "prop_d2f15d064174a622",
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀N:module_ops(complex, B). " +
				"∀v:(A → real). " +
				"∀w:(B → real). " +
				"∀T:(A → B).",
			Hypotheses: []string{
				"complex_normed_space(M, v)",
				"complex_normed_space(N, w)",
				"bounded_operator(M, v, N, w, T)",
			},
			Conclusion: "&0 ≤ bounded_op_norm(M, v, w, T) ∧ " +
				"(∀x:A. x ∈ M.carrier ⇒ w(T(x)) ≤ bounded_op_norm(M, v, w, T) * v(x))",
		},
		"Scale nonzero vectors into the unit ball; the zero "+
			"vector also shows the supremum set is nonempty."),
})}

var BoundedIffContinuous = boundedIffContinuousThm{family.Add(registry.ProofEntry{
	Name: "BoundedIffContinuous",
	Key:  "prop_affb2350fa564bd5",
	Deps: []registry.EntryLike{hilbert_space.NormMetric, metric_space.ContinuousMapIff},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀N:module_ops(complex, B). " +
				"∀v:(A → real). " +
				"∀w:(B → real). " +
				"∀T:(A → B).",
			Hypotheses: []string{
				"complex_normed_space(M, v)",
				"complex_normed_space(N, w)",
				"module_homomorphism(complex_ring, M, N, T)",
			},
			Conclusion: "bounded_operator(M, v, N, w, T) ⇔ " +
				"continuous_map(norm_topology(M, v), norm_topology(N, w), T)",
		},
		"Continuity at zero gives a bound by rescaling, and a norm bound gives continuity everywhere."),
})}

var OperatorSpaceBanach = operatorSpaceBanachThm{family.Add(registry.ProofEntry{
	Name: "OperatorSpaceBanach",
	Key:  "prop_b986a089969e6b57",
	Deps: []registry.EntryLike{
		OperatorNormBound,
		hilbert_space.NormMetric,
		hom_module.HomSetModuleOn,
		complete_metric.LimitUnique,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀M:module_ops(complex, A). ∀N:module_ops(complex, B). ∀v:(A → real). ∀w:(B → real).",
			Hypotheses: []string{"complex_normed_space(M, v)", "complex_banach_space(N, w)"},
			Conclusion: "complex_banach_space(operator_module(M, v, N, w), bounded_op_norm(M, v, w))",
		},
		"An operator-norm Cauchy sequence has pointwise limits in "+
			"the target; uniform bounds and linearity pass to the limit."),
})}

var BoundedExtension = boundedExtensionThm{family.Add(registry.ProofEntry{
	Name: "BoundedExtension",
	Key:  "prop_df9fb77158263296",
	Deps: []registry.EntryLike{hilbert_space.NormMetric, complete_metric.ClosureIffSequential},
	Reading: "The dense set is a submodule and the map is linear on it; " +
		"completeness is needed only in the target, where the Cauchy images converge.",
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀N:module_ops(complex, B). " +
				"∀v:(A → real). " +
				"∀w:(B → real). " +
				"∀D:set(A). " +
				"∀T:(A → B). " +
				"∀C:real.",
			Hypotheses: []string{
				"complex_normed_space(M, v)",
				"complex_banach_space(N, w)",
				"submodule(complex_ring, M, D)",
				"closure(norm_topology(M, v), D) = M.carrier",
				"module_homomorphism(complex_ring, restrict_module(M, D), N, T)",
				"∀x:A. x ∈ D ⇒ w(T(x)) ≤ C * v(x)",
			},
			Conclusion: "∃S:(A → B). " +
				"    bounded_operator(M, v, N, w, S) ∧ " +
				"    (∀x:A. x ∈ D ⇒ S(x) = T(x)) ∧ " +
				"    (∀x:A. x ∈ M.carrier ⇒ w(S(x)) ≤ C * v(x))",
		},
		"A vector of M is a limit of vectors of D; their images form a Cauchy sequence by "+
			"the bound, and its limit does not depend on the approximating sequence. Linearity "+
			"and the bound pass to the limit by continuity of the operations and of the norm."),
})}

var BoundedAgreeDense = boundedAgreeDenseThm{family.Add(registry.ProofEntry{
	Name: "BoundedAgreeDense",
	Key:  "prop_fc370595036368b7",
	Deps: []registry.EntryLike{BoundedIffContinuous, hilbert_space.NormMetric},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀N:module_ops(complex, B). " +
				"∀v:(A → real). " +
				"∀w:(B → real). " +
				"∀D:set(A). " +
				"∀S T:(A → B). " +
				"∀x:A.",
			Hypotheses: []string{
				"complex_normed_space(M, v)",
				"complex_normed_space(N, w)",
				"bounded_operator(M, v, N, w, S)",
				"bounded_operator(M, v, N, w, T)",
				"D ⊆ M.carrier",
				"closure(norm_topology(M, v), D) = M.carrier",
				"∀y:A. y ∈ D ⇒ S(y) = T(y)",
				"x ∈ M.carrier",
			},
			Conclusion: "S(x) = T(x)",
		},
		"The difference of the two operators is bounded, hence continuous, and vanishes "+
			"on D; its zero set is closed and contains D, so it contains the closure of D."),
})}

var NeumannInverse = neumannInverseThm{family.Add(registry.ProofEntry{
	Name: "NeumannInverse",
	Key:  "prop_faecec0a9a908987",
	Deps: []registry.EntryLike{
		OperatorNormBound,
		hilbert_space.NormMetric,
		complete_metric.BanachFixedPoint,
	},
	Reading: "This is the openness of the invertible operators at the identity; a small perturbation " +
		"of any operator with a bounded inverse reduces to it by composing with that inverse.",
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). ∀v:(A → real). ∀E:(A → A).",
			Hypotheses: []string{
				"complex_banach_space(M, v)",
				"bounded_operator(M, v, M, v, E)",
				"bounded_op_norm(M, v, v, E) < &1",
			},
			Conclusion: "injective_on(M.carrier, λx:A. M.add(x, E(x))) ∧ " +
				"image(λx:A. M.add(x, E(x)), M.carrier) = M.carrier ∧ " +
				"bounded_operator(M, v, M, v, inverse_on(M.carrier, λx:A. M.add(x, E(x))))",
		},
		"With q the operator norm of E, the map z ↦ y − E(z) is a contraction of the complete space "+
			"with constant q, so x + E(x) = y has exactly one solution; it is the limit of the partial "+
			"sums of the Neumann series, of norm at most v(y) / (1 − q), and depends linearly on y."),
})}

var BoundedInverse = boundedInverseThm{family.Add(registry.ProofEntry{
	Name: "BoundedInverse",
	Key:  "prop_b4d90d716693144f",
	Deps: []registry.EntryLike{
		complete_metric.BaireCategory,
		complete_metric.GeometricStepsCauchy,
		BoundedIffContinuous,
		hilbert_space.NormMetric,
	},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀N:module_ops(complex, B). " +
				"∀v:(A → real). " +
				"∀w:(B → real). " +
				"∀T:(A → B).",
			Hypotheses: []string{
				"complex_banach_space(M, v)",
				"complex_banach_space(N, w)",
				"bounded_operator(M, v, N, w, T)",
				"injective_on(M.carrier, T)",
				"image(T, M.carrier) = N.carrier",
			},
			Conclusion: "bounded_operator(N, w, M, v, inverse_on(M.carrier, T))",
		},
		"The Baire-category open mapping argument sends a source ball "+
			"onto a target neighbourhood; rescaling bounds the inverse."),
})}

var RieszRepresentation = rieszRepresentationThm{family.Add(registry.ProofEntry{
	Name: "RieszRepresentation",
	Key:  "prop_20f53a58154dfc0b",
	Deps: []registry.EntryLike{hilbert_space.OrthogonalDecomposition},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). ∀p:(A → A → complex). ∀f:(A → complex).",
			Hypotheses: []string{
				"complex_hilbert_space(M, p)",
				"bounded_operator(M, hilbert_norm(p), regular_module(complex_ring), complex_abs, f)",
			},
			Conclusion: "∃!y:A. y ∈ M.carrier ∧ ∀x:A. x ∈ M.carrier ⇒ f(x) = p(x, y)",
		},
		"Represent the zero functional by the zero vector. For a nonzero functional, "+
			"project onto its kernel and normalize the one-dimensional orthogonal complement."),
})}

var Adjoint = adjointThm{family.Add(registry.ProofEntry{
	Name: "Adjoint",
	Key:  "prop_10380007bc71ec80",
	Deps: []registry.EntryLike{
		RieszRepresentation,
		hilbert_space.CauchySchwarz,
		hilbert_space.InnerProductNorm,
		OperatorNormBound,
	},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀p:(A → A → complex). " +
				"∀N:module_ops(complex, B). " +
				"∀q:(B → B → complex). " +
				"∀T:(A → B).",
			Hypotheses: []string{
				"complex_hilbert_space(M, p)",
				"complex_hilbert_space(N, q)",
				"bounded_operator(M, hilbert_norm(p), N, hilbert_norm(q), T)",
			},
			Conclusion: "bounded_operator(N, " +
				"    hilbert_norm(q), " +
				"    M, " +
				"    hilbert_norm(p), " +
				"    hilbert_adjoint(M, p, N, q, T)) ∧ " +
				"(∀x:A. ∀y:B. " +
				"    x ∈ M.carrier ∧ y ∈ N.carrier ⇒ q(T(x), y) = p(x, hilbert_adjoint(M, p, N, q, T, y))) ∧ " +
				"bounded_op_norm(N, hilbert_norm(q), hilbert_norm(p), hilbert_adjoint(M, p, N, q, T)) = " +
				"bounded_op_norm(M, hilbert_norm(p), hilbert_norm(q), T)",
		},
		"Apply Riesz representation to each target vector, then "+
			"use dual norm estimates to identify the operator norms."),
})}

var FiniteRankCompact = finiteRankCompactThm{family.Add(registry.ProofEntry{
	Name: "FiniteRankCompact",
	Key:  "prop_a7ac036309700b4a",
	Deps: []registry.EntryLike{
		hilbert_space.FiniteDimensionalClosed,
		hilbert_space.FiniteDimensionalHeineBorel,
		hilbert_space.NormMetric,
	},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀N:module_ops(complex, B). " +
				"∀v:(A → real). " +
				"∀w:(B → real). " +
				"∀T:(A → B).",
			Hypotheses: []string{
				"complex_normed_space(M, v)",
				"complex_normed_space(N, w)",
				"bounded_operator(M, v, N, w, T)",
				"finite_rank_operator(M, N, T)",
			},
			Conclusion: "compact_operator(M, v, N, w, T)",
		},
		"The image of the unit ball is bounded in a finite dimensional "+
			"closed subspace, whose closed bounded sets are compact."),
})}

var CompactNormLimit = compactNormLimitThm{family.Add(registry.ProofEntry{
	Name: "CompactNormLimit",
	Key:  "prop_c37af93100bc085d",
	Deps: []registry.EntryLike{
		OperatorNormBound,
		hilbert_space.NormMetric,
		complete_metric.CompactCompleteTotallyBounded,
		complete_metric.TotallyBoundedSequential,
		complete_metric.ClosedComplete,
	},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀N:module_ops(complex, B). " +
				"∀v:(A → real). " +
				"∀w:(B → real). " +
				"∀T:(A → B). " +
				"∀K:(num → A → B).",
			Hypotheses: []string{
				"complex_normed_space(M, v)",
				"complex_banach_space(N, w)",
				"bounded_operator(M, v, N, w, T)",
				"∀j:num. compact_operator(M, v, N, w, K(j))",
				"∀ε:real. " +
					"    &0 < ε ⇒ " +
					"    ∃J:num. ∀j:num. J ≤ j ⇒ bounded_op_norm(M, v, w, λx:A. N.add(T(x), N.neg(K(j, x)))) < ε",
			},
			Conclusion: "compact_operator(M, v, N, w, T)",
		},
		"Approximate the image of the unit ball by a totally bounded compact image; "+
			"target completeness turns total boundedness of the closure into compactness."),
})}

var CompactAdd = compactAddThm{family.Add(registry.ProofEntry{
	Name: "CompactAdd",
	Key:  "prop_ceef76d3ed129d31",
	Deps: []registry.EntryLike{
		hilbert_space.NormMetric,
		product_topology.CompactProduct,
		continuous.ImageCompact,
		compact.ClosedSubsetCompact,
		metric_space.MetricHausdorff,
	},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀N:module_ops(complex, B). " +
				"∀v:(A → real). " +
				"∀w:(B → real). " +
				"∀S T:(A → B).",
			Hypotheses: []string{
				"complex_normed_space(M, v)",
				"complex_normed_space(N, w)",
				"compact_operator(M, v, N, w, S)",
				"compact_operator(M, v, N, w, T)",
			},
			Conclusion: "compact_operator(M, v, N, w, λx:A. N.add(S(x), T(x)))",
		},
		"The sum of two relatively compact sets is relatively "+
			"compact, by continuity of addition on their compact closures."),
})}

var CompactIdeal = compactIdealThm{family.Add(registry.ProofEntry{
	Name: "CompactIdeal",
	Key:  "prop_6036fb26016eab86",
	Deps: []registry.EntryLike{
		BoundedIffContinuous,
		hilbert_space.NormMetric,
		continuous.ImageCompact,
		compact.ClosedSubsetCompact,
	},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀N:module_ops(complex, B). " +
				"∀v:(A → real). " +
				"∀w:(B → real). " +
				"∀P:module_ops(complex, C). " +
				"∀z:(C → real). " +
				"∀S:(A → B). " +
				"∀T:(B → C).",
			Hypotheses: []string{
				"complex_normed_space(M, v)",
				"complex_normed_space(N, w)",
				"complex_normed_space(P, z)",
				"bounded_operator(M, v, N, w, S)",
				"bounded_operator(N, w, P, z, T)",
				"compact_operator(M, v, N, w, S) ∨ compact_operator(N, w, P, z, T)",
			},
			Conclusion: "compact_operator(M, v, P, z, T ∘ S)",
		},
		"A bounded map sends the source unit ball to a bounded ball, and a "+
			"continuous map preserves relative compactness of compact closures."),
})}

var CompactAdjoint = compactAdjointThm{family.Add(registry.ProofEntry{
	Name: "CompactAdjoint",
	Key:  "prop_2a290eafa7fd58e1",
	Deps: []registry.EntryLike{
		Adjoint,
		CompactApproximation,
		CompactNormLimit,
		FiniteRankCompact,
		hilbert_space.InnerProductNorm,
		hilbert_space.OrthogonalDecomposition,
		hilbert_space.FiniteDimensionalClosed,
	},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀p:(A → A → complex). " +
				"∀N:module_ops(complex, B). " +
				"∀q:(B → B → complex). " +
				"∀T:(A → B).",
			Hypotheses: []string{
				"complex_hilbert_space(M, p)",
				"complex_hilbert_space(N, q)",
				"bounded_operator(M, hilbert_norm(p), N, hilbert_norm(q), T)",
				"compact_operator(M, hilbert_norm(p), N, hilbert_norm(q), T)",
			},
			Conclusion: "compact_operator(N, " +
				"    hilbert_norm(q), " +
				"    M, " +
				"    hilbert_norm(p), " +
				"    hilbert_adjoint(M, p, N, q, T))",
		},
		"Approximate a compact Hilbert-space operator by finite-dimensional "+
			"orthogonal range projections, then pass to adjoints in operator norm."),
})}

var CompactApproximation = compactApproximationThm{family.Add(registry.ProofEntry{
	Name: "CompactApproximation",
	Key:  "prop_50468adf0c4b156b",
	Deps: []registry.EntryLike{
		hilbert_space.ProjectionLinearContraction,
		hilbert_space.FiniteDimensionalClosed,
		hilbert_space.OrthogonalDecomposition,
		hilbert_space.InnerProductNorm,
		complete_metric.CompactCompleteTotallyBounded,
		module_dimension.FiniteDimensionalSpanning,
	},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀p:(A → A → complex). " +
				"∀N:module_ops(complex, B). " +
				"∀q:(B → B → complex). " +
				"∀T:(A → B). " +
				"∀ε:real.",
			Hypotheses: []string{"&0 < ε",
				"complex_hilbert_space(M, p)",
				"complex_hilbert_space(N, q)",
				"bounded_operator(M, hilbert_norm(p), N, hilbert_norm(q), T)",
				"compact_operator(M, hilbert_norm(p), N, hilbert_norm(q), T)",
			},
			Conclusion: "∃F:(A → B). " +
				"    bounded_operator(M, hilbert_norm(p), N, hilbert_norm(q), F) ∧ " +
				"    finite_rank_operator(M, N, F) ∧ " +
				"    bounded_op_norm(M, hilbert_norm(p), hilbert_norm(q), λx:A. N.add(T(x), N.neg(F(x)))) < ε",
		},
		"Cover the compact image of the unit ball by finitely many "+
			"small balls and project onto the span of their centres."),
})}
