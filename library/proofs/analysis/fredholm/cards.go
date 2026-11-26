package fredholm

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	"github.com/euc-ai/xugo/library/proofs/analysis/bounded_operator"
	"github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/topology/complete_metric"
	"github.com/euc-ai/xugo/library/registry"
)

var Atkinson = atkinsonThm{family.Add(registry.ProofEntry{
	Name: "Atkinson",
	Key:  "prop_b79578c231f3bd08",
	Deps: []registry.EntryLike{
		bounded_operator.BoundedInverse,
		hilbert_space.OrthogonalDecomposition,
		bounded_operator.CompactAdjoint,
		bounded_operator.FiniteRankCompact,
		bounded_operator.Adjoint,
		hilbert_space.ProjectionLinearContraction,
		hilbert_space.ClosedSubspace,
		hilbert_space.OrthogonalComplementClosed,
		hilbert_space.FiniteDimensionalClosed,
		hilbert_space.InnerProductNorm,
		complete_metric.CompactImpSequential,
		module_dimension.SubmoduleDim,
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
			Conclusion: "fredholm_operator(M, p, N, q, T) ⇔ ∃S:(B → A). fredholm_parametrix(M, p, N, q, T, S)",
		},
		"Split kernel and image orthogonally to construct a parametrix; conversely "+
			"compactness excludes an infinite orthonormal kernel and yields a lower bound "+
			"off a finite dimensional subspace, hence closed image and finite cokernel."),
})}

var FredholmOpenIndexLocallyConstant = fredholmOpenIndexLocallyConstantThm{family.Add(registry.ProofEntry{
	Name: "FredholmOpenIndexLocallyConstant",
	Key:  "prop_156bf406847aa639",
	Deps: []registry.EntryLike{
		Atkinson,
		bounded_operator.NeumannInverse,
		bounded_operator.BoundedInverse,
		bounded_operator.FiniteRankCompact,
		bounded_operator.OperatorNormBound,
		hilbert_space.OrthogonalDecomposition,
		hilbert_space.ProjectionLinearContraction,
		hilbert_space.ClosedSubspace,
		module_dimension.RankNullity,
	},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀p:(A → A → complex). " +
				"∀N:module_ops(complex, B). " +
				"∀q:(B → B → complex). " +
				"∀T:(A → B).",
			Hypotheses: []string{"fredholm_operator(M, p, N, q, T)"},
			Conclusion: "∃ε:real. " +
				"    &0 < ε ∧ " +
				"    ∀S:(A → B). " +
				"        bounded_operator(M, hilbert_norm(p), N, hilbert_norm(q), S) ∧ " +
				"        bounded_op_norm(M, hilbert_norm(p), hilbert_norm(q), λx:A. N.add(S(x), N.neg(T(x)))) < " +
				"        ε ⇒ " +
				"        fredholm_operator(M, p, N, q, S) ∧ " +
				"        fredholm_index(M, N, q, S) = fredholm_index(M, N, q, T)",
		},
		"Split into the invertible block and finite dimensional kernel/cokernel blocks; a small "+
			"perturbation keeps the infinite block invertible and leaves the dimension difference unchanged."),
})}

var CompactPerturbation = compactPerturbationThm{family.Add(registry.ProofEntry{
	Name: "CompactPerturbation",
	Key:  "prop_ec9f1c57fba9413",
	Deps: []registry.EntryLike{
		Atkinson,
		FredholmOpenIndexLocallyConstant,
		bounded_operator.CompactIdeal,
		IndexHomotopy,
		bounded_operator.CompactAdd,
		bounded_operator.OperatorNormBound,
	},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀p:(A → A → complex). " +
				"∀N:module_ops(complex, B). " +
				"∀q:(B → B → complex). " +
				"∀T K:(A → B).",
			Hypotheses: []string{
				"fredholm_operator(M, p, N, q, T)",
				"compact_operator(M, hilbert_norm(p), N, hilbert_norm(q), K)",
			},
			Conclusion: "fredholm_operator(M, p, N, q, λx:A. N.add(T(x), K(x))) ∧ " +
				"fredholm_index(M, N, q, λx:A. N.add(T(x), K(x))) = fredholm_index(M, N, q, T)",
		},
		"Atkinson keeps T plus tK Fredholm for every real t; "+
			"local constancy along the interval fixes the index."),
})}

var IndexComposition = indexCompositionThm{family.Add(registry.ProofEntry{
	Name: "IndexComposition",
	Key:  "prop_b5c9a3eac6239fb4",
	Deps: []registry.EntryLike{
		Atkinson,
		bounded_operator.CompactIdeal,
		bounded_operator.CompactAdd,
		hilbert_space.OrthogonalDecomposition,
		module_dimension.RankNullity,
	},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀p:(A → A → complex). " +
				"∀N:module_ops(complex, B). " +
				"∀q:(B → B → complex). " +
				"∀P:module_ops(complex, C). " +
				"∀r:(C → C → complex). " +
				"∀T:(A → B). " +
				"∀S:(B → C).",
			Hypotheses: []string{"fredholm_operator(M, p, N, q, T)", "fredholm_operator(N, q, P, r, S)"},
			Conclusion: "fredholm_operator(M, p, P, r, S ∘ T) ∧ " +
				"fredholm_index(M, P, r, S ∘ T) = fredholm_index(M, N, q, T) + fredholm_index(N, P, r, S)",
		},
		"Compose parametrices for Fredholmness; the six-term exact "+
			"kernel/cokernel sequence gives the dimension identity."),
})}

var IndexDirectSum = indexDirectSumThm{family.Add(registry.ProofEntry{
	Name: "IndexDirectSum",
	Key:  "prop_3f5c2556a3b48ea7",
	Deps: []registry.EntryLike{hilbert_space.ProductHilbert, module_dimension.DimProduct},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀p:(A → A → complex). " +
				"∀N:module_ops(complex, B). " +
				"∀q:(B → B → complex). " +
				"∀P:module_ops(complex, C). " +
				"∀r:(C → C → complex). " +
				"∀Q:module_ops(complex, D). " +
				"∀s:(D → D → complex). " +
				"∀T:(A → B). " +
				"∀S:(C → D).",
			Hypotheses: []string{"fredholm_operator(M, p, N, q, T)", "fredholm_operator(P, r, Q, s, S)"},
			Conclusion: "fredholm_operator(product_module(M, P), " +
				"    direct_sum_inner(p, r), " +
				"    product_module(N, Q), " +
				"    direct_sum_inner(q, s), " +
				"    λx:prod(A, C). (T(fst(x)), S(snd(x)))) ∧ " +
				"fredholm_index(product_module(M, P), " +
				"    product_module(N, Q), " +
				"    direct_sum_inner(q, s), " +
				"    λx:prod(A, C). (T(fst(x)), S(snd(x)))) = " +
				"fredholm_index(M, N, q, T) + fredholm_index(P, Q, s, S)",
		},
		"The kernel and orthogonal cokernel are the direct sums of the corresponding subspaces."),
})}

var IndexAdjoint = indexAdjointThm{family.Add(registry.ProofEntry{
	Name: "IndexAdjoint",
	Key:  "prop_9bf2b5ccca9c2271",
	Deps: []registry.EntryLike{
		bounded_operator.Adjoint,
		hilbert_space.OrthogonalDecomposition,
		bounded_operator.BoundedInverse,
		hilbert_space.ClosedSubspace,
		hilbert_space.OrthogonalComplementClosed,
		hilbert_space.FiniteDimensionalClosed,
	},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀p:(A → A → complex). " +
				"∀N:module_ops(complex, B). " +
				"∀q:(B → B → complex). " +
				"∀T:(A → B).",
			Hypotheses: []string{"fredholm_operator(M, p, N, q, T)"},
			Conclusion: "fredholm_operator(N, q, M, p, hilbert_adjoint(M, p, N, q, T)) ∧ " +
				"fredholm_index(N, M, p, hilbert_adjoint(M, p, N, q, T)) = -fredholm_index(M, N, q, T)",
		},
		"The closed range theorem identifies the kernel of the "+
			"adjoint with the orthogonal cokernel and conversely."),
})}

var IndexHomotopy = indexHomotopyThm{family.Add(registry.ProofEntry{
	Name: "IndexHomotopy",
	Key:  "prop_a6cec2de56cf4ad3",
	Deps: []registry.EntryLike{FredholmOpenIndexLocallyConstant, real_topology.IntervalConnected},
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀p:(A → A → complex). " +
				"∀N:module_ops(complex, B). " +
				"∀q:(B → B → complex). " +
				"∀F:(real → A → B).",
			Hypotheses: []string{
				"∀t:real. &0 ≤ t ∧ t ≤ &1 ⇒ fredholm_operator(M, p, N, q, F(t))",
				"∀t:real. " +
					"    &0 ≤ t ∧ t ≤ &1 ⇒ " +
					"    ∀ε:real. " +
					"        &0 < ε ⇒ " +
					"        ∃δ:real. " +
					"            &0 < δ ∧ " +
					"            ∀u:real. " +
					"                &0 ≤ u ∧ u ≤ &1 ∧ |u - t| < δ ⇒ " +
					"                bounded_op_norm(M, " +
					"                    hilbert_norm(p), " +
					"                    hilbert_norm(q), " +
					"                    λx:A. N.add(F(u, x), N.neg(F(t, x)))) < " +
					"                ε",
			},
			Conclusion: "fredholm_index(M, N, q, F(&0)) = fredholm_index(M, N, q, F(&1))",
		},
		"A locally constant integer-valued function on the connected interval is constant."),
})}

var FiniteDimensionalStabilization = finiteDimensionalStabilizationThm{family.Add(registry.ProofEntry{
	Name: "FiniteDimensionalStabilization",
	Key:  "prop_6adb6427a1b0e89f",
	Deps: []registry.EntryLike{
		FredholmOpenIndexLocallyConstant,
		bounded_operator.BoundedInverse,
		bounded_operator.NeumannInverse,
		bounded_operator.OperatorNormBound,
		hilbert_space.OrthogonalDecomposition,
		hilbert_space.ProductHilbert,
		hilbert_space.ClosedSubspace,
	},
	Reading: "The finite dimensional space E is fixed throughout the " +
		"neighbourhood. This controls the augmented kernels and makes no " +
		"assertion that the unstabilized kernels of S have constant dimension.",
	Build: family.Card(
		Statement{
			Binders: "∀M:module_ops(complex, A). " +
				"∀p:(A → A → complex). " +
				"∀N:module_ops(complex, B). " +
				"∀q:(B → B → complex). " +
				"∀T:(A → B).",
			Hypotheses: []string{"fredholm_operator(M, p, N, q, T)"},
			Conclusion: "∃E:set(B). " +
				"    submodule(complex_ring, N, E) ∧ " +
				"    finite_dimensional(complex_ring, restrict_module(N, E)) ∧ " +
				"    ∃ε:real. " +
				"        &0 < ε ∧ " +
				"        ∀S:(A → B). " +
				"            bounded_operator(M, hilbert_norm(p), N, hilbert_norm(q), S) ∧ " +
				"            bounded_op_norm(M, " +
				"                hilbert_norm(p), " +
				"                hilbert_norm(q), " +
				"                λx:A. N.add(S(x), N.neg(T(x)))) < " +
				"            ε ⇒ " +
				"            image(λz:prod(A, B). N.add(S(fst(z)), snd(z)), set_cross(M.carrier, E)) = " +
				"            N.carrier ∧ " +
				"            finite_dimensional(complex_ring, " +
				"                restrict_module(product_module(M, restrict_module(N, E)), " +
				"                    {z:prod(A, B) | " +
				"                        z ∈ set_cross(M.carrier, E) ∧ N.add(S(fst(z)), snd(z)) = N.zero})) ∧ " +
				"            int_of_num(module_dim(complex_ring, " +
				"                    restrict_module(product_module(M, restrict_module(N, E)), " +
				"                        {z:prod(A, B) | " +
				"                            z ∈ set_cross(M.carrier, E) ∧ " +
				"                            N.add(S(fst(z)), snd(z)) = N.zero}))) = " +
				"            fredholm_index(M, N, q, T) + " +
				"            int_of_num(module_dim(complex_ring, restrict_module(N, E)))",
		},
		"Choose a finite dimensional complement to the original image; the "+
			"augmented surjection has a bounded right inverse, hence remains "+
			"surjective nearby and has the stated stable kernel dimension."),
})}
