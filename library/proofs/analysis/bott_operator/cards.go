package bott_operator

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/exterior_basis"
	"github.com/euc-ai/xugo/library/proofs/analysis/bounded_operator"
	"github.com/euc-ai/xugo/library/proofs/analysis/hilbert_space"
	"github.com/euc-ai/xugo/library/proofs/analysis/sequence_hilbert"
	"github.com/euc-ai/xugo/library/proofs/measure/integral_convergence"
	"github.com/euc-ai/xugo/library/proofs/real/hermite_function"
	"github.com/euc-ai/xugo/library/proofs/real/lebesgue_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/determinant"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_integral"
	"github.com/euc-ai/xugo/library/proofs/vector/vec_smooth"
	"github.com/euc-ai/xugo/library/registry"
)

var SequenceSquare = sequenceSquareThm{family.Add(registry.ProofEntry{
	Name: "SequenceSquare",
	Key:  "prop_2ed61f0f7ed49816",
	Deps: []registry.EntryLike{
		exterior_basis.MaskInsert,
		exterior_basis.MaskDelete,
		exterior_basis.SignToggle,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀u:(prod(num → num, num) → complex). ∀z:prod(num → num, num).",
		Hypotheses: []string{"z ∈ bott_indices(n)"},
		Conclusion: "bott_sequence_operator(n, bott_sequence_operator(n, u), z) = " +
			"complex_of_real(bott_energy(n, z)) * u(z)",
	},
		"Creation and annihilation satisfy their commutator relation, while exterior "+
			"wedge and contraction anticommute. The mixed coordinate terms cancel."),
})}

var SequenceHilbert = sequenceHilbertThm{family.Add(registry.ProofEntry{
	Name: "SequenceHilbert",
	Key:  "prop_301c733d91ed38cc",
	Deps: []registry.EntryLike{
		sequence_hilbert.WeightedHilbert,
		sequence_hilbert.NormSquaredFiniteSup,
		hilbert_space.ClosedSubspace,
	},
	Build: family.Card(
		"∀n e:num. ∀graph:bool. "+
			"    complex_hilbert_space(bott_sequence_module(n, e, graph), bott_sequence_inner(n, graph))",
		"The parity carrier is a closed coordinate subspace of a "+
			"weighted sequence Hilbert space; every weight is at least one."),
})}

var GraphBounded = graphBoundedThm{family.Add(registry.ProofEntry{
	Name: "GraphBounded",
	Key:  "prop_f54dca675bb832e8",
	Deps: []registry.EntryLike{
		SequenceSquare,
		SequenceHilbert,
		sequence_hilbert.NormSquaredFiniteSup,
		exterior_basis.MaskInsert,
		exterior_basis.MaskDelete,
	},
	Build: family.Card(
		"∀n:num. "+
			"    bounded_operator(bott_sequence_module(n, 0, True), "+
			"        hilbert_norm(bott_sequence_inner(n, True)), "+
			"        bott_sequence_module(n, 1, False), "+
			"        hilbert_norm(bott_sequence_inner(n, False)), "+
			"        bott_sequence_operator(n))",
		"Summing the square identity on finitely supported sequences bounds "+
			"the output norm by the graph norm; density extends the finite formula."),
})}

var GaussianKernel = gaussianKernelThm{family.Add(registry.ProofEntry{
	Name: "GaussianKernel",
	Key:  "prop_54d812e563ab13b1",
	Deps: []registry.EntryLike{
		SequenceSquare,
		exterior_basis.MaskEmpty,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀u:(prod(num → num, num) → complex).",
		Hypotheses: []string{"u ∈ (bott_sequence_module(n, 0, True)).carrier"},
		Conclusion: "bott_sequence_operator(n, u) = (λz:prod(num → num, num). complex_of_real(&0)) ⇔ " +
			"∃c:complex. u = (λz:prod(num → num, num). c * bott_ground_sequence(n, z))",
	},
		"The energy is positive on every coordinate except "+
			"the zero Hermite index and exterior degree zero."),
})}

var NoOddCokernel = noOddCokernelThm{family.Add(registry.ProofEntry{
	Name: "NoOddCokernel",
	Key:  "prop_d38f5e48027f5991",
	Deps: []registry.EntryLike{
		SequenceSquare,
		GraphBounded,
		sequence_hilbert.NormSquaredFiniteSup,
		exterior_basis.MaskInsert,
		exterior_basis.MaskDelete,
		exterior_basis.MaskEmpty,
	},
	Build: family.Card(
		"∀n:num. "+
			"    image(bott_sequence_operator(n), (bott_sequence_module(n, 0, True)).carrier) = "+
			"    (bott_sequence_module(n, 1, False)).carrier",
		"On odd coordinates the energy is at least two; applying B divided by "+
			"the energy gives a graph-domain preimage with a uniform norm bound."),
})}

var BottFredholmIndex = bottFredholmIndexThm{family.Add(registry.ProofEntry{
	Name: "BottFredholmIndex",
	Key:  "prop_58831567dd489b99",
	Deps: []registry.EntryLike{GaussianKernel, NoOddCokernel, GraphBounded, SequenceHilbert},
	Build: family.Card(
		"∀n:num. "+
			"    fredholm_operator(bott_sequence_module(n, 0, True), "+
			"        bott_sequence_inner(n, True), "+
			"        bott_sequence_module(n, 1, False), "+
			"        bott_sequence_inner(n, False), "+
			"        bott_sequence_operator(n)) ∧ "+
			"    fredholm_index(bott_sequence_module(n, 0, True), "+
			"        bott_sequence_module(n, 1, False), "+
			"        bott_sequence_inner(n, False), "+
			"        bott_sequence_operator(n)) = "+
			"    int_of_num(1)",
		"The Gaussian kernel is one-dimensional and the odd target "+
			"is the range, including the zero-dimensional fibre."),
})}

var HermiteCorrespondence = hermiteCorrespondenceThm{family.Add(registry.ProofEntry{
	Name: "HermiteCorrespondence",
	Key:  "prop_8efa478a0e96bf52",
	Deps: []registry.EntryLike{
		integral_convergence.DominatedConvergence,
		lebesgue_integral.LebesgueIntegralEq,
		HermiteSynthesis,
		HermiteComplete,
		SchwartzAlgebra,
		hermite_function.HermiteOrthonormal,
		vec_integral.IntegralAdd,
		vec_integral.IntegralScale,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀u:(prod(num → num, num) → complex).",
		Hypotheses: []string{"bott_rapid_sequence(n, u)"},
		Conclusion: "∃!f:((num → real) → num → complex). " +
			"    bott_schwartz_form(n, f) ∧ bott_hermite_transform(n, f) = u",
	},
		"The normalized Hermite functions form a complete orthonormal basis. Rapid coefficients give "+
			"a Schwartz synthesis, and repeated annihilation and creation estimates give the converse."),
})}

var HermiteParseval = hermiteParsevalThm{family.Add(registry.ProofEntry{
	Name: "HermiteParseval",
	Key:  "prop_bbbd4dfe06ab4eac",
	Deps: []registry.EntryLike{
		HermiteCorrespondence,
		sequence_hilbert.NormSquaredFiniteSup,
		integral_convergence.DominatedConvergence,
		HermiteSynthesis,
		HermiteComplete,
		SchwartzRapid,
		SchwartzAlgebra,
		SchwartzDerivativeCoordinate,
		hermite_function.HermiteOrthonormal,
		hermite_function.HermiteLadder,
		vec_integral.IntegralPartialZero,
		vec_integral.IntegralMono,
		vec_integral.IntegralSum,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀f:((num → real) → num → complex).",
		Hypotheses: []string{"bott_schwartz_form(n, f)"},
		Conclusion: "bott_rapid_sequence(n, bott_hermite_transform(n, f)) ∧ " +
			"real_pow(hilbert_norm(weighted_sequence_inner(bott_indices(n), λz:prod(num → num, num). &1), " +
			"        bott_hermite_transform(n, f)), " +
			"    2) = " +
			"vec_integral⟨n⟩( " +
			"    λx:(num → real). real_sum({a:num | a < nat_pow(2, n)}, λa:num. real_pow(|f(x, a)|, 2)))",
	},
		"Apply scalar Hermite completeness and Parseval componentwise. Schwartz decay "+
			"justifies every iterated integral and the limits of finite Hermite sums."),
})}

var HermiteIntertwining = hermiteIntertwiningThm{family.Add(registry.ProofEntry{
	Name: "HermiteIntertwining",
	Key:  "prop_55a2febc8825b34",
	Deps: []registry.EntryLike{
		HermiteParseval,
		vec_smooth.SmoothPartial,
		vec_smooth.SmoothMul,
		SchwartzAlgebra,
		SchwartzDerivativeCoordinate,
		hermite_function.HermiteLadder,
		vec_integral.IntegralPartialZero,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀f:((num → real) → num → complex).",
		Hypotheses: []string{"bott_schwartz_form(n, f)"},
		Conclusion: "bott_schwartz_form(n, bott_physical_operator(n, f)) ∧ " +
			"bott_hermite_transform(n, bott_physical_operator(n, f)) = " +
			"bott_sequence_operator(n, bott_hermite_transform(n, f))",
	},
		"Integration by parts gives the weighted annihilation and creation shifts. "+
			"Schwartz decay removes the boundary terms, and the exterior signs agree."),
})}

var GaussianPoincare = gaussianPoincareThm{family.Add(registry.ProofEntry{
	Name: "GaussianPoincare",
	Key:  "prop_186ed2616a442017",
	Deps: []registry.EntryLike{
		SequenceSquare,
		HermiteParseval,
		HermiteIntertwining,
		vec_integral.IntegralAdd,
		vec_integral.IntegralScale,
		vec_smooth.SmoothMul,
		vec_integral.GaussianIntegral,
		vec_integral.CcRapid,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀f:((num → real) → real).",
		Hypotheses: []string{
			"vec_smooth_on⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, f)",
			"vec_compactly_supported_in⟨n⟩({x:(num → real) | vec⟨n⟩(&0, x)}, f)",
		},
		Conclusion: "vec_integral⟨n⟩(λx:(num → real). " +
			"        real_exp(-real_sum({i:num | i < n}, λi:num. real_pow(x(i), 2))) * real_pow(f(x), 2)) - " +
			"real_pow(vec_integral⟨n⟩(λx:(num → real). " +
			"            real_exp(-real_sum({i:num | i < n}, λi:num. real_pow(x(i), 2))) * f(x)), " +
			"    2) / " +
			"real_pow(real_sqrt(pi), n) ≤ " +
			"(&1 / &2) * " +
			"vec_integral⟨n⟩(λx:(num → real). " +
			"        real_exp(-real_sum({i:num | i < n}, λi:num. real_pow(x(i), 2))) * " +
			"        real_sum({j:num | j < n}, λj:num. real_pow(partial_derivative(f, j, x), 2)))",
	},
		"Conjugate by the Gaussian and apply the first positive Hermite energy, two. The constant mode "+
			"gives the subtracted squared mean; all displayed nonconstant integrands have compact support."),
})}

var ExteriorOrthogonal = exteriorOrthogonalThm{family.Add(registry.ProofEntry{
	Name: "ExteriorOrthogonal",
	Key:  "prop_6b1591513e53b3b0",
	Reading: "Only b < 2ⁿ is asked: for c ≥ 2ⁿ every entry in column c is 0 and b ≠ c. Without it, " +
		"b = c ≥ 2ⁿ gives the sum 0 against 1. At n = 0 the sum is the empty determinant squared, 1.",
	Deps: []registry.EntryLike{
		exterior_basis.ExteriorPowerProduct,
		exterior_basis.ExteriorPowerTranspose,
		exterior_basis.ExteriorPowerIdentity,
	},
	Build: family.Card(Statement{
		Binders: "∀n:num. ∀O:(num → num → real). ∀b c:num.",
		Hypotheses: []string{
			"bott_orthogonal_matrix(n, O)",
			"b < nat_pow(2, n)",
		},
		Conclusion: "real_sum({a:num | a < nat_pow(2, n)}, " +
			"    λa:num. exterior_power(real_ring, n, O, a, b) * exterior_power(real_ring, n, O, a, c)) = " +
			"COND(b = c, &1, &0)",
	},
		"bott_orthogonal_matrix says O is zero off n × n and OᵀO is the identity there, so "+
			"matrix_product(real_ring, n, transpose(O), O) = matrix_identity(real_ring, n). The "+
			"exterior power of the transpose is the transpose (exterior_basis.ExteriorPowerTranspose), "+
			"of a product the product (ExteriorPowerProduct), of the identity the identity "+
			"(ExteriorPowerIdentity); the (b, c) entry of Λ(O)ᵀΛ(O) = I is the stated sum."),
})}

var OrthogonalCovariance = orthogonalCovarianceThm{family.Add(registry.ProofEntry{
	Name: "OrthogonalCovariance",
	Key:  "prop_d06d421c62e4d314",
	Deps: []registry.EntryLike{
		vec_smooth.PartialDerivativeChain,
		vec_smooth.SmoothCompose,
		determinant.MatrixInverse,
		determinant.DeterminantMultiplicative,
		ExteriorOrthogonal,
		SchwartzAlgebra,
		SchwartzDerivativeCoordinate,
		exterior_basis.SignToggle,
		exterior_basis.SlotSpec,
		determinant.MultilinearColumnExpansion,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀O:(num → num → real). ∀f:((num → real) → num → complex).",
		Hypotheses: []string{"bott_orthogonal_matrix(n, O)", "bott_schwartz_form(n, f)"},
		Conclusion: "bott_schwartz_form(n, bott_rotate_form(n, O, f)) ∧ " +
			"bott_physical_operator(n, bott_rotate_form(n, O, f)) = " +
			"bott_rotate_form(n, O, bott_physical_operator(n, f))",
	},
		"The chain rule transforms derivatives and position vectors by the same "+
			"orthogonal matrix. Exterior wedge and contraction transform by its "+
			"exterior representation, so the full operator commutes with the action."),
})}

var RotationIntertwining = rotationIntertwiningThm{family.Add(registry.ProofEntry{
	Name: "RotationIntertwining",
	Key:  "prop_20702c544e2e1a4e",
	Reading: "The rotation operator is chosen by ε against boundedness " +
		"on the unweighted sequence space and this intertwining; for an " +
		"orthogonal frame change the card is the existence the choice needs.",
	Deps: []registry.EntryLike{
		HermiteCorrespondence,
		HermiteParseval,
		OrthogonalCovariance,
		bounded_operator.BoundedExtension,
		sequence_hilbert.FiniteSupportDense,
		sequence_hilbert.WeightedHilbert,
		ExteriorOrthogonal,
		SchwartzRapid,
		SchwartzAlgebra,
		vec_integral.IntegralLinearChange,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀O:(num → num → real).",
		Hypotheses: []string{"bott_orthogonal_matrix(n, O)"},
		Conclusion: "bounded_operator( " +
			"    weighted_sequence_module(bott_indices(n), λz:prod(num → num, num). &1), " +
			"    hilbert_norm(weighted_sequence_inner(bott_indices(n), λz:prod(num → num, num). &1)), " +
			"    weighted_sequence_module(bott_indices(n), λz:prod(num → num, num). &1), " +
			"    hilbert_norm(weighted_sequence_inner(bott_indices(n), λz:prod(num → num, num). &1)), " +
			"    bott_rotation_operator(n, O)) ∧ " +
			"(∀f:((num → real) → num → complex). " +
			"    bott_schwartz_form(n, f) ⇒ " +
			"    bott_rotation_operator(n, O, bott_hermite_transform(n, f)) = " +
			"    bott_hermite_transform(n, bott_rotate_form(n, O, f)))",
	},
		"Exhibit an operator meeting the definition's two clauses; the choice then names one. On "+
			"Hermite transforms of Schwartz forms set U(Hf) = H(rot_O f): rotation keeps the Schwartz "+
			"class, Hermite Parseval and the orthogonal change of variables make U isometric there, "+
			"and the Hermite correspondence makes it well defined, with dense domain the rapid "+
			"sequences. Extend it by continuity and set it to zero off the sequence space."),
})}

var OrthogonalDomain = orthogonalDomainThm{family.Add(registry.ProofEntry{
	Name: "OrthogonalDomain",
	Key:  "prop_78e7ddf355a086c6",
	Deps: []registry.EntryLike{
		OrthogonalCovariance,
		HermiteIntertwining,
		HermiteParseval,
		RotationIntertwining,
		HermiteCorrespondence,
		SequenceHilbert,
		sequence_hilbert.FiniteSupportDense,
		bounded_operator.OperatorNormBound,
		ExteriorOrthogonal,
		vec_integral.IntegralLinearChange,
	},
	Build: family.Card(Statement{
		Binders: "∀n e:num. ∀O:(num → num → real). ∀graph:bool. ∀u v:(prod(num → num, num) → complex).",
		Hypotheses: []string{
			"bott_orthogonal_matrix(n, O)",
			"u ∈ (bott_sequence_module(n, e, graph)).carrier",
			"v ∈ (bott_sequence_module(n, e, graph)).carrier",
		},
		Conclusion: "bott_rotation_operator(n, O, u) ∈ (bott_sequence_module(n, e, graph)).carrier ∧ " +
			"bott_sequence_inner(n, " +
			"    graph, " +
			"    bott_rotation_operator(n, O, u), " +
			"    bott_rotation_operator(n, O, v)) = " +
			"bott_sequence_inner(n, graph, u, v)",
	},
		"Orthogonal change of variables preserves L² and exterior parity; "+
			"covariance preserves the graph quadratic form. Hermite finite spans "+
			"and graph-norm density extend both identities to the closed domains."),
})}

var OrthogonalOperatorCommutes = orthogonalOperatorCommutesThm{family.Add(registry.ProofEntry{
	Name: "OrthogonalOperatorCommutes",
	Reading: "The orthogonal action is compared on the graph domain. " +
		"This statement asserts no operator-norm continuity of the rotation " +
		"representation on the full infinite-dimensional Hilbert space.",
	Key: "prop_512fc54b0f8e0e08",
	Deps: []registry.EntryLike{
		OrthogonalDomain,
		OrthogonalCovariance,
		HermiteIntertwining,
		RotationIntertwining,
		GraphBounded,
		HermiteCorrespondence,
		sequence_hilbert.FiniteSupportDense,
		bounded_operator.BoundedAgreeDense,
	},
	Build: family.Card(Statement{
		Binders: "∀n e:num. ∀O:(num → num → real). ∀u:(prod(num → num, num) → complex).",
		Hypotheses: []string{
			"bott_orthogonal_matrix(n, O)",
			"u ∈ (bott_sequence_module(n, e, True)).carrier",
		},
		Conclusion: "bott_sequence_operator(n, bott_rotation_operator(n, O, u)) = " +
			"bott_rotation_operator(n, O, bott_sequence_operator(n, u))",
	},
		"Approximate in the graph norm by finite Hermite forms and pass the "+
			"Schwartz covariance identity through the two bounded realizations."),
})}

var GroundFrameIndependent = groundFrameIndependentThm{family.Add(registry.ProofEntry{
	Name: "GroundFrameIndependent",
	Key:  "prop_1ef0b4208e2b4ea5",
	Deps: []registry.EntryLike{
		OrthogonalDomain,
		HermiteParseval,
		RotationIntertwining,
		determinant.MatrixInverse,
		HermiteSchwartz,
		exterior_basis.MaskEmpty,
		hermite_function.HermiteOrthonormal,
	},
	Build: family.Card(Statement{
		Binders:    "∀n:num. ∀O:(num → num → real).",
		Hypotheses: []string{"bott_orthogonal_matrix(n, O)"},
		Conclusion: "bott_rotation_operator(n, O, bott_ground_sequence(n)) = bott_ground_sequence(n)",
	},
		"The Gaussian is radial and its exterior factor has degree "+
			"zero; both are fixed by every orthogonal frame change."),
})}
