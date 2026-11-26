package sequence_hilbert

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/registry"
)

var WeightedHilbert = weightedHilbertThm{family.Add(registry.ProofEntry{
	Name: "WeightedHilbert",
	Reading: "The index set may be empty or uncountable. Strict positivity " +
		"is required only on that set; the sequence is zero outside it. No " +
		"enumeration or uniform positive lower bound for the weights is assumed.",
	Key: "prop_2b26c5e62ecad00f",
	Deps: []registry.EntryLike{
		InnerProductSum,
		SumUnique,
		SumLinear,
		SumNonneg,
		NormSquaredFiniteSup,
		real_sequences.CauchyIffConvergent,
	},
	Build: family.Card(
		Statement{
			Binders:    "∀J:set(I). ∀w:(I → real).",
			Hypotheses: []string{"∀i:I. i ∈ J ⇒ &0 < w(i)"},
			Conclusion: "complex_hilbert_space(weighted_sequence_module(J, w), weighted_sequence_inner(J, w))",
		},
		"Finite-sum Cauchy–Schwarz makes the polarized sums converge; coordinate limits of "+
			"Cauchy sequences have bounded finite subsums, and tail estimates give norm convergence."),
})}

var InnerProductSum = innerProductSumThm{family.Add(registry.ProofEntry{
	Name: "InnerProductSum",
	Key:  "prop_5ea3227a7c61111b",
	Deps: []registry.EntryLike{SumAbsolute, SumUnique},
	Build: family.Card(
		Statement{
			Binders: "∀J:set(I). ∀w:(I → real). ∀u v:(I → complex).",
			Hypotheses: []string{
				"∀i:I. i ∈ J ⇒ &0 < w(i)",
				"weighted_square_summable(J, w, u)",
				"weighted_square_summable(J, w, v)",
			},
			Conclusion: "unordered_complex_sums(J, " +
				"    λi:I. complex_of_real(w(i)) * u(i) * complex_conj(v(i)), " +
				"    weighted_sequence_inner(J, w, u, v))",
		},
		"Apply finite-sum Cauchy–Schwarz to tails and completeness of the complex plane."),
})}

var NormSquaredFiniteSup = normSquaredFiniteSupThm{family.Add(registry.ProofEntry{
	Name: "NormSquaredFiniteSup",
	Key:  "prop_5dd3fbc957dfe5ff",
	Deps: []registry.EntryLike{SumNonneg, SumUnique},
	Build: family.Card(
		Statement{
			Binders:    "∀J:set(I). ∀w:(I → real). ∀u:(I → complex).",
			Hypotheses: []string{"∀i:I. i ∈ J ⇒ &0 < w(i)", "weighted_square_summable(J, w, u)"},
			Conclusion: "real_pow(hilbert_norm(weighted_sequence_inner(J, w), u), 2) = " +
				"real_sup( " +
				"    {r:real | ∃F:set(I). finite(F) ∧ F ⊆ J ∧ r = real_sum(F, λi:I. w(i) * real_pow(|u(i)|, 2))})",
		},
		"The nonnegative finite-subset net converges to the supremum of its finite subsums."),
})}

var FiniteSupportDense = finiteSupportDenseThm{family.Add(registry.ProofEntry{
	Name: "FiniteSupportDense",
	Key:  "prop_132a5011842a978b",
	Deps: []registry.EntryLike{NormSquaredFiniteSup},
	Build: family.Card(
		Statement{
			Binders:    "∀J:set(I). ∀w:(I → real). ∀u:(I → complex). ∀ε:real.",
			Hypotheses: []string{"&0 < ε", "∀i:I. i ∈ J ⇒ &0 < w(i)", "weighted_square_summable(J, w, u)"},
			Conclusion: "∃F:set(I). " +
				"    finite(F) ∧ " +
				"    F ⊆ J ∧ " +
				"    hilbert_norm(weighted_sequence_inner(J, w), λi:I. u(i) - sequence_truncate(F, u, i)) < ε",
		},
		"Choose a finite subsum within the squared error of "+
			"the total norm; the remaining weighted tail is small."),
})}

var SumReindex = sumReindexThm{family.Add(registry.ProofEntry{
	Name: "SumReindex",
	Key:  "prop_6a03f812bc7eb9b4",
	Build: family.Card(
		Statement{
			Binders:    "∀J:set(I). ∀K:set(B). ∀e:(I → B). ∀a:(B → complex). ∀z:complex.",
			Hypotheses: []string{"injective_on(J, e)", "image(e, J) = K"},
			Conclusion: "unordered_complex_sums(K, a, z) ⇔ unordered_complex_sums(J, a ∘ e, z)",
		},
		"The bijection identifies the directed systems of finite "+
			"subsets, so both epsilon definitions are the same."),
})}

var SumUnique = sumUniqueThm{family.Add(registry.ProofEntry{
	Name: "SumUnique",
	Key:  "prop_d7a7f99e4156df68",
	Build: family.Card(
		Statement{
			Binders:    "∀J:set(I). ∀a:(I → complex). ∀z w:complex.",
			Hypotheses: []string{"unordered_complex_sums(J, a, z)", "unordered_complex_sums(J, a, w)"},
			Conclusion: "z = w",
		},
		"Use the union of the two finite controlling sets and the triangle inequality."),
})}

var FiniteSum = finiteSumThm{family.Add(registry.ProofEntry{
	Name: "FiniteSum",
	Key:  "prop_56bcb0b888d43aac",
	Build: family.Card(
		Statement{
			Binders: "∀J F:set(I). ∀a:(I → complex).",
			Hypotheses: []string{
				"finite(F)",
				"F ⊆ J",
				"∀i:I. i ∈ J ∧ i ∉ F ⇒ a(i) = complex_of_real(&0)",
			},
			Conclusion: "unordered_complex_sums(J, a, module_sum(complex_add, complex_of_real(&0), F, a))",
		},
		"F itself is a final controlling set: every finite G between F and J "+
			"adds only zero terms to the sum over F. A finite J is the case F = J."),
})}

var SumAbsolute = sumAbsoluteThm{family.Add(registry.ProofEntry{
	Name: "SumAbsolute",
	Key:  "prop_ad482e7979b4122b",
	Reading: "The bound C is on every finite subsum of the moduli, so it is at " +
		"least zero; the index set may be uncountable, and the family is read only on J.",
	Deps: []registry.EntryLike{SumUnique},
	Build: family.Card(
		Statement{
			Binders:    "∀J:set(I). ∀a:(I → complex). ∀C:real.",
			Hypotheses: []string{"∀F:set(I). finite(F) ∧ F ⊆ J ⇒ real_sum(F, λi:I. |a(i)|) ≤ C"},
			Conclusion: "unordered_complex_sums(J, a, unordered_complex_sum(J, a)) ∧ " +
				"|unordered_complex_sum(J, a)| ≤ C",
		},
		"The finite subsums of the moduli increase to their supremum, so beyond a large finite F "+
			"every finite set disjoint from F has modulus sum below ε. The finite sums over sets "+
			"containing F_m, chosen for ε = 1/(m+1) and increasing, form a Cauchy sequence in ℂ; its "+
			"limit is the sum, which the choice then names, and every finite sum has modulus at most C."),
})}

var SumNonneg = sumNonnegThm{family.Add(registry.ProofEntry{
	Name: "SumNonneg",
	Key:  "prop_ce19403c88d513ca",
	Build: family.Card(
		Statement{
			Binders: "∀J:set(I). ∀r:(I → real).",
			Hypotheses: []string{
				"∀i:I. i ∈ J ⇒ &0 ≤ r(i)",
				"∃C:real. ∀F:set(I). finite(F) ∧ F ⊆ J ⇒ real_sum(F, r) ≤ C",
			},
			Conclusion: "unordered_complex_sums(J, " +
				"    λi:I. complex_of_real(r(i)), " +
				"    complex_of_real(real_sup({s:real | ∃F:set(I). finite(F) ∧ F ⊆ J ∧ s = real_sum(F, r)})))",
		},
		"The finite subsums are bounded and the empty set gives one, so the supremum "+
			"exists. Choose F with subsum within ε of it; every finite G between F and J "+
			"has a subsum between that of F and the supremum, by nonnegativity."),
})}

var SumLinear = sumLinearThm{family.Add(registry.ProofEntry{
	Name: "SumLinear",
	Key:  "prop_51bd47ee2e702412",
	Build: family.Card(
		Statement{
			Binders: "∀J:set(I). ∀a b:(I → complex). ∀c y z:complex.",
			Hypotheses: []string{
				"unordered_complex_sums(J, a, y)",
				"unordered_complex_sums(J, b, z)",
			},
			Conclusion: "unordered_complex_sums(J, λi:I. a(i) + b(i), y + z) ∧ " +
				"unordered_complex_sums(J, λi:I. c * a(i), c * y) ∧ " +
				"unordered_complex_sums(J, λi:I. complex_conj(a(i)), complex_conj(y))",
		},
		"Finite sums are additive, homogeneous and commute with conjugation. For the "+
			"sum take the union of the two controlling sets at ε/2; for the multiple the "+
			"controlling set at ε/(|c|+1); conjugation preserves the modulus."),
})}

var SumIterated = sumIteratedThm{family.Add(registry.ProofEntry{
	Name: "SumIterated",
	Key:  "prop_8a21ea46ba64583a",
	Reading: "Only absolute summability over the product is assumed; " +
		"summability of each row and of the row sums is part of the conclusion.",
	Deps: []registry.EntryLike{SumAbsolute, SumLinear, SumUnique},
	Build: family.Card(
		Statement{
			Binders: "∀J:set(I). ∀K:set(B). ∀a:(I → B → complex). ∀C:real.",
			Hypotheses: []string{
				"∀F:set(prod(I, B)). " +
					"    finite(F) ∧ F ⊆ set_cross(J, K) ⇒ real_sum(F, λz:prod(I, B). |a(fst(z), snd(z))|) ≤ C",
			},
			Conclusion: "unordered_complex_sums(J, " +
				"    λi:I. unordered_complex_sum(K, a(i)), " +
				"    unordered_complex_sum(set_cross(J, K), λz:prod(I, B). a(fst(z), snd(z))))",
		},
		"Each row is absolutely summable with the same bound, so SumAbsolute gives its sum. For "+
			"a finite F of rows and a finite G of the product that controls the double sum, the sum "+
			"over the rows of F differs from the sum over G by tails of absolute size below ε."),
})}
