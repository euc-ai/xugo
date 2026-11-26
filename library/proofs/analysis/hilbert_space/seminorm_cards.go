package hilbert_space

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	"github.com/euc-ai/xugo/library/proofs/relations/equivalence"
	"github.com/euc-ai/xugo/library/registry"
)

var SeminormQuotientNormed = seminormQuotientNormedThm{family.Add(registry.ProofEntry{
	Name: "SeminormQuotientNormed",
	Deps: []registry.EntryLike{
		submodule.QuotientModuleOn,
		submodule.SubmoduleCosetEq,
		equivalence.InducedMapClass,
	},
	Key: "prop_b6ebe66c54f4bf4c",
	Build: family.Card(SeminormDef.Statement(Statement{
		Conclusion: "submodule(complex_ring, M, seminorm_kernel(M, v)) ∧ " +
			"complex_normed_space(quotient_module(M, seminorm_kernel(M, v)), quotient_norm(v)) ∧ " +
			"(∀x:A. x ∈ M.carrier ⇒ quotient_norm(v, left_coset(M.add, x, seminorm_kernel(M, v))) = v(x))"}),
		"The triangle inequality makes the seminorm constant on cosets of its kernel. Apply the "+
			"quotient module laws and induced-map evaluation; the zero coset is exactly the kernel."),
})}

var SeminormQuotientComplete = seminormQuotientCompleteThm{family.Add(registry.ProofEntry{
	Name: "SeminormQuotientComplete",
	Reading: "The predicate metric_cauchy is a condition on a carrier and distance " +
		"function and does not itself require separation. It therefore expresses the " +
		"intended Cauchy condition for a seminorm before passage to its quotient.",
	Deps: []registry.EntryLike{SeminormQuotientNormed},
	Key:  "prop_c5bc2e2e6dc84185",
	Build: family.Card(SeminormDef.Statement(Statement{
		Hypotheses: []string{
			"∀f:(num → A). " +
				"    metric_cauchy(M.carrier, norm_distance(M, v), f) ⇒ " +
				"    ∃x:A. x ∈ M.carrier ∧ real_converges_to(λn:num. v(M.add(f(n), M.neg(x))), &0)",
		},
		Conclusion: "complex_banach_space(quotient_module(M, seminorm_kernel(M, v)), quotient_norm(v))"}),
		"Choose representatives of a quotient Cauchy sequence. The coset norm identifies its "+
			"Cauchy condition with the assumed function-layer condition; project the resulting limit."),
})}

var SemiInnerQuotient = semiInnerQuotientThm{family.Add(registry.ProofEntry{
	Name: "SemiInnerQuotient",
	Deps: []registry.EntryLike{
		SeminormQuotientNormed,
		equivalence.InducedMapClass,
		CauchySchwarz,
		submodule.SubmoduleCosetEq,
	},
	Key: "prop_1b0effb7dd0c69b0",
	Build: family.Card(SemiInnerDef.Statement(Statement{
		Conclusion: "complex_seminorm(M, hilbert_norm(p)) ∧ " +
			"complex_inner_space(quotient_module(M, seminorm_kernel(M, hilbert_norm(p))), " +
			"    quotient_inner(p)) ∧ " +
			"(∀Q:set(A). " +
			"    Q ∈ quotient_module(M, seminorm_kernel(M, hilbert_norm(p))).carrier ⇒ " +
			"    hilbert_norm(quotient_inner(p), Q) = quotient_norm(hilbert_norm(p), Q))"}),
		"The quadratic nonnegativity argument gives Cauchy–Schwarz for the "+
			"semidefinite form and makes its null space orthogonal to all vectors. Descend "+
			"each variable with induced_map; the diagonal norm is the descended seminorm."),
})}
