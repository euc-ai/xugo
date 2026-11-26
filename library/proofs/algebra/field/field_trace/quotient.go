// quotient.go — the chapter's quotient statements.

package field_trace

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/polynomial_quotient"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_division"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/quotient_ring"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialQuotientPowerBasis — Short monomial classes form a basis of a positive-degree monic polynomial quotient.
var PolynomialQuotientPowerBasis = polynomialQuotientPowerBasisThm{family.Add(registry.ProofEntry{
	Name: "PolynomialQuotientPowerBasis",
	Key:  "prop_7d0ea214dd233fff",
	Deps: []registry.EntryLike{
		polynomial_quotient.PolynomialPrincipalIdealDivides,
		polynomial_division.DivisionExists,
		quotient_ring.IdealQuotientProjection,
	},
	Build: family.Card(Statement{
		Binders: "∀L:field_on(A). ∀p:(num → A).",
		Hypotheses: []string{
			"polynomial_over(L.carrier, p)",
			"polynomial_monic(p)",
			"0 < polynomial_degree(p)",
		},
		Conclusion: "module_on(field_ring(L), trace_quotient_module(L, p)) ∧ " +
			"module_basis(field_ring(L), " +
			"    trace_quotient_module(L, p), " +
			"    {ideal_quotient_projection(mk_ring(vec_add, " +
			"                vec_zero, " +
			"                vec_neg, " +
			"                polynomial_mul, " +
			"                basis_vector(0), " +
			"                vec_sub, " +
			"                {h:num → A | polynomial_over(L.carrier, h)}), " +
			"            ideal_span(mk_ring(vec_add, " +
			"                    vec_zero, " +
			"                    vec_neg, " +
			"                    polynomial_mul, " +
			"                    basis_vector(0), " +
			"                    vec_sub, " +
			"                    {h:num → A | polynomial_over(L.carrier, h)}), " +
			"                {p}), " +
			"            basis_vector(i)) | " +
			"        i:num | " +
			"        i < polynomial_degree(p)}) ∧ " +
			"has_size({ideal_quotient_projection(mk_ring(vec_add, " +
			"                vec_zero, " +
			"                vec_neg, " +
			"                polynomial_mul, " +
			"                basis_vector(0), " +
			"                vec_sub, " +
			"                {h:num → A | polynomial_over(L.carrier, h)}), " +
			"            ideal_span(mk_ring(vec_add, " +
			"                    vec_zero, " +
			"                    vec_neg, " +
			"                    polynomial_mul, " +
			"                    basis_vector(0), " +
			"                    vec_sub, " +
			"                    {h:num → A | polynomial_over(L.carrier, h)}), " +
			"                {p}), " +
			"            basis_vector(i)) | " +
			"        i:num | " +
			"        i < polynomial_degree(p)}, " +
			"    polynomial_degree(p))",
	},
		"DivisionExists expresses each class by a remainder of degree below deg "+
			"p. PolynomialPrincipalIdealDivides and degree of a nonzero multiple "+
			"give independence and distinctness of the displayed monomials."),
})}
