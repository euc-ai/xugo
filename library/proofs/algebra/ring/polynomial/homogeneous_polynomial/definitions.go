// definitions.go — the chapter's definition, a form of degree d in the
// variables up to n, followed by the laws that state its two parts, which a
// proof cites in place of the unfolded definition.

package homogeneous_polynomial

import (
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_element"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/module_dimension"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/module/submodule"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/partial_derivative"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/free_algebra"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/ring_ideal"
	_ "github.com/euc-ai/xugo/library/proofs/iterate/nat/nat_sum"
	"github.com/euc-ai/xugo/library/registry"
)

var HomogeneousPolynomialDef = homogeneousPolynomialDefThm{family.Define(registry.DefEntry{
	Name:  "HomogeneousPolynomialDef",
	Key:   "prop_3f3294f14d2a1075",
	Deps:  []registry.EntryLike{},
	Const: "homogeneous_polynomial",
	Type:  "ring_ops(A) → num → num → ((num → num) → A) → bool",
	Equations: []string{
		"∀R:ring_ops(A). ∀n d:num. ∀P:((num → num) → A). " +
			"    homogeneous_polynomial(R, n, d, P) ⇔ " +
			"    P ∈ polynomial_algebra_ring(R, {i:num | i ≤ n}).carrier ∧ " +
			"    (∀m:(num → num). P(m) ≠ R.zero ⇒ nat_sum({i:num | i ≤ n}, m) = d)",
	},
})}

// FormPolynomial — a form is a polynomial in the variables up to n.
var FormPolynomial = formPolynomialThm{family.Add(registry.ProofEntry{
	Name: "FormPolynomial",
	Key:  "prop_584ae89187f7aace",
	Build: HomogeneousPolynomialDef.Entry().Conjunct(
		"P ∈ polynomial_algebra_ring(R, {i:num | i ≤ n}).carrier"),
})}

// FormDegree — every monomial at which a form is nonzero has the form's degree.
var FormDegree = formDegreeThm{family.Add(registry.ProofEntry{
	Name: "FormDegree",
	Key:  "prop_16df6c32957c359a",
	Build: HomogeneousPolynomialDef.Entry().Conjunct(Statement{
		Binders: "∀m:(num → num).",
		Hypotheses: []string{
			"P(m) ≠ R.zero",
		},
		Conclusion: "nat_sum({i:num | i ≤ n}, m) = d",
	}),
})}
