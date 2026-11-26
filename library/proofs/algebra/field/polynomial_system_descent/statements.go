package polynomial_system_descent

import (
	"github.com/euc-ai/xugo/ext/on"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/algebraic_closure"
	"github.com/euc-ai/xugo/library/registry"

	// algebraically_closed_field_transfer states EmbeddingElementary, which ByElementarity's
	// embedding mode reads by name, and polynomial_encoding mints polynomial_value and
	// ring_tuple, which PolynomialSystemDef's equation spells: the imports keep this chapter
	// above them in Go's import graph.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/algebraically_closed_field_transfer"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_encoding"
)

// PolynomialSystemDef — A tuple satisfying a finite list of equations and a finite list of inequations.
var PolynomialSystemDef = polynomialSystemDefThm{family.Define(registry.DefEntry{
	Name:  "PolynomialSystemDef",
	Const: "polynomial_system_solution",
	Type: "ring_ops(A) → " +
		"num → " +
		"num → " +
		"num → " +
		"(num → (num → num) → A) → " +
		"(num → (num → num) → A) → " +
		"(num → A) → " +
		"bool",
	Key: "prop_cac2de71f4de8b97",
	Equations: []string{
		"∀R:ring_ops(A). ∀n r s:num. ∀P Q:(num → (num → num) → A). ∀x:(num → A). " +
			"    polynomial_system_solution(R, n, r, s, P, Q, x) ⇔ " +
			"    ring_tuple(R, n, x) ∧ " +
			"    (∀j:num. j < r ⇒ polynomial_value(R, P(j), x) = R.zero) ∧ " +
			"    (∀j:num. j < s ⇒ polynomial_value(R, Q(j), x) ≠ R.zero)",
	},
})}

// SolutionDescent — finite polynomial systems with inequations descend along algebraically closed
// embeddings: both systems read as one formula with P and Q its parameters, bounded at the common
// degree bound of their memberships, encoded in one environment over F and their images in its
// image over G, and algebraically_closed_field_transfer.EmbeddingElementary makes the embedding
// elementary at it.
var SolutionDescent = solutionDescentThm{family.Add(registry.ProofEntry{
	Name: "SolutionDescent",
	Key:  "prop_b241084949111f6d",
	Reading: "The system over G applies i to every coefficient of P and Q. " +
		"Solvability goes both ways, inequations included, because i embeds one " +
		"algebraically closed field elementarily in the other. With no constraints " +
		"the zero tuple is a solution; dimension zero leaves only constant conditions.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀G:field_ops(B). " +
			"∀i:(A → B). " +
			"∀n r s:num. " +
			"∀P Q:(num → (num → num) → A).",
		Hypotheses: []string{
			"algebraically_closed_field_on(F)",
			"algebraically_closed_field_on(G)",
			"ring_homomorphism(field_ring(F), field_ring(G), i)",
			"∀j:num. j < r ⇒ P(j) ∈ polynomial_algebra(field_ring(F), {v:num | v < n})",
			"∀j:num. j < s ⇒ Q(j) ∈ polynomial_algebra(field_ring(F), {v:num | v < n})",
		},
		Conclusion: "(∃y:(num → B). " +
			"    polynomial_system_solution(field_ring(G), " +
			"        n, " +
			"        r, " +
			"        s, " +
			"        λj:num. λm:(num → num). i(P(j, m)), " +
			"        λj:num. λm:(num → num). i(Q(j, m)), " +
			"        y)) ⇔ " +
			"∃x:(num → A). polynomial_system_solution(field_ring(F), n, r, s, P, Q, x)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		G *Expr[FieldOps[B]],
		i *Arrow[A, B],
		n, r, s *Expr[Nat],
		P, Q *Arrow2[Nat, Fun[Nat, Nat], A],
		closedF algebraic_closure.AlgebraicallyClosedFieldFact[on.F],
		closedG algebraic_closure.AlgebraicallyClosedFieldFact[on.G],
		hom, pIn, qIn Fact,
	) {
		a.Show(
			"solvable over G exactly when over F, i being elementary "+
				"(algebraically_closed_field_transfer.EmbeddingElementary)",
			ByElementarity(nil, closedF, closedG, hom, pIn, qIn))
	}),
})}
