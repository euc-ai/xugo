package polynomial_brouwer

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_polynomial_geometry"
	"github.com/euc-ai/xugo/library/registry"

	// real_closed_field_transfer states SentenceTransfer, and real_closed_instance the reals' instance,
	// which ByElementarity reads by name and by statement: the imports keep this chapter above them in
	// Go's import graph.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field_transfer"
	_ "github.com/euc-ai/xugo/library/proofs/real/real_closed_instance"
)

// PolynomialBrouwer — every polynomial self-map of the n-cube over a real closed field has a fixed
// point: its n coordinate polynomials have a common degree bound d, and polynomial_brouwer_property
// at d, Brouwer's theorem for the self-maps of degree at most d and a closed sentence true over the
// reals (real_polynomial_geometry.BrouwerSource), holds in F by
// real_closed_field_transfer.SentenceTransfer and is read at P, its one ∀ binder.
var PolynomialBrouwer = polynomialBrouwerThm{family.Add(registry.ProofEntry{
	Name: "PolynomialBrouwer",
	Key:  "prop_8531cf66c191b05b",
	Reading: "Both the witness and polynomial image are zero-padded, so " +
		"the conclusion may use total-function equality. At dimension zero the " +
		"cube is a singleton and unused polynomial coordinates are irrelevant.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num. ∀P:(num → (num → num) → A).",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"∀j:num. j < n ⇒ P(j) ∈ polynomial_algebra(field_ring(F), {i:num | i < n})",
			"∀x:(num → A). " +
				"    x ∈ carrier_cube(F, lt, n) ⇒ polynomial_map(field_ring(F), n, P, x) ∈ carrier_cube(F, lt, n)",
		},
		Conclusion: "∃x:(num → A). x ∈ carrier_cube(F, lt, n) ∧ polynomial_map(field_ring(F), n, P, x) = x",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		n *Expr[Nat],
		P *Expr[Fun2[Nat, Fun[Nat, Nat], A]],
		closedF, polynomials, keepsCube Fact,
	) {
		a.Show(
			"Brouwer's theorem over the reals, transferred at P's common degree bound and read at P",
			ByElementarity(real_polynomial_geometry.BrouwerSource, closedF, polynomials, keepsCube).At(P))
	}),
})}
