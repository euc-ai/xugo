package artin

import (
	. "github.com/euc-ai/xugo/library/authoring"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field_ordering"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/multivariate_rational_function"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_field"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/ordered_ring_formula"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closure"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_formula"
	_ "github.com/euc-ai/xugo/library/proofs/real/rational"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"

	// real_closed_field_transfer states EmbeddingElementary, which ByElementarity's embedding mode
	// reads by name: the import keeps this chapter above it in Go's import graph.
	_ "github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field_transfer"
)

// NegativeValueDescent — a negative value in a real closed extension descends along an ordered
// embedding: the embedding is a ring homomorphism of real closed fields, so it is elementary
// (real_closed_field_transfer.EmbeddingElementary), and a negative value of p over F is one of its
// image over G, p's coefficients the formula's parameters.
var NegativeValueDescent = negativeValueDescentThm{family.Add(registry.ProofEntry{
	Name: "NegativeValueDescent",
	Key:  "prop_42ad862b19a4cdbd",
	Reading: "The coefficient parameters are mapped by the specified " +
		"embedding; the conclusion uses the backward existential implication. " +
		"At dimension zero the constant coefficient is still a free parameter.",
	Build: family.Theorem(Statement{
		Binders: "∀F:field_ops(A). " +
			"∀lt:(A → A → bool). " +
			"∀G:field_ops(B). " +
			"∀ls:(B → B → bool). " +
			"∀i:(A → B). " +
			"∀n:num. " +
			"∀p:((num → num) → A).",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"real_closed_field(G, ls)",
			"ordered_field_embedding(F, lt, G, ls, i)",
			"p ∈ polynomial_algebra(field_ring(F), {j:num | j < n})",
			"∃y:(num → B). " +
				"    ring_tuple(field_ring(G), n, y) ∧ " +
				"    ls(polynomial_value(field_ring(G), λm:(num → num). i(p(m)), y), G.zero)",
		},
		Conclusion: "∃x:(num → A). " +
			"    ring_tuple(field_ring(F), n, x) ∧ lt(polynomial_value(field_ring(F), p, x), F.zero)",
	}, func(
		a *Argument,
		F *Expr[FieldOps[A]],
		lt *Arrow2[A, A, Bool],
		G *Expr[FieldOps[B]],
		ls *Arrow2[B, B, Bool],
		i *Arrow[A, B],
		n *Expr[Nat],
		p *Arrow[Fun[Nat, Nat], A],
		closedF, closedG, embedding, member, negative Fact,
	) {
		parts := a.Conjuncts(
			a.Unfolded(embedding, ordered_field.OrderedEmbeddingDef),
			"F is an ordered field",
			"so is G",
			"i is a ring homomorphism",
			"one to one",
			"keeping the order")
		descent := a.Have(
			"p is negative somewhere over F exactly when its image is over G, "+
				"i being elementary (real_closed_field_transfer.EmbeddingElementary)",
			"(∃x:(num → A). "+
				"    ring_tuple(field_ring(F), n, x) ∧ lt(polynomial_value(field_ring(F), p, x), F.zero)) ⇔ "+
				"∃y:(num → B). "+
				"    ring_tuple(field_ring(G), n, y) ∧ "+
				"    ls(polynomial_value(field_ring(G), λm:(num → num). i(p(m)), y), G.zero)",
			ByElementarity(nil, closedF, closedG, parts[2], member))
		a.Show(
			"its image is negative somewhere over G",
			By(descent, negative))
	}),
})}

// Artin — Every everywhere-nonnegative polynomial over a real closed field is a sum of rational squares.
var Artin = artinThm{family.Add(registry.ProofEntry{
	Name: "Artin",
	Key:  "prop_ea2a1df1b9993507",
	Deps: []registry.EntryLike{
		NegativeValueDescent,
		multivariate_rational_function.RationalFormallyReal,
		multivariate_rational_function.GenericPointEvaluation,
		multivariate_rational_function.ClearDenominators,
		field_ordering.SeparateNonsquareSum,
		real_closure.RealClosureExists,
		real_closed_field.HomomorphismOrderEmbedding,
	},
	Reading: "The ordering produced by square-sum separation restricts to " +
		"the original real-closed order because positive base elements are " +
		"squares. This is what makes the later elementary descent applicable.",
	Build: family.Card(Statement{
		Binders: "∀F:field_ops(A). ∀lt:(A → A → bool). ∀n:num. ∀p:((num → num) → A).",
		Hypotheses: []string{
			"real_closed_field(F, lt)",
			"p ∈ polynomial_algebra(field_ring(F), {j:num | j < n})",
			"∀x:(num → A). " +
				"    ring_tuple(field_ring(F), n, x) ⇒ " +
				"    ordered_le(lt, F.zero, polynomial_value(field_ring(F), p, x))",
		},
		Conclusion: "polynomial_rational_sos(F, n, p)",
	},
		"Real closed field transfer design, Artin theorem. If the rational function p is not a sum of "+
			"squares, separate it by an order, take the ordered real closure, and evaluate at the generic "+
			"point. The embedding of the real closed base preserves its order, so NegativeValueDescent "+
			"contradicts nonnegativity; ClearDenominators gives the stated certificate."),
})}
