package boolean_degree

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/registry"
)

// DegreeMaximum identifies the degree as the maximum of zero and the sizes of nonzero monomials.
var DegreeMaximum = degreeMaximumThm{family.Add(registry.ProofEntry{
	Name: "DegreeMaximum",
	Key:  "prop_285f8a43559ff36e",
	Build: family.Theorem(Statement{
		Binders:    "∀U:set(A). ∀f:(set(A) → bool).",
		Hypotheses: []string{"finite(U)"},
		Conclusion: "«Size»(boolean_degree(U, f)) ∧ " +
			"(∀S:set(A). S ⊆ U ∧ boolean_coefficient(f, S) ≠ 0 ⇒ card(S) ≤ boolean_degree(U, f))",
		Abbrev: Abbrev{
			{Name: "Size", Text: "λd:num. " +
				"    d = 0 ∨ (∃S:set(A). S ⊆ U ∧ boolean_coefficient(f, S) ≠ 0 ∧ card(S) = d)"},
		},
	}, func(a *Argument, U *Expr[Set[A]], f *Arrow[Set[A], Bool], finite Fact) {
		a.Have(
			"the candidate sizes have a largest element",
			"∃d:num. «Size»(d) ∧ (∀S:set(A). S ⊆ U ∧ boolean_coefficient(f, S) ≠ 0 ⇒ card(S) ≤ d)",
			Derive(func(b *Argument) {
				some := b.Have(
					"zero is always a candidate",
					"∃d:num. «Size»(d)",
					Witness(b.TermAs[Nat]("0")),
					Basic())
				bounded := b.Have(
					"every candidate is bounded by the dimension",
					"∃M:num. ∀d:num. «Size»(d) ⇒ d ≤ M",
					Witness(b.TermAs[Nat]("card(U)")),
					By(finite, cardinality.CardSubset, nat_order.ZeroLessEq.At(b.TermAs[Nat]("card(U)"))))
				b.Show(
					"nonempty bounded sets of natural numbers attain their maximum",
					By(some, bounded, nat_order.MaximumExists.At(b.TermAs[Set[Nat]]("«Size»"))))
			}))
		a.Show(
			"the degree selects that maximum",
			Unfold(BooleanDegreeDef))
	}),
})}

// DegreeFace selects a monomial attaining a positive degree. Its coordinates specify a face
// by fixing every other coordinate to zero.
var DegreeFace = degreeFaceThm{family.Add(registry.ProofEntry{
	Name: "DegreeFace",
	Key:  "prop_a93fd09b9304bd35",
	Build: family.Theorem(Statement{
		Binders:    "∀U:set(A). ∀f:(set(A) → bool).",
		Hypotheses: []string{"finite(U)", "0 < boolean_degree(U, f)"},
		Conclusion: "∃S:set(A). S ⊆ U ∧ boolean_coefficient(f, S) ≠ 0 ∧ card(S) = boolean_degree(U, f)",
	}, func(a *Argument, U *Expr[Set[A]], f *Arrow[Set[A], Bool], finite, positive Fact) {
		a.Show(
			"a positive maximum must come from a nonzero monomial",
			By(finite, positive, DegreeMaximum.At(U, f), nat_order.LessThanIrrefl.At(a.TermAs[Nat]("0"))))
	}),
})}
