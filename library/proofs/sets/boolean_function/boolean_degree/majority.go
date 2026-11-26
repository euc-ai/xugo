package boolean_degree

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// CoefficientMajority finds a strict parity majority on a nonempty face whose coefficient is nonzero.
// Omitted-coordinate parity supplies equally many signs, so the signed coefficient detects an imbalance.
var CoefficientMajority = coefficientMajorityThm{family.Add(registry.ProofEntry{
	Name: "CoefficientMajority",
	Key:  "prop_68ecebb0ae3c3ef1",
	Build: family.Theorem(Statement{
		Binders:    "∀S:set(A). ∀f:(set(A) → bool).",
		Hypotheses: []string{"finite(S)", "S ≠ ∅", "boolean_coefficient(f, S) ≠ 0"},
		Conclusion: "∃b:bool. card(«Face») < 2 * card(boolean_parity_class(S, f, b))",
		Abbrev: Abbrev{
			{Name: "Face", Text: "{Y:set(A) | Y ⊆ S}"},
			{Name: "EvenOmitted", Text: "λX:set(A). nat_even(card(S ∖ X))"},
			{Name: "Agree", Text: "{X:set(A) | X ∈ «Face» ∧ (f(X) ⇔ «EvenOmitted»(X))}"},
			{Name: "Disagree", Text: "{X:set(A) | X ∈ «Face» ∧ ¬(f(X) ⇔ «EvenOmitted»(X))}"},
			{Name: "Value", Text: "λX:set(A). COND(f(X), &1, &0)"},
		},
	}, func(a *Argument, S *Expr[Set[A]], f *Arrow[Set[A], Bool], finite, nonempty, nonzero Fact) {
		signed := a.Have(
			"the signed sum retains the nonzero integer coefficient",
			"sum(«Face», λX:set(A). COND(«EvenOmitted»(X), «Value»(X), -«Value»(X))) ≠ &0",
			By(
				finite,
				nonzero,
				CoefficientAsSum.At(S, f),
				int_construction.RepresentativeInjective.At(
					a.TermAs[Int]("boolean_coefficient(f, S)"), a.TermAs[Int]("int_of_num(0)")),
				int_construction.OfNumBridge.At(a.TermAs[Nat]("0"))))
		majority := a.Have(
			"agreement or disagreement with the signs occurs on more than half the face",
			"card(«Face») < 2 * card(«Agree») ∨ card(«Face») < 2 * card(«Disagree»)",
			By(
				finite,
				nonempty,
				signed,
				finite_set.FinitePowerset.At(S),
				EvenComplementCounts.At(S),
				SignedMajority.At(a.TermAs[Set[Set[A]]]("«Face»"), f, a.TermAs[Set[Set[A]]]("«EvenOmitted»"))))
		a.Cases(a.TermAs[Bool]("card(«Face») < 2 * card(«Agree»)"))
		a.When(
			"agreement with omitted-coordinate parity is in the majority",
			func(b *Argument, agree Fact) {
				b.Take(b.TermAs[Bool]("nat_even(card(S))"))
				b.Show(
					"translate the agreement class to input parity",
					By(finite, agree, ComplementParityClass.At(S, f, b.TermAs[Bool]("⊤"))))
			})
		a.Otherwise(
			"disagreement with omitted-coordinate parity is in the majority",
			func(b *Argument, noAgreeMajority Fact) {
				b.Take(b.TermAs[Bool]("¬nat_even(card(S))"))
				b.Show(
					"translate the disagreement class to input parity",
					By(finite, noAgreeMajority, majority, ComplementParityClass.At(S, f, b.TermAs[Bool]("⊥"))))
			})
	}),
})}

// MajorityFace selects a strict parity majority on a face having dimension equal to the degree.
var MajorityFace = majorityFaceThm{family.Add(registry.ProofEntry{
	Name: "MajorityFace",
	Key:  "prop_b4d1562da82e5315",
	Build: family.Theorem(Statement{
		Binders:    "∀U:set(A). ∀f:(set(A) → bool).",
		Hypotheses: []string{"finite(U)", "0 < boolean_degree(U, f)"},
		Conclusion: "∃S:set(A). " +
			"    S ⊆ U ∧ " +
			"    card(S) = boolean_degree(U, f) ∧ " +
			"    (∃b:bool. card({Y:set(A) | Y ⊆ S}) < 2 * card(boolean_parity_class(S, f, b)))",
	},
		func(a *Argument, U *Expr[Set[A]], f *Arrow[Set[A], Bool], finite, positive Fact) {
			S, top := a.ObtainAs[Set[A]](
				"choose a nonzero monomial of maximum degree",
				"∃S:set(A). S ⊆ U ∧ boolean_coefficient(f, S) ≠ 0 ∧ card(S) = boolean_degree(U, f)",
				By(finite, positive, DegreeFace.At(U, f)))
			finiteS := a.Have(
				"its coordinates form a finite set",
				"finite(S)",
				By(finite, top, finite_set.FiniteSubset.At(S, U)))
			nonempty := a.Have(
				"positive degree gives at least one coordinate",
				"S ≠ ∅",
				By(
					Normalized,
					finiteS,
					positive,
					top,
					cardinality.CardEqZero.At(S),
					nat_order.LessThanIrrefl.At(a.TermAs[Nat]("0"))))
			a.Take(S)
			a.Show(
				"the nonzero coefficient gives the majority on this face",
				By(finiteS, nonempty, top, CoefficientMajority.At(S, f)))
		}),
})}
