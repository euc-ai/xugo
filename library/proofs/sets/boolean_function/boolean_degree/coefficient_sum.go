package boolean_degree

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/module/module"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/multilinear_polynomial"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_real_lift"
	"github.com/euc-ai/xugo/library/proofs/iterate/int/int_sum"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/registry"
)

// RealOfIntegerFold transports the finite integer additive fold to a real sum.
var RealOfIntegerFold = realOfIntegerFoldThm{family.Add(registry.ProofEntry{
	Name: "RealOfIntegerFold",
	Key:  "prop_a02851da06827d0f",
	Build: family.Theorem(Statement{
		Binders:    "∀T:set(A). ∀g:(A → int).",
		Hypotheses: []string{"finite(T)"},
		Conclusion: "real_of_int(module_sum(int_add, int_of_num(0), T, g)) = " +
			"sum(T, λx:A. real_of_int(g(x)))",
	},
		func(a *Argument, T *Expr[Set[A]], g *Arrow[A, Int], finite Fact) {
			fold := a.Have(
				"integer addition gives the integer sum",
				"module_sum(int_add, int_of_num(0), T, g) = int_sum(T, g)",
				Unfold(int_sum.IntSumDef),
				By(finite, module.ModuleSumIteratedOp.Read(int_real_lift.AddMonoid).At(T, g)))
			a.Show(
				"the embedding preserves the sum",
				By(Normalized, finite, fold, int_sum.IntSumBridge.At(T, g)))
		}),
})}

// SignedBooleanCast carries both choices of sign and both Boolean values into the reals.
var SignedBooleanCast = signedBooleanCastThm{family.Add(registry.ProofEntry{
	Name: "SignedBooleanCast",
	Key:  "prop_de3f355a829e01bc",
	Build: family.Theorem(Statement{
		Binders: "∀p q:bool.",
		Conclusion: "real_of_int(COND(q, «IntegerValue», -«IntegerValue»)) = " +
			"COND(q, «RealValue», -«RealValue»)",
		Abbrev: Abbrev{
			{Name: "IntegerValue", Text: "COND(p, int_of_num(1), int_of_num(0))"},
			{Name: "RealValue", Text: "COND(p, real_of_num(1), real_of_num(0))"},
		},
	}, func(a *Argument, p, q *Expr[Bool]) {
		sign := func(b *Argument, value Fact) {
			b.Cases(q)
			b.When(
				"the positive sign preserves the numeral",
				func(c *Argument, positive Fact) {
					c.Show(
						"embed the numeral",
						By(value, positive, int_construction.OfNumBridge))
				})
			b.Otherwise(
				"the negative sign negates the numeral",
				func(c *Argument, negative Fact) {
					c.Show(
						"embedding commutes with negation",
						ByArith(value, negative, int_construction.OfNumBridge, int_construction.NegBridge))
				})
		}
		a.Cases(p)
		a.When(
			"the Boolean value is one",
			sign)
		a.Otherwise(
			"the Boolean value is zero",
			sign)
	}),
})}

// CoefficientAsSum reads the top coefficient on a face as the alternating sum of its Boolean values.
var CoefficientAsSum = coefficientAsSumThm{family.Add(registry.ProofEntry{
	Name: "CoefficientAsSum",
	Key:  "prop_bb2c94aa12a9eacc",
	Build: family.Theorem(Statement{
		Binders:    "∀S:set(A). ∀f:(set(A) → bool).",
		Hypotheses: []string{"finite(S)"},
		Conclusion: "real_of_int(boolean_coefficient(f, S)) = " +
			"sum(«Face», λX:set(A). COND(nat_even(card(S ∖ X)), COND(f(X), &1, &0), -COND(f(X), &1, &0)))",
		Abbrev: Abbrev{
			{Name: "Face", Text: "{X:set(A) | X ⊆ S}"},
			{Name: "Value", Text: "λX:set(A). COND(f(X), int_of_num(1), int_of_num(0))"},
		},
	}, func(a *Argument, S *Expr[Set[A]], f *Arrow[Set[A], Bool], finite Fact) {
		face := a.Have(
			"the face has finitely many inputs",
			"finite(«Face»)",
			By(finite, finite_set.FinitePowerset.At(S)))
		a.Show(
			"unfold the coefficient and transport its signed values",
			Unfold(BooleanCoefficientDef),
			Unfold(multilinear_polynomial.MultilinearCoeffDef),
			Simp(Rev(SignedBooleanCast)),
			By(
				face,
				RealOfIntegerFold.At(a.TermAs[Set[Set[A]]]("«Face»"),
					a.TermAs[Fun[Set[A], Int]]("λX:set(A). COND(nat_even(card(S ∖ X)), «Value»(X), -«Value»(X))"))))
	}),
})}

// RealBooleanCoefficient identifies the integer Boolean coefficient with the coefficient of the real multilinear representation.
var RealBooleanCoefficient = realBooleanCoefficientThm{family.Add(registry.ProofEntry{
	Name: "RealBooleanCoefficient",
	Key:  "prop_8dfc188517ae16dd",
	Build: family.Theorem(Statement{
		Binders:    "∀S:set(A). ∀f:(set(A) → bool).",
		Hypotheses: []string{"finite(S)"},
		Conclusion: "real_of_int(boolean_coefficient(f, S)) = " +
			"multilinear_coeff(real_ring, λX:set(A). COND(f(X), &1, &0), S)",
		Abbrev: Abbrev{{Name: "Value", Text: "λX:set(A). COND(f(X), &1, &0)"}},
	}, func(a *Argument, S *Expr[Set[A]], f *Arrow[Set[A], Bool], finite Fact) {
		a.Show(
			"the real coefficient and the embedded integer coefficient have the same alternating sum",
			Unfold(multilinear_polynomial.MultilinearCoeffDef),
			By(
				finite,
				finite_set.FinitePowerset.At(S),
				CoefficientAsSum.At(S, f),
				real_sum.RealModuleSum.At(
					a.TermAs[Fun[Set[A], Real]]("λX:set(A). COND(nat_even(card(S ∖ X)), «Value»(X), -«Value»(X))"),
					a.TermAs[Set[Set[A]]]("{X:set(A) | X ⊆ S}"))))
	}),
})}
