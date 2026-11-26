package real_closed_instance

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/real_closed_field"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial"
	_ "github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_algebra"
	"github.com/euc-ai/xugo/library/proofs/algebra/ring/polynomial/polynomial_evaluation"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ordered_instance"
	"github.com/euc-ai/xugo/library/proofs/real/real_polynomial"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	_ "github.com/euc-ai/xugo/library/proofs/sets/cardinality"
	_ "github.com/euc-ai/xugo/library/proofs/sets/finite_set"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	_ "github.com/euc-ai/xugo/library/proofs/topology/topological_space"
	"github.com/euc-ai/xugo/library/registry"
)

// PolynomialFunctionBridge — a coefficient sequence of finite support,
// evaluated on ℝ, is a real polynomial function. Evaluation sums the
// monomials p(i)·xⁱ over the support, which is finite, and a finite sum of
// monomials is a polynomial function.
var PolynomialFunctionBridge = polynomialFunctionBridgeThm{family.Add(registry.ProofEntry{
	Name: "PolynomialFunctionBridge",
	Key:  "prop_817a5858b326c5fd",
	Build: family.Theorem(Statement{
		Binders: "∀p:(num → real).",
		Hypotheses: []string{
			"polynomial_over(&0, 𝕌, p)",
		},
		Conclusion: "polynomial_function(λx:real. polynomial_eval(real_add, &0, real_mul, &1, p, x))",
	}, func(a *Argument, p *Arrow[Nat, Real], over Fact) {
		support := a.Have(
			"only finitely many coefficients are nonzero",
			"finite(fun_support(&0, p))",
			By(over, polynomial.PolynomialFiniteSupport))
		monomials := a.Have(
			"each monomial p(i)·xⁱ is a polynomial function",
			"∀i:num. polynomial_function(λx:real. p(i) * x ^ i)",
			By(real_polynomial.ScalarLeft, real_polynomial.Pow, real_polynomial.Id))
		evaluation := a.Have(
			"evaluation is the real sum of the monomials over the support",
			"∀x:real. "+
				"    polynomial_eval(real_add, &0, real_mul, &1, p, x) = Σ_{i∈fun_support(&0, p)} p(i) * x ^ i",
			By(support, polynomial_evaluation.PolynomialEvalDef, real_sum.RealModuleSum, real_pow.MonoidPow))
		a.Show(
			"a finite sum of polynomial functions is one",
			Simp(Fwd(evaluation)),
			By(support, monomials, real_polynomial.Sum))
	}),
})}

// PolynomialIntermediateValue — a real polynomial negative at a and positive
// at a later point b has a root strictly between them: its evaluation is a
// polynomial function, so it is continuous on ⟦a, b⟧, the intermediate value
// theorem gives it a root in ⟦a, b⟧, and the root is neither endpoint, where
// the polynomial is not zero.
var PolynomialIntermediateValue = polynomialIntermediateValueThm{family.Add(registry.ProofEntry{
	Name: "PolynomialIntermediateValue",
	Key:  "prop_ac8740f24b89b461",
	Build: family.Theorem(Statement{
		Binders: "∀p:(num → real). ∀a b:real.",
		Hypotheses: []string{
			"polynomial_over(&0, 𝕌, p)",
			"a < b",
			"polynomial_eval(real_add, &0, real_mul, &1, p, a) < &0",
			"&0 < polynomial_eval(real_add, &0, real_mul, &1, p, b)",
		},
		Conclusion: "∃x:real. a < x ∧ x < b ∧ polynomial_eval(real_add, &0, real_mul, &1, p, x) = &0",
	}, func(arg *Argument, p *Arrow[Nat, Real], a, b *Expr[Real], over, ab, negative, positive Fact) {
		value := arg.TermAs[Fun[Real, Real]]("λx:real. polynomial_eval(real_add, &0, real_mul, &1, p, x)")
		polynomialFunction := arg.Have(
			"evaluation of p is a real polynomial function",
			"polynomial_function(λx:real. polynomial_eval(real_add, &0, real_mul, &1, p, x))",
			By(over, PolynomialFunctionBridge))
		continuity := arg.Have(
			"so it is continuous on ⟦a, b⟧",
			"real_continuous_on(⟦a, b⟧, λx:real. polynomial_eval(real_add, &0, real_mul, &1, p, x))",
			By(
				polynomialFunction,
				real_continuous.PolynomialFunctionContinuous.At(value),
				real_continuous.ContinuousMapIffPointwise.At(value),
				real_continuous.ContinuousAtOn.At(value, arg.TermAs[Set[Real]]("⟦a, b⟧"))))
		x, root := arg.ObtainAs[Real](
			"the intermediate value theorem gives a root in ⟦a, b⟧",
			"∃x:real. a ≤ x ∧ x ≤ b ∧ polynomial_eval(real_add, &0, real_mul, &1, p, x) = &0",
			By(
				continuity,
				ab,
				negative,
				positive,
				real_continuous.IntermediateValue.At(value, a, b, arg.TermAs[Real]("&0")),
				real_order_ring.LessEqOfLessThan))
		bounds := arg.Conjuncts(
			root,
			"x is at least a",
			"x is at most b",
			"x is a root")
		aboveA := arg.Have(
			"x is not a, where p is negative",
			"a < x",
			By(bounds[2], bounds[0], negative, real_order_ring.LessEqSplit, real_order_ring.LessThanIrrefl))
		belowB := arg.Have(
			"x is not b, where p is positive",
			"x < b",
			By(bounds[2], bounds[1], positive, real_order_ring.LessEqSplit, real_order_ring.LessThanIrrefl))
		arg.Take(x)
		arg.Show(
			"x is a root strictly between a and b",
			By(aboveA, belowB, bounds[2]))
	}),
})}

// RealClosed — the reals with their strict order are a real closed field:
// they are an ordered field, and a real polynomial that rises through zero
// has a root strictly between the two points.
var RealClosed = realClosedThm{family.Add(registry.ProofEntry{
	Name: "RealClosed",
	Key:  "prop_9f9eef19f78c0a1b",
	Reading: "This concrete instance is a consumer of the " +
		"abstract foundation and is not used by its QE proof.",
	Build: family.Instance(real_closed_field.RealClosedField, "real_closed_field(real_field_ops, "+
		"    real_lt)",
		Case(
			"ℝ with its strict order is an ordered field",
			By(real_ordered_instance.RealOrderedField)),
		Case(
			"a real polynomial negative at a and positive at a later point b has a root strictly between them",
			Simp(Fwd(set_basic.InUniv)),
			By(PolynomialIntermediateValue))),
})}
