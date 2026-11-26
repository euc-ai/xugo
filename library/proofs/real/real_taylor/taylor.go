// taylor.go — Taylor's theorem with the Lagrange remainder. The Taylor
// sum of f = D(0) about a centre y, read at x, is Σ_{k ≤ n} D(k)(y)·(x −
// y)^k/k!, where D(k + 1) is the derivative of D(k). As a function of its
// centre the sum telescopes under differentiation: the derivative of each
// term's power (x − y)^k/k! cancels the derivative of the term before it,
// and what survives is D(n + 1)(y)·(x − y)^n/n!.

package real_taylor

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// PowerFactorialDerivative — as a function of t, (x − t)^(m+1)/(m + 1)!
// has derivative −(x − t)^m/m!.
//
// t ↦ x − t has derivative −1, so by the chain rule (x − t)^(m+1) has
// derivative −(m + 1)·(x − t)^m; dividing by (m + 1)! = (m + 1)·m! leaves
// −(x − t)^m/m!.
var PowerFactorialDerivative = powerFactorialDerivativeThm{family.Add(registry.ProofEntry{
	Name: "PowerFactorialDerivative",
	Key:  "prop_11d359217f0cde22",
	Build: family.Theorem(
		"∀m:num. ∀x y:real. "+
			"    real_derivative_at(λt:real. real_pow(x - t, m + 1) / &factorial(m + 1), "+
			"        y, "+
			"        -(real_pow(x - y, m) / &factorial(m)))",
		func(a *Argument, m *Expr[Nat], x, y *Expr[Real]) {
			difference := a.TermAs[Fun[Real, Real]]("λt:real. x - t")
			power := a.TermAs[Fun[Real, Real]]("λu:real. real_pow(u, m + 1)")
			inverse := a.TermAs[Real]("real_inv(&factorial(m + 1))")
			slope := a.TermAs[Real]("&(m + 1) * real_pow(x - y, m) * (&0 - &1)")
			line := a.Have(
				"t ↦ x − t has derivative 0 − 1",
				"real_derivative_at(λt:real. x - t, y, &0 - &1)",
				By(
					real_derivative.DerivativeSub.At(
						a.TermAs[Fun[Real, Real]]("λt:real. x"),
						a.TermAs[Fun[Real, Real]]("λt:real. t"),
						y,
						a.TermAs[Real]("&0"),
						a.TermAs[Real]("&1")),
					real_derivative.DerivativeConst.At(x, y),
					real_derivative.DerivativeId.At(y)))
			composite := a.Have(
				"by the chain rule through u ↦ u^(m+1), (x − t)^(m+1) has derivative (m + 1)·(x − y)^m·(0 − 1)",
				"real_derivative_at((λu:real. real_pow(u, m + 1)) ∘ (λt:real. x - t), "+
					"    y, "+
					"    &(m + 1) * real_pow(x - y, m) * (&0 - &1))",
				By(
					real_derivative.DerivativeChain.At(power, difference, y,
						a.TermAs[Real]("&(m + 1) * real_pow(x - y, m)"), a.TermAs[Real]("&0 - &1")),
					line,
					real_derivative.DerivativePowSuc.At(m, a.TermAs[Real]("x - y"))))
			// The composite read pointwise, λt. (x − t)^(m+1), as the product rule below takes it.
			powerRate := a.Unfolded(composite, functions.ComposeApply)

			// Dividing by (m + 1)! is multiplying by its inverse, a constant.
			a.Do(Unfold(real_field.RealDivDef))
			positive := a.Have(
				"m + 1 is positive",
				"&0 < &suc(m)",
				ByArith())
			rate := a.Have(
				"(m + 1)/(m + 1)! = 1/m!, as (m + 1)! = (m + 1)·m!",
				"&(m + 1) * real_pow(x - y, m) * (&0 - &1) * real_inv(&factorial(m + 1)) + "+
					"real_pow(x - y, m + 1) * &0 = "+
					"-(real_pow(x - y, m) * real_inv(&factorial(m)))",
				Simp(
					Rev(nat_arith.Add1),
					Fwd(nat_arith.Factorial),
					Fwd(real_construction.OfNumMul),
					Fwd(field.InvMul.Read(real_field.Field))),
				ByArith(positive))
			a.Show(
				"the product rule with the constant factor 1/(m + 1)!",
				By(
					rate,
					powerRate,
					real_derivative.DerivativeMul.At(
						a.TermAs[Fun[Real, Real]]("λt:real. real_pow(x - t, m + 1)"),
						a.TermAs[Fun[Real, Real]]("λt:real. real_inv(&factorial(m + 1))"),
						y,
						slope,
						a.TermAs[Real]("&0")),
					real_derivative.DerivativeConst.At(inverse, y)))
		}),
})}

// TaylorSumRecursion — the Taylor sum Σ_{k ≤ n} D(k)(t)·(x − t)^k/k!, as
// a function of its centre t, is D(0) to order 0, and to order n + 1 it
// is the sum to n plus the new term D(n + 1)(t)·(x − t)^(n+1)/(n + 1)!.
//
// At each t the sum over 0 .. 0 is its one term, (x − t)⁰ = 1 and 0! = 1,
// and the sum over 0 .. n + 1 is the sum over 0 .. n and its last term;
// functions with the same values are equal.
var TaylorSumRecursion = taylorSumRecursionThm{family.Add(registry.ProofEntry{
	Name: "TaylorSumRecursion",
	Key:  "prop_e90232377fbb5730",
	Build: family.Theorem(
		"∀D:(num → real → real). ∀n:num. ∀x:real. "+
			"    (λt:real. Σ_{k∈0 .. 0} D(k)(t) * real_pow(x - t, k) / &factorial(k)) = D(0) ∧ "+
			"    (λt:real. Σ_{k∈0 .. n + 1} D(k)(t) * real_pow(x - t, k) / &factorial(k)) = "+
			"    (λt:real. "+
			"        Σ_{k∈0 .. n} D(k)(t) * real_pow(x - t, k) / &factorial(k) + "+
			"        D(n + 1)(t) * (real_pow(x - t, n + 1) / &factorial(n + 1)))",
		func(a *Argument, D *Arrow[Nat, Fun[Real, Real]], n *Expr[Nat], x *Expr[Real]) {
			single := a.Have(
				"the sum over 0 .. 0 is its one term D(0)(t), as (x − t)⁰ = 1 and 0! = 1",
				"∀t:real. Σ_{k∈0 .. 0} D(k)(t) * real_pow(x - t, k) / &factorial(k) = D(0)(t)",
				Simp(Fwd(real_sum.IntervalPoint), Fwd(real_pow.PowExpZeroClause), Fwd(nat_arith.Factorial)),
				ByArith())
			peel := a.Have(
				"the sum over 0 .. n + 1 is the sum over 0 .. n plus its last term",
				"∀t:real. "+
					"    Σ_{k∈0 .. n + 1} D(k)(t) * real_pow(x - t, k) / &factorial(k) = "+
					"    Σ_{k∈0 .. n} D(k)(t) * real_pow(x - t, k) / &factorial(k) + "+
					"    D(n + 1)(t) * (real_pow(x - t, n + 1) / &factorial(n + 1))",
				Simp(Rev(nat_arith.Add1)),
				Simp(Fwd(real_sum.IntervalClauses), Fwd(nat_arith.Add1), Fwd(nat_order.ZeroLessEq)),
				ByArith())
			a.Show(
				"so the two equations hold between the sums as functions of t",
				By(single, peel))
		}),
})}

// TaylorSumDerivative — the Taylor sum Σ_{k ≤ n} D(k)(t)·(x − t)^k/k!,
// as a function of its centre t, has derivative D(n + 1)(y)·(x − y)^n/n!
// at y wherever each D(k), k ≤ n, has derivative D(k + 1)(y) there.
//
// By induction on n. For n = 0 the sum is D(0) itself. Write T for the
// sum to n and T'(y) = D(n + 1)(y)·(x − y)^n/n! for its derivative, and
// Q(t) = (x − t)^(n+1)/(n + 1)!, whose derivative is Q'(t) = −(x − t)^n/n!.
// The sum to n + 1 is T plus the new term D(n + 1)(t)·Q(t), whose
// derivative by the product rule is D(n + 2)(y)·Q(y) + D(n + 1)(y)·Q'(y);
// its second part cancels T'(y).
var TaylorSumDerivative = taylorSumDerivativeThm{family.Add(registry.ProofEntry{
	Name: "TaylorSumDerivative",
	Key:  "prop_ef7590e0b09d2aa9",
	Build: family.Theorem(Statement{
		Binders: "∀D:(num → real → real). ∀n:num. ∀x y:real.",
		Hypotheses: []string{
			"∀k:num. k ≤ n ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
		},
		Conclusion: "real_derivative_at( " +
			"    λt:real. Σ_{k∈0 .. n} D(k)(t) * real_pow(x - t, k) / &factorial(k), " +
			"    y, " +
			"    D(n + 1)(y) * real_pow(x - y, n) / &factorial(n))",
		Abbrev: Abbrev{
			{Name: "T", Text: "λt:real. Σ_{k∈0 .. n} D(k)(t) * real_pow(x - t, k) / &factorial(k)"},
			{Name: "T'", Text: "λt:real. D(n + 1)(t) * real_pow(x - t, n) / &factorial(n)"},
			{Name: "Q", Text: "λt:real. real_pow(x - t, n + 1) / &factorial(n + 1)"},
			{Name: "Q'", Text: "λt:real. -(real_pow(x - t, n) / &factorial(n))"},
		},
	},
		func(a *Argument, D *Arrow[Nat, Fun[Real, Real]]) {
			a.Induct("n")
			a.Base(
				"for n = 0 the sum is its one term D(0)(t), with derivative D(1)(y)",
				func(b *Argument) {
					b.FixAs[Real]()
					b.FixAs[Real]()
					given := b.Assume()
					rate := b.Have(
						"the claimed derivative is D(1)(y), as (x − y)⁰ = 1 and 0! = 1",
						"D(0 + 1)(y) * real_pow(x - y, 0) / &factorial(0) = D(0 + 1)(y)",
						ByArith(nat_arith.Factorial))
					b.Do(Simp(Fwd(TaylorSumRecursion)))
					b.Show(
						"the sum to 0 is D(0), which has derivative D(1)(y) at y",
						By(given.At(b.TermAs[Nat]("0")), rate, nat_order.LessEqRefl))
				})
			a.Step(
				"the sum to n + 1 adds D(n + 1)(t)·Q(t), Q(t) = (x − "+
					"t)^(n+1)/(n + 1)!, whose derivative cancels the sum's own",
				func(b *Argument, ih Fact) {
					x := b.FixAs[Real]()
					y := b.FixAs[Real]()
					given := b.Assume()
					lower := b.Have(
						"the derivatives of D(k) for k ≤ n are among those given",
						"∀k:num. k ≤ n ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
						Derive(func(c *Argument) {
							k := c.FixAs[Nat]()
							below := c.Assume()
							c.Show(
								"k ≤ n ≤ n + 1",
								ByArith(given.At(k), below))
						}))
					old := b.Have(
						"by induction, T, the sum to n, has derivative T'(y) = D(n + 1)(y)·(x − y)ⁿ/n!",
						"real_derivative_at(«T», y, «T'»(y))",
						By(ih.At(x, y), lower))
					top := b.Have(
						"D(n + 1) has derivative D(n + 1 + 1)(y)",
						"real_derivative_at(D(n + 1), y, D(n + 1 + 1)(y))",
						ByArith(given.At(b.TermAs[Nat]("n + 1"))))
					freshRate := b.TermAs[Real]("D(n + 1 + 1)(y) * «Q»(y) + D(n + 1)(y) * «Q'»(y)")
					fresh := b.Have(
						"by the product rule the new term has derivative D(n + "+
							"2)(y)·Q(y) + D(n + 1)(y)·Q'(y), Q' = −(x − t)ⁿ/n! being Q's",
						"real_derivative_at(λt:real. D(n + 1)(t) * «Q»(t), "+
							"    y, "+
							"    D(n + 1 + 1)(y) * «Q»(y) + D(n + 1)(y) * «Q'»(y))",
						By(
							top,
							At(PowerFactorialDerivative, b.TermAs[Nat]("n"), x, y),
							real_derivative.DerivativeMul.At(
								b.TermAs[Fun[Real, Real]]("D(n + 1)"),
								b.TermAs[Fun[Real, Real]]("«Q»"),
								y,
								b.TermAs[Real]("D(n + 1 + 1)(y)"),
								b.TermAs[Real]("«Q'»(y)"))))
					both := b.Have(
						"so T plus the new term has the sum of the two derivatives",
						"real_derivative_at(λt:real. «T»(t) + D(n + 1)(t) * «Q»(t), "+
							"    y, "+
							"    «T'»(y) + (D(n + 1 + 1)(y) * «Q»(y) + D(n + 1)(y) * «Q'»(y)))",
						By(
							old,
							fresh,
							real_derivative.DerivativeAdd.At(
								b.TermAs[Fun[Real, Real]]("«T»"),
								b.TermAs[Fun[Real, Real]]("λt:real. D(n + 1)(t) * «Q»(t)"),
								y,
								b.TermAs[Real]("«T'»(y)"),
								freshRate)))
					rate := b.Have(
						"T'(y) and D(n + 1)(y)·Q'(y) cancel",
						"«T'»(y) + (D(n + 1 + 1)(y) * «Q»(y) + D(n + 1)(y) * «Q'»(y)) = "+
							"D(n + 1 + 1)(y) * real_pow(x - y, n + 1) / &factorial(n + 1)",
						ByArith())
					b.Do(Simp(Fwd(nat_arith.Add1), Fwd(TaylorSumRecursion)))
					b.Show(
						"the sum to n + 1 is the sum to n plus the new term, "+
							"and what survives is D(n + 2)(y)·(x − y)^(n+1)/(n + 1)!",
						By(rate, both))
				})
		}),
})}

// TaylorLagrange — Taylor's theorem with the Lagrange remainder on an
// interval ⟦a, b⟧ whose two ends are the centre c and the point x, in
// either order: D(0)(x) is its Taylor sum about c plus D(n + 1)(z)·(x −
// c)^(n+1)/(n + 1)! for some z strictly between a and b.
//
// Write T(y) for the Taylor sum about y read at x, R(y) = D(0)(x) − T(y)
// for what it leaves of D(0)(x), and Q(y) for (x − y)^(n+1)/(n + 1)!.
// The function h(y) = Q(c)·R(y) − R(c)·Q(y) vanishes at c, and at x too,
// where T(x) = D(0)(x) and Q(x) = 0. It is continuous on ⟦a, b⟧, and
// inside, T having the telescoped derivative T'(y) = D(n + 1)(y)·(x −
// y)^n/n! and Q the derivative Q'(y) = −(x − y)^n/n!, h has derivative
// Q(c)·(0 − T'(y)) − R(c)·Q'(y) = (x − y)^n/n!·(R(c) − D(n + 1)(y)·Q(c)).
// Rolle's theorem gives z where this is 0; z is not x, so (x − z)^n ≠ 0,
// and R(c) = D(n + 1)(z)·Q(c), which is the expansion.
var TaylorLagrange = taylorLagrangeThm{family.Add(registry.ProofEntry{
	Name: "TaylorLagrange",
	Key:  "prop_41f0773001618ff5",
	Build: family.Sections(Statement{
		Binders: "∀D:(num → real → real). ∀n:num. ∀a b c x:real.",
		Hypotheses: []string{
			"a < b",
			"c = a ∧ x = b ∨ c = b ∧ x = a",
			"∀k:num. k ≤ n ⇒ real_continuous_on(⟦a, b⟧, D(k))",
			"∀k:num. ∀y:real. k ≤ n ∧ a < y ∧ y < b ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
		},
		Conclusion: "∃z:real. " +
			"    a < z ∧ " +
			"    z < b ∧ " +
			"    D(0)(x) = «taylorSum» + D(n + 1)(z) * real_pow(x - c, n + 1) / &factorial(n + 1)",
		Abbrev: Abbrev{
			{Name: "T", Text: "λy:real. Σ_{k∈0 .. n} D(k)(y) * real_pow(x - y, k) / &factorial(k)"},
			{Name: "R", Text: "λy:real. D(0)(x) - «T»(y)"},
			{Name: "Q", Text: "λy:real. real_pow(x - y, n + 1) / &factorial(n + 1)"},
			{Name: "T'", Text: "λy:real. D(n + 1)(y) * real_pow(x - y, n) / &factorial(n)"},
			{Name: "Q'", Text: "λy:real. -(real_pow(x - y, n) / &factorial(n))"},
			{Name: "h", Text: "λy:real. «Q»(c) * «R»(y) - «R»(c) * «Q»(y)"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// The Taylor sum, as a function of its centre, is continuous on
			// any set on which D(0), …, D(n) are: by induction, each new term
			// is D(n + 1) times the continuous Q.
			sumContinuous := ctx.Lemma(Statement{
				Binders: "∀D:(num → real → real). ∀n:num. ∀x:real. ∀s:set(real).",
				Hypotheses: []string{
					"∀k:num. k ≤ n ⇒ real_continuous_on(s, D(k))",
				},
				Conclusion: "real_continuous_on(s, «T»)",
			},
				func(arg *Argument, D *Arrow[Nat, Fun[Real, Real]]) {
					arg.Induct("n")
					arg.Base(
						"for n = 0 the sum is D(0)",
						func(b *Argument) {
							b.FixAs[Real]()
							b.FixAs[Set[Real]]()
							given := b.Assume()
							b.Do(Simp(Fwd(TaylorSumRecursion)))
							b.Show(
								"the sum to 0 is D(0), which is continuous on s",
								By(given.At(b.TermAs[Nat]("0")), nat_order.LessEqRefl))
						})
					arg.Step(
						"the sum to n + 1 adds D(n + 1)(y)·Q(y), a product of continuous functions",
						func(b *Argument, ih Fact) {
							x := b.FixAs[Real]()
							s := b.FixAs[Set[Real]]()
							given := b.Assume()
							T := b.TermAs[Fun[Real, Real]]("«T»")
							Q := b.TermAs[Fun[Real, Real]]("«Q»")
							lower := b.Have(
								"D(k) is continuous on s for k ≤ n",
								"∀k:num. k ≤ n ⇒ real_continuous_on(s, D(k))",
								Derive(func(c *Argument) {
									k := c.FixAs[Nat]()
									below := c.Assume()
									c.Show(
										"k ≤ n ≤ n + 1",
										ByArith(given.At(k), below))
								}))
							old := b.Have(
								"by induction T, the sum to n, is continuous on s",
								"real_continuous_on(s, «T»)",
								By(ih.At(x, s), lower))
							top := b.Have(
								"D(n + 1) is continuous on s",
								"real_continuous_on(s, D(n + 1))",
								ByArith(given.At(b.TermAs[Nat]("n + 1"))))
							QContinuous := b.Have(
								"Q, having a derivative everywhere, is continuous on s",
								"real_continuous_on(s, «Q»)",
								By(
									real_derivative.DerivativeContinuousOn.At(
										Q,
										b.TermAs[Fun[Real, Real]]("«Q'»"),
										s),
									PowerFactorialDerivative))
							fresh := b.Have(
								"so the new term D(n + 1)·Q, their product, is continuous on s",
								"real_continuous_on(s, λy:real. D(n + 1)(y) * «Q»(y))",
								By(
									top,
									QContinuous,
									real_continuous.ContinuousOnMul.At(b.TermAs[Fun[Real, Real]]("D(n + 1)"), Q, s)))
							both := b.Have(
								"and so is T plus the new term",
								"real_continuous_on(s, λy:real. «T»(y) + D(n + 1)(y) * «Q»(y))",
								By(
									old,
									fresh,
									real_continuous.ContinuousOnAdd.At(
										T,
										b.TermAs[Fun[Real, Real]]("λy:real. D(n + 1)(y) * «Q»(y)"),
										s)))
							b.Do(Simp(Fwd(nat_arith.Add1), Fwd(TaylorSumRecursion)))
							b.Show(
								"the sum to n + 1 is that sum, so it is continuous on s",
								By(both))
						})
				})

			return ctx.Theorem(headline, func(
				arg *Argument,
				D *Arrow[Nat, Fun[Real, Real]],
				n *Expr[Nat],
				a, b, c, x *Expr[Real],
				ordered, ends, continuous, derivatives Fact,
			) {
				segment := arg.TermAs[Set[Real]]("⟦a, b⟧")
				T := arg.TermAs[Fun[Real, Real]]("«T»")
				R := arg.TermAs[Fun[Real, Real]]("«R»")
				Q := arg.TermAs[Fun[Real, Real]]("«Q»")
				h := arg.TermAs[Fun[Real, Real]]("«h»")
				hPrime := arg.TermAs[Fun[Real, Real]]("λy:real. «Q»(c) * (&0 - «T'»(y)) - «R»(c) * «Q'»(y)")
				value := arg.TermAs[Real]("D(0)(x)")
				Rc := arg.TermAs[Real]("«R»(c)")
				Qc := arg.TermAs[Real]("«Q»(c)")
				// The constant D(0)(x) that R subtracts T from, and the two
				// terms of h, Q(c)·R and R(c)·Q, as functions of y.
				valueConstant := arg.TermAs[Fun[Real, Real]]("λy:real. D(0)(x)")
				QcR := arg.TermAs[Fun[Real, Real]]("λy:real. «Q»(c) * «R»(y)")
				RcQ := arg.TermAs[Fun[Real, Real]]("λy:real. «R»(c) * «Q»(y)")

				TOnSegment := arg.Have(
					"T, the Taylor sum as a function of its centre, is continuous on ⟦a, b⟧",
					"real_continuous_on(⟦a, b⟧, «T»)",
					By(At(sumContinuous, D, n, x, segment), continuous))
				QOnSegment := arg.Have(
					"so is Q, having a derivative everywhere",
					"real_continuous_on(⟦a, b⟧, «Q»)",
					By(
						real_derivative.DerivativeContinuousOn.At(
							Q,
							arg.TermAs[Fun[Real, Real]]("«Q'»"),
							segment),
						PowerFactorialDerivative))
				hContinuous := arg.Have(
					"so h, built from T, Q and the constants D(0)(x), Q(c) and "+
						"R(c) by products and differences, is continuous on ⟦a, b⟧",
					"real_continuous_on(⟦a, b⟧, «h»)",
					By(
						real_continuous.ContinuousOnConst.At(value, segment),
						real_continuous.ContinuousOnConst.At(Qc, segment),
						real_continuous.ContinuousOnConst.At(Rc, segment),
						TOnSegment,
						QOnSegment,
						real_continuous.ContinuousOnSub.At(valueConstant, T, segment),
						real_continuous.ContinuousOnMul.At(arg.TermAs[Fun[Real, Real]]("λy:real. «Q»(c)"), R, segment),
						real_continuous.ContinuousOnMul.At(arg.TermAs[Fun[Real, Real]]("λy:real. «R»(c)"), Q, segment),
						real_continuous.ContinuousOnSub.At(QcR, RcQ, segment)))
				hDerivative := arg.Have(
					"inside ⟦a, b⟧, h has derivative Q(c)·(0 − T'(y)) − R(c)·Q'(y)",
					"∀y:real. a < y ∧ y < b ⇒ real_derivative_at(«h», y, «Q»(c) * (&0 - «T'»(y)) - «R»(c) * «Q'»(y))",
					Derive(func(d *Argument) {
						y := d.FixAs[Real]()
						inside := d.Assume()
						TRate := d.TermAs[Real]("«T'»(y)")
						RRate := d.TermAs[Real]("&0 - «T'»(y)")
						QRate := d.TermAs[Real]("«Q'»(y)")
						atY := d.Have(
							"each D(k), k ≤ n, has its derivative at y",
							"∀k:num. k ≤ n ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
							By(derivatives, inside))
						RDerivative := d.Have(
							"by the telescoped derivative T'(y) of T, R has derivative 0 − T'(y)",
							"real_derivative_at(«R», y, &0 - «T'»(y))",
							By(
								atY,
								At(TaylorSumDerivative, D, n, x, y),
								real_derivative.DerivativeSub.At(valueConstant, T, y, d.TermAs[Real]("&0"), TRate),
								real_derivative.DerivativeConst.At(value, y)))
						d.Show(
							"h is Q(c) times R less R(c) times Q",
							By(
								RDerivative,
								At(PowerFactorialDerivative, n, x, y),
								real_derivative.DerivativeScale.At(R, y, RRate, Qc),
								real_derivative.DerivativeScale.At(Q, y, QRate, Rc),
								real_derivative.DerivativeSub.At(
									QcR,
									RcQ,
									y,
									d.TermAs[Real]("«Q»(c) * (&0 - «T'»(y))"),
									d.TermAs[Real]("«R»(c) * «Q'»(y)"))))
					}))

				atCentre := arg.TermAs[Fun[Nat, Real]]("λk:num. D(k)(x) * real_pow(x - x, k) / &factorial(k)")
				tail := arg.Have(
					"read at x itself, every term past the first vanishes, (x − x)^k being 0 for k ≥ 1",
					"∀i:num. 1 ≤ i ∧ i ≤ n ⇒ D(i)(x) * real_pow(x - x, i) / &factorial(i) = &0",
					Derive(func(d *Argument) {
						d.FixAs[Nat]()
						bounds := d.Assume()
						d.Show(
							"0^i = 0 for i ≠ 0",
							Simp(Fwd(real_ring.SubRefl), Fwd(real_pow.ZeroPow)),
							ByArith(bounds))
					}))
				centre := arg.Have(
					"so T(x), the Taylor sum about x read at x, is D(0)(x)",
					"«T»(x) = D(0)(x)",
					ByArith(
						tail,
						real_sum.PeelLeft.At(arg.TermAs[Nat]("0"), n, atCentre),
						real_sum.IntervalEqZero.At(arg.TermAs[Nat]("1"), n, atCentre),
						nat_order.ZeroLessEq.At(n),
						nat_arith.Factorial))
				fallingAtX := arg.Have(
					"and (x − x)^(n+1) = 0",
					"real_pow(x - x, n + 1) = &0",
					ByArith(real_pow.PowAddOne.At(arg.TermAs[Real]("x - x"), n)))
				atC := arg.Have(
					"h vanishes at c",
					"«h»(c) = &0",
					ByArith())
				atX := arg.Have(
					"and at x, where R(x) = 0 and Q(x) = 0",
					"«h»(x) = &0",
					ByArith(centre, fallingAtX))
				level := arg.Have(
					"c and x being the two ends, h takes the same value at a and at b",
					"«h»(a) = «h»(b)",
					By(atC, atX, ends))

				z, found := arg.ObtainAs[Real](
					"Rolle's theorem for h hands a point z strictly between a and b where its derivative vanishes",
					"∃z:real. a < z ∧ z < b ∧ «Q»(c) * (&0 - «T'»(z)) - «R»(c) * «Q'»(z) = &0",
					By(real_derivative.Rolle.At(h, hPrime, a, b), ordered, level, hContinuous, hDerivative))
				parts := arg.Conjuncts(
					found,
					"a < z",
					"z < b",
					"the derivative of h vanishes at z")
				apart := arg.Have(
					"z lies strictly inside ⟦a, b⟧ and x is one of its ends, so z ≠ x",
					"&0 < |x - z|",
					ByArith(parts[0], parts[1], ends))
				distance := arg.TermAs[Real]("|x - z|")
				gap := arg.TermAs[Real]("real_pow(x - z, n)")
				lengthPower := arg.Have(
					"|x − z|ⁿ is positive",
					"&0 < real_pow(|x - z|, n)",
					By(real_pow.PowPos.At(distance, n), apart))
				gapNonzero := arg.Have(
					"so (x − z)ⁿ, whose size it is, is not 0",
					"real_pow(x - z, n) ≠ &0",
					By(
						lengthPower,
						real_pow.AbsPow.At(arg.TermAs[Real]("x - z"), n),
						real_sgn_abs.AbsPosIffNonzero.At(gap)))
				factorialPositive := arg.Have(
					"n! is not 0, so its image in ℝ is positive",
					"&0 < &factorial(n)",
					ByArith(
						nat_arith.FactorialNonzero.At(n),
						real_order_ring.OfNumLessThan.At(arg.TermAs[Nat]("0"), arg.TermAs[Nat]("factorial(n)"))))
				cleared := arg.Have(
					"multiplying the vanishing derivative by n!",
					"«Q»(c) * (&0 - D(n + 1)(z) * real_pow(x - z, n)) - «R»(c) * -real_pow(x - z, n) = &0",
					ByArith(factorialPositive, Scaled(arg.TermAs[Real]("&factorial(n)"), parts[2])))
				rest := arg.Have(
					"and cancelling (x − z)ⁿ ≠ 0: R(c) = D(n + 1)(z)·Q(c)",
					"«R»(c) = D(n + 1)(z) * «Q»(c)",
					ByArith(gapNonzero, Scaled(gap, cleared)))
				arg.Take(z)
				arg.Show(
					"z is the point: D(0)(x) is T(c) plus D(n + 1)(z)·Q(c)",
					ByArith(rest, parts[0], parts[1]))
			})
		}),
})}

// TaylorLagrangeAbove — Taylor's theorem with the Lagrange remainder at
// a point x to the right of the centre c.
//
// The general theorem on ⟦c, x⟧, expanded at its left end.
var TaylorLagrangeAbove = taylorLagrangeAboveThm{family.Add(registry.ProofEntry{
	Name: "TaylorLagrangeAbove",
	Key:  "prop_fabd5941453f2c98",
	Build: family.Theorem(Statement{
		Binders: "∀D:(num → real → real). ∀n:num. ∀c x:real.",
		Hypotheses: []string{
			"c < x",
			"∀k:num. k ≤ n ⇒ real_continuous_on(⟦c, x⟧, D(k))",
			"∀k:num. ∀y:real. k ≤ n ∧ c < y ∧ y < x ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
		},
		Conclusion: "∃z:real. " +
			"    c < z ∧ " +
			"    z < x ∧ " +
			"    D(0)(x) = «taylorSum» + D(n + 1)(z) * real_pow(x - c, n + 1) / &factorial(n + 1)",
	},
		func(
			a *Argument,
			D *Arrow[Nat, Fun[Real, Real]],
			n *Expr[Nat],
			c, x *Expr[Real],
			ordered, continuous, derivatives Fact,
		) {
			ends := a.Have(
				"c is the left end of ⟦c, x⟧ and x the right",
				"c = c ∧ x = x ∨ c = x ∧ x = c",
				ByArith())
			a.Show(
				"Taylor's theorem on ⟦c, x⟧, expanded at its left end",
				By(At(TaylorLagrange, D, n, c, x, c, x), ordered, ends, continuous, derivatives))
		}),
})}

// TaylorLagrangeBelow — Taylor's theorem with the Lagrange remainder at
// a point x to the left of the centre c.
//
// The general theorem on ⟦x, c⟧, expanded at its right end.
var TaylorLagrangeBelow = taylorLagrangeBelowThm{family.Add(registry.ProofEntry{
	Name: "TaylorLagrangeBelow",
	Key:  "prop_758986e2110cc447",
	Build: family.Theorem(Statement{
		Binders: "∀D:(num → real → real). ∀n:num. ∀c x:real.",
		Hypotheses: []string{
			"x < c",
			"∀k:num. k ≤ n ⇒ real_continuous_on(⟦x, c⟧, D(k))",
			"∀k:num. ∀y:real. k ≤ n ∧ x < y ∧ y < c ⇒ real_derivative_at(D(k), y, D(k + 1)(y))",
		},
		Conclusion: "∃z:real. " +
			"    x < z ∧ " +
			"    z < c ∧ " +
			"    D(0)(x) = «taylorSum» + D(n + 1)(z) * real_pow(x - c, n + 1) / &factorial(n + 1)",
	},
		func(
			a *Argument,
			D *Arrow[Nat, Fun[Real, Real]],
			n *Expr[Nat],
			c, x *Expr[Real],
			ordered, continuous, derivatives Fact,
		) {
			ends := a.Have(
				"c is the right end of ⟦x, c⟧ and x the left",
				"c = x ∧ x = c ∨ c = c ∧ x = x",
				ByArith())
			a.Show(
				"Taylor's theorem on ⟦x, c⟧, expanded at its right end",
				By(At(TaylorLagrange, D, n, x, c, c, x), ordered, ends, continuous, derivatives))
		}),
})}
