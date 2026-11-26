// rules.go — the derivative's first facts and the rules that compute it
// (README, "The derivative", "The rules"): a function has at most one
// derivative at a point and is continuous where it has one, a linear
// approximation with a quadratic error is a derivative, the derivative
// is the linear approximation whose error is small against the distance,
// and a derivative sees the function only near the point; constants, the
// identity, sums and finite sums, negatives, differences, multiples,
// products, reciprocals, quotients and powers. Each rule rearranges a difference
// quotient into the operation on quotients the limit laws already know.
//
// The rules end the same way. Two facts are established first: the
// rearranged function's limit, and the equation between the goal's
// difference quotient and that function. The last step unfolds the goal
// to its limit statement, rewrites the goal's quotient by the equation
// into the rearranged function, and closes on that function's limit. The
// equations between quotients are the arithmetic closer's: it reads a
// quotient as its numerator times the inverse of its divisor, and cancels
// a divisor against its inverse on evidence that it is not zero.

package real_derivative

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_function_limits"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/registry"
)

// DerivativeUnique — a function has at most one derivative at a point.
//
// Both are limits of the same difference quotient, and a limit is one
// number.
var DerivativeUnique = derivativeUniqueThm{family.Add(registry.ProofEntry{
	Name: "DerivativeUnique",
	Key:  "prop_b447266b879742e4",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c l m:real.",
		Hypotheses: []string{
			"real_derivative_at(f, c, l)",
			"real_derivative_at(f, c, m)",
		},
		Conclusion: "l = m",
	},
		func(a *Argument, f *Arrow[Real, Real], c, l, m *Expr[Real], derivatives Fact) {
			a.Show(
				"l and m are both limits of f's difference quotient at c",
				By(real_function_limits.LimitAtUnique, a.Unfolded(derivatives, RealDerivativeAtDef)))
		}),
})}

// DerivativeContinuous — a function with a derivative at a point is
// continuous there.
//
// Write f through its difference quotient q at c: f(x) = f(c) + q(x)·(x − c)
// at every x — off c the factor x − c cancels the quotient's denominator,
// and at c it is 0, so both sides are f(c). Every piece of the right-hand
// side has a known limit at c: q tends to l and x − c to c − c, so their
// product tends to l·(c − c), and the whole to f(c) + l·(c − c), which is
// f(c). So f ⟶ f(c) (at c), which is continuity at c.
var DerivativeContinuous = derivativeContinuousThm{family.Add(registry.ProofEntry{
	Name: "DerivativeContinuous",
	Key:  "prop_decfd9d7a51e483e",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c l:real.",
		Hypotheses: []string{
			"real_derivative_at(f, c, l)",
		},
		Conclusion: "real_continuous_at(f, c)",
		Abbrev: Abbrev{
			{Name: "throughQuotient", Text: "(λx:real. f(c) + (f(x) - f(c)) / (x - c) * (x - c))"},
		},
	},
		func(a *Argument, f *Arrow[Real, Real], c, l *Expr[Real], derivative Fact) {
			quotient := a.Unfolded(derivative, RealDerivativeAtDef)
			offset := a.Have(
				"x − c tends to c − c, the identity minus the constant c",
				"(λx:real. x - c) ⟶ c - c (at c)",
				By(
					real_function_limits.LimitAtSub,
					real_function_limits.LimitAtId.At(c),
					real_function_limits.LimitAtConst.At(c, c)))
			product := a.Have(
				"so the quotient times x − c tends to l·(c − c)",
				"(λx:real. (f(x) - f(c)) / (x - c) * (x - c)) ⟶ l * (c - c) (at c)",
				By(real_function_limits.LimitAtMul, quotient, offset))
			limit := a.Have(
				"and f(c) plus that product tends to f(c) + l·(c − c)",
				"«throughQuotient» ⟶ f(c) + l * (c - c) (at c)",
				By(real_function_limits.LimitAtAdd, real_function_limits.LimitAtConst.At(f.Apply(c), c), product))
			identity := a.Have(
				"f is that function: f(x) = f(c) + q(x)·(x − c) at every x",
				"f = «throughQuotient»",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Real]()
					b.Cases(b.Term("x = c"))
					b.When(
						"at c",
						func(d *Argument, atCentre Fact) {
							d.Show(
								"the product has the factor c − c = 0, so both sides are f(c)",
								ByArith(atCentre))
						})
					b.Otherwise(
						"off c",
						func(d *Argument, offCentre Fact) {
							d.Show(
								"x − c ≠ 0 cancels the quotient's denominator, leaving f(x) − f(c)",
								ByArith(offCentre))
						})
				}))
			value := a.Have(
				"the limit f(c) + l·(c − c) is f(c)",
				"f(c) + l * (c - c) = f(c)",
				ByArith())
			a.Show(
				"continuity at c is f ⟶ f(c) (at c), and f is the function just shown to tend to that value",
				Simp(Fwd(real_continuous.ContinuousAtIffLimit)),
				By(identity, value, limit))
		}),
})}

// DerivativeContinuousOn — a function with a derivative at every point of
// a set is continuous on the set: at each point by DerivativeContinuous,
// and on the set by ContinuousAtOn.
var DerivativeContinuousOn = derivativeContinuousOnThm{family.Add(registry.ProofEntry{
	Name: "DerivativeContinuousOn",
	Key:  "prop_796be1d70d8ca3ce",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"∀x:real. x ∈ s ⇒ real_derivative_at(f, x, f'(x))",
		},
		Conclusion: "real_continuous_on(s, f)",
	},
		func(arg *Argument, f, fPrime *Arrow[Real, Real], s *Expr[Set[Real]], everywhere Fact) {
			pointwise := arg.Have(
				"at every point of s, f is continuous, having a derivative there",
				"∀x:real. x ∈ s ⇒ real_continuous_at(f, x)",
				Derive(func(d *Argument) {
					x := d.FixAs[Real]()
					in := d.Assume()
					d.Show(
						"a function with a derivative at x is continuous there",
						By(in, everywhere, DerivativeContinuous.At(f, x, fPrime.Apply(x))))
				}))
			arg.Show(
				"continuous at each point of s, so on s",
				By(pointwise, real_continuous.ContinuousAtOn))
		}),
})}

// DerivativeFromQuadraticRemainder — a first-order approximation with a
// quadratic error bound on a ball is a derivative.
//
// Shown on the ε-δ definition of the limit. Given ε, the radius is
// min(d, ε/(K + 1)) — K + 1 rather than K, so that the quotient is
// defined and positive whether or not K is 0; K is nonnegative, since at
// the point d/2 of the ball the bound makes K·(d/2)² at least a size. For
// x in the punctured ball put h = x − c: the difference quotient exceeds
// L by the remainder quotient (f(x) − f(c) − L·h)/h, whose numerator is
// at most K·h² = K·|h|·|h| in size, so the remainder quotient is at most
// K·|h| in size, and K·|h| ≤ (K + 1)·|h| < (K + 1)·(ε/(K + 1)) = ε.
var DerivativeFromQuadraticRemainder = derivativeFromQuadraticRemainderThm{family.Add(registry.ProofEntry{
	Name: "DerivativeFromQuadraticRemainder",
	Key:  "prop_785038a2a867d950",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c L K d:real.",
		Hypotheses: []string{
			"&0 < d",
			"∀h:real. |h| < d ⇒ |f(c + h) - f(c) - L * h| ≤ K * real_pow(h, 2)",
		},
		Conclusion: "real_derivative_at(f, c, L)",
	},
		func(arg *Argument, f *Arrow[Real, Real], c, L, K, d *Expr[Real], hyps Fact) {
			given := arg.Conjuncts(
				hyps,
				"the radius d is positive",
				"on the ball of radius d the increment f(c + h) − f(c) is L·h to within K·h²")
			radius, bound := given[0], given[1]
			zero := arg.TermAs[Real]("&0")
			half := arg.TermAs[Real]("d / &2")
			halfSquare := arg.TermAs[Real]("real_pow(d / &2, 2)")
			squarePositive := arg.Have(
				"(d/2)² is positive",
				"&0 < real_pow(d / &2, 2)",
				ByArith(radius))
			atHalf := arg.Have(
				"d/2 lies in the ball, so the bound holds at h = d/2",
				"|f(c + d / &2) - f(c) - L * (d / &2)| ≤ K * real_pow(d / &2, 2)",
				ByArith(bound.At(half), radius))
			nonneg := arg.Have(
				"so K·(d/2)² is at least a size, hence at least 0·(d/2)², and the positive (d/2)² cancels: K ≥ 0",
				"&0 ≤ K",
				ByArith(atHalf, squarePositive, real_order_ring.LessEqMulRightEq.At(zero, K, halfSquare)))
			scalePositive := arg.Have(
				"so K + 1 is positive",
				"&0 < K + &1",
				ByArith(nonneg))

			arg.Do(Simp(Fwd(RealDerivativeAtDef)), Simp(Fwd(real_function_limits.RealLimitAtDef)))
			// ↦ ∀ε. &0 < ε ⇒ ∃δ. &0 < δ ∧ (∀x. &0 < |x − c| ∧ |x − c| < δ ⇒
			//     |(f(x) − f(c))/(x − c) − L| < ε)
			arg.FixAs[Real]("ε")
			epsilonPositive := arg.Assume()
			scale := arg.TermAs[Real]("K + &1")
			epsRadius := arg.TermAs[Real]("ε / (K + &1)")
			radiusPositive := arg.Have(
				"ε/(K + 1) is positive, ε and K + 1 being positive",
				"&0 < ε / (K + &1)",
				ByArith(epsilonPositive, scalePositive))
			arg.Take(arg.TermAs[Real]("min(d, ε / (K + &1))"))
			arg.Do(SplitConj(
				Case(
					"the radius, the smaller of d and ε/(K + 1), is positive, both being positive",
					ByArith(radius, radiusPositive, real_sup_inf.LessThanMin.At(d, epsRadius, zero))),
				Case(
					"and at every point of its punctured ball the quotient is within ε of L",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						ball := b.Assume()
						h := b.TermAs[Real]("x - c")
						distance := b.TermAs[Real]("|x - c|")
						near := b.Have(
							"a distance below the smaller radius is below d and below ε/(K + 1)",
							"|x - c| < d ∧ |x - c| < ε / (K + &1)",
							By(ball, real_sup_inf.LessThanMin.At(d, epsRadius, distance)))
						excess := b.Have(
							"x − c is not 0, so the quotient exceeds L by the remainder f(x) − f(c) − L·(x − c) over x − c",
							"(f(x) - f(c)) / (x - c) - L = (f(x) - f(c) - L * (x - c)) / (x - c)",
							ByArith(ball))
						remainder := b.Have(
							"the bound at h = x − c, as c + (x − c) = x: the remainder "+
								"is at most K·(x − c)² = K·|x − c|·|x − c| in size",
							"|f(x) - f(c) - L * (x - c)| ≤ K * (|x - c| * |x - c|)",
							ByArith(
								bound.At(h),
								near,
								real_ring.SubAddLeft.At(x, c),
								real_pow.SquareOfAbs.At(h),
								real_pow.PowTwo.At(distance)))
						remainderBound := b.Have(
							"so the remainder quotient, that numerator over |x − c| > 0, is at most K·|x − c| in size",
							"|(f(x) - f(c) - L * (x - c)) / (x - c)| ≤ K * |x - c|",
							Simp(Fwd(real_sgn_abs.AbsDiv)),
							ByArith(remainder, ball))
						b.Show(
							"the distance is the remainder quotient's size, at most "+
								"K·|x − c| ≤ (K + 1)·|x − c| < (K + 1)·(ε/(K + 1)) = ε",
							excess.Rw(),
							ByArith(
								remainderBound,
								near,
								scalePositive,
								real_order_ring.LessThanMulLeft.At(scale, distance, epsRadius)))
					})),
			))
		}),
})}

// DerivativeIncrement — f has derivative l at c exactly when, for every
// ε > 0, near c the increment f(x) − f(c) lies within ε·|x − c| of
// l·(x − c).
//
// Off the centre the quotient's distance from l is the distance of the
// increment from l·(x − c), divided by |x − c|; so the one is below ε
// exactly when the other is below ε·|x − c|, and the definition's limit
// and this bound ask the same of the same punctured balls.
var DerivativeIncrement = derivativeIncrementThm{family.Add(registry.ProofEntry{
	Name: "DerivativeIncrement",
	Key:  "prop_c83f9953af4355f0",
	Build: family.Theorem("∀f:(real → real). ∀c l:real. "+
		"    real_derivative_at(f, c, l) ⇔ "+
		"    ∀ε:real. "+
		"        &0 < ε ⇒ "+
		"        ∃δ:real. "+
		"            &0 < δ ∧ "+
		"            ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - f(c) - l * (x - c)| < ε * |x - c|",
		func(arg *Argument, f *Arrow[Real, Real], c, l *Expr[Real]) {
			pointwise := arg.Have(
				"off the centre the quotient is within ε of l exactly "+
					"when the increment is within ε·|x − c| of l·(x − c)",
				Statement{
					Binders: "∀x:real.",
					Hypotheses: []string{
						"&0 < |x - c|",
					},
					Conclusion: "∀ε:real. " +
						"    |(f(x) - f(c)) / (x - c) - l| < ε ⇔ |f(x) - f(c) - l * (x - c)| < ε * |x - c|",
				},
				Derive(func(b *Argument) {
					b.FixAs[Real]()
					apart := b.Assume()
					ε := b.FixAs[Real]()
					quotient := b.Have(
						"the quotient less l is the increment less l·(x − c), divided by x − c",
						"(f(x) - f(c)) / (x - c) - l = (f(x) - f(c) - l * (x - c)) / (x - c)",
						ByArith(apart))
					deviation := b.TermAs[Real]("f(x) - f(c) - l * (x - c)")
					b.Show(
						"a quotient's size is the quotient of the sizes, "+
							"and dividing by the positive |x − c| keeps the order",
						By(
							quotient,
							apart,
							real_sgn_abs.AbsDiv.At(deviation, b.TermAs[Real]("x - c")),
							real_order_field.LessThanDivMulRight.At(
								b.TermAs[Real]("|f(x) - f(c) - l * (x - c)|"),
								ε,
								b.TermAs[Real]("|x - c|"))))
				}))

			arg.Do(Unfold(RealDerivativeAtDef), Unfold(real_function_limits.RealLimitAtDef))
			arg.Iff()
			arg.Forward(
				"a radius that keeps the quotient within ε of l keeps the increment within ε·|x − c| of l·(x − c)",
				func(b *Argument, quotients Fact) {
					ε := b.FixAs[Real]()
					pos := b.Assume()
					δ, ball := b.ObtainAs[Real](
						"a radius inside which the quotient is within ε of l",
						"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |(f(x) - f(c)) / (x - c) - l| < ε",
						By(quotients.At(ε), pos))
					b.Take(δ)
					b.Show(
						"the same radius serves the increment, point by point",
						By(pointwise, ball))
				})
			arg.Backward(
				"a radius that keeps the increment within ε·|x − c| of l·(x − c) keeps the quotient within ε of l",
				func(b *Argument, increments Fact) {
					ε := b.FixAs[Real]()
					pos := b.Assume()
					δ, ball := b.ObtainAs[Real](
						"a radius inside which the increment is within ε·|x − c| of l·(x − c)",
						"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - f(c) - l * (x - c)| < ε * |x - c|",
						By(increments.At(ε), pos))
					b.Take(δ)
					b.Show(
						"the same radius serves the quotient, point by point",
						By(pointwise, ball))
				})
		}),
})}

// DerivativeLocal — two functions that agree on a ball about c have the
// same derivative at c.
//
// The centre lies in the ball, so f(c) = g(c), and then the two
// difference quotients agree at every other point of the ball. A limit
// sees only a punctured ball (LimitAtLocal), so the quotients have the
// same limits at c, and g's tends to l.
var DerivativeLocal = derivativeLocalThm{family.Add(registry.ProofEntry{
	Name: "DerivativeLocal",
	Key:  "prop_ed9247cd6d66ecc7",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀c d l:real.",
		Hypotheses: []string{
			"&0 < d",
			"∀x:real. |x - c| < d ⇒ f(x) = g(x)",
			"real_derivative_at(g, c, l)",
		},
		Conclusion: "real_derivative_at(f, c, l)",
	},
		func(a *Argument, f, g *Arrow[Real, Real], c, d, l *Expr[Real], radius, agree, gDerivative Fact) {
			atCentre := a.Have(
				"the centre lies in the ball, so f(c) = g(c)",
				"f(c) = g(c)",
				ByArith(agree.At(c), radius))
			quotients := a.Have(
				"off the centre the two difference quotients agree",
				"∀x:real. &0 < |x - c| ∧ |x - c| < d ⇒ (f(x) - f(c)) / (x - c) = (g(x) - g(c)) / (x - c)",
				Derive(func(b *Argument) {
					x := b.FixAs[Real]()
					inBall := b.Assume()
					b.Show(
						"f(x) = g(x) in the ball, and f(c) = g(c)",
						By(agree.At(x), inBall, atCentre))
				}))
			limits := a.Have(
				"a limit sees only a punctured ball, so the two quotients have the same limits at c",
				"real_limit_at(λx:real. (f(x) - f(c)) / (x - c), c) = "+
					"real_limit_at(λx:real. (g(x) - g(c)) / (x - c), c)",
				By(real_function_limits.LimitAtLocal, radius, quotients))
			gQuotient := a.Unfolded(gDerivative, RealDerivativeAtDef)
			a.Show(
				"f's difference quotient has the limits of g's, and g's tends to l",
				Unfold(RealDerivativeAtDef),
				limits.Rw(),
				By(gQuotient))
		}),
})}

// DerivativeConst — a constant function has derivative 0.
//
// Its difference quotient is (k − k)/(x − c) = 0 at every x — at the
// centre too, since 0 divided by anything is 0 — and the constant 0
// tends to 0.
var DerivativeConst = derivativeConstThm{family.Add(registry.ProofEntry{
	Name: "DerivativeConst",
	Key:  "prop_1f02f19685ebf827",
	Build: family.Theorem("∀k c:real. real_derivative_at(λx:real. k, c, &0)",
		func(a *Argument, k, c *Expr[Real]) {
			zero := a.Have(
				"the constant 0 tends to 0",
				"(λx:real. &0) ⟶ &0 (at c)",
				By(real_function_limits.LimitAtConst.At(a.TermAs[Real]("&0"), c)))
			quotient := a.Have(
				"the difference quotient of a constant is 0 everywhere",
				"(λx:real. (k - k) / (x - c)) = (λx:real. &0)",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Real]()
					b.Show(
						"k − k = 0, and 0 divided by anything is 0",
						ByArith())
				}))
			// Unfolded, the goal is the limit of the quotient; rewritten by the
			// identity, it is the limit of the constant 0, which is resident.
			a.Do(Unfold(RealDerivativeAtDef), quotient.Rw())
			a.Show(
				"the quotient is the constant 0, which tends to 0",
				By(zero))
		}),
})}

// DerivativeId — the identity has derivative 1.
//
// Its difference quotient (x − c)/(x − c) is 1 at every x off the
// centre, so any radius answers any ε: on the punctured ball the
// quotient is at distance 0 from 1. The radius is taken to be 1. At the
// centre itself the quotient is 0/0 = 0, which a limit never sees — and
// which is why this rule does not follow the others: the equation between
// the quotient and the constant 1 fails at c, so the limit is read off the
// ε-δ definition directly rather than carried across an equation.
var DerivativeId = derivativeIdThm{family.Add(registry.ProofEntry{
	Name: "DerivativeId",
	Key:  "prop_53a941465d07ce1b",
	Build: family.Theorem("∀c:real. real_derivative_at(λx:real. x, c, &1)",
		func(a *Argument, c *Expr[Real]) {
			a.Do(Unfold(RealDerivativeAtDef), Unfold(real_function_limits.RealLimitAtDef))
			a.FixAs[Real]()
			pos := a.Assume()
			a.Take(a.TermAs[Real]("&1"))
			a.Do(SplitConj(
				Case(
					"the radius 1 is positive",
					Cite(real_order_ring.ZeroLessThanOne)),
				Case(
					"and at every point of the punctured ball the quotient is 1, at distance 0 from 1",
					Derive(func(b *Argument) {
						b.FixAs[Real]()
						ball := b.Assume()
						b.Show(
							"x − c is not 0, so the quotient is 1, and |1 − 1| = 0 < ε",
							ByArith(ball, pos))
					})),
			))
		}),
})}

// DerivativeAdd — the derivative of a sum is the sum of the
// derivatives.
//
// The difference quotient of f + g is the sum of the two quotients —
// dividing by x − c is multiplying by its inverse, which distributes
// over the sum — so it tends to l + m by the limit of a sum.
var DerivativeAdd = derivativeAddThm{family.Add(registry.ProofEntry{
	Name: "DerivativeAdd",
	Key:  "prop_22a76f4341e6a7e2",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀c l m:real.",
		Hypotheses: []string{
			"real_derivative_at(f, c, l)",
			"real_derivative_at(g, c, m)",
		},
		Conclusion: "real_derivative_at(λx:real. f(x) + g(x), c, l + m)",
	},
		func(a *Argument, f, g *Arrow[Real, Real], c, l, m *Expr[Real], derivatives Fact) {
			quotients := a.Unfolded(derivatives, RealDerivativeAtDef)
			sum := a.Have(
				"the quotients of f and g tend to l and m, so their sum tends to l + m",
				"(λx:real. (f(x) - f(c)) / (x - c) + (g(x) - g(c)) / (x - c)) ⟶ l + m (at c)",
				By(real_function_limits.LimitAtAdd, quotients))
			quotient := a.Have(
				"the difference quotient of f + g is the sum of the quotients of f and g",
				"(λx:real. (f(x) + g(x) - (f(c) + g(c))) / (x - c)) = "+
					"(λx:real. (f(x) - f(c)) / (x - c) + (g(x) - g(c)) / (x - c))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Real]()
					b.Show(
						"dividing by x − c distributes over the sum",
						ByArith())
				}))
			// Unfolded, the goal is the limit of the quotient of f + g; rewritten
			// by the identity, it is the limit of the sum, which is resident.
			a.Do(Unfold(RealDerivativeAtDef), quotient.Rw())
			a.Show(
				"the quotient of f + g is the sum of the quotients, which tends to l + m",
				By(sum))
		}),
})}

// DerivativeSum — a finite sum of functions is differentiated term by
// term: where each F(k), k ≤ n, has derivative G(k) at x, the sum
// Σ_{k ≤ n} F(k) has derivative Σ_{k ≤ n} G(k) there. By induction on n:
// the sum to 0 is F(0) itself, and the sum to n + 1 is the sum to n plus
// F(n + 1), whose derivatives add.
var DerivativeSum = derivativeSumThm{family.Add(registry.ProofEntry{
	Name: "DerivativeSum",
	Key:  "prop_d5e2c0dbffd2bc8b",
	Build: family.Theorem(Statement{
		Binders: "∀F:(num → real → real). ∀G:(num → real). ∀n:num. ∀x:real.",
		Hypotheses: []string{
			"∀k:num. k ≤ n ⇒ real_derivative_at(F(k), x, G(k))",
		},
		Conclusion: "real_derivative_at(λt:real. Σ_{k∈0 .. n} F(k)(t), x, Σ_{k∈0 .. n} G(k))",
	},
		func(
			arg *Argument,
			F *Arrow[Nat, Fun[Real, Real]],
			G *Arrow[Nat, Real],
			n *Expr[Nat],
			x *Expr[Real],
		) {
			zero := arg.TermAs[Nat]("0")
			arg.Induct(n)
			arg.Base(
				"the sum over 0 .. 0 is its one term F(0)(t), with derivative G(0)",
				func(b *Argument) {
					given := b.Assume()
					b.Show(
						"F(0) has derivative G(0) at x",
						Simp(Fwd(real_sum.IntervalPoint)),
						By(given.At(zero), nat_order.LessEqRefl.At(zero)))
				})
			arg.Step(
				"the sum to n + 1 is the sum to n plus F(n + 1), and derivatives add",
				func(b *Argument, ih Fact) {
					next := b.TermAs[Nat]("suc(n)")
					given := b.Assume()
					split := b.Have(
						"as functions of t, the sum to n + 1 is the sum to n plus F(n + 1)(t)",
						"(λt:real. Σ_{k∈0 .. suc(n)} F(k)(t)) = (λt:real. Σ_{k∈0 .. n} F(k)(t) + F(suc(n))(t))",
						Simp(Fwd(real_sum.IntervalClauses), Fwd(nat_order.ZeroLessEq)),
						ByArith())
					lower := b.Have(
						"the derivatives of F(k) for k ≤ n are among those given",
						"∀k:num. k ≤ n ⇒ real_derivative_at(F(k), x, G(k))",
						ByArith(given))
					sum := b.Have(
						"by induction the sum to n has derivative Σ_{k ≤ n} G(k), and F(n + 1) adds G(n + 1)",
						"real_derivative_at(λt:real. Σ_{k∈0 .. n} F(k)(t) + F(suc(n))(t), "+
							"    x, "+
							"    Σ_{k∈0 .. n} G(k) + G(suc(n)))",
						By(
							lower,
							given.At(next),
							ih,
							nat_order.LessEqRefl.At(next),
							DerivativeAdd.At(
								b.TermAs[Fun[Real, Real]]("λt:real. Σ_{k∈0 .. n} F(k)(t)"),
								b.TermAs[Fun[Real, Real]]("F(suc(n))"),
								x,
								b.TermAs[Real]("Σ_{k∈0 .. n} G(k)"),
								b.TermAs[Real]("G(suc(n))"))))
					b.Show(
						"and Σ_{k ≤ n + 1} G(k) is Σ_{k ≤ n} G(k) + G(n + 1)",
						By(split, sum, real_sum.IntervalClauses.At(zero, n, G), nat_order.ZeroLessEq.At(next)))
				})
		}),
})}

// DerivativeNeg — the derivative of −f is −l.
//
// The difference quotient of −f is the negative of f's, so it tends to
// −l by the limit of a negative.
var DerivativeNeg = derivativeNegThm{family.Add(registry.ProofEntry{
	Name: "DerivativeNeg",
	Key:  "prop_d5b1e1da0e125361",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c l:real.",
		Hypotheses: []string{
			"real_derivative_at(f, c, l)",
		},
		Conclusion: "real_derivative_at(λx:real. -f(x), c, -l)",
	},
		func(a *Argument, f *Arrow[Real, Real], c, l *Expr[Real], derivative Fact) {
			quotient := a.Unfolded(derivative, RealDerivativeAtDef)
			negative := a.Have(
				"f's quotient tends to l, so its negative tends to −l",
				"(λx:real. -((f(x) - f(c)) / (x - c))) ⟶ -l (at c)",
				By(real_function_limits.LimitAtNeg, quotient))
			negated := a.Have(
				"the difference quotient of −f is the negative of f's",
				"(λx:real. (-f(x) - -f(c)) / (x - c)) = (λx:real. -((f(x) - f(c)) / (x - c)))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Real]()
					b.Show(
						"dividing by x − c commutes with the negation",
						ByArith())
				}))
			// Unfolded, the goal is the limit of the quotient of −f; rewritten
			// by the identity, it is the limit of the negative, which is resident.
			a.Do(Unfold(RealDerivativeAtDef), negated.Rw())
			a.Show(
				"the quotient of −f is the negative of f's, which tends to −l",
				By(negative))
		}),
})}

// DerivativeSub — the derivative of a difference is the difference of
// the derivatives.
//
// The difference quotient of f − g is the difference of the two
// quotients, so it tends to l − m by the limit of a difference.
var DerivativeSub = derivativeSubThm{family.Add(registry.ProofEntry{
	Name: "DerivativeSub",
	Key:  "prop_d423d4da2beac020",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀c l m:real.",
		Hypotheses: []string{
			"real_derivative_at(f, c, l)",
			"real_derivative_at(g, c, m)",
		},
		Conclusion: "real_derivative_at(λx:real. f(x) - g(x), c, l - m)",
	},
		func(a *Argument, f, g *Arrow[Real, Real], c, l, m *Expr[Real], derivatives Fact) {
			quotients := a.Unfolded(derivatives, RealDerivativeAtDef)
			difference := a.Have(
				"the quotients of f and g tend to l and m, so their difference tends to l − m",
				"(λx:real. (f(x) - f(c)) / (x - c) - (g(x) - g(c)) / (x - c)) ⟶ l - m (at c)",
				By(real_function_limits.LimitAtSub, quotients))
			quotient := a.Have(
				"the difference quotient of f − g is the difference of the quotients of f and g",
				"(λx:real. (f(x) - g(x) - (f(c) - g(c))) / (x - c)) = "+
					"(λx:real. (f(x) - f(c)) / (x - c) - (g(x) - g(c)) / (x - c))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Real]()
					b.Show(
						"dividing by x − c distributes over the difference",
						ByArith())
				}))
			// Unfolded, the goal is the limit of the quotient of f − g; rewritten
			// by the identity, it is the limit of the difference, which is resident.
			a.Do(Unfold(RealDerivativeAtDef), quotient.Rw())
			a.Show(
				"the quotient of f − g is the difference of the quotients, which tends to l − m",
				By(difference))
		}),
})}

// DerivativeScale — the derivative of k·f is k·l.
//
// The difference quotient of k·f is k times f's, so it tends to k·l by
// the limit of a scalar multiple.
var DerivativeScale = derivativeScaleThm{family.Add(registry.ProofEntry{
	Name: "DerivativeScale",
	Key:  "prop_29d00107696f9ec7",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c l k:real.",
		Hypotheses: []string{
			"real_derivative_at(f, c, l)",
		},
		Conclusion: "real_derivative_at(λx:real. k * f(x), c, k * l)",
	},
		func(a *Argument, f *Arrow[Real, Real], c, l, k *Expr[Real], derivative Fact) {
			quotient := a.Unfolded(derivative, RealDerivativeAtDef)
			multiple := a.Have(
				"f's quotient tends to l, so k times it tends to k·l",
				"(λx:real. k * ((f(x) - f(c)) / (x - c))) ⟶ k * l (at c)",
				By(real_function_limits.LimitAtScale, quotient))
			scaled := a.Have(
				"the difference quotient of k·f is k times f's",
				"(λx:real. (k * f(x) - k * f(c)) / (x - c)) = (λx:real. k * ((f(x) - f(c)) / (x - c)))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Real]()
					b.Show(
						"the factor k comes out of the difference",
						ByArith())
				}))
			// Unfolded, the goal is the limit of the quotient of k·f; rewritten
			// by the identity, it is the limit of the multiple, which is resident.
			a.Do(Unfold(RealDerivativeAtDef), scaled.Rw())
			a.Show(
				"the quotient of k·f is k times f's, which tends to k·l",
				By(multiple))
		}),
})}

// DerivativeMul — the product rule: f·g has derivative l·g(c) + f(c)·m.
//
// The difference quotient of f·g splits as f(x) times g's quotient plus
// g(c) times f's: f(x)g(x) − f(c)g(c) = f(x)(g(x) − g(c)) + g(c)(f(x) − f(c)).
// A function with a derivative is continuous, so f(x) tends to f(c), and
// the limits of a product, a multiple and a sum give f(c)·m + g(c)·l.
var DerivativeMul = derivativeMulThm{family.Add(registry.ProofEntry{
	Name: "DerivativeMul",
	Key:  "prop_1e9b03a784efca9f",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀c l m:real.",
		Hypotheses: []string{
			"real_derivative_at(f, c, l)",
			"real_derivative_at(g, c, m)",
		},
		Conclusion: "real_derivative_at(λx:real. f(x) * g(x), c, l * g(c) + f(c) * m)",
	},
		func(a *Argument, f, g *Arrow[Real, Real], c, l, m *Expr[Real], derivatives Fact) {
			parts := a.Conjuncts(
				derivatives,
				"f has derivative l at c",
				"g has derivative m at c")
			fLimit := a.Have(
				"f has a derivative at c, so it is continuous there: f ⟶ f(c) (at c)",
				"f ⟶ f(c) (at c)",
				By(real_continuous.ContinuousAtIffLimit.At(f, c), DerivativeContinuous.At(f, c, l), parts[0]))
			quotients := a.Unfolded(derivatives, RealDerivativeAtDef)
			moving := a.Have(
				"f(x) times g's quotient tends to f(c)·m",
				"(λx:real. f(x) * ((g(x) - g(c)) / (x - c))) ⟶ f(c) * m (at c)",
				By(real_function_limits.LimitAtMul, fLimit, quotients))
			fixed := a.Have(
				"g(c) times f's quotient tends to g(c)·l",
				"(λx:real. g(c) * ((f(x) - f(c)) / (x - c))) ⟶ g(c) * l (at c)",
				By(real_function_limits.LimitAtScale, quotients))
			value := a.Have(
				"f(c)·m + g(c)·l is l·g(c) + f(c)·m",
				"f(c) * m + g(c) * l = l * g(c) + f(c) * m",
				ByArith())
			sum := a.Have(
				"so their sum tends to l·g(c) + f(c)·m",
				"(λx:real. f(x) * ((g(x) - g(c)) / (x - c)) + g(c) * ((f(x) - f(c)) / (x - c))) ⟶ "+
					"l * g(c) + f(c) * m (at c)",
				Derive(func(b *Argument) {
					b.Do(value.RwRev())
					b.Show(
						"the limit of a sum is the sum of the limits",
						By(real_function_limits.LimitAtAdd, moving, fixed))
				}))
			quotient := a.Have(
				"the difference quotient of f·g is that sum",
				"(λx:real. (f(x) * g(x) - f(c) * g(c)) / (x - c)) = "+
					"(λx:real. f(x) * ((g(x) - g(c)) / (x - c)) + g(c) * ((f(x) - f(c)) / (x - c)))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Real]()
					b.Show(
						"f(x)g(x) − f(c)g(c) = f(x)(g(x) − g(c)) + g(c)(f(x) − f(c)), each term divided by x − c",
						ByArith())
				}))
			// Unfolded, the goal is the limit of the quotient of f·g; rewritten
			// by the identity, it is the limit of the sum, which is resident.
			a.Do(Unfold(RealDerivativeAtDef), quotient.Rw())
			a.Show(
				"the quotient of f·g is that sum, which tends to l·g(c) + f(c)·m",
				By(sum))
		}),
})}

// DerivativeInv — the reciprocal rule: where g has derivative m at c and
// g(c) ≠ 0, 1/g has derivative −m/g(c)².
//
// Wherever g(x) ≠ 0 the difference quotient of 1/g factors as −1/g(c)
// times g's quotient times 1/g(x): multiplied out, the two sides differ
// only by the factors g(c)·(1/g(c)) and g(x)·(1/g(x)), both 1. g has a
// derivative, so it is continuous at c, and continuity read at ε = |g(c)|
// gives a punctured ball on which g(x) lies nearer to g(c) than 0 does, so
// the factorization holds there. A limit at c sees only such a ball, so
// the quotient of 1/g has the limits of the factored function, which tends
// to −(1/g(c))·(m·(1/g(c))) = −m/g(c)² by the limits of a reciprocal, a
// product and a multiple.
var DerivativeInv = derivativeInvThm{family.Add(registry.ProofEntry{
	Name: "DerivativeInv",
	Key:  "prop_fc5563d3aaffcb94",
	Build: family.Theorem(Statement{
		Binders: "∀g:(real → real). ∀c m:real.",
		Hypotheses: []string{
			"real_derivative_at(g, c, m)",
			"g(c) ≠ &0",
		},
		Conclusion: "real_derivative_at(λx:real. real_inv(g(x)), c, -m / real_pow(g(c), 2))",
		Abbrev: Abbrev{
			{Name: "factoredReciprocal", Text: "(λx:real. " +
				"    -real_inv(g(c)) * ((g(x) - g(c)) / (x - c) * real_inv(g(x))))"},
		},
	},
		func(a *Argument, g *Arrow[Real, Real], c, m *Expr[Real], given Fact) {
			parts := a.Conjuncts(
				given,
				"g has derivative m at c",
				"and g(c) is not zero")
			derivative, nonzero := parts[0], parts[1]
			gc := a.TermAs[Real]("g(c)")
			quotient := a.Unfolded(derivative, RealDerivativeAtDef)
			gLimit := a.Have(
				"g has a derivative at c, so it is continuous there: g ⟶ g(c) (at c)",
				"g ⟶ g(c) (at c)",
				By(real_continuous.ContinuousAtIffLimit.At(g, c), DerivativeContinuous.At(g, c, m), derivative))

			reciprocal := a.Have(
				"g tends to g(c) ≠ 0, so 1/g tends to 1/g(c)",
				"(λx:real. real_inv(g(x))) ⟶ real_inv(g(c)) (at c)",
				By(real_function_limits.LimitAtInv, gLimit, nonzero))
			product := a.Have(
				"so g's quotient times 1/g tends to m·(1/g(c))",
				"(λx:real. (g(x) - g(c)) / (x - c) * real_inv(g(x))) ⟶ m * real_inv(g(c)) (at c)",
				By(real_function_limits.LimitAtMul, quotient, reciprocal))
			value := a.Have(
				"−(1/g(c))·(m·(1/g(c))) is −m/g(c)², g(c)² being g(c)·g(c)",
				"-real_inv(g(c)) * (m * real_inv(g(c))) = -m / real_pow(g(c), 2)",
				ByArith())
			factored := a.Have(
				"and −1/g(c) times that product tends to −m/g(c)²",
				"«factoredReciprocal» ⟶ -m / real_pow(g(c), 2) (at c)",
				Derive(func(b *Argument) {
					b.Do(value.RwRev())
					b.Show(
						"the limit of a multiple is the multiple of the limit",
						By(real_function_limits.LimitAtScale, product))
				}))

			near := a.Unfolded(gLimit, real_function_limits.RealLimitAtDef)
			// The witness is named δ₀ after the claim's ∃δ; the texts below
			// spell it.
			_, radius := a.Obtain(
				"g(c) ≠ 0 makes |g(c)| positive, and g ⟶ g(c) (at c) at |g(c)| "+
					"hands over a radius δ₀ inside which g(x) is nearer to g(c) than 0 is",
				"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |g(x) - g(c)| < |g(c)|",
				By(near.At(a.TermAs[Real]("|g(c)|")), real_sgn_abs.AbsPosIffNonzero.At(gc), nonzero))
			ball := a.Conjuncts(
				radius,
				"the radius δ₀ is positive",
				"and on the punctured ball of radius δ₀, g(x) is within |g(c)| of g(c)")
			radiusPos, within := ball[0], ball[1]
			agree := a.Have(
				"on that ball the quotient of 1/g is −1/g(c) times g's quotient times 1/g(x)",
				Statement{
					Binders: "∀x:real.",
					Hypotheses: []string{
						"&0 < |x - c|",
						"|x - c| < δ₀",
					},
					Conclusion: "(real_inv(g(x)) - real_inv(g(c))) / (x - c) = " +
						"-real_inv(g(c)) * ((g(x) - g(c)) / (x - c) * real_inv(g(x)))",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[Real]()
					inBall := b.Assume()
					gxSize := b.Have(
						"x lies in the ball, so |g(x)| is positive: |g(c)| ≤ |g(x)| + |g(x) − g(c)|",
						"&0 < |g(x)|",
						ByArith(within.At(x), inBall))
					b.Show(
						"g(x) and g(c) are not zero, so each cancels against "+
							"its own reciprocal and the two sides multiply out alike",
						ByArith(gxSize, nonzero))
				}))
			limits := a.Have(
				"so the quotient of 1/g has, at c, the limits of the factored function",
				"real_limit_at(λx:real. (real_inv(g(x)) - real_inv(g(c))) / (x - c), c) = "+
					"real_limit_at(«factoredReciprocal», c)",
				By(real_function_limits.LimitAtLocal, radiusPos, agree))
			// Unfolded, the goal is the limit of 1/g's quotient; rewritten by
			// the equation of limits, it is the factored function's limit at
			// −m/g(c)², which is resident.
			a.Do(Unfold(RealDerivativeAtDef), limits.Rw())
			a.Show(
				"the quotient of 1/g has the factored function's limits, and that function tends to −m/g(c)²",
				By(factored))
		}),
})}

// DerivativeDiv — the quotient rule: where g(c) ≠ 0, f/g has derivative
// (l·g(c) − f(c)·m)/g(c)².
//
// f/g is f times 1/g, so the product rule applies to f and the
// reciprocal of g, whose derivative −m/g(c)² the reciprocal rule gives.
// The value l·(1/g(c)) + f(c)·(−m/g(c)²) is the quotient rule's once l is
// written as l·g(c)·(1/g(c))·(1/g(c)) — g(c) times its reciprocal is 1.
var DerivativeDiv = derivativeDivThm{family.Add(registry.ProofEntry{
	Name: "DerivativeDiv",
	Key:  "prop_899e96be65ff4dac",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀c l m:real.",
		Hypotheses: []string{
			"real_derivative_at(f, c, l)",
			"real_derivative_at(g, c, m)",
			"g(c) ≠ &0",
		},
		Conclusion: "real_derivative_at(λx:real. f(x) / g(x), " +
			"    c, " +
			"    (l * g(c) - f(c) * m) / real_pow(g(c), 2))",
	},
		func(a *Argument, f, g *Arrow[Real, Real], c, l, m *Expr[Real], given Fact) {
			held := a.Conjuncts(
				given,
				"f has derivative l at c",
				"g has derivative m at c",
				"g(c) is not 0")
			reciprocal := a.Have(
				"1/g has derivative −m/g(c)² at c",
				"real_derivative_at(λx:real. real_inv(g(x)), c, -m / real_pow(g(c), 2))",
				By(DerivativeInv, held[1], held[2]))
			product := a.Have(
				"so f times 1/g has derivative l·(1/g(c)) + f(c)·(−m/g(c)²)",
				"real_derivative_at(λx:real. f(x) * real_inv(g(x)), "+
					"    c, "+
					"    l * real_inv(g(c)) + f(c) * (-m / real_pow(g(c), 2)))",
				By(
					DerivativeMul.At(
						f,
						a.TermAs[Fun[Real, Real]]("λx:real. real_inv(g(x))"),
						c,
						l,
						a.TermAs[Real]("-m / real_pow(g(c), 2)")),
					held[0],
					reciprocal))
			value := a.Have(
				"that value is the quotient rule's: g(c) is not zero, so l·(1/g(c)) is l·g(c)·(1/g(c))·(1/g(c))",
				"l * real_inv(g(c)) + f(c) * (-m / real_pow(g(c), 2)) = (l * g(c) - f(c) * m) / real_pow(g(c), 2)",
				ByArith(held[2]))
			quotient := a.Have(
				"f/g is f times 1/g",
				"(λx:real. f(x) / g(x)) = (λx:real. f(x) * real_inv(g(x)))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Real]()
					b.Show(
						"division is multiplication by the reciprocal",
						Cite(real_field.RealDivDef))
				}))
			a.Do(quotient.Rw(), value.RwRev())
			a.Show(
				"f times 1/g has that derivative",
				By(product))
		}),
})}

// DerivativePowSuc — the power rule at a successor exponent: x ↦ x^(n+1)
// has derivative (n + 1)·xⁿ. Read with the exponent as suc(n), by
// induction on n: x¹ is the identity, with derivative 1 = 1·c⁰, and
// x^(n+2) is x·x^(n+1), whose derivative by the product rule is
// 1·c^(n+1) + c·((n+1)·cⁿ), which is (n+2)·c^(n+1).
var DerivativePowSuc = derivativePowSucThm{family.Add(registry.ProofEntry{
	Name: "DerivativePowSuc",
	Key:  "prop_e37dbc01e8dd226d",
	Build: family.Theorem("∀n:num. ∀c:real. "+
		"    real_derivative_at(λx:real. real_pow(x, n + 1), c, &(n + 1) * real_pow(c, n))",
		func(a *Argument) {
			zero := a.TermAs[Nat]("0")
			a.Do(Simp(Rev(nat_arith.Add1)))
			n := a.Binder("n")
			a.Induct(n)
			a.Base(
				"x¹ is the identity, and its derivative 1 is 1·c⁰",
				func(b *Argument) {
					c := b.FixAs[Real]()
					firstPower := b.Have(
						"x¹ = x·x⁰ = x·1 = x at every x",
						"(λx:real. real_pow(x, suc(0))) = (λx:real. x)",
						Derive(func(d *Argument) {
							d.Do(Funext())
							x := d.FixAs[Real]()
							d.Show(
								"Pow's two clauses, and 1 is a unit",
								ByArith(real_pow.PowExpSucClause.At(x, zero), real_pow.PowExpZeroClause.At(x)))
						}))
					value := b.Have(
						"1·c⁰ = 1",
						"&suc(0) * real_pow(c, 0) = &1",
						ByArith(real_pow.PowExpZeroClause.At(c), real_ring.OfNumSuc.At(zero)))
					b.Show(
						"so x¹ has the identity's derivative",
						By(Normalized, firstPower, value, DerivativeId.At(c)))
				})
			a.Step(
				"x^(n+2) is x·x^(n+1), a product of two functions whose derivatives are known",
				func(b *Argument, ih Fact) {
					c := b.FixAs[Real]()
					identity := b.TermAs[Fun[Real, Real]]("λx:real. x")
					power := b.TermAs[Fun[Real, Real]]("λx:real. real_pow(x, suc(n))")
					one := b.TermAs[Real]("&1")
					product := b.Have(
						"by the product rule, x·x^(n+1) has derivative 1·c^(n+1) + c·((n+1)·cⁿ)",
						"real_derivative_at(λx:real. x * real_pow(x, suc(n)), "+
							"    c, "+
							"    &1 * real_pow(c, suc(n)) + c * (&suc(n) * real_pow(c, n)))",
						By(
							DerivativeMul.At(identity, power, c, one, b.TermAs[Real]("&suc(n) * real_pow(c, n)")),
							DerivativeId.At(c),
							ih.At(c)))
					value := b.Have(
						"that value is (n+2)·c^(n+1)",
						"&1 * real_pow(c, suc(n)) + c * (&suc(n) * real_pow(c, n)) = &suc(suc(n)) * real_pow(c, suc(n))",
						Derive(func(d *Argument) {
							d.Do(Simp(Fwd(real_pow.PowExpSucClause), Fwd(real_ring.OfNumSuc)))
							d.Show(
								"with c^(n+1) = c·cⁿ and n + 2 = n + 1 + 1, both sides are (n+2)·c·cⁿ",
								ByArith())
						}))
					b.Show(
						"and x^(n+2) is x·x^(n+1) by Pow's step clause",
						By(value, product, real_pow.PowExpSucClause))
				})
		}),
})}

// DerivativePow — the power rule: x ↦ xⁿ has derivative n·xⁿ⁻¹.
//
// The exponent is 0 or a successor. x⁰ is the constant 1, with
// derivative 0; ℕ's subtraction truncates, so the stated value there is
// 0 times c^(0 − 1), which is 0 whatever that power is. At a successor
// n + 1 the successor rule applies, since (n + 1) − 1 = n.
var DerivativePow = derivativePowThm{family.Add(registry.ProofEntry{
	Name: "DerivativePow",
	Key:  "prop_d7b296e7153b7ef",
	Build: family.Theorem("∀n:num. ∀c:real. "+
		"    real_derivative_at(λx:real. real_pow(x, n), c, &n * real_pow(c, n - 1))",
		func(a *Argument) {
			nBinder := a.Binder("n")
			n := ext.As[Nat](nBinder)
			// The induction is ℕ's case split: the step never reads its
			// hypothesis.
			a.Induct(nBinder)
			a.Base(
				"x⁰ is the constant 1, whose derivative 0 is 0 times c^(0 − 1)",
				func(b *Argument) {
					c := b.FixAs[Real]()
					// Pow's zero clause makes x⁰ the constant 1 under the λ, and
					// 0 times c^(0 − 1) is 0.
					b.Do(Simp(Fwd(real_pow.PowExpZeroClause), Fwd(real_ring.MulLeftZero)))
					b.Show(
						"a constant has derivative 0",
						By(DerivativeConst.At(b.TermAs[Real]("&1"), c)))
				})
			a.Step(
				"x^(n+1) is a successor power, and (n + 1) − 1 = n",
				a.ForEach(func(c *Expr[Real]) Action {
					return By(Normalized, DerivativePowSuc.At(n, c), nat_arith.Add1.At(n), nat_monus.SucSubOne.At(n))
				}))
		}),
})}
