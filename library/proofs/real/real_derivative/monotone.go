// monotone.go — the sign of the derivative and monotonicity (README,
// "Monotonicity"). By the mean value theorem, a nonnegative derivative
// strictly between a and b makes a function continuous on ⟦a, b⟧
// increasing there, a positive one strictly increasing; the decreasing
// criteria are those for −f, and a zero derivative, both at once, makes f
// constant. Conversely a function increasing on a ball about c has a
// nonnegative derivative at c, its difference quotient being nonnegative
// there; on an open interval where f has a derivative everywhere the two
// directions meet.

package real_derivative

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_function_limits"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// DerivativeNonnegIncreasing — a function whose derivative is
// nonnegative strictly between a and b, and which is continuous on
// ⟦a, b⟧, is increasing on ⟦a, b⟧.
//
// Between two points x < y of ⟦a, b⟧ the mean value theorem finds a z
// with f(y) − f(x) = f'(z)·(y − x), a product of two nonnegative numbers.
var DerivativeNonnegIncreasing = derivativeNonnegIncreasingThm{family.Add(registry.ProofEntry{
	Name: "DerivativeNonnegIncreasing",
	Key:  "prop_53fb0e643e078ea",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(real → real). ∀a b x y:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦a, b⟧, f)",
			"∀t:real. a < t ∧ t < b ⇒ real_derivative_at(f, t, f'(t))",
			"∀t:real. a < t ∧ t < b ⇒ &0 ≤ f'(t)",
			"a ≤ x",
			"x ≤ y",
			"y ≤ b",
		},
		Conclusion: "f(x) ≤ f(y)",
	},
		func(arg *Argument, f, fPrime *Arrow[Real, Real], a, b *Expr[Real], given Fact) {
			held := arg.Conjuncts(
				given,
				"f is continuous on ⟦a, b⟧",
				"f has derivative f'(x) at every x strictly between a and b",
				"f' is nonnegative there")
			x := arg.FixAs[Real]()
			y := arg.FixAs[Real]()
			bounds := arg.Conjuncts(
				arg.Assume(),
				"a ≤ x",
				"x ≤ y",
				"y ≤ b")
			lower, ordered, upper := bounds[0], bounds[1], bounds[2]
			arg.Cases(arg.Term("x = y"))
			arg.When(
				"x = y: the two values are one",
				func(d *Argument, same Fact) {
					d.Do(same.Rw())
					d.Show(
						"f(y) ≤ f(y)",
						By(real_order_ring.LessEqRefl.At(f.Apply(y))))
				})
			arg.Otherwise(
				"x < y: the mean value theorem",
				func(d *Argument, apart Fact) {
					strict := d.Have(
						"x < y",
						"x < y",
						By(real_order_ring.LessThanSplit.At(x, y), ordered, apart))
					z0, found := d.ObtainAs[Real](
						"the mean value theorem finds z₀ strictly between x and y where the rise is f'(z₀) times the run",
						"∃z:real. x < z ∧ z < y ∧ f(y) - f(x) = f'(z) * (y - x)",
						By(MeanValueBetween.At(f, fPrime, a, b, x, y), held[0], held[1], lower, strict, upper))
					parts := d.Conjuncts(
						found,
						"x < z₀",
						"z₀ < y",
						"f(y) − f(x) = f'(z₀)·(y − x)")
					inside := d.Have(
						"z₀ is strictly between a and b",
						"a < z₀ ∧ z₀ < b",
						ByArith(parts[0], parts[1], lower, upper))
					sign := d.Have(
						"so f'(z₀) ≥ 0",
						"&0 ≤ f'(z₀)",
						By(held[2].At(z0), inside))
					run := d.Have(
						"and the run y − x is nonnegative",
						"&0 ≤ y - x",
						ByArith(strict))
					rise := d.Have(
						"so the rise is a product of two nonnegative numbers",
						"&0 ≤ f'(z₀) * (y - x)",
						By(real_construction.LessEqMul.At(fPrime.Apply(z0), d.TermAs[Real]("y - x")), sign, run))
					d.Show(
						"f(y) − f(x) ≥ 0",
						ByArith(parts[2], rise))
				})
		}),
})}

// DerivativePositiveStrictlyIncreasing — a positive derivative strictly
// between a and b, with continuity on ⟦a, b⟧, makes f strictly increasing
// on ⟦a, b⟧.
//
// Between x < y the mean value theorem's f(y) − f(x) = f'(z)·(y − x) is
// now a product of two positive numbers.
var DerivativePositiveStrictlyIncreasing = derivativePositiveStrictlyIncreasingThm{family.Add(registry.ProofEntry{
	Name: "DerivativePositiveStrictlyIncreasing",
	Key:  "prop_84d41690846e0708",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(real → real). ∀a b x y:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦a, b⟧, f)",
			"∀t:real. a < t ∧ t < b ⇒ real_derivative_at(f, t, f'(t))",
			"∀t:real. a < t ∧ t < b ⇒ &0 < f'(t)",
			"a ≤ x",
			"x < y",
			"y ≤ b",
		},
		Conclusion: "f(x) < f(y)",
	},
		func(arg *Argument, f, fPrime *Arrow[Real, Real], a, b *Expr[Real], given Fact) {
			held := arg.Conjuncts(
				given,
				"f is continuous on ⟦a, b⟧",
				"f has derivative f'(x) at every x strictly between a and b",
				"f' is positive there")
			x := arg.FixAs[Real]()
			y := arg.FixAs[Real]()
			bounds := arg.Conjuncts(
				arg.Assume(),
				"a ≤ x",
				"x < y",
				"y ≤ b")
			lower, strict, upper := bounds[0], bounds[1], bounds[2]
			z0, found := arg.ObtainAs[Real](
				"the mean value theorem finds z₀ strictly between x and y where the rise is f'(z₀) times the run",
				"∃z:real. x < z ∧ z < y ∧ f(y) - f(x) = f'(z) * (y - x)",
				By(MeanValueBetween.At(f, fPrime, a, b, x, y), held[0], held[1], lower, strict, upper))
			parts := arg.Conjuncts(
				found,
				"x < z₀",
				"z₀ < y",
				"f(y) − f(x) = f'(z₀)·(y − x)")
			inside := arg.Have(
				"z₀ is strictly between a and b",
				"a < z₀ ∧ z₀ < b",
				ByArith(parts[0], parts[1], lower, upper))
			sign := arg.Have(
				"so f'(z₀) > 0",
				"&0 < f'(z₀)",
				By(held[2].At(z0), inside))
			run := arg.Have(
				"and the run y − x is positive",
				"&0 < y - x",
				ByArith(strict))
			rise := arg.Have(
				"so the rise is a product of two positive numbers",
				"&0 < f'(z₀) * (y - x)",
				By(real_order_ring.MulPos.At(fPrime.Apply(z0), arg.TermAs[Real]("y - x")), sign, run))
			arg.Show(
				"f(y) − f(x) > 0",
				ByArith(parts[2], rise))
		}),
})}

// DerivativeNonposDecreasing — a derivative at most 0 strictly between a
// and b, with continuity on ⟦a, b⟧, makes f decreasing on ⟦a, b⟧.
//
// −f is continuous on ⟦a, b⟧ with the nonnegative derivative −f', so −f
// is increasing.
var DerivativeNonposDecreasing = derivativeNonposDecreasingThm{family.Add(registry.ProofEntry{
	Name: "DerivativeNonposDecreasing",
	Key:  "prop_eb66d077b34add37",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(real → real). ∀a b x y:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦a, b⟧, f)",
			"∀t:real. a < t ∧ t < b ⇒ real_derivative_at(f, t, f'(t))",
			"∀t:real. a < t ∧ t < b ⇒ f'(t) ≤ &0",
			"a ≤ x",
			"x ≤ y",
			"y ≤ b",
		},
		Conclusion: "f(y) ≤ f(x)",
	},
		func(arg *Argument, f, fPrime *Arrow[Real, Real], a, b *Expr[Real], given Fact) {
			held := arg.Conjuncts(
				given,
				"f is continuous on ⟦a, b⟧",
				"f has derivative f'(x) at every x strictly between a and b",
				"f' is at most 0 there")
			continuous := arg.Have(
				"−f is continuous on ⟦a, b⟧",
				"real_continuous_on(⟦a, b⟧, λt:real. -f(t))",
				By(real_continuous.ContinuousOnNeg, held[0]))
			derivatives := arg.Have(
				"−f has derivative −f'(x) at every x strictly between a and b",
				"∀x:real. a < x ∧ x < b ⇒ real_derivative_at(λt:real. -f(t), x, -f'(x))",
				Derive(func(d *Argument) {
					x := d.FixAs[Real]()
					inside := d.Assume()
					d.Show(
						"the negative of f's derivative at x",
						By(DerivativeNeg, held[1].At(x), inside))
				}))
			signs := arg.Have(
				"and −f'(x) ≥ 0 there",
				"∀x:real. a < x ∧ x < b ⇒ &0 ≤ -f'(x)",
				Derive(func(d *Argument) {
					x := d.FixAs[Real]()
					inside := d.Assume()
					d.Show(
						"f'(x) ≤ 0, and negation reverses it",
						ByArith(held[2].At(x), inside))
				}))
			negF := arg.TermAs[Fun[Real, Real]]("λt:real. -f(t)")
			negFPrime := arg.TermAs[Fun[Real, Real]]("λt:real. -f'(t)")
			x := arg.FixAs[Real]()
			y := arg.FixAs[Real]()
			pair := arg.Assume()
			below := arg.Have(
				"so −f is increasing on ⟦a, b⟧, and −f(x) ≤ −f(y)",
				"-f(x) ≤ -f(y)",
				By(
					DerivativeNonnegIncreasing.At(negF, negFPrime, a, b, x, y),
					continuous,
					derivatives,
					signs,
					pair))
			arg.Show(
				"that is, f(y) ≤ f(x)",
				ByArith(below))
		}),
})}

// DerivativeNegativeStrictlyDecreasing — a negative derivative strictly
// between a and b, with continuity on ⟦a, b⟧, makes f strictly
// decreasing on ⟦a, b⟧.
//
// −f is continuous on ⟦a, b⟧ with the positive derivative −f', so −f is
// strictly increasing.
var DerivativeNegativeStrictlyDecreasing = derivativeNegativeStrictlyDecreasingThm{family.Add(registry.ProofEntry{
	Name: "DerivativeNegativeStrictlyDecreasing",
	Key:  "prop_bfcc180e0e8f2cb3",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(real → real). ∀a b x y:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦a, b⟧, f)",
			"∀t:real. a < t ∧ t < b ⇒ real_derivative_at(f, t, f'(t))",
			"∀t:real. a < t ∧ t < b ⇒ f'(t) < &0",
			"a ≤ x",
			"x < y",
			"y ≤ b",
		},
		Conclusion: "f(y) < f(x)",
	},
		func(arg *Argument, f, fPrime *Arrow[Real, Real], a, b *Expr[Real], given Fact) {
			held := arg.Conjuncts(
				given,
				"f is continuous on ⟦a, b⟧",
				"f has derivative f'(x) at every x strictly between a and b",
				"f' is negative there")
			continuous := arg.Have(
				"−f is continuous on ⟦a, b⟧",
				"real_continuous_on(⟦a, b⟧, λt:real. -f(t))",
				By(real_continuous.ContinuousOnNeg, held[0]))
			derivatives := arg.Have(
				"−f has derivative −f'(x) at every x strictly between a and b",
				"∀x:real. a < x ∧ x < b ⇒ real_derivative_at(λt:real. -f(t), x, -f'(x))",
				Derive(func(d *Argument) {
					x := d.FixAs[Real]()
					inside := d.Assume()
					d.Show(
						"the negative of f's derivative at x",
						By(DerivativeNeg, held[1].At(x), inside))
				}))
			signs := arg.Have(
				"and −f'(x) > 0 there",
				"∀x:real. a < x ∧ x < b ⇒ &0 < -f'(x)",
				Derive(func(d *Argument) {
					x := d.FixAs[Real]()
					inside := d.Assume()
					d.Show(
						"f'(x) < 0, and negation reverses it",
						ByArith(held[2].At(x), inside))
				}))
			negF := arg.TermAs[Fun[Real, Real]]("λt:real. -f(t)")
			negFPrime := arg.TermAs[Fun[Real, Real]]("λt:real. -f'(t)")
			x := arg.FixAs[Real]()
			y := arg.FixAs[Real]()
			pair := arg.Assume()
			below := arg.Have(
				"so −f is strictly increasing on ⟦a, b⟧, and −f(x) < −f(y)",
				"-f(x) < -f(y)",
				By(
					DerivativePositiveStrictlyIncreasing.At(negF, negFPrime, a, b, x, y),
					continuous,
					derivatives,
					signs,
					pair))
			arg.Show(
				"that is, f(y) < f(x)",
				ByArith(below))
		}),
})}

// DerivativeZeroConstant — a function continuous on ⟦a, b⟧ whose
// derivative is 0 strictly between a and b is constant on ⟦a, b⟧.
//
// A zero derivative is both nonnegative and at most 0, so f is increasing
// and decreasing on ⟦a, b⟧: f(a) ≤ f(x) ≤ f(a).
var DerivativeZeroConstant = derivativeZeroConstantThm{family.Add(registry.ProofEntry{
	Name: "DerivativeZeroConstant",
	Key:  "prop_34d0ccf31d970f01",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a b x:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦a, b⟧, f)",
			"∀t:real. a < t ∧ t < b ⇒ real_derivative_at(f, t, &0)",
			"a ≤ x",
			"x ≤ b",
		},
		Conclusion: "f(x) = f(a)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a, b *Expr[Real], given Fact) {
			held := arg.Conjuncts(
				given,
				"f is continuous on ⟦a, b⟧",
				"f has derivative 0 at every x strictly between a and b")
			// Both criteria are read at the derivative function λt. &0, whose
			// sign hypotheses are this one fact.
			flat := arg.Have(
				"the derivative 0 is both at least and at most 0",
				"∀x:real. a < x ∧ x < b ⇒ &0 ≤ &0",
				Derive(func(d *Argument) {
					d.FixAs[Real]()
					d.Assume()
					d.Show(
						"0 ≤ 0",
						ByArith())
				}))
			zero := arg.TermAs[Fun[Real, Real]]("λt:real. &0")
			x := arg.FixAs[Real]()
			inside := arg.Assume()
			ends := arg.Have(
				"a and x are two points of ⟦a, b⟧, in order",
				"a ≤ a ∧ a ≤ x ∧ x ≤ b",
				ByArith(inside))
			up := arg.Have(
				"f is increasing on ⟦a, b⟧, so f(a) ≤ f(x)",
				"f(a) ≤ f(x)",
				By(DerivativeNonnegIncreasing.At(f, zero, a, b, a, x), held[0], held[1], flat, ends))
			down := arg.Have(
				"and decreasing, so f(x) ≤ f(a)",
				"f(x) ≤ f(a)",
				By(DerivativeNonposDecreasing.At(f, zero, a, b, a, x), held[0], held[1], flat, ends))
			arg.Show(
				"so f(x) = f(a)",
				ByArith(up, down))
		}),
})}

// IncreasingDerivativeNonneg — where f is increasing on an open interval
// ⟬c − d, c + d⟭ about c, its derivative at c is nonnegative.
//
// On the punctured ball the difference quotient is nonnegative. Its
// product with x − c is the increment f(x) − f(c), which monotonicity —
// read at the pair (x, c) to the left of c and at (c, x) to the right —
// makes at most 0 on the left and at least 0 on the right. So the
// quotient times a positive number, c − x on the left and x − c on the
// right, is nonnegative, and cancelling that factor leaves the quotient
// nonnegative. The quotient tends to l, the constant 0 tends to 0, and
// limits respect ≤ on a punctured ball.
var IncreasingDerivativeNonneg = increasingDerivativeNonnegThm{family.Add(registry.ProofEntry{
	Name: "IncreasingDerivativeNonneg",
	Key:  "prop_89a322660d727493",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c d l:real.",
		Hypotheses: []string{
			"&0 < d",
			"real_increasing_on(⟬c - d, c + d⟭, f)",
			"real_derivative_at(f, c, l)",
		},
		Conclusion: "&0 ≤ l",
	},
		func(a *Argument, f *Arrow[Real, Real], c, d, l *Expr[Real], given Fact) {
			held := a.Conjuncts(
				given,
				"the radius d is positive",
				"f is increasing on the interval of radius d about c",
				"f has derivative l at c")
			rises := a.Unfolded(held[1], real_continuous.RealIncreasingOnDef)
			quotientLimit := a.Unfolded(held[2], RealDerivativeAtDef)

			nonneg := a.Have(
				"on the punctured ball of radius d the difference quotient is nonnegative",
				"∀x:real. &0 < |x - c| ∧ |x - c| < d ⇒ &0 ≤ (f(x) - f(c)) / (x - c)",
				Derive(func(b *Argument) {
					x := b.FixAs[Real]()
					ball := b.Assume()
					offset := b.TermAs[Real]("x - c")
					increment := b.Have(
						"the quotient times x − c, which is not 0, is the increment f(x) − f(c)",
						"(f(x) - f(c)) / (x - c) * (x - c) = f(x) - f(c)",
						ByArith(ball))
					quotient := b.TermAs[Real]("(f(x) - f(c)) / (x - c)")
					zero := b.TermAs[Real]("&0")

					b.Cases(b.Term("x < c"))
					b.When(
						"to the left of c the increment is at most 0",
						func(e *Argument, left Fact) {
							falls := e.Have(
								"x and c lie in the ball with x ≤ c, so f(x) ≤ f(c)",
								"f(x) ≤ f(c)",
								ByArith(rises.At(x, c), held[0], ball, left))
							e.Show(
								"the quotient times the positive c − x is f(c) − f(x) ≥ 0, so the quotient is ≥ 0",
								ByArith(
									real_order_ring.LessEqCancelMulRight.At(zero, quotient, e.TermAs[Real]("c - x")),
									increment,
									falls,
									left))
						})
					b.Otherwise(
						"to the right of c the increment is at least 0",
						func(e *Argument, notLeft Fact) {
							rises := e.Have(
								"c and x lie in the ball with c ≤ x, so f(c) ≤ f(x)",
								"f(c) ≤ f(x)",
								ByArith(rises.At(c, x), held[0], ball, notLeft))
							e.Show(
								"the quotient times the positive x − c is f(x) − f(c) ≥ 0, so the quotient is ≥ 0",
								ByArith(
									real_order_ring.LessEqCancelMulRight.At(zero, quotient, offset),
									increment,
									rises,
									notLeft,
									ball))
						})
				}))

			a.Show(
				"the constant 0 tends to 0 and lies below the quotient on the punctured ball, and limits respect ≤",
				By(
					real_function_limits.LimitAtLessEq,
					held[0],
					nonneg,
					real_function_limits.LimitAtConst.At(a.TermAs[Real]("&0"), c),
					quotientLimit))
		}),
})}

// DecreasingDerivativeNonpos — where f is decreasing on an open interval
// ⟬c − d, c + d⟭ about c, its derivative at c is at most 0.
//
// −f is increasing on the same interval and has derivative −l at c, so
// −l ≥ 0.
var DecreasingDerivativeNonpos = decreasingDerivativeNonposThm{family.Add(registry.ProofEntry{
	Name: "DecreasingDerivativeNonpos",
	Key:  "prop_3c5d4ab3f02cebef",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c d l:real.",
		Hypotheses: []string{
			"&0 < d",
			"real_decreasing_on(⟬c - d, c + d⟭, f)",
			"real_derivative_at(f, c, l)",
		},
		Conclusion: "l ≤ &0",
	},
		func(a *Argument, f *Arrow[Real, Real], c, d, l *Expr[Real], given Fact) {
			held := a.Conjuncts(
				given,
				"the radius d is positive",
				"f is decreasing on the interval of radius d about c",
				"f has derivative l at c")
			falls := a.Unfolded(held[1], real_continuous.RealDecreasingOnDef)
			rising := a.Have(
				"so −f is increasing on that interval",
				"real_increasing_on(⟬c - d, c + d⟭, λx:real. -f(x))",
				Unfold(real_continuous.RealIncreasingOnDef),
				Derive(func(b *Argument) {
					x := b.FixAs[Real]()
					y := b.FixAs[Real]()
					pair := b.Assume()
					b.Show(
						"f(y) ≤ f(x), and negation reverses it",
						ByArith(falls.At(x, y), pair))
				}))
			negated := a.Have(
				"−f has derivative −l at c",
				"real_derivative_at(λx:real. -f(x), c, -l)",
				By(DerivativeNeg, held[2]))
			nonneg := a.Have(
				"so −l ≥ 0",
				"&0 ≤ -l",
				By(
					IncreasingDerivativeNonneg.At(
						a.TermAs[Fun[Real, Real]]("λx:real. -f(x)"), c, d, a.TermAs[Real]("-l")),
					held[0],
					rising,
					negated))
			a.Show(
				"that is, l ≤ 0",
				ByArith(nonneg))
		}),
})}

// IncreasingIffDerivativeNonneg — on an open interval where f has a
// derivative everywhere, f is increasing exactly when its derivative is
// nonnegative.
//
// If f is increasing on ⟬a, b⟭, then at a point c of ⟬a, b⟭ the interval
// of radius min(c − a, b − c) about c lies in ⟬a, b⟭, so f is increasing
// on that interval, and its derivative at c is nonnegative. Conversely,
// for a < x ≤ y < b every point of ⟦x, y⟧ lies in ⟬a, b⟭, where f has a
// derivative and so is continuous: f is continuous on ⟦x, y⟧, with a
// nonnegative derivative strictly between x and y, so it is increasing
// on ⟦x, y⟧, and in particular f(x) ≤ f(y).
var IncreasingIffDerivativeNonneg = increasingIffDerivativeNonnegThm{family.Add(registry.ProofEntry{
	Name: "IncreasingIffDerivativeNonneg",
	Key:  "prop_dc131b9a4254c30a",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(real → real). ∀a b:real.",
		Hypotheses: []string{
			"∀x:real. a < x ∧ x < b ⇒ real_derivative_at(f, x, f'(x))",
		},
		Conclusion: "real_increasing_on(⟬a, b⟭, f) ⇔ ∀x:real. a < x ∧ x < b ⇒ &0 ≤ f'(x)",
	},
		func(arg *Argument, f, fPrime *Arrow[Real, Real], a, b *Expr[Real], derivatives Fact) {
			arg.Iff()

			arg.Forward(
				"increasing on ⟬a, b⟭, f is increasing on an interval "+
					"about each point, so its derivative there is at least 0",
				func(d *Argument, increasing Fact) {
					rises := d.Unfolded(increasing, real_continuous.RealIncreasingOnDef)
					c := d.FixAs[Real]("c")
					inside := d.Assume()
					toA, toB := d.TermAs[Real]("c - a"), d.TermAs[Real]("b - c")
					radius := d.TermAs[Real]("min(c - a, b - c)")
					positive := d.Have(
						"c is a positive distance from the nearer end",
						"&0 < min(c - a, b - c)",
						ByArith(inside, real_sup_inf.LessThanMin.At(toA, toB, d.TermAs[Real]("&0"))))
					onBall := d.Have(
						"the interval of that radius about c lies in ⟬a, b⟭, so f is increasing on it",
						"real_increasing_on(⟬c - min(c - a, b - c), c + min(c - a, b - c)⟭, f)",
						Unfold(real_continuous.RealIncreasingOnDef),
						Derive(func(e *Argument) {
							x := e.FixAs[Real]()
							y := e.FixAs[Real]()
							near := e.Assume()
							pair := e.Have(
								"x and y are nearer to c than both ends are, so both lie in ⟬a, b⟭",
								"x ∈ ⟬a, b⟭ ∧ y ∈ ⟬a, b⟭ ∧ x ≤ y",
								ByArith(near, real_sup_inf.MinLowerBound.At(toA, toB)))
							e.Show(
								"so f(x) ≤ f(y)",
								By(rises.At(x, y), pair))
						}))
					derivative := d.Have(
						"f has derivative f'(c) at c",
						"real_derivative_at(f, c, f'(c))",
						By(derivatives.At(c), inside))
					d.Show(
						"a function increasing on an interval about c has a nonnegative derivative at c",
						By(IncreasingDerivativeNonneg.At(f, c, radius, fPrime.Apply(c)), positive, onBall, derivative))
				})

			arg.Backward(
				"with f' ≥ 0, f is increasing on ⟦x, y⟧ for any a < x ≤ y < b",
				func(d *Argument, nonneg Fact) {
					d.Do(Unfold(real_continuous.RealIncreasingOnDef))
					x := d.FixAs[Real]()
					y := d.FixAs[Real]()
					pair := d.Assume()
					onSegment := d.Have(
						"f has derivative f'(c) at every point c of ⟦x, y⟧, each strictly between a and b",
						"∀c:real. c ∈ ⟦x, y⟧ ⇒ real_derivative_at(f, c, f'(c))",
						Derive(func(e *Argument) {
							c := e.FixAs[Real]()
							in := e.Assume()
							bounds := e.Have(
								"x ≤ c ≤ y",
								"x ≤ c ∧ c ≤ y",
								BySets(in))
							inside := e.Have(
								"so c is strictly between a and b",
								"a < c ∧ c < b",
								ByArith(bounds, pair))
							e.Show(
								"where f has derivative f'(c)",
								By(derivatives.At(c), inside))
						}))
					continuous := d.Have(
						"so f is continuous on ⟦x, y⟧",
						"real_continuous_on(⟦x, y⟧, f)",
						By(onSegment, DerivativeContinuousOn.At(f, fPrime, d.TermAs[Set[Real]]("⟦x, y⟧"))))
					between := d.Have(
						"f has derivative f'(t) at every t strictly between x and y",
						"∀t:real. x < t ∧ t < y ⇒ real_derivative_at(f, t, f'(t))",
						Derive(func(e *Argument) {
							t := e.FixAs[Real]()
							strictly := e.Assume()
							inside := e.Have(
								"t is strictly between a and b",
								"a < t ∧ t < b",
								ByArith(strictly, pair))
							e.Show(
								"where f has its derivative",
								By(derivatives.At(t), inside))
						}))
					signs := d.Have(
						"and f'(t) ≥ 0 there",
						"∀t:real. x < t ∧ t < y ⇒ &0 ≤ f'(t)",
						Derive(func(e *Argument) {
							t := e.FixAs[Real]()
							strictly := e.Assume()
							inside := e.Have(
								"t is strictly between a and b",
								"a < t ∧ t < b",
								ByArith(strictly, pair))
							e.Show(
								"where f' is nonnegative",
								By(nonneg.At(t), inside))
						}))
					ends := d.Have(
						"x and y are the two ends of ⟦x, y⟧, in order",
						"x ≤ x ∧ x ≤ y ∧ y ≤ y",
						ByArith(pair))
					d.Show(
						"f is increasing on ⟦x, y⟧, its derivative being nonnegative inside: read at the two ends",
						By(DerivativeNonnegIncreasing.At(f, fPrime, x, y, x, y), continuous, between, signs, ends))
				})
		}),
})}

// DecreasingIffDerivativeNonpos — on an open interval where f has a
// derivative everywhere, f is decreasing exactly when its derivative is
// at most 0.
//
// −f has the derivative −f' there, and f is decreasing exactly when −f is
// increasing, which is exactly when −f' ≥ 0, that is f' ≤ 0.
var DecreasingIffDerivativeNonpos = decreasingIffDerivativeNonposThm{family.Add(registry.ProofEntry{
	Name: "DecreasingIffDerivativeNonpos",
	Key:  "prop_97f4e684b2453036",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(real → real). ∀a b:real.",
		Hypotheses: []string{
			"∀x:real. a < x ∧ x < b ⇒ real_derivative_at(f, x, f'(x))",
		},
		Conclusion: "real_decreasing_on(⟬a, b⟭, f) ⇔ ∀x:real. a < x ∧ x < b ⇒ f'(x) ≤ &0",
	},
		func(arg *Argument, f, fPrime *Arrow[Real, Real], a, b *Expr[Real], derivatives Fact) {
			negatedDerivatives := arg.Have(
				"−f has derivative −f'(x) at every x strictly between a and b",
				"∀x:real. a < x ∧ x < b ⇒ real_derivative_at(λt:real. -f(t), x, -f'(x))",
				Derive(func(d *Argument) {
					x := d.FixAs[Real]()
					inside := d.Assume()
					derivative := d.Have(
						"f has derivative f'(x) at x",
						"real_derivative_at(f, x, f'(x))",
						By(derivatives.At(x), inside))
					d.Show(
						"the negative of that derivative",
						By(DerivativeNeg, derivative))
				}))
			// The equivalence read at −f and −f'; it lands resident, for the
			// two directions to rewrite by.
			equivalent := arg.Have(
				"so −f is increasing on ⟬a, b⟭ exactly when −f' ≥ 0 there",
				"real_increasing_on(⟬a, b⟭, λt:real. -f(t)) ⇔ (∀x:real. a < x ∧ x < b ⇒ &0 ≤ -f'(x))",
				By(
					IncreasingIffDerivativeNonneg.At(
						arg.TermAs[Fun[Real, Real]]("λt:real. -f(t)"),
						arg.TermAs[Fun[Real, Real]]("λt:real. -f'(t)"),
						a,
						b),
					negatedDerivatives))
			arg.Iff()
			arg.Forward(
				"f decreasing makes −f increasing, so −f' ≥ 0 and f' ≤ 0",
				func(d *Argument, decreasing Fact) {
					falling := d.Unfolded(decreasing, real_continuous.RealDecreasingOnDef)
					rising := d.Have(
						"−f is increasing on ⟬a, b⟭",
						"real_increasing_on(⟬a, b⟭, λt:real. -f(t))",
						Unfold(real_continuous.RealIncreasingOnDef),
						Derive(func(e *Argument) {
							x := e.FixAs[Real]()
							y := e.FixAs[Real]()
							pair := e.Assume()
							below := e.Have(
								"f(y) ≤ f(x)",
								"f(y) ≤ f(x)",
								By(falling.At(x, y), pair))
							e.Show(
								"negation reverses it",
								ByArith(below))
						}))
					signs := d.Have(
						"so −f'(x) ≥ 0 on ⟬a, b⟭",
						"∀x:real. a < x ∧ x < b ⇒ &0 ≤ -f'(x)",
						Derive(func(e *Argument) {
							e.Do(equivalent.RwRev())
							e.Show(
								"that is −f increasing",
								By(rising))
						}))
					x := d.FixAs[Real]()
					inside := d.Assume()
					d.Show(
						"−f'(x) ≥ 0, so f'(x) ≤ 0",
						ByArith(signs.At(x), inside))
				})
			arg.Backward(
				"f' ≤ 0 makes −f' ≥ 0, so −f is increasing and f decreasing",
				func(d *Argument, nonpositive Fact) {
					signs := d.Have(
						"−f'(x) ≥ 0 on ⟬a, b⟭",
						"∀x:real. a < x ∧ x < b ⇒ &0 ≤ -f'(x)",
						Derive(func(e *Argument) {
							x := e.FixAs[Real]()
							inside := e.Assume()
							sign := e.Have(
								"f'(x) ≤ 0",
								"f'(x) ≤ &0",
								By(nonpositive.At(x), inside))
							e.Show(
								"negation reverses it",
								ByArith(sign))
						}))
					rising := d.Have(
						"so −f is increasing on ⟬a, b⟭",
						"real_increasing_on(⟬a, b⟭, λt:real. -f(t))",
						Derive(func(e *Argument) {
							e.Do(equivalent.Rw())
							e.Show(
								"that is −f' ≥ 0",
								By(signs))
						}))
					rises := d.Unfolded(rising, real_continuous.RealIncreasingOnDef)
					d.Do(Unfold(real_continuous.RealDecreasingOnDef))
					x := d.FixAs[Real]()
					y := d.FixAs[Real]()
					pair := d.Assume()
					d.Show(
						"−f(x) ≤ −f(y), so f(y) ≤ f(x)",
						ByArith(rises.At(x, y), pair))
				})
		}),
})}
