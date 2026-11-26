// extrema.go — local extrema (README, "Local extrema"): the sign of the
// derivative says on which side of c the function lies above f(c), and
// so at a local maximum or minimum the derivative is 0.

package real_derivative

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_function_limits"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/registry"
)

// PositiveDerivativeRises — where the derivative is positive, f lies
// below f(c) just to the left of c and above it just to the right.
//
// The difference quotient tends to l > 0, so it is positive on some
// punctured ball (LimitAtPositive). There the increment f(x) − f(c) is
// the quotient times x − c, so it has the sign of x − c: negative to the
// left of c, positive to the right.
var PositiveDerivativeRises = positiveDerivativeRisesThm{family.Add(registry.ProofEntry{
	Name: "PositiveDerivativeRises",
	Key:  "prop_e5298c6e4f8836ab",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c l:real.",
		Hypotheses: []string{
			"real_derivative_at(f, c, l)",
			"&0 < l",
		},
		Conclusion: "∃d:real. " +
			"    &0 < d ∧ " +
			"    (∀x:real. c - d < x ∧ x < c ⇒ f(x) < f(c)) ∧ " +
			"    (∀x:real. c < x ∧ x < c + d ⇒ f(c) < f(x))",
	},
		func(a *Argument, f *Arrow[Real, Real], c, l *Expr[Real], given Fact) {
			d0, positiveBall := a.ObtainAs[Real](
				"the quotient tends to l > 0, so it is positive on a punctured ball of some radius d₀",
				"∃d:real. &0 < d ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < d ⇒ &0 < (f(x) - f(c)) / (x - c)",
				By(real_function_limits.LimitAtPositive, a.Unfolded(given, RealDerivativeAtDef)))
			held := a.Conjuncts(
				positiveBall,
				"d₀ is positive",
				"on the punctured ball of radius d₀ the quotient is positive")
			increment := a.Have(
				"on that ball f(x) − f(c) is the positive quotient times x − c",
				Statement{
					Binders: "∀x:real.",
					Hypotheses: []string{
						"&0 < |x - c|",
						"|x - c| < d₀",
					},
					Conclusion: "&0 < (f(x) - f(c)) / (x - c) ∧ (f(x) - f(c)) / (x - c) * (x - c) = f(x) - f(c)",
				},
				Derive(func(b *Argument) {
					x := b.FixAs[Real]()
					ball := b.Assume()
					b.Do(SplitConj(
						Case(
							"the quotient is positive there",
							By(held[1].At(x), ball)),
						Case(
							"and multiplying it back by x − c, which is not 0, returns the increment",
							ByArith(ball)),
					))
				}))
			a.Take(d0)
			a.Do(SplitConjAll(
				Case(
					"the radius d₀ is positive",
					By(held[0])),
				Case(
					"to the left of c the increment is the positive quotient times the negative x − c",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						left := b.Assume()
						ball := b.Have(
							"x lies in the punctured ball",
							"&0 < |x - c| ∧ |x - c| < d₀",
							ByArith(left))
						factored := b.Have(
							"there the increment is the positive quotient times x − c",
							"&0 < (f(x) - f(c)) / (x - c) ∧ (f(x) - f(c)) / (x - c) * (x - c) = f(x) - f(c)",
							By(increment.At(x), ball))
						gap := b.Have(
							"c − x is positive",
							"&0 < c - x",
							ByArith(left))
						product := b.Have(
							"so the quotient times c − x is positive",
							"&0 < (f(x) - f(c)) / (x - c) * (c - x)",
							By(
								real_order_ring.MulPos.At(b.TermAs[Real]("(f(x) - f(c)) / (x - c)"), b.TermAs[Real]("c - x")),
								factored,
								gap))
						b.Show(
							"and f(x) − f(c) is its negative",
							ByArith(factored, product))
					})),
				Case(
					"to the right of c it is the positive quotient times the positive x − c",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						right := b.Assume()
						ball := b.Have(
							"x lies in the punctured ball",
							"&0 < |x - c| ∧ |x - c| < d₀",
							ByArith(right))
						factored := b.Have(
							"there the increment is the positive quotient times x − c",
							"&0 < (f(x) - f(c)) / (x - c) ∧ (f(x) - f(c)) / (x - c) * (x - c) = f(x) - f(c)",
							By(increment.At(x), ball))
						gap := b.Have(
							"x − c is positive",
							"&0 < x - c",
							ByArith(right))
						product := b.Have(
							"so the quotient times x − c is positive",
							"&0 < (f(x) - f(c)) / (x - c) * (x - c)",
							By(
								real_order_ring.MulPos.At(b.TermAs[Real]("(f(x) - f(c)) / (x - c)"), b.TermAs[Real]("x - c")),
								factored,
								gap))
						b.Show(
							"and that product is f(x) − f(c)",
							ByArith(factored, product))
					})),
			))
		}),
})}

// NegativeDerivativeFalls — where the derivative is negative, f lies
// above f(c) just to the left of c and below it just to the right.
//
// −f has the positive derivative −l at c, so it rises through c; its
// being below −f(c) is f's being above f(c), and the other way round.
var NegativeDerivativeFalls = negativeDerivativeFallsThm{family.Add(registry.ProofEntry{
	Name: "NegativeDerivativeFalls",
	Key:  "prop_4c90f0808c8ae83b",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c l:real.",
		Hypotheses: []string{
			"real_derivative_at(f, c, l)",
			"l < &0",
		},
		Conclusion: "∃d:real. " +
			"    &0 < d ∧ " +
			"    (∀x:real. c - d < x ∧ x < c ⇒ f(c) < f(x)) ∧ " +
			"    (∀x:real. c < x ∧ x < c + d ⇒ f(x) < f(c))",
	},
		func(a *Argument, f *Arrow[Real, Real], c, l *Expr[Real], given Fact) {
			parts := a.Conjuncts(
				given,
				"f has derivative l at c",
				"l is negative")
			negated := a.Have(
				"−f has derivative −l at c",
				"real_derivative_at(λx:real. -f(x), c, -l)",
				By(DerivativeNeg, parts[0]))
			pos := a.Have(
				"−l is positive",
				"&0 < -l",
				ByArith(parts[1]))
			d0, sides := a.ObtainAs[Real](
				"so −f rises through c: within some radius d₀ it lies "+
					"below −f(c) to the left and above it to the right",
				"∃d:real. "+
					"    &0 < d ∧ "+
					"    (∀x:real. c - d < x ∧ x < c ⇒ -f(x) < -f(c)) ∧ "+
					"    (∀x:real. c < x ∧ x < c + d ⇒ -f(c) < -f(x))",
				By(
					PositiveDerivativeRises.At(a.TermAs[Fun[Real, Real]]("λx:real. -f(x)"), c, a.TermAs[Real]("-l")),
					negated,
					pos))
			held := a.Conjuncts(
				sides,
				"d₀ is positive",
				"to the left −f lies below −f(c)",
				"to the right −f lies above −f(c)")
			a.Take(d0)
			a.Do(SplitConjAll(
				Case(
					"the radius d₀ is positive",
					By(held[0])),
				Case(
					"to the left of c, −f below −f(c) is f above f(c)",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						left := b.Assume()
						b.Show(
							"−f(x) < −f(c), so f(c) < f(x)",
							ByArith(held[1].At(x), left))
					})),
				Case(
					"to the right of c, −f above −f(c) is f below f(c)",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						right := b.Assume()
						b.Show(
							"−f(c) < −f(x), so f(x) < f(c)",
							ByArith(held[2].At(x), right))
					})),
			))
		}),
})}

// LocalMaxDerivativeZero — at a local maximum the derivative is 0
// (Fermat).
//
// Were the derivative l positive, f would rise through c: within some
// radius δ₀ it lies above f(c) just to the right of c. Halfway out along
// the smaller of d and δ₀ the point is both just right of c and within d
// of it, so f there is above f(c) and at most f(c). Were l negative, f
// would fall through c and the same happens halfway out to the left. So l
// is neither positive nor negative.
var LocalMaxDerivativeZero = localMaxDerivativeZeroThm{family.Add(registry.ProofEntry{
	Name: "LocalMaxDerivativeZero",
	Key:  "prop_fac6dcf94b736d8b",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c d l:real.",
		Hypotheses: []string{
			"&0 < d",
			"∀x:real. |x - c| < d ⇒ f(x) ≤ f(c)",
			"real_derivative_at(f, c, l)",
		},
		Conclusion: "l = &0",
	},
		func(a *Argument, f *Arrow[Real, Real], c, d, l *Expr[Real], given Fact) {
			held := a.Conjuncts(
				given,
				"d is positive",
				"within d of c, f is at most f(c)",
				"f has derivative l at c")
			zero := a.TermAs[Real]("&0")

			notPositive := a.Have(
				"l is not positive",
				"¬(&0 < l)",
				Derive(func(b *Argument) {
					positive := b.SupposeNot()
					delta, rises := b.ObtainAs[Real](
						"then f rises through c: within some radius δ₀ it "+
							"lies below f(c) to the left and above it to the right",
						"∃δ:real. "+
							"    &0 < δ ∧ "+
							"    (∀x:real. c - δ < x ∧ x < c ⇒ f(x) < f(c)) ∧ "+
							"    (∀x:real. c < x ∧ x < c + δ ⇒ f(c) < f(x))",
						By(Normalized, PositiveDerivativeRises.At(f, c, l), held[2], positive))
					side := b.Conjuncts(
						rises,
						"δ₀ is positive",
						"to the left f lies below f(c)",
						"to the right f lies above f(c)")
					cut := b.Have(
						"the smaller of d and δ₀ is positive, both being positive",
						"&0 < min(d, δ₀)",
						By(real_sup_inf.LessThanMin.At(d, delta, zero), held[0], side[0]))
					point := b.TermAs[Real]("c + min(d, δ₀) / &2")
					placed := b.Have(
						"the point halfway out along it lies right of c within δ₀, and within d of c",
						"c < c + min(d, δ₀) / &2 ∧ c + min(d, δ₀) / &2 < c + δ₀ ∧ |(c + min(d, δ₀) / &2) - c| < d",
						ByArith(cut, real_sup_inf.MinLowerBound.At(d, delta)))
					b.Show(
						"f there lies above f(c) and, c being a maximum within d, at most f(c): it cannot be both",
						ByArith(side[2].At(point), placed, held[1].At(point)))
				}))

			notNegative := a.Have(
				"nor is l negative",
				"¬(l < &0)",
				Derive(func(b *Argument) {
					negative := b.SupposeNot()
					delta, falls := b.ObtainAs[Real](
						"then f falls through c: within some radius δ₀ it "+
							"lies above f(c) to the left and below it to the right",
						"∃δ:real. "+
							"    &0 < δ ∧ "+
							"    (∀x:real. c - δ < x ∧ x < c ⇒ f(c) < f(x)) ∧ "+
							"    (∀x:real. c < x ∧ x < c + δ ⇒ f(x) < f(c))",
						By(Normalized, NegativeDerivativeFalls.At(f, c, l), held[2], negative))
					side := b.Conjuncts(
						falls,
						"δ₀ is positive",
						"to the left f lies above f(c)",
						"to the right f lies below f(c)")
					cut := b.Have(
						"the smaller of d and δ₀ is positive, both being positive",
						"&0 < min(d, δ₀)",
						By(real_sup_inf.LessThanMin.At(d, delta, zero), held[0], side[0]))
					point := b.TermAs[Real]("c - min(d, δ₀) / &2")
					placed := b.Have(
						"the point halfway out along it lies left of c within δ₀, and within d of c",
						"c - δ₀ < c - min(d, δ₀) / &2 ∧ c - min(d, δ₀) / &2 < c ∧ |(c - min(d, δ₀) / &2) - c| < d",
						ByArith(cut, real_sup_inf.MinLowerBound.At(d, delta)))
					b.Show(
						"f there lies above f(c) and, c being a maximum within d, at most f(c): it cannot be both",
						ByArith(side[1].At(point), placed, held[1].At(point)))
				}))

			a.Show(
				"l is neither positive nor negative, so it is 0",
				ByArith(notPositive, notNegative))
		}),
})}

// LocalMinDerivativeZero — at a local minimum the derivative is 0.
//
// A local minimum of f is a local maximum of −f, whose derivative there
// is −l; so −l = 0.
var LocalMinDerivativeZero = localMinDerivativeZeroThm{family.Add(registry.ProofEntry{
	Name: "LocalMinDerivativeZero",
	Key:  "prop_4b004300bea2cbb2",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c d l:real.",
		Hypotheses: []string{
			"&0 < d",
			"∀x:real. |x - c| < d ⇒ f(c) ≤ f(x)",
			"real_derivative_at(f, c, l)",
		},
		Conclusion: "l = &0",
	},
		func(a *Argument, f *Arrow[Real, Real], c, d, l *Expr[Real], given Fact) {
			held := a.Conjuncts(
				given,
				"the radius d is positive",
				"f(c) is the least value on the ball of radius d about c",
				"f has derivative l at c")
			largest := a.Have(
				"so −f(c) is the largest value of −f on that ball",
				"∀x:real. |x - c| < d ⇒ -f(x) ≤ -f(c)",
				Derive(func(b *Argument) {
					x := b.FixAs[Real]()
					inBall := b.Assume()
					b.Show(
						"f(c) ≤ f(x), and negation reverses it",
						ByArith(held[1].At(x), inBall))
				}))
			negated := a.Have(
				"−f has derivative −l at c",
				"real_derivative_at(λx:real. -f(x), c, -l)",
				By(DerivativeNeg, held[2]))
			zero := a.Have(
				"so −l = 0, by Fermat's theorem at the maximum of −f",
				"-l = &0",
				By(
					LocalMaxDerivativeZero.At(a.TermAs[Fun[Real, Real]]("λx:real. -f(x)"), c, d, a.TermAs[Real]("-l")),
					held[0],
					largest,
					negated))
			a.Show(
				"that is, l = 0",
				ByArith(zero))
		}),
})}
