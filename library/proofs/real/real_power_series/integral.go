// integral.go — term-by-term integration: inside the interval where a
// power series converges, the sum of its integrated series is an
// antiderivative of its sum, and so its value at x is the integral of
// the sum from 0 to x.

package real_power_series

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_integral"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/registry"
)

// PowerSeriesAntiderivative — inside the interval where a power series
// converges, the sum F of its integrated series Σ a(n)·xⁿ⁺¹/(n + 1) has
// the sum f of the series as its derivative. F is itself the sum of a
// power series, with coefficients b(0) = 0 and b(n + 1) = a(n)/(n + 1),
// and the derived series of b, Σ (n + 1)·b(n + 1)·cⁿ, is Σ a(n)·cⁿ: term-by-
// term differentiation gives F a derivative at c, the sum of that series,
// which is f(c).
var PowerSeriesAntiderivative = powerSeriesAntiderivativeThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesAntiderivative",
	Key:  "prop_3db5f2c9aee3b998",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀f F:(real → real). ∀R c:real.",
		Hypotheses: []string{
			"∀x:real. |x| < R ⇒ real_sums(λn:num. a(n) * real_pow(x, n), f(x))",
			"∀x:real. |x| < R ⇒ real_sums(λn:num. a(n) * real_pow(x, n + 1) / &(n + 1), F(x))",
			"|c| < R",
		},
		Conclusion: "real_derivative_at(F, c, f(c))",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Real],
			f, F *Arrow[Real, Real],
			R, c *Expr[Real],
			sums, integrated, inside Fact,
		) {
			b, bDef := arg.LetAs[Fun[Nat, Real]]("b", "λn:num. COND(n = 0, &0, a(n - 1) / &n)")
			shifted := arg.Have(
				"past b(0), the coefficients b are those of the integrated series, a(n)/(n + 1)",
				"∀n:num. b(n + 1) = a(n) / &(n + 1)",
				bDef.Rw(),
				ByArith())
			series := arg.Have(
				"F is the power series with coefficients b: shifted by "+
					"one index, its terms are those of the integrated series",
				"∀x:real. |x| < R ⇒ real_sums(λn:num. b(n) * real_pow(x, n), F(x))",
				Derive(func(g *Argument) {
					x := g.FixAs[Real]()
					within := g.Assume()
					reindexed := g.Have(
						"the terms of the integrated series are b(n + 1)·xⁿ⁺¹",
						"(λn:num. a(n) * real_pow(x, n + 1) / &(n + 1)) = (λn:num. b(n + 1) * real_pow(x, n + 1))",
						Funext(),
						g.ForEach(func(n *Expr[Nat]) Action {
							return Chain(shifted.At(n).Rw(), ByArith())
						}))
					first := g.Have(
						"the first term b(0)·x⁰ vanishes, b(0) being 0",
						"F(x) - b(0) * real_pow(x, 0) = F(x)",
						bDef.Rw(),
						ByArith())
					tail := g.Have(
						"so the series of b(n + 1)·xⁿ⁺¹ sums to F(x) less the first term",
						"real_sums(λn:num. b(n + 1) * real_pow(x, n + 1), F(x) - b(0) * real_pow(x, 0))",
						By(integrated.At(x), within, reindexed, first))
					g.Show(
						"and with the first term put back, the series of b(n)·xⁿ sums to F(x)",
						By(tail, real_series.SumsShift))
				}))
			d, derivative := arg.ObtainAs[Real](
				"term by term, F has a derivative at c, the sum of the derived series of b",
				"∃d:real. real_sums(λn:num. &(n + 1) * b(n + 1) * real_pow(c, n), d) ∧ real_derivative_at(F, c, d)",
				By(series, inside, PowerSeriesDerivative.At(b, F, R, c)))
			derived := arg.Have(
				"the derived series of b is the series a at c: (n + 1)·b(n + 1) = a(n)",
				"(λn:num. &(n + 1) * b(n + 1) * real_pow(c, n)) = (λn:num. a(n) * real_pow(c, n))",
				Funext(),
				Derive(func(g *Argument) {
					n := g.FixAs[Nat]()
					positive := g.Have(
						"n + 1 is positive",
						"&0 < &(n + 1)",
						ByArith())
					g.Show(
						"so it cancels against the division by n + 1",
						shifted.At(n).Rw(),
						ByArith(positive))
				}))
			arg.Show(
				"the series a at c sums to f(c), and a series has only one sum, so the derivative is f(c)",
				By(
					derivative,
					derived,
					inside,
					sums.At(c),
					real_series.SumsUnique.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. a(n) * real_pow(c, n)"), d, f.Apply(c))))
		}),
})}

// PowerSeriesIntegral — term-by-term integration: inside the interval
// where a power series converges, its integrated series
// Σ a(n)·xⁿ⁺¹/(n + 1) sums to the integral of its sum f from 0 to x. Let
// F(y) be the sum of the integrated series at each y in ⟬−R, R⟭; it is an
// antiderivative of f there, and f and F are continuous there, so on
// every interval ⟦u, v⟧ inside ⟬−R, R⟭ the Newton–Leibniz theorem makes
// F(v) − F(u) the integral of f. Every term of the integrated series
// vanishes at 0, so F(0) = 0. For x ≥ 0 the integral from 0 to x is the
// integral over ⟦0, x⟧, F(x); for x < 0 it is minus the integral over
// ⟦x, 0⟧, −(F(0) − F(x)) = F(x).
var PowerSeriesIntegral = powerSeriesIntegralThm{family.Add(registry.ProofEntry{
	Name: "PowerSeriesIntegral",
	Key:  "prop_b49592f8e26eeb37",
	Build: family.Theorem(Statement{
		Binders: "∀a:(num → real). ∀f:(real → real). ∀R x:real.",
		Hypotheses: []string{
			"∀y:real. |y| < R ⇒ real_sums(λn:num. a(n) * real_pow(y, n), f(y))",
			"|x| < R",
		},
		Conclusion: "real_sums(λn:num. a(n) * real_pow(x, n + 1) / &(n + 1), real_integral(f, &0, x))",
	},
		func(
			arg *Argument,
			a *Arrow[Nat, Real],
			f *Arrow[Real, Real],
			R, x *Expr[Real],
			sums, inside Fact,
		) {
			F, sumsF := arg.ObtainAs[Fun[Real, Real]](
				"let F(y) be the sum of the integrated series at each y in ⟬−R, R⟭",
				"∃F:(real → real). ∀y:real. "+
					"    |y| < R ⇒ real_sums(λn:num. a(n) * real_pow(y, n + 1) / &(n + 1), F(y))",
				Derive(func(d *Argument) {
					d.Take(d.TermAs[Fun[Real, Real]](
						"λy:real. εs:real. real_sums(λn:num. a(n) * real_pow(y, n + 1) / &(n + 1), s)"))
					d.Show(
						"at each y in ⟬−R, R⟭ the integrated series converges, so the sum chosen there is one it has",
						d.ForEach(func(y *Expr[Real]) Action {
							return By(sums, PowerSeriesIntegratedConverges.At(a, R, y))
						}))
				}))
			antiderivative := arg.Have(
				"F has derivative f(y) at every y in ⟬−R, R⟭",
				"∀y:real. |y| < R ⇒ real_derivative_at(F, y, f(y))",
				By(sums, sumsF, PowerSeriesAntiderivative))
			onIntervals := arg.Have(
				"over every interval ⟦u, v⟧ inside ⟬−R, R⟭, f has integral F(v) − F(u)",
				"∀u v:real. |u| < R ∧ |v| < R ∧ u ≤ v ⇒ real_has_integral(f, u, v, F(v) - F(u))",
				Derive(func(d *Argument) {
					u := d.FixAs[Real]()
					v := d.FixAs[Real]()
					bounds := d.Assume()
					interval := d.TermAs[Set[Real]]("⟦u, v⟧")
					within := d.Have(
						"⟦u, v⟧ lies inside ⟬−R, R⟭",
						"∀y:real. u ≤ y ∧ y ≤ v ⇒ |y| < R",
						ByArith(bounds))
					pointwise := d.Have(
						"f, the sum of the series, is continuous at every point of ⟦u, v⟧",
						"∀y:real. u ≤ y ∧ y ≤ v ⇒ real_continuous_at(f, y)",
						By(sums, within, PowerSeriesContinuous))
					fContinuous := d.Have(
						"so f is continuous on ⟦u, v⟧",
						"real_continuous_on(⟦u, v⟧, f)",
						By(pointwise, real_continuous.ContinuousAtOn.At(f, interval)))
					FContinuous := d.Have(
						"F, having a derivative at every point of ⟦u, v⟧, is continuous there",
						"real_continuous_on(⟦u, v⟧, F)",
						By(antiderivative, within, real_derivative.DerivativeContinuousOn.At(F, f, interval)))
					open := d.Have(
						"strictly between u and v, F has derivative f",
						"∀y:real. u < y ∧ y < v ⇒ real_derivative_at(F, y, f(y))",
						ByArith(antiderivative, bounds))
					d.Show(
						"so by the Newton–Leibniz theorem F(v) − F(u) is the integral of f over ⟦u, v⟧",
						By(bounds, fContinuous, FContinuous, open, real_integral.NewtonLeibnizContinuous.At(F, f, u, v)))
				}))
			zero := arg.TermAs[Real]("&0")
			vanishing := arg.Have(
				"at 0 every term of the integrated series vanishes",
				"(λn:num. a(n) * real_pow(&0, n + 1) / &(n + 1)) = (λn:num. &0)",
				Funext(),
				arg.ForEach(func(n *Expr[Nat]) Action {
					return ByArith()
				}))
			atZero := arg.Have(
				"so F(0) = 0: the series of zeros sums only to 0",
				"F(&0) = &0",
				ByArith(
					sumsF.At(zero),
					inside,
					vanishing,
					real_series.SumsZero,
					real_series.SumsUnique.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. &0"), arg.TermAs[Real]("F(&0)"), zero)))
			integral := arg.Have(
				"the integral of f from 0 to x is F(x)",
				"real_integral(f, &0, x) = F(x)",
				Derive(func(d *Argument) {
					d.Cases(d.Term("&0 ≤ x"))
					d.When(
						"for x ≥ 0 it is the integral over ⟦0, x⟧, F(x) − F(0)",
						func(e *Argument, nonneg Fact) {
							e.Show(
								"which is F(x), F(0) being 0",
								ByArith(
									nonneg,
									inside,
									atZero,
									onIntervals.At(zero, x),
									real_integral.HasIntegralValue.At(f, zero, x, e.TermAs[Real]("F(x) - F(&0)"))))
						})
					d.Otherwise(
						"for x < 0 it is minus the integral over ⟦x, 0⟧, −(F(0) − F(x))",
						func(e *Argument, negative Fact) {
							e.Show(
								"which is F(x) again, F(0) being 0",
								ByArith(
									negative,
									inside,
									atZero,
									onIntervals.At(x, zero),
									real_integral.HasIntegralValue.At(f, x, zero, e.TermAs[Real]("F(&0) - F(x)")),
									real_integral.RealIntegralDef.At(f, zero, x),
									real_integral.RealIntegralDef.At(f, x, zero)))
						})
				}))
			arg.Show(
				"so the integrated series, which sums to F(x), sums to the integral of f from 0 to x",
				By(sumsF.At(x), inside, integral))
		}),
})}
