// exp_derivative.go — exp near 0, its derivative, and what the
// derivative gives: continuity, of exp and of c·exp(b·(x − m)²), hence
// every positive value.

package real_exp_log

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/proofs/sets/set_order"
	"github.com/euc-ai/xugo/library/registry"
)

// ExpQuadraticBound — dropping the series' first two terms, 1 and h,
// leaves the series of hⁿ⁺²/(n + 2)!, which sums to exp(h) − 1 − h.
// With |h| ≤ 1 its n-th term is at most h²/2·(1/2)ⁿ in size, since
// |h|ⁿ ≤ 1 and (n + 2)! ≥ 2ⁿ⁺¹; those bounds sum to
// h²/2·(1 − 1/2)⁻¹ = h², and a series dominated termwise in size sums
// to no more in size.
var ExpQuadraticBound = expQuadraticBoundThm{family.Add(registry.ProofEntry{
	Name: "ExpQuadraticBound",
	Key:  "prop_8ab8a2ec9ce02bfd",
	Build: family.Theorem(Statement{
		Binders: "∀h:real.",
		Hypotheses: []string{
			"|h| ≤ &1",
		},
		Conclusion: "|exp(h) - &1 - h| ≤ real_pow(h, 2)",
	},
		func(arg *Argument, h *Expr[Real], small Fact) {
			factorialBound := arg.Have(
				"(n + 2)! is at least 2ⁿ⁺¹, by induction on n",
				"∀n:num. nat_pow(2, n + 1) ≤ factorial(n + 2)",
				Derive(func(d *Argument) {
					d.Induct("n")
					d.Base(
						"at n = 0 both sides are 2",
						ByArith())
					d.Step(
						"the next step doubles the power and multiplies the factorial by n + 3 ≥ 2",
						func(b *Argument, ih Fact) {
							b.Show(
								"2ⁿ⁺² = 2·2ⁿ⁺¹ ≤ 2·(n + 2)! ≤ (n + 3)·(n + 2)! = (n + 3)!",
								Simp(Fwd(nat_arith.AddLeftSucClause), Fwd(nat_arith.NatPow), Fwd(nat_arith.Factorial)),
								ByArith(ih))
						})
				}))

			terms := arg.TermAs[Fun[Nat, Real]]("λn:num. real_pow(h, n) / &factorial(n)")
			zero, one := arg.TermAs[Nat]("0"), arg.TermAs[Nat]("1")
			remainder := arg.Have(
				"the first two terms contribute 1 + h, leaving exp(h) − 1 − h",
				"exp(h) - Σ_{k∈0 .. 1} (real_pow(h, k) / &factorial(k)) = exp(h) - &1 - h",
				ByArith(real_sum.PeelRight.At(one, zero, terms), real_sum.IntervalPoint.At(zero, terms)))
			remainderSeries := arg.Have(
				"dropping the first two terms leaves the series from index 2, summing to exp(h) − 1 − h",
				"real_sums(λn:num. real_pow(h, n + 2) / &factorial(n + 2), exp(h) - &1 - h)",
				Simp(Fwd(nat_arith.Two), Fwd(nat_arith.AddSuc)),
				Simp(Fwd(nat_arith.Add1)),
				By(remainder, ExpSums.At(h), real_series.SumsOffset.At(terms, arg.TermAs[Real]("exp(h)"), one)))

			termBound := arg.Have(
				"with |h| ≤ 1 its n-th term, hⁿ⁺²/(n + 2)!, is at most h²/2·(1/2)ⁿ in size",
				"∀n:num. |real_pow(h, n + 2) / &factorial(n + 2)| ≤ real_pow(h, 2) / &2 * real_pow(&1 / &2, n)",
				Derive(func(d *Argument) {
					n := d.FixAs[Nat]()
					factorialAbove := d.Have(
						"2ⁿ⁺¹ ≤ (n + 2)!, carried into ℝ",
						"real_pow(&2, n + 1) ≤ &factorial(n + 2)",
						By(
							factorialBound.At(n),
							real_pow.OfNumPow.At(d.TermAs[Nat]("2"), d.TermAs[Nat]("n + 1")),
							real_construction.OfNumLessEq.At(
								d.TermAs[Nat]("nat_pow(2, n + 1)"), d.TermAs[Nat]("factorial(n + 2)"))))
					positive := d.Have(
						"2ⁿ⁺¹ is positive",
						"&0 < real_pow(&2, n + 1)",
						ByArith())
					factorialPositive := d.Have(
						"and so is (n + 2)!",
						"&0 < &factorial(n + 2)",
						ByArith(factorialAbove, positive))
					shrink := d.Have(
						"|h|ⁿ ≤ 1ⁿ = 1, as 0 ≤ |h| ≤ 1",
						"real_pow(|h|, n) ≤ &1",
						By(
							Normalized,
							small,
							real_pow.PowMonoBase.At(d.TermAs[Real]("|h|"), d.TermAs[Real]("&1"), n),
							real_sgn_abs.AbsNonneg.At(h),
							real_pow.OnePow.At(n)))
					inverse := d.Have(
						"inverses reverse the order between positives: 1/(n + 2)! ≤ 1/2ⁿ⁺¹",
						"real_inv(&factorial(n + 2)) ≤ real_inv(real_pow(&2, n + 1))",
						By(factorialAbove, positive, real_order_field.InvAntitoneWeak))
					quotient := d.TermAs[Real]("real_pow(h, 2) / &factorial(n + 2)")
					quotientNonneg := d.Have(
						"h²/(n + 2)! is a square over a positive number, so nonnegative",
						"&0 ≤ real_pow(h, 2) / &factorial(n + 2)",
						ByArith(factorialPositive))
					termSize := d.TermAs[Real]("|real_pow(h, n + 2) / &factorial(n + 2)|")
					d.Show(
						"so the term is at most h²/2·(1/2)ⁿ in size",
						real_order_ring.OrderCalc(d.Ctx()).CalcLeibniz(termSize,
							LeLeg(
								quotient,
								"the size is |h|ⁿ·h²/(n + 2)!, and |h|ⁿ ≤ 1 scales the nonnegative h²/(n + 2)! down",
								Simp(
									Fwd(real_sgn_abs.AbsDiv),
									Fwd(real_sgn_abs.AbsOfNum),
									Fwd(real_pow.AbsPow),
									Fwd(real_pow.PowAdd)),
								ByArith(shrink, quotientNonneg)),
							LeLeg(
								d.TermAs[Real]("real_pow(h, 2) / real_pow(&2, n + 1)"),
								"1/(n + 2)! ≤ 1/2ⁿ⁺¹, scaled by h² ≥ 0",
								Simp(Fwd(real_field.RealDivDef)),
								ByArith(inverse)),
							EqLeg(
								d.TermAs[Real]("real_pow(h, 2) / &2 * real_pow(&1 / &2, n)"),
								"2ⁿ⁺¹ is 2ⁿ·2, and h²/(2ⁿ·2) is h²/2 times (1/2)ⁿ",
								Simp(
									Fwd(real_pow.PowAdd),
									Fwd(real_pow.PowOne),
									Fwd(real_field.RealDivDef),
									Fwd(field.InvMul.Read(real_field.Field))),
								ByArith())))
				}))

			dominating := arg.Have(
				"h²/2 times the geometric series of 1/2 sums to h²/2·(1 − 1/2)⁻¹ = h²",
				"real_sums(λn:num. real_pow(h, 2) / &2 * real_pow(&1 / &2, n), real_pow(h, 2))",
				Derive(func(d *Argument) {
					halfSmall := d.Have(
						"1/2 is below 1 in size",
						"|&1 / &2| < &1",
						ByArith())
					value := d.Have(
						"(1 − 1/2)⁻¹ = 2, as 2·(1 − 1/2) = 1, so h²/2·(1 − 1/2)⁻¹ = h²",
						"real_pow(h, 2) / &2 * real_inv(&1 - &1 / &2) = real_pow(h, 2)",
						ByArith(field.InvLeftUnique.Read(real_field.Field).At(
							d.TermAs[Real]("&2"), d.TermAs[Real]("&1 - &1 / &2"))))
					d.Show(
						"the geometric series of 1/2, scaled by h²/2",
						By(
							halfSmall,
							value,
							real_series.Geometric.At(d.TermAs[Real]("&1 / &2")),
							real_series.SumsScale.At(d.TermAs[Fun[Nat, Real]]("λn:num. real_pow(&1 / &2, n)"),
								d.TermAs[Real]("real_inv(&1 - &1 / &2)"), d.TermAs[Real]("real_pow(h, 2) / &2"))))
				}))

			arg.Show(
				"exp(h) − 1 − h is the sum of a series dominated termwise by one summing to h²",
				By(termBound, remainderSeries, dominating, real_series.ComparisonBound))
		}),
})}

// ExpDerivative — exp is its own derivative. The functional equation
// turns the increment at c, less its linear part exp(c)·h, into exp(c)
// times the remainder exp(h) − 1 − h at 0, which the quadratic bound
// makes at most h² in size on the ball |h| < 1; a first-order
// approximation with a quadratic error on a ball is a derivative.
var ExpDerivative = expDerivativeThm{family.Add(registry.ProofEntry{
	Name: "ExpDerivative",
	Key:  "prop_a29adcaf16c976dc",
	Build: family.Theorem("∀c:real. real_derivative_at(real_exp, c, exp(c))",
		func(arg *Argument, c *Expr[Real]) {
			exp := arg.TermAs[Fun[Real, Real]]("real_exp")
			expC := arg.TermAs[Real]("exp(c)")
			bound := arg.Have(
				"for |h| < 1 the increment exp(c + h) − exp(c) is exp(c)·h to within exp(c)·h²",
				"∀h:real. |h| < &1 ⇒ |exp(c + h) - exp(c) - exp(c) * h| ≤ exp(c) * real_pow(h, 2)",
				Derive(func(d *Argument) {
					h := d.FixAs[Real]()
					small := d.Assume()
					remainder := d.TermAs[Real]("exp(h) - &1 - h")
					factored := d.Have(
						"exp(c + h) = exp(c)·exp(h), so the increment less "+
							"exp(c)·h is exp(c) times the remainder exp(h) − 1 − h",
						"exp(c + h) - exp(c) - exp(c) * h = exp(c) * (exp(h) - &1 - h)",
						ByArith(ExpAdd.At(c, h)))
					remainderBound := d.Have(
						"|h| < 1 is within the quadratic bound's reach: the remainder is at most h² in size",
						"|exp(h) - &1 - h| ≤ real_pow(h, 2)",
						ByArith(small, ExpQuadraticBound.At(h)))
					size := d.Have(
						"exp(c) is positive, so it is its own size",
						"|exp(c)| = exp(c)",
						ByArith(ExpPositive.At(c)))
					d.Show(
						"sizes multiply: the increment is exp(c)·|exp(h) − 1 − h| "+
							"≤ exp(c)·h² in size, the positive exp(c) keeping the order",
						factored.Rw(),
						ByArith(size, remainderBound, ExpPositive.At(c), real_sgn_abs.AbsMul.At(expC, remainder)))
				}))
			arg.Show(
				"a first-order approximation with a quadratic error on a ball is a "+
					"derivative: the criterion at L = K = exp(c) on the ball of radius 1",
				By(
					bound,
					real_derivative.DerivativeFromQuadraticRemainder.At(exp, c, expC, expC, arg.TermAs[Real]("&1"))))
		}),
})}

// ExpContinuous — exp is continuous on the whole line: it has a
// derivative at every point (ExpDerivative).
var ExpContinuous = expContinuousThm{family.Add(registry.ProofEntry{
	Name: "ExpContinuous",
	Key:  "prop_3fb4eb3a22837a3d",
	Build: family.Theorem("real_continuous_on(𝕌, real_exp)",
		func(arg *Argument) {
			exp := arg.TermAs[Fun[Real, Real]]("real_exp")
			arg.Show(
				"a function with a derivative at every point of a set is continuous on it",
				By(ExpDerivative, real_derivative.DerivativeContinuousOn.At(exp, exp, arg.TermAs[Set[Real]]("𝕌"))))
		}),
})}

// ExponentialQuadraticContinuous — c·exp(b·(x − m)²) is continuous on
// the line. x − m is, hence its square and b times the square; exp is
// continuous (ExpContinuous), so the composite is, and c times it.
var ExponentialQuadraticContinuous = exponentialQuadraticContinuousThm{family.Add(registry.ProofEntry{
	Name: "ExponentialQuadraticContinuous",
	Key:  "prop_af5c51bc7eee2c99",
	Build: family.Theorem(
		"∀m b c:real. real_continuous_on(𝕌, λx:real. c * exp(b * ((x - m) * (x - m))))",
		func(arg *Argument, m, b, c *Expr[Real]) {
			identity := arg.TermAs[Fun[Real, Real]]("λx:real. x")
			shift := arg.TermAs[Fun[Real, Real]]("λx:real. x - m")
			square := arg.TermAs[Fun[Real, Real]]("λx:real. (x - m) * (x - m)")
			polynomial := arg.TermAs[Fun[Real, Real]]("λx:real. b * ((x - m) * (x - m))")
			exp := arg.TermAs[Fun[Real, Real]]("real_exp")
			line := arg.TermAs[Set[Real]]("𝕌")
			shiftContinuous := arg.Have(
				"the translated identity is continuous",
				"real_continuous_on(𝕌, λx:real. x - m)",
				By(
					real_continuous.ContinuousOnId.At(line),
					real_continuous.ContinuousOnConst.At(m, line),
					real_continuous.ContinuousOnSub.At(identity, arg.TermAs[Fun[Real, Real]]("λx:real. m"), line)))
			squareContinuous := arg.Have(
				"the square of the translated identity is continuous",
				"real_continuous_on(𝕌, λx:real. (x - m) * (x - m))",
				By(shiftContinuous, real_continuous.ContinuousOnMul.At(shift, shift, line)))
			polynomialContinuous := arg.Have(
				"scaling the square preserves continuity",
				"real_continuous_on(𝕌, λx:real. b * ((x - m) * (x - m)))",
				By(
					squareContinuous,
					real_continuous.ContinuousOnConst.At(b, line),
					real_continuous.ContinuousOnMul.At(arg.TermAs[Fun[Real, Real]]("λx:real. b"), square, line)))
			composite := arg.Have(
				"exp is continuous, so the exponential of the quadratic is",
				"real_continuous_on(𝕌, λx:real. exp(b * ((x - m) * (x - m))))",
				By(
					polynomialContinuous,
					ExpContinuous,
					set_basic.InUniv.Inst[Real](),
					real_continuous.ContinuousOnCompose.At(exp, polynomial, line, line),
					functions.ComposeApply.At(exp, polynomial)))
			arg.Show(
				"multiplying the composite by a constant preserves continuity",
				By(
					composite,
					real_continuous.ContinuousOnConst.At(c, line),
					real_continuous.ContinuousOnMul.At(
						arg.TermAs[Fun[Real, Real]]("λx:real. c"),
						arg.TermAs[Fun[Real, Real]]("λx:real. exp(b * ((x - m) * (x - m)))"),
						line)))
		}),
})}

// ExpSurjective — exp takes every positive value. exp is continuous
// (ExpContinuous). A value y ≥ 1 lies between exp(0) = 1 and
// exp(y − 1) ≥ 1 + (y − 1) = y, so the intermediate value theorem on
// ⟦0, y − 1⟧ finds it. A value y below 1 has its reciprocal above 1,
// taken at some x, and then exp(−x) = 1/exp(x) = y.
var ExpSurjective = expSurjectiveThm{family.Add(registry.ProofEntry{
	Name: "ExpSurjective",
	Key:  "prop_28a1227e21a25ef2",
	Build: family.Theorem(Statement{
		Binders: "∀y:real.",
		Hypotheses: []string{
			"&0 < y",
		},
		Conclusion: "∃x:real. exp(x) = y",
	},
		func(arg *Argument, y *Expr[Real], positive Fact) {
			exp := arg.TermAs[Fun[Real, Real]]("real_exp")

			fromOne := arg.Have(
				"exp takes every value from 1 on",
				"∀z:real. &1 ≤ z ⇒ ∃x:real. exp(x) = z",
				Derive(func(d *Argument) {
					z := d.FixAs[Real]()
					above := d.Assume()
					top := d.TermAs[Real]("z - &1")
					interval := d.TermAs[Set[Real]]("⟦&0, z - &1⟧")
					onInterval := d.Have(
						"continuous on the line, exp is continuous on ⟦0, z − 1⟧",
						"real_continuous_on(⟦&0, z - &1⟧, real_exp)",
						By(
							ExpContinuous,
							set_order.SubsetUniv.At(interval),
							real_continuous.ContinuousOnSubset.At(exp, d.TermAs[Set[Real]]("𝕌"), interval)))
					ends := d.Have(
						"z − 1 ≥ 0, and z lies between exp(0) = 1 and exp(z − 1) ≥ 1 + (z − 1) = z",
						"&0 ≤ z - &1 ∧ exp(&0) ≤ z ∧ z ≤ exp(z - &1)",
						ByArith(above, ExpZero, ExpLowerBound.At(top)))
					d.Show(
						"so exp takes the value z on ⟦0, z − 1⟧, by the intermediate value theorem",
						By(onInterval, ends, real_continuous.IntermediateValue.At(exp, d.TermAs[Real]("&0"), top, z)))
				}))

			below := arg.Unless(
				arg.Term("&1 ≤ y"),
				"a value from 1 on is taken, as just proved",
				Given(func(b *Argument, above Fact) {
					b.Show(
						"as just proved",
						By(fromOne, above))
				}))
			reciprocalAbove := arg.Have(
				"0 < y < 1, and inverses reverse the order between positives: 1/y ≥ 1/1 = 1",
				"&1 ≤ real_inv(y)",
				ByArith(
					below,
					positive,
					real_order_field.InvAntitoneWeak.At(y, arg.TermAs[Real]("&1")),
					field.InvOne.Read(real_field.Field)))
			_, value := arg.ObtainAs[Real](
				"so exp takes the value 1/y at some x",
				"∃x:real. exp(x) = real_inv(y)",
				By(fromOne.At(arg.TermAs[Real]("real_inv(y)")), reciprocalAbove))
			arg.Take(arg.TermAs[Real]("-x"))
			arg.Show(
				"and exp(−x) = 1/exp(x) = 1/(1/y) = y",
				Simp(Fwd(ExpNeg)), // ↦ 1/exp(x) = y
				value.Rw(),        // ↦ 1/(1/y) = y
				Cite(field.InvInv.Read(real_field.Field)))
		}),
})}
