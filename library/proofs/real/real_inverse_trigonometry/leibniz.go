// leibniz.go — Leibniz's series for π: π/4 = 1 − 1/3 + 1/5 − ….

package real_inverse_trigonometry

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/iterate/real/real_sum"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_series"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// LeibnizPartialDerivative — the partial sums of the arctangent series
// differentiate to the geometric sums in −x²: the term
// (−1)^k t^(2k+1)/(2k+1) is the constant (−1)^k/(2k+1) times t^(2k+1), so
// its derivative is (−1)^k x^(2k) = (−x²)^k, and a finite sum is
// differentiated term by term.
var LeibnizPartialDerivative = leibnizPartialDerivativeThm{family.Add(registry.ProofEntry{
	Name: "LeibnizPartialDerivative",
	Key:  "prop_5ead92ad3b606575",
	Build: family.Theorem(Statement{
		Binders: "∀n:num. ∀x:real.",
		Conclusion: "real_derivative_at( " +
			"    λt:real. Σ_{k∈0 .. n} real_pow(-&1, k) * real_pow(t, 2 * k + 1) / &(2 * k + 1), " +
			"    x, " +
			"    Σ_{k∈0 .. n} real_pow(-real_pow(x, 2), k))",
		Abbrev: Abbrev{
			{Name: "term", Text: "λk:num. λt:real. real_pow(-&1, k) * real_pow(t, 2 * k + 1) / &(2 * k + 1)"},
		},
	},
		func(arg *Argument, n *Expr[Nat], x *Expr[Real]) {
			term := arg.Have(
				"each term (−1)^k t^(2k+1)/(2k+1) has derivative (−x²)^k at x",
				"∀k:num. real_derivative_at(«term»(k), x, real_pow(-real_pow(x, 2), k))",
				Derive(func(b *Argument) {
					k := b.FixAs[Nat]()
					square := b.TermAs[Real]("real_pow(x, 2)")
					sign := b.Have(
						"(−1)^k x^(2k) = (−1)^k (x²)^k = (−x²)^k",
						"real_pow(-&1, k) * real_pow(x, 2 * k) = real_pow(-real_pow(x, 2), k)",
						By(
							real_pow.PowPow.At(x, b.TermAs[Nat]("2"), k),
							real_pow.MulPowDistrib.At(b.TermAs[Real]("-&1"), square, k),
							real_ring.NegMinusOne.At(square)))
					constant := b.Have(
						"the term is t^(2k+1) times the constant (−1)^k/(2k+1)",
						"«term»(k) = (λt:real. real_pow(-&1, k) / &(2 * k + 1) * real_pow(t, 2 * k + 1))",
						Funext(),
						ByArith())
					scaled := b.Have(
						"t^(2k+1) has derivative (2k+1)·x^(2k), and the constant factor stays",
						"real_derivative_at(λt:real. real_pow(-&1, k) / &(2 * k + 1) * real_pow(t, 2 * k + 1), "+
							"    x, "+
							"    real_pow(-&1, k) / &(2 * k + 1) * (&(2 * k + 1) * real_pow(x, 2 * k)))",
						By(
							real_derivative.DerivativePowSuc.At(b.TermAs[Nat]("2 * k"), x),
							real_derivative.DerivativeScale.At(
								b.TermAs[Fun[Real, Real]]("λt:real. real_pow(t, 2 * k + 1)"),
								x,
								b.TermAs[Real]("&(2 * k + 1) * real_pow(x, 2 * k)"),
								b.TermAs[Real]("real_pow(-&1, k) / &(2 * k + 1)"))))
					positive := b.Have(
						"2k + 1 is positive",
						"&0 < &(2 * k + 1)",
						ByArith())
					value := b.Have(
						"the factor 2k + 1 cancels, leaving (−1)^k x^(2k) = (−x²)^k",
						"real_pow(-&1, k) / &(2 * k + 1) * (&(2 * k + 1) * real_pow(x, 2 * k)) = "+
							"real_pow(-real_pow(x, 2), k)",
						ByArith(sign, positive))
					b.Show(
						"so the term has derivative (−x²)^k",
						By(constant, value, scaled))
				}))
			arg.Show(
				"a finite sum is differentiated term by term",
				By(
					term,
					real_derivative.DerivativeSum.At(
						arg.TermAs[Fun2[Nat, Real, Real]]("«term»"),
						arg.TermAs[Fun[Nat, Real]]("λk:num. real_pow(-real_pow(x, 2), k)"),
						n,
						x)))
		}),
})}

// LeibnizRemainderBound — the n-th partial sum of Leibniz's series is
// within 1/(2n + 3) of π/4. Write P(t) for Σ_{k ≤ n} (−1)^k t^(2k+1)/(2k+1)
// and R(t) = arctan t − P(t). R has derivative
// R'(t) = 1/(1 + t²) − Σ_{k ≤ n} (−t²)^k, which is (−t²)^(n+1)/(1 + t²) by
// the geometric sum, so at most t^(2n+2) in size: the derivative of
// G(t) = t^(2n+3)/(2n+3). So R changes on ⟦0, 1⟧ by no more than G does,
// |R(1) − R(0)| ≤ G(1) − G(0) = 1/(2n + 3), and R(0) = arctan 0 − 0 = 0,
// R(1) = π/4 − Σ_{k ≤ n} (−1)^k/(2k+1).
var LeibnizRemainderBound = leibnizRemainderBoundThm{family.Add(registry.ProofEntry{
	Name: "LeibnizRemainderBound",
	Key:  "prop_2e3da21ef08fdca7",
	Build: family.Theorem(Statement{
		Binders:    "∀n:num.",
		Conclusion: "|pi / &4 - Σ_{k∈0 .. n} real_pow(-&1, k) / &(2 * k + 1)| ≤ real_inv(&(2 * n + 3))",
		Abbrev: Abbrev{
			{Name: "P", Text: "λt:real. Σ_{k∈0 .. n} real_pow(-&1, k) * real_pow(t, 2 * k + 1) / &(2 * k + 1)"},
			{Name: "R", Text: "λt:real. arctan(t) - «P»(t)"},
			{Name: "R'", Text: "λt:real. " +
				"    real_inv(&1 + real_pow(t, 2)) - Σ_{k∈0 .. n} real_pow(-real_pow(t, 2), k)"},
			{Name: "G", Text: "λt:real. real_inv(&(2 * n + 3)) * real_pow(t, 2 * n + 3)"},
		},
	},
		func(arg *Argument, n *Expr[Nat]) {
			zero, one := arg.TermAs[Real]("&0"), arg.TermAs[Real]("&1")
			slope := arg.Have(
				"R has derivative 1/(1 + t²) − Σ_{k ≤ n} (−t²)^k: the arctangent's, less its partial sum's",
				"∀t:real. real_derivative_at(«R», t, «R'»(t))",
				Derive(func(b *Argument) {
					t := b.FixAs[Real]()
					b.Show(
						"the difference rule",
						By(
							ArctanDerivative.At(t),
							At(LeibnizPartialDerivative, n, t),
							real_derivative.DerivativeSub.At(
								b.TermAs[Fun[Real, Real]]("real_arctan"),
								b.TermAs[Fun[Real, Real]]("«P»"),
								t,
								b.TermAs[Real]("real_inv(&1 + real_pow(t, 2))"),
								b.TermAs[Real]("Σ_{k∈0 .. n} real_pow(-real_pow(t, 2), k)"))))
				}))
			exponent := arg.Have(
				"2n + 3 is the successor of 2n + 2",
				"2 * n + 2 + 1 = 2 * n + 3",
				ByArith())
			positive := arg.Have(
				"2n + 3 is positive",
				"&0 < &(2 * n + 3)",
				ByArith())
			majorantSlope := arg.Have(
				"G has derivative t^(2n+2), by the power rule scaled by 1/(2n + 3)",
				"∀t:real. real_derivative_at(«G», t, real_pow(t, 2 * n + 2))",
				Derive(func(b *Argument) {
					t := b.FixAs[Real]()
					value := b.Have(
						"the factor 2n + 3 cancels",
						"real_inv(&(2 * n + 3)) * (&(2 * n + 3) * real_pow(t, 2 * n + 2)) = real_pow(t, 2 * n + 2)",
						ByArith(positive))
					b.Show(
						"t^(2n+3) has derivative (2n + 3)·t^(2n+2)",
						By(
							exponent,
							value,
							real_derivative.DerivativePowSuc.At(b.TermAs[Nat]("2 * n + 2"), t),
							real_derivative.DerivativeScale.At(
								b.TermAs[Fun[Real, Real]]("λs:real. real_pow(s, 2 * n + 3)"),
								t,
								b.TermAs[Real]("&(2 * n + 3) * real_pow(t, 2 * n + 2)"),
								b.TermAs[Real]("real_inv(&(2 * n + 3))"))))
				}))
			bound := arg.Have(
				"and |R'(t)| ≤ t^(2n+2) = G'(t) at every t",
				"∀t:real. |«R'»(t)| ≤ real_pow(t, 2 * n + 2)",
				Derive(func(b *Argument) {
					t := b.FixAs[Real]()
					negSquare := b.TermAs[Real]("-real_pow(t, 2)")
					next := b.TermAs[Nat]("n + 1")
					difference := b.TermAs[Real]("«R'»(t)")
					shifted := b.Have(
						"2(n + 1) = 2n + 2",
						"2 * (n + 1) = 2 * n + 2",
						ByArith())
					size := b.Have(
						"|(−t²)^(n+1)| = (t²)^(n+1) = t^(2n+2)",
						"|real_pow(-real_pow(t, 2), n + 1)| = real_pow(t, 2 * n + 2)",
						ByArith(
							real_pow.AbsPow.At(negSquare, next),
							real_pow.PowPow.At(t, b.TermAs[Nat]("2"), next),
							shifted))
					times := b.Have(
						"(1 + t²)·Σ_{k ≤ n} (−t²)^k = 1 − (−t²)^(n+1), so the difference times 1 + t² is (−t²)^(n+1)",
						"«R'»(t) * (&1 + real_pow(t, 2)) = real_pow(-real_pow(t, 2), n + 1)",
						ByArith(
							real_series.GeometricPartialSum.At(negSquare, n),
							real_construction.MulLeftInverse.At(b.TermAs[Real]("&1 + real_pow(t, 2)"))))
					sizes := b.Have(
						"taking sizes, |difference|·|1 + t²| = t^(2n+2)",
						"|«R'»(t)| * |&1 + real_pow(t, 2)| = real_pow(t, 2 * n + 2)",
						By(times, size, real_sgn_abs.AbsMul.At(difference, b.TermAs[Real]("&1 + real_pow(t, 2)"))))
					atLeastOne := b.Have(
						"1 + t² is at least 1",
						"&1 ≤ |&1 + real_pow(t, 2)|",
						ByArith())
					b.Show(
						"so the difference is at most t^(2n+2) in size",
						ByArith(sizes, atLeastOne, real_sgn_abs.AbsNonneg.At(difference)))
				}))
			interval := arg.TermAs[Set[Real]]("⟦&0, &1⟧")
			remainder := arg.TermAs[Fun[Real, Real]]("«R»")
			remainderSlope := arg.TermAs[Fun[Real, Real]]("«R'»")
			majorant := arg.TermAs[Fun[Real, Real]]("«G»")
			majorantSlopeFn := arg.TermAs[Fun[Real, Real]]("λt:real. real_pow(t, 2 * n + 2)")
			comparison := arg.Have(
				"|R'| ≤ G' on ⟦0, 1⟧, so R changes there by no more than G does: |R(1) − R(0)| ≤ G(1) − G(0)",
				"|«R»(&1) - «R»(&0)| ≤ «G»(&1) - «G»(&0)",
				By(
					bound,
					majorantSlope,
					slope,
					real_order_ring.ZeroLessEqOne,
					real_derivative.DerivativeContinuousOn.At(remainder, remainderSlope, interval),
					real_derivative.DerivativeContinuousOn.At(majorant, majorantSlopeFn, interval),
					real_derivative.MeanValueComparison.At(
						remainder, remainderSlope, majorant, majorantSlopeFn, zero, one)))
			atOne := arg.Have(
				"at t = 1 every power of 1 is 1, so P(1) = Σ_{k ≤ n} (−1)^k/(2k+1)",
				"«P»(&1) = Σ_{k∈0 .. n} real_pow(-&1, k) / &(2 * k + 1)",
				Simp(Fwd(real_pow.OnePow), Fwd(real_ring.MulRightId)),
				Refl())
			vanishing := arg.Have(
				"at t = 0 every term (−1)^k·0^(2k+1)/(2k+1) is 0",
				"∀k:num. real_pow(-&1, k) * real_pow(&0, 2 * k + 1) / &(2 * k + 1) = &0",
				Derive(func(b *Argument) {
					b.FixAs[Nat]()
					b.Show(
						"0^(2k+1) = 0·0^(2k)",
						ByArith(real_pow.PowAddOne.At(zero, b.TermAs[Nat]("2 * k"))))
				}))
			atZero := arg.Have(
				"so P(0) = 0",
				"«P»(&0) = &0",
				By(
					vanishing,
					real_sum.IntervalEqZero.At(
						arg.TermAs[Nat]("0"),
						n,
						arg.TermAs[Fun[Nat, Real]]("λk:num. real_pow(-&1, k) * real_pow(&0, 2 * k + 1) / &(2 * k + 1)"))))
			threeAndUp := arg.TermAs[Nat]("2 * n + 3")
			arg.Show(
				"arctan 1 = π/4 and arctan 0 = 0, while 1^(2n+3) = 1 and 0^(2n+3) = 0",
				ByArith(
					comparison,
					atOne,
					atZero,
					ArctanOne,
					ArctanZero,
					real_pow.OnePow.At(threeAndUp),
					real_pow.ZeroPow.At(threeAndUp)))
		}),
})}

// LeibnizPi — Leibniz's series: 1 − 1/3 + 1/5 − 1/7 + … = π/4. The n-th
// partial sum is within 1/(2n + 3) of π/4, and 1/(2n + 3) < 1/(n + 1), so
// each partial sum is within 1/(n + 1) of π/4, and a sequence that close
// to a number tends to it.
var LeibnizPi = leibnizPiThm{family.Add(registry.ProofEntry{
	Name: "LeibnizPi",
	Key:  "prop_a49b6db49b82e3a9",
	Build: family.Theorem("real_sums(λn:num. real_pow(-&1, n) / &(2 * n + 1), pi / &4)",
		func(arg *Argument) {
			near := arg.Have(
				"the n-th partial sum is within 1/(2n + 3) < 1/(n + 1) of π/4",
				"∀n:num. |Σ_{k∈0 .. n} real_pow(-&1, k) / &(2 * k + 1) - pi / &4| < real_inv(&n + &1)",
				Derive(func(b *Argument) {
					n := b.FixAs[Nat]()
					b.Show(
						"0 < n + 1 < 2n + 3, so 1/(2n + 3) < 1/(n + 1)",
						ByArith(
							At(LeibnizRemainderBound, n),
							real_order_field.InvAntitone.At(b.TermAs[Real]("&n + &1"), b.TermAs[Real]("&(2 * n + 3)"))))
				}))
			arg.Show(
				"so the partial sums tend to π/4",
				Unfold(real_series.RealSumsDef),
				By(
					near,
					real_sequences.WithinReciprocalConverges.At(
						arg.TermAs[Fun[Nat, Real]]("λn:num. Σ_{k∈0 .. n} real_pow(-&1, k) / &(2 * k + 1)"),
						arg.TermAs[Real]("pi / &4"))))
		}),
})}
