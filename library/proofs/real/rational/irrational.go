// irrational.go — a prime has no rational square root: README.md,
// movement 3. √2 is the first instance, and shifting a
// rational by √2 puts an irrational in every interval.

package rational

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_prime"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sqrt"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// PrimeNotRationalSquare — no rational squares to a prime.
//
// Write x = m / n and clear the denominator: m² = x²·n² = p·n². The
// integers m and n have natural absolute values a and b, and a square
// forgets the sign of its root, so the equation is a·a = p·(b·b) seen in
// ℝ, hence in ℕ, where `nat_prime.SquareEqPrimeTimesSquare` leaves b = 0.
// Then n = 0, which a denominator is not.
var PrimeNotRationalSquare = primeNotRationalSquareThm{family.Add(registry.ProofEntry{
	Name: "PrimeNotRationalSquare",
	Key:  "prop_7ca9a0fac9d4ca9b",
	Build: family.Sections(Statement{
		Binders: "∀p:num. ∀x:real.",
		Hypotheses: []string{
			"nat_prime(p)",
			"rational(x)",
		},
		Conclusion: "real_pow(x, 2) ≠ &p",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// A square forgets the sign of its root: y·y = |y|·|y|, so a real
			// whose absolute value is the natural k squares to the natural k·k.
			squareForgetsSign := ctx.Lemma(Statement{
				Binders: "∀y:real. ∀k:num.",
				Hypotheses: []string{
					"|y| = &k",
				},
				Conclusion: "y * y = &(k * k)",
			},
				func(a *Argument, y *Expr[Real], k *Expr[Nat], absY Fact) {
					a.Show(
						"y·y = y² = |y|² = &k·&k = &(k·k)",
						By(
							absY,
							real_pow.PowTwo.At(y),      // y² = y · y
							real_pow.SquareOfAbs.At(y), // y² = |y|²
							real_pow.PowTwo.At(a.TermAs[Real]("|y|")), // |y|² = |y| · |y|
							real_construction.OfNumMul.At(k, k)))      // &(k · k) = &k · &k
				})

			// The receiver is `arg` because the argument names the naturals a and b.
			return ctx.Theorem(headline,
				func(arg *Argument, p *Expr[Nat], x *Expr[Real], primeAndRational Fact) {
					squaresToP := arg.SupposeNot() // suppose x² = &p

					m, n, xQuotient := arg.Obtain2As[Real, Real](
						"write x = m / n",
						"∃m n:real. integer(m) ∧ integer(n) ∧ n ≠ &0 ∧ x = m / n",
						By(primeAndRational, RationalDef.At(x)))

					cleared := arg.Have(
						"clear the denominator",
						"m = x * n",
						By(
							Normalized,
							xQuotient,
							field.DivRightMul.Read(real_field.Field).At(m, n))) // n ≠ &0 ⇒ m / n · n = m
					squared := arg.Have(
						"square both sides",
						"m * m = x * x * (n * n)",
						cleared.Rw(),
						ByArith())
					realSide := arg.Have(
						"and x·x is p",
						"m * m = &p * (n * n)",
						By(Normalized, squaresToP, squared, real_pow.PowTwo.At(x))) // x² = x · x

					a, absM := arg.ObtainAs[Nat](
						"m is an integer, so its absolute value is a natural a",
						"∃a:num. |m| = &a",
						Unfold(int_construction.IntegerDef))
					b, absN := arg.ObtainAs[Nat](
						"and that of n is a natural b",
						"∃b:num. |n| = &b",
						Unfold(int_construction.IntegerDef))

					embedded := arg.Have(
						"the two squares are the naturals a·a and b·b seen in ℝ, and the embedding is multiplicative",
						"&(a * a) = &(p * (b * b))",
						By(
							Normalized,
							realSide,
							absM,
							absN,
							At(squareForgetsSign, m, a), // |m| = &a ⇒ m · m = &(a · a)
							At(squareForgetsSign, n, b), // |n| = &b ⇒ n · n = &(b · b)
							real_construction.OfNumMul.At(p, arg.TermAs[Nat]("b * b")))) // &(p · (b · b)) = &p · &(b · b)
					naturalSolution := arg.Have(
						"the embedding is injective, so the equation holds in ℕ",
						"a * a = p * (b * b)",
						By(
							embedded,
							// &u = &v ⇔ u = v
							real_construction.OfNumEq.At(arg.TermAs[Nat]("a * a"), arg.TermAs[Nat]("p * (b * b)"))))
					bZero := arg.Have(
						"the descent in ℕ leaves b = 0, p being prime",
						"b = 0",
						By(
							primeAndRational,
							naturalSolution,
							nat_prime.SquareEqPrimeTimesSquare.At(p, a, b))) // nat_prime(p) ∧ a·a = p·(b·b) ⇒ a = 0 ∧ b = 0

					arg.Show(
						"then |n| = &0, so n = &0 — but n is a nonzero denominator",
						By(bZero, absN, xQuotient, real_sgn_abs.AbsVanishes.At(n))) // |n| = &0 ⇔ n = &0
				})
		}),
})}

// SqrtPrimeIrrational — the square root of a prime is irrational: √p
// squares to p, and no rational does.
var SqrtPrimeIrrational = sqrtPrimeIrrationalThm{family.Add(registry.ProofEntry{
	Name: "SqrtPrimeIrrational",
	Key:  "prop_57c8bbbeaa014a5a",
	Build: family.Theorem(Statement{
		Binders: "∀p:num.",
		Hypotheses: []string{
			"nat_prime(p)",
		},
		Conclusion: "¬rational(real_sqrt(&p))",
	},
		func(a *Argument, p *Expr[Nat], prime Fact) {
			embedded := a.TermAs[Real]("&p")
			root := a.TermAs[Real]("real_sqrt(&p)")

			a.Show(
				"(√p)² = p, since &p is nonnegative; a rational √p would be a rational squaring to the prime p",
				By(
					prime,
					PrimeNotRationalSquare.At(p, root), // nat_prime(p) ∧ rational(√p) ⇒ (√p)² ≠ &p
					real_sqrt.SqrtPowTwo.At(embedded),  // &0 ≤ &p ⇒ (√p)² = &p
					real_order_ring.NumNonneg.At(p)))   // &0 ≤ &p
		}),
})}

// IrrationalBetween — between two reals lies an irrational: shift the
// gap by √2, take a rational r inside the shifted gap, and shift back.
// r + √2 is irrational, since otherwise √2 = (r + √2) - r would be a
// difference of rationals.
var IrrationalBetween = irrationalBetweenThm{family.Add(registry.ProofEntry{
	Name: "IrrationalBetween",
	Key:  "prop_d91fc8cf6e670e75",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"x < y",
		},
		Conclusion: "∃z:real. ¬rational(z) ∧ x < z ∧ z < y",
	},
		func(a *Argument, x, y *Expr[Real], below Fact) {
			lowShifted, highShifted := a.TermAs[Real]("x - real_sqrt(&2)"), a.TermAs[Real]("y - real_sqrt(&2)")

			shifted := a.Have(
				"shifting both ends by √2 keeps them in order",
				"x - real_sqrt(&2) < y - real_sqrt(&2)",
				ByArith(below))
			r, between := a.ObtainAs[Real](
				"so a rational r lies between the shifted ends",
				"∃r:real. rational(r) ∧ x - real_sqrt(&2) < r ∧ r < y - real_sqrt(&2)",
				By(shifted, RationalBetween.At(lowShifted, highShifted)))
			z := a.TermAs[Real]("r + real_sqrt(&2)")

			shiftBack := a.Have(
				"shifting back recovers √2",
				"r + real_sqrt(&2) - r = real_sqrt(&2)",
				ByArith())
			irrational := a.Have(
				"r + √2 is irrational: were it rational, √2 = (r + √2) - r would be a difference of rationals",
				"¬rational(r + real_sqrt(&2))",
				By(
					between,
					shiftBack,
					SqrtPrimeIrrational.At(a.Ctx().Nat(2)), // nat_prime(2) ⇒ ¬rational(√2)
					nat_prime.PrimeTwo,                     // nat_prime(2)
					RationalSub.At(z, r)))                  // rational(r + √2) ∧ rational(r) ⇒ rational((r + √2) - r)
			bounds := a.Have(
				"and it lies between x and y",
				"x < r + real_sqrt(&2) ∧ r + real_sqrt(&2) < y",
				ByArith(between))

			a.Take(z)
			a.Show(
				"an irrational strictly between x and y",
				By(irrational, bounds))
		}),
})}
