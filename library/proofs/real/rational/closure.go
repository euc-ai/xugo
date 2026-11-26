// closure.go — the rationals are a subfield of ℝ containing the
// integers: README.md, movement 1.
//
// Every member here reads a rational hypothesis the way the textbook
// does — "write x = m / n" — as a named step that fixes the numerator and
// the denominator on the page, proved from the hypothesis and the
// definition. The goal `rational(…)` is opened by citing the definition
// too, never by unfolding the constant: an unfold rewrites every
// occurrence at once, the hypotheses among them, and a quotient already
// written down would be taken apart under its name.

package rational

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// IntegerRational — every integer is rational: x is the quotient x / &1.
var IntegerRational = integerRationalThm{family.Add(registry.ProofEntry{
	Name: "IntegerRational",
	Key:  "prop_9c9886649b36fd88",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"integer(x)",
		},
		Conclusion: "rational(x)",
	},
		func(a *Argument, x *Expr[Real], isInteger Fact) {
			zero, one := a.TermAs[Real]("&0"), a.TermAs[Real]("&1")

			a.Do(Simp(Fwd(RationalDef)))
			a.Take(x)
			a.Take(one)
			a.Show(
				"x is an integer, so is &1, &1 is not &0, and x / &1 = x",
				By(
					isInteger,
					int_construction.IntegerOfNum.At(a.Ctx().Nat(1)),  // integer(&1)
					field.DivOne.Read(real_field.Field).At(x),         // x / &1 = x
					real_order_ring.ZeroLessThanOne,                   // &0 < &1
					real_order_ring.NotEqualOfLessThan.At(zero, one))) // &0 < &1 ⇒ &0 ≠ &1
		}),
})}

// OfNumRational — every natural is rational: it is an integer seen in ℝ.
var OfNumRational = ofNumRationalThm{family.Add(registry.ProofEntry{
	Name: "OfNumRational",
	Key:  "prop_5ffc6921808897d6",
	Build: family.Theorem("∀n:num. rational(&n)",
		func(a *Argument, n *Expr[Nat]) {
			a.Show(
				"&n is an integer, so it is rational",
				By(
					IntegerRational.At(a.TermAs[Real]("&n")), // integer(&n) ⇒ rational(&n)
					int_construction.IntegerOfNum.At(n)))     // integer(&n)
		}),
})}

// RationalNeg — the negation of a rational is rational: -(m / n) is
// (-m) / n, the sign passing into the numerator once the quotient is
// read as m · n⁻¹.
var RationalNeg = rationalNegThm{family.Add(registry.ProofEntry{
	Name: "RationalNeg",
	Key:  "prop_b0a84176b295e57b",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"rational(x)",
		},
		Conclusion: "rational(-x)",
	},
		func(a *Argument, x *Expr[Real], xRational Fact) {
			m, n, xQuotient := a.Obtain2As[Real, Real](
				"write x = m / n",
				"∃m n:real. integer(m) ∧ integer(n) ∧ n ≠ &0 ∧ x = m / n",
				By(xRational, RationalDef.At(x)))
			negM := a.TermAs[Real]("-m")

			a.Do(Simp(Fwd(RationalDef)))
			a.Take(negM)
			a.Take(n)
			a.Show(
				"-x is -m / n: -m is an integer, and the sign moves from the quotient into its numerator",
				By(
					Normalized,
					xQuotient,
					int_construction.IntegerClosedUnderNeg.At(m),               // integer(m) ⇒ integer(-m)
					real_field.RealDivDef.At(m, n),                             // m / n = m · n⁻¹
					real_field.RealDivDef.At(negM, n),                          // -m / n = -m · n⁻¹
					real_ring.MulLeftNeg.At(m, a.TermAs[Real]("real_inv(n)")))) // -m · n⁻¹ = -(m · n⁻¹)
		}),
})}

// RationalAdd — the sum of two rationals is rational: m₁/n₁ + m₂/n₂ is
// (m₁n₂ + m₂n₁)/(n₁n₂), which cross-multiplied is a ring identity.
var RationalAdd = rationalAddThm{family.Add(registry.ProofEntry{
	Name: "RationalAdd",
	Key:  "prop_e32a5841db43aac2",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"rational(x)",
			"rational(y)",
		},
		Conclusion: "rational(x + y)",
	},
		func(a *Argument, x, y *Expr[Real], bothRational Fact) {
			m1, n1, xQuotient := a.Obtain2As[Real, Real](
				"write x = m₁ / n₁",
				"∃m₁ n₁:real. integer(m₁) ∧ integer(n₁) ∧ n₁ ≠ &0 ∧ x = m₁ / n₁",
				By(bothRational, RationalDef.At(x)))
			m2, n2, yQuotient := a.Obtain2As[Real, Real](
				"and y = m₂ / n₂",
				"∃m₂ n₂:real. integer(m₂) ∧ integer(n₂) ∧ n₂ ≠ &0 ∧ y = m₂ / n₂",
				By(bothRational, RationalDef.At(y)))
			numerator := a.TermAs[Real]("m₁ * n₂ + m₂ * n₁")
			denominator := a.TermAs[Real]("n₁ * n₂")

			a.Do(Simp(Fwd(RationalDef)))
			a.Take(numerator)
			a.Take(denominator)

			numeratorInteger := a.Have(
				"the numerator is an integer: a sum of two products of integers",
				"integer(m₁ * n₂ + m₂ * n₁)",
				By(
					xQuotient,
					yQuotient,
					int_construction.IntegerClosedUnderAdd.At(a.TermAs[Real]("m₁ * n₂"), a.TermAs[Real]("m₂ * n₁")),
					int_construction.IntegerClosedUnderMul.At(m1, n2),
					int_construction.IntegerClosedUnderMul.At(m2, n1)))
			denominatorInteger := a.Have(
				"the denominator is an integer: a product of integers",
				"integer(n₁ * n₂)",
				By(xQuotient, yQuotient, int_construction.IntegerClosedUnderMul.At(n1, n2)))
			denominatorNonzero := a.Have(
				"the denominator is nonzero: a product of nonzero reals",
				"n₁ * n₂ ≠ &0",
				By(xQuotient, yQuotient, real_ring.MulEqZero.At(n1, n2))) // n₁ · n₂ = &0 ⇔ n₁ = &0 ∨ n₂ = &0

			identity := a.Have(
				"x + y is the quotient (m₁n₂ + m₂n₁)/(n₁n₂): clear the denominators, cross-multiply, divide back",
				"x + y = (m₁ * n₂ + m₂ * n₁) / (n₁ * n₂)",
				Derive(func(b *Argument) {
					m1Cleared := b.Have(
						"clear n₁ from x = m₁ / n₁",
						"m₁ = x * n₁",
						By(
							Normalized,
							xQuotient,
							field.DivRightMul.Read(real_field.Field).At(m1, n1))) // n₁ ≠ &0 ⇒ m₁ / n₁ · n₁ = m₁
					m2Cleared := b.Have(
						"clear n₂ from y = m₂ / n₂",
						"m₂ = y * n₂",
						By(
							Normalized,
							yQuotient,
							field.DivRightMul.Read(real_field.Field).At(m2, n2))) // n₂ ≠ &0 ⇒ m₂ / n₂ · n₂ = m₂
					crossMultiplied := b.Have(
						"cross-multiplied, with m₁ = x·n₁ and m₂ = y·n₂ substituted, the claim is a ring identity",
						"(x + y) * (n₁ * n₂) = m₁ * n₂ + m₂ * n₁",
						m1Cleared.Rw(),
						m2Cleared.Rw(),
						ByArith())
					quotient := b.TermAs[Real]("(m₁ * n₂ + m₂ * n₁) / (n₁ * n₂)")
					b.Show(
						"divide back by n₁·n₂, which is nonzero",
						By(
							crossMultiplied,
							denominatorNonzero,
							// the quotient times n₁n₂ is the numerator
							field.DivRightMul.Read(real_field.Field).At(numerator, denominator),
							// a nonzero right factor cancels
							real_ring.MulRightCancel.At(b.TermAs[Real]("x + y"), quotient, denominator)))
				}))

			a.Show(
				"the four clauses of the definition are in hand",
				By(numeratorInteger, denominatorInteger, denominatorNonzero, identity))
		}),
})}

// RationalSub — a difference of rationals is rational: x - y is the sum
// x + -y, and both summands are rational.
var RationalSub = rationalSubThm{family.Add(registry.ProofEntry{
	Name: "RationalSub",
	Key:  "prop_f2e1c0999575012c",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"rational(x)",
			"rational(y)",
		},
		Conclusion: "rational(x - y)",
	},
		func(a *Argument, x, y *Expr[Real], bothRational Fact) {
			negY := a.TermAs[Real]("-y")

			a.Show(
				"x - y is x + -y, a sum of the rational x and the rational -y",
				By(
					Normalized,
					bothRational,
					RationalAdd.At(x, negY),        // rational(x) ∧ rational(-y) ⇒ rational(x + -y)
					RationalNeg.At(y),              // rational(y) ⇒ rational(-y)
					real_ring.RealSubDef.At(x, y))) // x - y = x + -y
		}),
})}

// RationalMul — the product of two rationals is rational: (m₁/n₁)(m₂/n₂)
// is (m₁m₂)/(n₁n₂), the inverse of a product being the product of the
// inverses.
var RationalMul = rationalMulThm{family.Add(registry.ProofEntry{
	Name: "RationalMul",
	Key:  "prop_9037a2de31a83fa8",
	Build: family.Sections(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"rational(x)",
			"rational(y)",
		},
		Conclusion: "rational(x * y)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// Quotients multiply numerator by numerator and denominator by
			// denominator: with the divisions opened, the inverse of a
			// product is the product of the inverses, and the rest is a
			// ring identity.
			quotientsMultiply := ctx.Lemma("∀m₁ n₁ m₂ n₂:real. m₁ / n₁ * (m₂ / n₂) = (m₁ * m₂) / (n₁ * n₂)",
				func(a *Argument, m1, n1, m2, n2 *Expr[Real]) {
					a.Do(
						Unfold(real_field.RealDivDef),
						Simp(Fwd(field.InvMul.Read(real_field.Field))), // real_inv(n₁ · n₂) = n₁⁻¹ · n₂⁻¹
						ByArith(),
					)
				})

			return ctx.Theorem(headline, func(a *Argument, x, y *Expr[Real], bothRational Fact) {
				m1, n1, xQuotient := a.Obtain2As[Real, Real](
					"write x = m₁ / n₁",
					"∃m₁ n₁:real. integer(m₁) ∧ integer(n₁) ∧ n₁ ≠ &0 ∧ x = m₁ / n₁",
					By(bothRational, RationalDef.At(x)))
				m2, n2, yQuotient := a.Obtain2As[Real, Real](
					"and y = m₂ / n₂",
					"∃m₂ n₂:real. integer(m₂) ∧ integer(n₂) ∧ n₂ ≠ &0 ∧ y = m₂ / n₂",
					By(bothRational, RationalDef.At(y)))

				a.Do(Simp(Fwd(RationalDef)))
				a.Take(a.TermAs[Real]("m₁ * m₂"))
				a.Take(a.TermAs[Real]("n₁ * n₂"))

				numeratorInteger := a.Have(
					"the numerator m₁m₂ is a product of integers",
					"integer(m₁ * m₂)",
					By(xQuotient, yQuotient, int_construction.IntegerClosedUnderMul.At(m1, m2)))
				denominatorInteger := a.Have(
					"so is the denominator n₁n₂",
					"integer(n₁ * n₂)",
					By(xQuotient, yQuotient, int_construction.IntegerClosedUnderMul.At(n1, n2)))
				denominatorNonzero := a.Have(
					"and n₁n₂ is nonzero, since neither factor is and ℝ has no zero divisors",
					"n₁ * n₂ ≠ &0",
					By(xQuotient, yQuotient, real_ring.MulEqZero.At(n1, n2))) // n₁ · n₂ = &0 ⇔ n₁ = &0 ∨ n₂ = &0

				a.Show(
					"with x = m₁ / n₁ and y = m₂ / n₂, the product of the quotients is the quotient of the products",
					By(
						Normalized,
						numeratorInteger,
						denominatorInteger,
						denominatorNonzero,
						xQuotient,
						yQuotient,
						At(quotientsMultiply, m1, n1, m2, n2)))
			})
		}),
})}

// RationalInv — the inverse of a rational is rational: zero inverts to
// zero, and otherwise the inverse of m / n is n / m.
var RationalInv = rationalInvThm{family.Add(registry.ProofEntry{
	Name: "RationalInv",
	Key:  "prop_8729dc89b2c82419",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"rational(x)",
		},
		Conclusion: "rational(real_inv(x))",
	},
		func(a *Argument, x *Expr[Real], xRational Fact) {
			xNonzero := a.Unless(
				a.Term("x = &0"),
				"x is zero: its inverse is zero, the natural 0 seen in ℝ, which is rational",
				Given(func(b *Argument, xZero Fact) {
					b.Show(
						"real_inv(&0) = &0, and &0 is rational",
						By(Normalized, xZero, real_construction.InvZero, OfNumRational.At(b.Ctx().Nat(0))))
				}))

			m, n, xQuotient := a.Obtain2As[Real, Real](
				"write x = m / n",
				"∃m n:real. integer(m) ∧ integer(n) ∧ n ≠ &0 ∧ x = m / n",
				By(xRational, RationalDef.At(x)))

			mNonzero := a.Have(
				"m is nonzero: were m = &0, x = m / n = &0 · n⁻¹ would be &0 too",
				"m ≠ &0",
				By(
					Normalized,
					xNonzero,
					xQuotient,
					real_field.RealDivDef.At(m, n), // m / n = m · n⁻¹
					real_ring.MulLeftZero.At(a.TermAs[Real]("real_inv(n)")))) // &0 · n⁻¹ = &0

			a.Do(Simp(Fwd(RationalDef)))
			a.Take(n)
			a.Take(m)
			a.Show(
				"x⁻¹ = n / m: n and m are integers, m is nonzero, and inverting m / n swaps the two",
				By(
					Normalized,
					xQuotient,
					mNonzero,
					field.InvDiv.Read(real_field.Field).At(m, n))) // real_inv(m / n) = n / m
		}),
})}

// RationalDiv — a quotient of rationals is rational: x / y is the
// product x · y⁻¹, and both factors are rational.
var RationalDiv = rationalDivThm{family.Add(registry.ProofEntry{
	Name: "RationalDiv",
	Key:  "prop_2fe9f03f6cc07118",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"rational(x)",
			"rational(y)",
		},
		Conclusion: "rational(x / y)",
	},
		func(a *Argument, x, y *Expr[Real], bothRational Fact) {
			invY := a.TermAs[Real]("real_inv(y)")

			a.Show(
				"x / y is x · y⁻¹, a product of the rational x and the rational y⁻¹",
				By(
					Normalized,
					bothRational,
					RationalMul.At(x, invY),         // rational(x) ∧ rational(y⁻¹) ⇒ rational(x · y⁻¹)
					RationalInv.At(y),               // rational(y) ⇒ rational(y⁻¹)
					real_field.RealDivDef.At(x, y))) // x / y = x · y⁻¹
		}),
})}
