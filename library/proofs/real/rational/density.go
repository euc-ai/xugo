// density.go — the rationals are dense in ℝ: README.md, movement 2. The integer part and the
// nearest integer first, then a rational between any two reals, then one within any distance of a
// given real.

package rational

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/int_num/int_construction"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_order"
	"github.com/euc-ai/xugo/library/proofs/nat_num/peano"
	"github.com/euc-ai/xugo/library/proofs/real/real_archimedean"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// NonnegIntegerPart — a nonnegative real has a natural integer part.
//
// Some natural lies strictly above x (the Archimedean property), so by
// the well-ordering of ℕ there is a least one, k. It is not 0, since x
// is not below &0; so k = m + 1 for some natural m. Then m < k, and the
// minimality of k says x is not below &m — that is, &m ≤ x — while
// x < &k = &(m + 1) = &m + &1 by the additivity of the embedding.
var NonnegIntegerPart = nonnegIntegerPartThm{family.Add(registry.ProofEntry{
	Name: "NonnegIntegerPart",
	Key:  "prop_e9c76dc20dc8a89c",
	Build: family.Theorem(Statement{
		Binders: "∀x:real.",
		Hypotheses: []string{
			"&0 ≤ x",
		},
		Conclusion: "∃m:num. &m ≤ x ∧ x < &m + &1",
	},
		func(a *Argument, x *Expr[Real], nonneg Fact) {
			zero := a.TermAs[Real]("&0")
			strictlyAbove := a.TermAs[Set[Nat]]("λk:num. x < &k")

			k, least := a.ObtainAs[Nat](
				"the least natural strictly above x",
				"∃k:num. x < &k ∧ (∀m:num. m < k ⇒ ¬(x < &m))",
				By(real_archimedean.ExistsNumStrictlyAbove, nat_order.WellOrdering.At(strictlyAbove)))
			nonzero := a.Have(
				"k is not 0, since x is not below &0",
				"k ≠ 0",
				By(least, nonneg, real_order_ring.NotLessThan.At(x, zero)))
			m, succ := a.ObtainAs[Nat](
				"so k is a successor, k = m + 1",
				"∃m:num. k = m + 1",
				By(nonzero, peano.Cases.At(k), nat_arith.Add1))
			below := a.Have(
				"m lies below k",
				"m < k",
				ByArith(succ))

			a.Take(m)
			a.Show(
				"no natural below k exceeds x, so &m ≤ x; and x < &k = &(m + 1) = &m + &1",
				By(
					Normalized,
					least,
					below,
					succ,
					real_order_ring.NotLessThan.At(x, a.TermAs[Real]("&m")),
					real_construction.OfNumAdd.At(m, a.Ctx().Nat(1)))) // &(m + 1) = &m + &1
		}),
})}

// IntegerPart — every real has an integer part.
//
// Shift x into the nonnegative half by a natural and shift back, with
// no case on the sign of x: a
// natural N above -x makes x + N nonnegative, x + N has a natural
// integer part k, and k − N — a natural minus a natural, so an integer —
// is an integer part of x, both bounds on x + N moving across by N.
var IntegerPart = integerPartThm{family.Add(registry.ProofEntry{
	Name: "IntegerPart",
	Key:  "prop_c3523703ce6afc70",
	Build: family.Theorem("∀x:real. ∃m:real. integer(m) ∧ m ≤ x ∧ x < m + &1",
		func(a *Argument, x *Expr[Real]) {
			nTerm, aboveNegX := a.ObtainAs[Nat](
				"by the Archimedean property, some natural lies above -x",
				"∃N:num. -x < &N",
				By(real_archimedean.ExistsNumStrictlyAbove))
			shifted := a.TermAs[Real]("x + &N")
			nonneg := a.Have(
				"so the shift x + &N is nonnegative",
				"&0 ≤ x + &N",
				ByArith(aboveNegX))
			kTerm, bounds := a.ObtainAs[Nat](
				"the shift has a natural integer part k",
				"∃k:num. &k ≤ x + &N ∧ x + &N < &k + &1",
				By(nonneg, NonnegIntegerPart.At(shifted)))

			embeddedK, embeddedN := a.TermAs[Real]("&k"), a.TermAs[Real]("&N")
			integral := a.Have(
				"&k - &N is &k + -&N, a natural plus the negation of a natural",
				"integer(&k - &N)",
				By(
					Normalized,
					int_construction.IntegerOfNum.At(kTerm),
					int_construction.IntegerOfNum.At(nTerm),
					int_construction.IntegerClosedUnderNeg.At(embeddedN),
					int_construction.IntegerClosedUnderAdd.At(embeddedK, a.TermAs[Real]("-&N")),
					real_ring.RealSubDef.At(embeddedK, embeddedN)))

			a.Take(a.TermAs[Real]("&k - &N"))
			a.Show(
				"subtract &N across &k ≤ x + &N < &k + &1",
				ByArith(integral, bounds))
		}),
})}

// NearestInteger — every real lies within a half of an integer: below x
// lies an integer n with x < n + 1, and x is within a half of n or of
// n + 1.
var NearestInteger = nearestIntegerThm{family.Add(registry.ProofEntry{
	Name: "NearestInteger",
	Key:  "prop_eba7034d072e6cce",
	Build: family.Theorem("∀x:real. ∃m:real. integer(m) ∧ |x - m| ≤ &1 / &2",
		func(a *Argument, x *Expr[Real]) {
			n, part := a.UnpackAs[Real](IntegerPart.At(x), "n")
			a.Cases(a.Term("x - n ≤ &1 / &2"))
			a.When(
				"x is at most a half above n",
				func(b *Argument, near Fact) {
					b.Take(n)
					b.Show(
						"n is an integer within a half of x",
						ByArith(near, part))
				})
			a.Otherwise(
				"x is more than a half above n, so less than a half below n + 1",
				func(b *Argument, far Fact) {
					b.Take(b.TermAs[Real]("n + &1"))
					b.Show(
						"n + 1 is an integer within a half of x",
						ByArith(
							far,
							part,
							int_construction.IntegerClosedUnderAdd.At(n, b.TermAs[Real]("&1")),
							int_construction.IntegerOfNum.At(b.TermAs[Nat]("1"))))
				})
		}),
})}

// RationalBetween — between two reals lies a rational.
//
// The gap y − x is positive, so the Archimedean property gives a natural
// n with n·(y − x) > 1: a step 1/n shorter than the gap. Let m be the
// integer part of x·n. The multiple (m + 1)/n of that step is rational;
// it lies above x because x·n < m + 1, and below y because
// m + 1 ≤ x·n + 1 < x·n + n·(y − x) = y·n — each comparison with a
// quotient read through the positive n.
var RationalBetween = rationalBetweenThm{family.Add(registry.ProofEntry{
	Name: "RationalBetween",
	Key:  "prop_78e98b6d07fd87f",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"x < y",
		},
		Conclusion: "∃r:real. rational(r) ∧ x < r ∧ r < y",
	},
		func(a *Argument, x, y *Expr[Real], below Fact) {
			zero, one := a.TermAs[Real]("&0"), a.TermAs[Real]("&1")
			gap := a.TermAs[Real]("y - x")

			nTerm, stepFits := a.ObtainAs[Nat](
				"the gap y - x is positive, so some multiple of it exceeds &1",
				"∃n:num. &1 < &n * (y - x)",
				By(
					below,
					real_order_ring.SubPos.At(y, x), // &0 < y - x ⇔ x < y
					real_archimedean.Archimedean.At(gap, one))) // &0 < y - x ⇒ ∃n. &1 < &n · (y - x)
			n, embeddedN := nTerm, a.TermAs[Real]("&n")
			nonzero := a.Have(
				"n is not 0, since &0 · (y - x) = &0 is not above &1",
				"n ≠ 0",
				By(
					stepFits,
					real_ring.MulLeftZero.At(gap),               // &0 · (y - x) = &0
					real_order_ring.ZeroLessThanOne,             // &0 < &1
					real_order_ring.LessThanAsym.At(zero, one))) // &0 < &1 ⇒ ¬(&1 < &0)
			positive := a.Have(
				"so &n is positive",
				"&0 < &n",
				By(
					nonzero,
					nat_order.PosIffNonzero.At(n), // n ≠ 0 ⇔ 0 < n
					real_order_ring.OfNumLessThan.At(a.Ctx().Nat(0), n))) // &0 < &n ⇔ 0 < n

			m, bounds := a.ObtainAs[Real](
				"x · &n has an integer part m",
				"∃m:real. integer(m) ∧ m ≤ x * &n ∧ x * &n < m + &1",
				By(IntegerPart.At(a.TermAs[Real]("x * &n"))))
			numerator := a.TermAs[Real]("m + &1")

			a.Take(a.TermAs[Real]("(m + &1) / &n"))
			rationalR := a.Have(
				"m + &1 is rational, an integer plus a natural, and so is its quotient by the natural &n",
				"rational((m + &1) / &n)",
				By(
					bounds,
					IntegerRational.At(m),                 // integer(m) ⇒ rational(m)
					OfNumRational.At(a.Ctx().Nat(1)),      // rational(&1)
					RationalAdd.At(m, one),                // rational(m) ∧ rational(&1) ⇒ rational(m + &1)
					OfNumRational.At(n),                   // rational(&n)
					RationalDiv.At(numerator, embeddedN))) // rational(m + &1) ∧ rational(&n) ⇒ rational((m + &1) / &n)
			aboveX := a.Have(
				"above x, since x · &n < m + &1 and &n is positive",
				"x < (m + &1) / &n",
				By(
					positive,
					bounds,
					// &0 < &n ⇒ (x < (m + &1) / &n ⇔ x · &n < m + &1)
					real_order_field.LessThanDivMulLeft.At(x, numerator, embeddedN)))
			belowY := a.Have(
				"below y, since m + &1 ≤ x · &n + &1 < x · &n + &n · (y - x) = y · &n",
				"(m + &1) / &n < y",
				ByArith(
					positive,
					stepFits,
					bounds,
					// &0 < &n ⇒ ((m + &1) / &n < y ⇔ m + &1 < y · &n)
					real_order_field.LessThanDivMulRight.At(numerator, y, embeddedN)))
			a.Show(
				"a rational strictly between x and y",
				By(rationalR, aboveX, belowY))
		}),
})}

// RationalApproximation — every real is within any positive distance of
// a rational: a rational between x and x + e is closer to x than e.
var RationalApproximation = rationalApproximationThm{family.Add(registry.ProofEntry{
	Name: "RationalApproximation",
	Key:  "prop_7091d42e251d0326",
	Build: family.Theorem(Statement{
		Binders: "∀x e:real.",
		Hypotheses: []string{
			"&0 < e",
		},
		Conclusion: "∃r:real. rational(r) ∧ |r - x| < e",
	},
		func(a *Argument, x, e *Expr[Real], positive Fact) {
			r, between := a.ObtainAs[Real](
				"x < x + e, so a rational r lies between them",
				"∃r:real. rational(r) ∧ x < r ∧ r < x + e",
				By(
					positive,
					RationalBetween.At(x, a.TermAs[Real]("x + e")), // x < x + e ⇒ ∃r. rational(r) ∧ x < r ∧ r < x + e
					real_order_ring.LessThanSelfAddRight.At(x, e))) // x < x + e ⇔ &0 < e

			lower := a.Have(
				"and r lies above x - e, being above x",
				"x - e < r",
				ByArith(between, positive))
			a.Take(r)
			a.Show(
				"so |r - x| < e",
				By(
					between,
					lower,
					positive,
					real_sgn_abs.AbsBetween.At(x, r, e))) // |r - x| < e ⇔ x - e < r ∧ r < x + e ∧ &0 < e
		}),
})}
