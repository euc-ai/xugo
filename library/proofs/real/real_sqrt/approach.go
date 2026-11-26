// approach.go — the two approximation lemmas the existence theorem
// stands on: below a target y a value whose square is under y is never
// the largest such, and above it one whose square is over y is never
// the smallest. Together they say the set of reals squaring below y has
// no greatest element and its complement no least, which is exactly the
// gap the completeness of ℝ fills to give the root — the content
// `SquareRootExists` (existence.go) rests on.

package real_sqrt

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// ApproachFromBelow — a real whose square is under y is not the largest
// such: some strictly larger real still squares to less than y. The
// witness is z = |x| + min(&1, e) with e = (y − x²)/(2|x| + 2); it lies
// strictly above x because |x| ≥ x and the increment is positive, and
// it squares below y because the increment w = min(&1, e) contributes
// only w·(2|x| + w), which the clip w ≤ &1 and the bound w ≤ e keep
// under e·(2|x| + 2) = y − x², so z² = x² + w·(2|x| + w) < y.
//
// The denominator 2|x| + 2 rather than 2|x| is what makes the estimate
// unconditional: it is positive whatever x is, so e is a genuine
// positive slack, and clipping it at &1 keeps w small enough that the
// quadratic term never overshoots.
var ApproachFromBelow = approachFromBelowThm{family.Add(registry.ProofEntry{
	Name: "ApproachFromBelow",
	Key:  "prop_606f69d84472482f",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"real_pow(x, 2) < y",
		},
		Conclusion: "∃z:real. x < z ∧ real_pow(z, 2) < y",
	}, func(a *Argument, x, y Term, below Fact) {
		ctx := a.Ctx()

		absX := a.Term("|x|")
		x2 := a.Term("real_pow(x, 2)")
		numer := a.Term("y - real_pow(x, 2)") // the slack y − x²
		denom := a.Term("&2 * |x| + &2")      // the increment's denominator
		zero, one := a.Term("&0"), a.Term("&1")

		// The slack y − x² and the denominator 2|x| + 2 are both
		// positive, so the increment e below is a positive real.
		denomPos := a.Have(
			"the denominator 2|x| + 2 is positive",
			"&0 < &2 * |x| + &2",
			ByArith(At(real_sgn_abs.AbsNonneg, x)))
		numerPos := a.Have(
			"the slack y − x² is positive",
			"&0 < y - real_pow(x, 2)",
			By(below, At(real_order_ring.SubPos, y, x2)))

		// e := (y − x²)/(2|x| + 2). It is positive, and rescaling it by
		// the denominator recovers the slack.
		_, eDef := a.Obtain(
			"let e be the increment (y − x²)/(2|x| + 2)",
			"∃e:real. e = (y - real_pow(x, 2)) / (&2 * |x| + &2)",
			Basic())
		ePos := a.Have(
			"e is positive, a positive over a positive",
			"&0 < e₀",
			By(Normalized, eDef, numerPos, denomPos, At(real_order_field.DivPos, numer, denom)))
		eScaled := a.Have(
			"e rescaled by the denominator is the slack",
			"e₀ * (&2 * |x| + &2) = y - real_pow(x, 2)",
			By(eDef, denomPos, At(real_order_field.EqDivMulLeft, a.Term("e₀"), numer, denom)))

		// w := min(&1, e). Positive, at most &1, and at most e — the clip
		// that keeps the quadratic term from overshooting.
		_, wDef := a.Obtain(
			"let w be min(&1, e)",
			"∃w:real. w = min(&1, e₀)",
			Basic())
		wPos := a.Have(
			"w is positive, being the smaller of two positives",
			"&0 < w₀",
			By(wDef, ePos, At(real_sup_inf.MinIsArgument, one, a.Term("e₀")), real_order_ring.ZeroLessThanOne))
		wBounds := a.Have(
			"w is at most &1 and at most e",
			"w₀ ≤ &1 ∧ w₀ ≤ e₀",
			By(Normalized, wDef, At(real_sup_inf.MinLowerBound, one, a.Term("e₀"))))

		// The witness z := |x| + w.
		a.Take(a.Term("|x| + w₀"))

		// x < |x| + w = z, since x ≤ |x| and w is positive.
		xBelow := a.Have(
			"x is strictly below the witness |x| + w",
			"x < |x| + w₀",
			ByArith(wPos, At(real_sgn_abs.AbsDominates, x)))

		// z² = x² + w·(2|x| + w). Expand the square over |x| and w, do
		// the same to the increment, then regroup so the leading term
		// stands alone as x² = |x|².
		double := a.Have(
			"twice |x| is |x| + |x|",
			"&2 * |x| = |x| + |x|",
			ByArith())
		sqExpand := a.Have(
			"the square of |x| + w, term by term",
			"real_pow(|x| + w₀, 2) = |x| * |x| + w₀ * |x| + (w₀ * |x| + w₀ * w₀)",
			By(
				At(real_pow.PowTwo, a.Term("|x| + w₀")),
				At(real_ring.RightDistrib, absX, a.Term("w₀"), a.Term("|x| + w₀")),
				At(real_construction.LeftDistrib, absX, absX, a.Term("w₀")),
				At(real_construction.LeftDistrib, a.Term("w₀"), absX, a.Term("w₀")),
				At(real_construction.MulSym, absX, a.Term("w₀"))))
		incExpand := a.Have(
			"the increment w·(2|x| + w), term by term",
			"w₀ * (&2 * |x| + w₀) = w₀ * |x| + w₀ * |x| + w₀ * w₀",
			By(
				double,
				At(real_construction.LeftDistrib, a.Term("w₀"), a.Term("|x| + |x|"), a.Term("w₀")),
				At(real_construction.LeftDistrib, a.Term("w₀"), absX, absX)))
		regroup := a.Have(
			"the four terms regroup so the leading square stands alone",
			"|x| * |x| + w₀ * |x| + (w₀ * |x| + w₀ * w₀) = |x| * |x| + (w₀ * |x| + w₀ * |x| + w₀ * w₀)",
			ACRegroupWith(real_construction.AddAC(ctx)))
		binom := a.Have(
			"so z² = x² + w·(2|x| + w), the leading square being x² = |x|²",
			"real_pow(|x| + w₀, 2) = real_pow(x, 2) + w₀ * (&2 * |x| + w₀)",
			By(sqExpand, incExpand, regroup, At(real_pow.SquareOfAbs, x), At(real_pow.PowTwo, absX)))

		// The increment stays below the slack: w·(2|x| + w) < w·(2|x| + 2)
		// ≤ e·(2|x| + 2) = y − x².
		incLess := a.Have(
			"2|x| + w < 2|x| + 2, since w ≤ &1 < &2",
			"&2 * |x| + w₀ < &2 * |x| + &2",
			ByArith(wBounds))
		mulLess := a.Have(
			"scaling by the positive w keeps the strict order",
			"w₀ * (&2 * |x| + w₀) < w₀ * (&2 * |x| + &2)",
			By(
				wPos,
				incLess,
				At(real_order_ring.LessThanMulLeft, a.Term("w₀"), a.Term("&2 * |x| + w₀"), denom)))
		mulLeq := a.Have(
			"and w ≤ e scales the larger factor up to e·(2|x| + 2)",
			"w₀ * (&2 * |x| + &2) ≤ e₀ * (&2 * |x| + &2)",
			By(
				wBounds,
				denomPos,
				At(real_order_ring.LessEqMulRight, a.Term("w₀"), a.Term("e₀"), denom),
				At(real_order_ring.LessEqOfLessThan, zero, denom)))
		gap := a.Have(
			"so the increment is below the slack y − x²",
			"w₀ * (&2 * |x| + w₀) < y - real_pow(x, 2)",
			By(
				mulLess,
				mulLeq,
				eScaled,
				At(real_order_ring.LessThanLessEqTrans,
					a.Term("w₀ * (&2 * |x| + w₀)"),
					a.Term("w₀ * (&2 * |x| + &2)"),
					a.Term("e₀ * (&2 * |x| + &2)"))))
		sqLess := a.Have(
			"hence z² = x² + increment < x² + (y − x²) = y",
			"real_pow(|x| + w₀, 2) < y",
			By(
				binom,
				gap,
				At(real_order_ring.LessThanAddLeftImp, x2, a.Term("w₀ * (&2 * |x| + w₀)"), numer),
				At(real_ring.SubAddLeft, y, x2)))

		a.Show(
			"z = |x| + w is strictly above x and still squares below y",
			By(xBelow, sqLess))
	}),
})}

// ApproachFromAbove — below a positive x whose square exceeds y there is
// a positive real whose square still exceeds y: x − w for w the smaller
// of x/2 and (x² − y)/(2x). The first candidate keeps x − w positive,
// the second keeps the cross term 2·w·x within x² − y, and then
// (x − w)² = x² − 2·w·x + w² exceeds y by at least w².
var ApproachFromAbove = approachFromAboveThm{family.Add(registry.ProofEntry{
	Name: "ApproachFromAbove",
	Key:  "prop_5f41312133a8e427",
	Build: family.Theorem(Statement{
		Binders: "∀x y:real.",
		Hypotheses: []string{
			"&0 < x",
			"y < real_pow(x, 2)",
		},
		Conclusion: "∃z:real. z < x ∧ &0 < z ∧ y < real_pow(z, 2)",
	},
		func(a *Argument, x, y Term, h Fact) {
			two, twoX := a.Term("&2"), a.Term("&2 * x")
			half, gap := a.Term("x / &2"), a.Term("real_pow(x, 2) - y")
			quotient := a.Term("(real_pow(x, 2) - y) / (&2 * x)")

			// Step down from x by w, the smaller of x/2 and (x² − y)/(2x).
			a.Take(a.Term("x - min(x / &2, (real_pow(x, 2) - y) / (&2 * x))"))
			wDef := a.Denote("w", a.Term("min(x / &2, (real_pow(x, 2) - y) / (&2 * x))"))
			w := a.Term("w")

			// Both candidates are positive, so w is.
			halfPos := a.Have(
				"x/2 is positive",
				"&0 < x / &2",
				By(h, At(real_order_field.DivPos, x, two)))
			quotientPos := a.Have(
				"(x² − y)/(2x) is positive, numerator and denominator both being so",
				"&0 < (real_pow(x, 2) - y) / (&2 * x)",
				ByArith(h, At(real_order_field.DivPos, gap, twoX)))
			wPos := a.Have(
				"w is one of the two, hence positive",
				"&0 < w",
				ByArith(wDef, halfPos, quotientPos, At(real_sup_inf.MinIsArgument, half, quotient)))

			// w ≤ x/2 is what keeps x − w positive.
			wBelowHalf := a.Have(
				"w is at most x/2, that is 2w ≤ x",
				"w * &2 ≤ x",
				ByArith(
					wDef,
					At(real_sup_inf.MinLowerBound, half, quotient),
					At(real_order_field.LessEqDivMulLeft, w, x, two)))

			// w ≤ (x² − y)/(2x) is what keeps the cross term within x² − y.
			twoXPos := a.Have(
				"2x is positive",
				"&0 < &2 * x",
				ByArith(h))
			crossTermBound := a.Have(
				"w is at most (x² − y)/(2x), so 2·w·x ≤ x² − y",
				"&2 * (w * x) ≤ real_pow(x, 2) - y",
				By(
					wDef,
					twoXPos,
					At(real_sup_inf.MinLowerBound, half, quotient),
					At(real_order_field.LessEqDivMulLeft, w, gap, twoX),
					At(real_ring.MulAC, two, w, x)))

			// The square of x − w: distribute twice, and the two cross
			// terms are one product.
			expansion := a.Have(
				"(x − w)² = x² − 2·w·x + w²",
				"real_pow(x - w, 2) = real_pow(x, 2) - &2 * (w * x) + real_pow(w, 2)",
				Simp(Fwd(real_pow.PowTwo), Fwd(real_ring.SubRightDistrib), Fwd(real_ring.SubLeftDistrib)),
				ByArith(At(real_construction.MulSym, x, w)))
			wSquarePos := a.Have(
				"w² is positive",
				"&0 < real_pow(w, 2)",
				By(Normalized, wPos, At(real_order_ring.MulPos, w, w), At(real_pow.PowTwo, w)))

			// Naming w put the spine in ⊥-form — the conclusion is negated
			// among the hypotheses — so the close is a refutation with the
			// supposition among its premises. The arithmetic is linear over
			// the one product left, w·x.
			supposition := a.Hyp("¬(x - w < x ∧ &0 < x - w ∧ y < real_pow(x - w, 2))")
			a.Show(
				"x − w is below x as w > 0, positive as 2w ≤ x, and (x − w)² = x² − 2·w·x + w² ≥ y + w² > y",
				ByArith(supposition, wPos, wBelowHalf, crossTermBound, expansion, wSquarePos))
		}),
})}
