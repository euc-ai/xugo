// existence.go — a positive real has a square root: the completeness of
// ℝ at work.
//
// The candidates are the nonnegative reals whose square is at most y.
// There is one (&0) and they are bounded (by y + &1), so completeness
// hands them a least upper bound s, and s² can be neither below y nor
// above it. Below: some larger real still squares to less than y, and it
// is a candidate — above the cap. Above: s is positive, so some smaller
// positive real still squares to more than y; every candidate is at most
// that real (a larger one would out-square it), so the least cap is at
// most it — below the smaller real. Hence s² = y.
//
// The two approximation facts the argument turns on — a real whose
// square is under y is not the largest such, a positive real whose
// square is over y is not the smallest such — are lemmas of independent
// value, proved as members of their own (approach.go); the theorem
// cites them where the argument needs them.

package real_sqrt

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_completeness"
	"github.com/euc-ai/xugo/library/registry"
)

// SquareRootExists — every positive real is a square. The root is the
// least upper bound of the nonnegative reals whose square is at most y:
// a square below y or above it would contradict that bound being the
// least one, through the two approximation lemmas ApproachFromBelow
// and ApproachFromAbove.
var SquareRootExists = squareRootExistsThm{family.Add(registry.ProofEntry{
	Name: "SquareRootExists",
	Key:  "prop_38a015dc238c5155",
	Build: family.Theorem(Statement{
		Binders: "∀y:real.",
		Hypotheses: []string{
			"&0 < y",
		},
		Conclusion: "∃r:real. real_pow(r, 2) = y",
	}, func(a *Argument, y Term, pos Fact) {
		zero, one, two := a.Term("&0"), a.Term("&1"), a.Term("2")

		// The candidates are the nonnegative reals whose square is at
		// most y; completeness hands them a least upper bound s once one
		// of them and a cap on all of them are exhibited.
		s, leastUpperBound := a.Obtain(
			"by completeness the candidates have a least upper bound s",
			"∃s:real. "+
				"    (∀x:real. &0 ≤ x ∧ real_pow(x, 2) ≤ y ⇒ x ≤ s) ∧ "+
				"    (∀b:real. (∀x:real. &0 ≤ x ∧ real_pow(x, 2) ≤ y ⇒ x ≤ b) ⇒ s ≤ b)",
			Derive(func(a *Argument) {
				nonempty := a.Have(
					"&0 is a candidate, its square being &0 and y positive",
					"∃x:real. &0 ≤ x ∧ real_pow(x, 2) ≤ y",
					Derive(func(a *Argument) {
						a.Take(zero)
						a.Show(
							"&0 ≤ &0, and &0² = &0·&0 = &0 ≤ y",
							ByArith(pos, At(real_pow.PowTwo, zero)))
					}))
				bounded := a.Have(
					"y + &1 caps the candidates",
					"∃M:real. ∀x:real. &0 ≤ x ∧ real_pow(x, 2) ≤ y ⇒ x ≤ M",
					Derive(func(a *Argument) {
						a.Take(a.Term("y + &1"))
						x := a.Fix()
						candidate := a.Assume()
						growth := a.Have(
							"above &1 a real is at most its square: x = x·&1 ≤ x·x",
							"&1 ≤ x ⇒ x ≤ real_pow(x, 2)",
							By(
								Normalized,
								candidate,
								At(real_order_ring.LessEqMulLeft, x, one, x),
								At(real_ring.MulRightId, x),
								At(real_pow.PowTwo, x)))
						a.Show(
							"either x ≤ &1 < y + &1, or &1 ≤ x and then x ≤ x² ≤ y < y + &1",
							ByArith(growth, candidate, pos))
					}))
				a.Show(
					"completeness, at the candidate predicate",
					By(
						nonempty,
						bounded,
						At(real_completeness.RealComplete, a.Term("λx:real. &0 ≤ x ∧ real_pow(x, 2) ≤ y"))))
			}))
		lub := a.Conjuncts(
			leastUpperBound,
			"s caps every candidate",
			"and s is at most every cap")
		sNonneg := a.Have(
			"s is nonnegative, capping the candidate &0",
			"&0 ≤ s",
			ByArith(lub[0].At(zero), pos, At(real_pow.PowTwo, zero)))

		// The root is s: its square is neither below y nor above it.
		a.Take(s)
		squareNotBelow := a.Unless(
			a.Term("real_pow(s, 2) < y"),
			"s² < y is impossible: a larger real still squaring below y is a candidate above the cap",
			Given(func(a *Argument, squareBelow Fact) {
				z, zAboveS := a.Obtain(
					"some z > s still has z² < y",
					"∃z:real. s < z ∧ real_pow(z, 2) < y",
					By(At(ApproachFromBelow, s, y), squareBelow))
				a.Show(
					"z is a candidate, &0 ≤ s < z, so z ≤ s — against s < z",
					ByArith(lub[0].At(z), zAboveS, sNonneg))
			}))
		squareNotAbove := a.Unless(
			a.Term("y < real_pow(s, 2)"),
			"y < s² is impossible: a smaller positive real still squaring above y caps the candidates below s",
			Given(func(a *Argument, squareAbove Fact) {
				// s is positive: at s ≤ &0 — that is, s = &0 — its square
				// would be &0, not above the positive y.
				squareVanishes := a.Have(
					"were s ≤ &0, its square would be at most &0² = &0",
					"s ≤ &0 ⇒ real_pow(s, 2) ≤ &0",
					By(
						Normalized,
						sNonneg,
						At(real_pow.PowMonoBase, s, zero, two),
						At(real_pow.PowTwo, zero),
						At(real_ring.MulLeftZero, zero)))
				sPos := a.Have(
					"so s is positive, its square lying above the positive y",
					"&0 < s",
					ByArith(sNonneg, squareAbove, pos, squareVanishes))
				z, zBelowS := a.Obtain(
					"some positive z < s still has y < z²",
					"∃z:real. z < s ∧ &0 < z ∧ y < real_pow(z, 2)",
					By(At(ApproachFromAbove, s, y), sPos, squareAbove))
				zCaps := a.Have(
					"z caps every candidate: a candidate above z would out-square z, hence y",
					"∀x:real. &0 ≤ x ∧ real_pow(x, 2) ≤ y ⇒ x ≤ z",
					Derive(func(a *Argument) {
						x := a.Fix()
						candidate := a.Assume()
						zBelowX := a.Assuming(
							a.Term("z < x"),
							"otherwise x ≤ z outright",
							Given(func(a *Argument, xNotAboveZ Fact) {
								a.Show(
									"¬(z < x) is x ≤ z",
									ByArith(xNotAboveZ))
							}))
						squares := a.Have(
							"&0 < z < x gives z·z < x·x, that is z² < x²",
							"real_pow(z, 2) < real_pow(x, 2)",
							By(
								Normalized,
								zBelowS,
								zBelowX,
								At(real_order_ring.LessEqOfLessThan, zero, z),
								At(real_order_ring.LessThanMul2, z, x, z, x),
								At(real_pow.PowTwo, z),
								At(real_pow.PowTwo, x)))
						a.Show(
							"but x² ≤ y < z² < x²",
							ByArith(squares, candidate, zBelowS))
					}))
				sAtMostZ := a.Have(
					"so the least cap s is at most z",
					"s ≤ z",
					By(lub[1].At(z), zCaps))
				a.Show(
					"against z < s",
					ByArith(sAtMostZ, zBelowS))
			}))
		a.Show(
			"s² is neither below y nor above it, so s² = y",
			ByArith(squareNotBelow, squareNotAbove))
	}),
})}
