// balls.go — the punctured balls the definition speaks of: a point of one,
// and one ball serving two limits.
//
// The definition hands each limit its own punctured ball for each ε. An
// argument that plays two limits against each other needs one ball serving
// both — the ball of the smaller of the two radii — and, to reach a
// contradiction or a comparison, a POINT of that ball: the point halfway
// out along its radius.

package real_function_limits

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/registry"
)

// PuncturedBallPoint — the point halfway out along a radius lies in the
// punctured ball.
//
// The point c + d/2 sits at distance d/2 from c: that distance is
// positive, so the point is not c itself, and it is below d, so the
// point is inside the ball. The distance is read off in two steps —
// c cancels, leaving the half, and the half is nonnegative, so it is
// its own absolute value — and the bounds on the half then bound the
// distance.
var PuncturedBallPoint = puncturedBallPointThm{family.Add(registry.ProofEntry{
	Name: "PuncturedBallPoint",
	Key:  "prop_e4231b875da94341",
	Build: family.Theorem(Statement{
		Binders: "∀c d:real.",
		Hypotheses: []string{
			"&0 < d",
		},
		Conclusion: "&0 < |c + d / &2 - c| ∧ |c + d / &2 - c| < d",
	},
		func(a *Argument, c, d *Expr[Real], pos Fact) {
			zero, two := a.TermAs[Real]("&0"), a.TermAs[Real]("&2")
			half := a.TermAs[Real]("d / &2")

			halfBounds := a.Have(
				"half of d is positive and below d",
				"&0 < d / &2 ∧ d / &2 < d",
				ByArith(pos))
			// The arith closer clears the /2 and is left needing 2·(d/2) = d,
			// the field law it is handed.
			offset := a.Have(
				"the point lies d/2 from c: c cancels, and twice the half is the whole",
				"(c + d / &2) - c = d / &2",
				ByArith(field.DivLeftMul.Read(real_field.Field).At(d, two)))
			absHalf := a.Have(
				"the half is nonnegative, so it is its own absolute value",
				"|d / &2| = d / &2",
				By(
					real_sgn_abs.AbsFixedIffNonneg.At(half),
					real_order_ring.LessEqOfLessThan.At(zero, half),
					halfBounds))

			a.Show(
				"the distance from c is the half, which is positive and below d",
				By(offset, absHalf, halfBounds))
		}),
})}

// LimitAtCommonRadius — two limits at one point share, for every ε, one
// punctured ball on which both functions are within ε of their limits.
//
// Each limit answers ε with a radius of its own. The smaller of the two
// is positive, since both are, and it is at most either, so a point of
// its punctured ball lies in both balls — and there the value of f is
// within ε of l and the value of g within ε of m.
var LimitAtCommonRadius = limitAtCommonRadiusThm{family.Add(registry.ProofEntry{
	Name: "LimitAtCommonRadius",
	Key:  "prop_d43fd520a2bf83a2",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀c l m ε:real.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"g ⟶ m (at c)",
			"&0 < ε",
		},
		Conclusion: "∃δ:real. " +
			"    &0 < δ ∧ (∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - l| < ε ∧ |g(x) - m| < ε)",
	},
		func(a *Argument, f, g *Arrow[Real, Real], c, l, m *Expr[Real], toL, toM Fact) {
			nearL := a.Unfolded(toL, RealLimitAtDef)
			nearM := a.Unfolded(toM, RealLimitAtDef)

			eps := a.FixAs[Real]()
			pos := a.Assume()
			d0, radiusL := a.ObtainAs[Real](
				"f ⟶ l (at c) at ε hands over a radius δ₀ inside which the values of f are within ε of l",
				"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - l| < ε",
				By(nearL.At(eps), pos))
			d1, radiusM := a.ObtainAs[Real](
				"and g ⟶ m (at c) at ε hands over a radius δ₁ inside which the values of g are within ε of m",
				"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |g(x) - m| < ε",
				By(nearM.At(eps), pos))
			withinL := a.Have(
				"on the punctured ball of radius δ₀ the values of f are within ε of l",
				"∀x:real. &0 < |x - c| ∧ |x - c| < δ₀ ⇒ |f(x) - l| < ε",
				By(radiusL))
			withinM := a.Have(
				"on the punctured ball of radius δ₁ the values of g are within ε of m",
				"∀x:real. &0 < |x - c| ∧ |x - c| < δ₁ ⇒ |g(x) - m| < ε",
				By(radiusM))

			a.Take(a.TermAs[Real]("min(δ₀, δ₁)"))
			a.Do(SplitConj(
				Case(
					"the smaller radius is positive, both radii being positive",
					By(real_sup_inf.LessThanMin.At(d0, d1, a.TermAs[Real]("&0")), radiusL, radiusM)),
				Case(
					"and a point of its punctured ball lies in both balls, where both values are within ε",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						ball := b.Assume()
						inBoth := b.Have(
							"a distance below the smaller radius is below δ₀ and below δ₁",
							"|x - c| < δ₀ ∧ |x - c| < δ₁",
							By(real_sup_inf.LessThanMin.At(d0, d1, b.TermAs[Real]("|x - c|")), ball))
						b.Show(
							"so x lies in both balls: |f(x) − l| < ε and |g(x) − m| < ε",
							By(withinL.At(x), withinM.At(x), ball, inBoth))
					})),
			))
		}),
})}
