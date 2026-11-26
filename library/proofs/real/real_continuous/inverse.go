// inverse.go — the inverse of a strictly increasing function is
// continuous: order alone, with no continuity of the function inverted,
// pins the values of its inverse.

package real_continuous

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/registry"
)

// MonotoneInverseContinuous — a local right inverse of a strictly
// increasing function is continuous: when f is strictly increasing on s,
// g carries every y near c into s with f(g(y)) = y, and s holds a ball
// about g(c), then g is continuous at c. Nothing is asked of f beyond
// its order.
//
// Given ε, let r be half the smaller of ε and d, so that g(c) − r and
// g(c) + r lie in s, and f puts c = f(g(c)) strictly between their
// values. Inside the smallest of e and the two gaps c − f(g(c) − r) and
// f(g(c) + r) − c, a point y has g(y) in s with f(g(y)) = y strictly
// between those values; a strictly increasing f reflects the strict
// order, so g(y) lies strictly between g(c) − r and g(c) + r, within
// r < ε of g(c).
var MonotoneInverseContinuous = monotoneInverseContinuousThm{family.Add(registry.ProofEntry{
	Name: "MonotoneInverseContinuous",
	Key:  "prop_5ee069ce2187ca00",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀s:set(real). ∀c e d:real.",
		Hypotheses: []string{
			"real_strictly_increasing_on(s, f)",
			"&0 < e",
			"∀y:real. |y - c| < e ⇒ g(y) ∈ s ∧ f(g(y)) = y",
			"&0 < d",
			"∀x:real. |x - g(c)| < d ⇒ x ∈ s",
		},
		Conclusion: "real_continuous_at(g, c)",
	},
		func(a *Argument, f, g *Arrow[Real, Real], s *Expr[Set[Real]], c, e, d *Expr[Real],
			strictlyIncreasing, ePos, inverse, dPos, ball Fact) {
			increasing := a.Unfolded(strictlyIncreasing, RealStrictlyIncreasingOnDef)
			reflects := a.Have(
				"a strictly increasing f reflects the strict order between points of s",
				"∀p q:real. p ∈ s ∧ q ∈ s ∧ f(p) < f(q) ⇒ p < q",
				Derive(func(b *Argument) {
					p := b.FixAs[Real]("p")
					q := b.FixAs[Real]("q")
					below := b.Assume()
					b.Cases(b.Term("p = q"))
					b.When(
						"p = q would make f(p) < f(q) the impossible f(q) < f(q)",
						func(b *Argument, same Fact) {
							b.Show(
								"so p = q is ruled out",
								By(same, below, real_order_ring.LessThanIrrefl.At(f.Apply(q))))
						})
					b.Otherwise(
						"and q < p would give f(q) < f(p) instead",
						func(b *Argument, apart Fact) {
							b.Show(
								"so p < q",
								ByArith(apart, below, increasing.At(q, p)))
						})
				}))

			a.Do(Unfold(RealContinuousAtDef))
			eps := a.FixAs[Real]()
			pos := a.Assume()
			centre := a.Have(
				"g undoes f at c itself: g(c) lies in s and f(g(c)) = c",
				"g(c) ∈ s ∧ f(g(c)) = c",
				ByArith(inverse.At(c), ePos))
			_, rDef := a.LetAs[Real]("r", "min(ε, d) / &2")
			radius := a.Have(
				"r is positive and below both ε and d",
				"&0 < r ∧ r < ε ∧ r < d",
				ByArith(
					rDef,
					dPos,
					pos,
					real_sup_inf.LessThanMin.At(eps, d, a.TermAs[Real]("&0")),
					real_sup_inf.MinLowerBound.At(eps, d)))
			gc := g.Apply(c)
			lo := a.TermAs[Real]("g(c) - r")
			hi := a.TermAs[Real]("g(c) + r")
			ends := a.Have(
				"g(c) − r and g(c) + r lie within d of g(c), so in s",
				"g(c) - r ∈ s ∧ g(c) + r ∈ s",
				ByArith(ball.At(lo), ball.At(hi), radius))
			straddle := a.Have(
				"f, strictly increasing, puts c = f(g(c)) strictly between f(g(c) − r) and f(g(c) + r)",
				"f(g(c) - r) < c ∧ c < f(g(c) + r)",
				ByArith(increasing.At(lo, gc), increasing.At(gc, hi), centre, ends, radius))

			a.Take(a.TermAs[Real]("min(e, min(c - f(g(c) - r), f(g(c) + r) - c))"))
			a.Do(SplitConj(
				Case(
					"the radius is positive, a minimum of positive terms: e is, and so are both gaps",
					Simp(Fwd(real_sup_inf.LessThanMin)),
					ByArith(ePos, straddle)),
				Case(
					"and inside it g stays within ε of g(c)",
					Derive(func(b *Argument) {
						y := b.FixAs[Real]("y")
						near := b.Simplified(b.Assume(), Fwd(real_sup_inf.LessThanMin))
						inside := b.Have(
							"y lies within e of c, and within both gaps of c, so strictly between f(g(c) − r) and f(g(c) + r)",
							"|y - c| < e ∧ f(g(c) - r) < y ∧ y < f(g(c) + r)",
							ByArith(near))
						preimage := b.Have(
							"so g(y) lies in s, and f(g(y)) = y",
							"g(y) ∈ s ∧ f(g(y)) = y",
							By(inverse.At(y), inside))
						gy := g.Apply(y)
						b.Show(
							"f reflects the order, so g(y) lies strictly between g(c) − r and g(c) + r, within r < ε of g(c)",
							ByArith(reflects.At(lo, gy), reflects.At(gy, hi), preimage, ends, inside, radius))
					})),
			))
		}),
})}
