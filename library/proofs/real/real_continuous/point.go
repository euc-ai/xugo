// point.go — continuity at a point and on a set: the ε-δ definitions
// read against the limit of real_function_limits, and against each
// other.

package real_continuous

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_function_limits"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// ---------------------------------------------------------------------------
// Continuity at a point
// ---------------------------------------------------------------------------

// ContinuousAtIffLimit — a real function is continuous at c exactly when
// it tends to its value f(c) at c.
//
// The two definitions differ only at the point c itself: the limit asks
// nothing there, its ball being punctured, while continuity asks
// |f(c) − f(c)| < ε, which every positive ε grants. So the same radius
// answers the same ε both ways. Continuity's radius serves the limit,
// the punctured ball lying inside the ball. The limit's radius serves
// continuity once the centre is added back: at x = c the values are at
// distance 0, and any other point of the ball is at a positive distance
// from c, so inside the punctured ball.
var ContinuousAtIffLimit = continuousAtIffLimitThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtIffLimit",
	Key:  "prop_4b319976b7db5980",
	Build: family.Theorem("∀f:(real → real). ∀c:real. real_continuous_at(f, c) ⇔ f ⟶ f(c) (at c)",
		func(a *Argument, f *Arrow[Real, Real], c *Expr[Real]) {
			a.Iff()

			a.Forward(
				"continuity's radius serves the limit: the punctured ball lies inside the ball",
				func(b *Argument, continuous Fact) {
					near := b.Unfolded(continuous, RealContinuousAtDef)
					b.Do(Unfold(real_function_limits.RealLimitAtDef))
					eps := b.FixAs[Real]()
					pos := b.Assume()
					d0, radius := b.ObtainAs[Real](
						"continuity at ε hands over a radius δ₀ inside which the values of f are within ε of f(c)",
						"∃δ:real. &0 < δ ∧ ∀x:real. |x - c| < δ ⇒ |f(x) - f(c)| < ε",
						By(near.At(eps), pos))
					within := b.Have(
						"on the ball of radius δ₀ the values of f are within ε of f(c)",
						"∀x:real. |x - c| < δ₀ ⇒ |f(x) - f(c)| < ε",
						By(radius))
					b.Take(d0)
					b.Do(SplitConj(
						Case(
							"the radius δ₀ is positive, as it was obtained",
							By(radius)),
						Case(
							"and a point of the punctured ball lies in the ball, where the value of f is within ε of f(c)",
							Derive(func(d *Argument) {
								x := d.FixAs[Real]()
								punctured := d.Assume()
								d.Show(
									"the punctured ball's second condition puts x within δ₀ of c, so f(x) is within ε of f(c)",
									By(within.At(x), punctured))
							})),
					))
				})

			a.Backward(
				"the limit's radius serves continuity once the centre is added back",
				func(b *Argument, limit Fact) {
					near := b.Unfolded(limit, real_function_limits.RealLimitAtDef)
					b.Do(Unfold(RealContinuousAtDef))
					eps := b.FixAs[Real]()
					pos := b.Assume()
					d0, radius := b.ObtainAs[Real](
						"f ⟶ f(c) (at c) at ε hands over a radius δ₀ inside "+
							"which, off c, the values of f are within ε of f(c)",
						"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - f(c)| < ε",
						By(near.At(eps), pos))
					within := b.Have(
						"on the punctured ball of radius δ₀ the values of f are within ε of f(c)",
						"∀x:real. &0 < |x - c| ∧ |x - c| < δ₀ ⇒ |f(x) - f(c)| < ε",
						By(radius))
					b.Take(d0)
					b.Do(SplitConj(
						Case(
							"the radius δ₀ is positive, as it was obtained",
							By(radius)),
						Case(
							"and at every point of the ball the value of f is within ε of f(c)",
							Derive(func(d *Argument) {
								x := d.FixAs[Real]()
								ball := d.Assume()
								d.Cases(d.Term("x = c"))
								d.When(
									"at the centre the value is f(c) itself, at distance 0 from f(c)",
									func(e *Argument, atCentre Fact) {
										e.Show(
											"|f(c) − f(c)| = 0 < ε",
											atCentre.Rw(),
											ByArith(pos))
									})
								d.Otherwise(
									"off the centre the point lies in the punctured ball",
									func(e *Argument, offCentre Fact) {
										punctured := e.Have(
											"x ≠ c puts x at a positive distance from c",
											"&0 < |x - c|",
											ByArith(offCentre))
										e.Show(
											"so f(x) is within ε of f(c)",
											By(within.At(x), punctured, ball))
									})
							})),
					))
				})
		}),
})}

// ContinuousAtSequential — a function continuous at c carries every
// sequence tending to c to a sequence tending to f(c).
//
// Fix ε > 0. Continuity at c answers ε with a radius δ₀, inside which the
// values of f are within ε of f(c); the sequence limit, asked for δ₀ as
// its ε, answers with an index N₀ past which the terms are within δ₀ of
// c. Past N₀, f carries each term within ε of f(c). No term need avoid c:
// continuity, unlike the limit, asks nothing of the centre.
var ContinuousAtSequential = continuousAtSequentialThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtSequential",
	Key:  "prop_5dd30f5d0ef8fb7b",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀a:(num → real). ∀c:real.",
		Hypotheses: []string{
			"real_continuous_at(f, c)",
			"a ⟶ c",
		},
		Conclusion: "f ∘ a ⟶ f(c)",
	},
		func(arg *Argument, f *Arrow[Real, Real], a *Arrow[Nat, Real], c *Expr[Real], given Fact) {
			parts := arg.Conjuncts(
				given,
				"f is continuous at c",
				"a ⟶ c")
			near := arg.Unfolded(parts[0], RealContinuousAtDef)
			approach := arg.Unfolded(parts[1], real_sequences.RealConvergesToDef)

			// The goal read as its ε-N statement, and `o` unfolded so that the
			// terms of f ∘ a are the values f(a(n)).
			arg.Do(Unfold(real_sequences.RealConvergesToDef), Unfold(functions.ComposeApply))
			eps := arg.FixAs[Real]()
			pos := arg.Assume()
			d0, radius := arg.ObtainAs[Real](
				"continuity at c answers ε with a radius δ₀ inside which the values of f are within ε of f(c)",
				"∃δ:real. &0 < δ ∧ ∀x:real. |x - c| < δ ⇒ |f(x) - f(c)| < ε",
				By(near.At(eps), pos))
			held := arg.Conjuncts(
				radius,
				"δ₀ is positive",
				"inside δ₀ the values of f are within ε of f(c)")
			N0, tail := arg.ObtainAs[Nat](
				"a ⟶ c, asked for the positive radius δ₀ as its ε, hands "+
					"over an index N₀ past which the terms are within δ₀ of c",
				"∃N:num. ∀n:num. N ≤ n ⇒ |a(n) - c| < δ₀",
				By(approach.At(d0), held[0]))

			arg.Take(N0)
			n := arg.FixAs[Nat]()
			past := arg.Assume()
			arg.Show(
				"past N₀ the term a(n) lies within δ₀ of c, so f carries it within ε of f(c)",
				By(held[1].At(a.Apply(n)), tail.At(n), past))
		}),
})}

// ---------------------------------------------------------------------------
// Continuity on a set
// ---------------------------------------------------------------------------

// ContinuousAtOn — a function continuous at every point of s is
// continuous on s. At a point c of s the radius continuity at c gives
// for ε keeps every value within ε of f(c), those at points of s among
// them; continuity on s asks for no more.
var ContinuousAtOn = continuousAtOnThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtOn",
	Key:  "prop_b3ae9afa42c6b91d",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"∀c:real. c ∈ s ⇒ real_continuous_at(f, c)",
		},
		Conclusion: "real_continuous_on(s, f)",
	},
		func(a *Argument, f *Arrow[Real, Real], s *Expr[Set[Real]], pointwise Fact) {
			a.Do(Unfold(RealContinuousOnDef))
			c := a.FixAs[Real]()
			inS := a.Assume()
			near := a.Unfolded(a.Have(
				"f is continuous at c, a point of s",
				"real_continuous_at(f, c)",
				By(pointwise.At(c), inS)), RealContinuousAtDef)
			eps := a.FixAs[Real]()
			pos := a.Assume()
			d0, radius := a.ObtainAs[Real](
				"continuity at c answers ε with a radius δ₀",
				"∃δ:real. &0 < δ ∧ ∀x:real. |x - c| < δ ⇒ |f(x) - f(c)| < ε",
				By(near.At(eps), pos))
			held := a.Conjuncts(
				radius,
				"δ₀ is positive",
				"inside δ₀ the values are within ε of f(c)")
			a.Take(d0)
			a.Do(SplitConj(
				Case(
					"the radius δ₀ is positive",
					By(held[0])),
				Case(
					"and at the points of s inside it the values are within ε of f(c)",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						inside := b.Conjuncts(
							b.Assume(),
							"x lies in s",
							"and within δ₀ of c")
						b.Show(
							"as at every point inside δ₀",
							By(held[1].At(x), inside[1]))
					})),
			))
		}),
})}

// ContinuousAtInterior — a function continuous on a set is continuous at
// every point the set holds a ball about: continuity on s at c gives a
// radius η inside which the points of s keep f within ε of f(c), and
// inside the smaller of η and the ball's radius δ every point lies in s.
var ContinuousAtInterior = continuousAtInteriorThm{family.Add(registry.ProofEntry{
	Name: "ContinuousAtInterior",
	Key:  "prop_4b2bf033ad48f289",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀s:set(real). ∀c δ:real.",
		Hypotheses: []string{
			"real_continuous_on(s, f)",
			"&0 < δ",
			"∀x:real. |x - c| < δ ⇒ x ∈ s",
		},
		Conclusion: "real_continuous_at(f, c)",
	},
		func(
			a *Argument,
			f *Arrow[Real, Real],
			s *Expr[Set[Real]],
			c, δ *Expr[Real],
			continuous, positive, ball Fact,
		) {
			near := a.Unfolded(continuous, RealContinuousOnDef)
			centre := a.Have(
				"c lies in s, at the centre of its own ball",
				"c ∈ s",
				ByArith(ball.At(c), positive))

			a.Do(Unfold(RealContinuousAtDef))
			ε := a.FixAs[Real]()
			pos := a.Assume()
			η, within := a.ObtainAs[Real](
				"f is continuous on s at c: inside some radius η the points of s keep f within ε of f(c)",
				"∃η:real. &0 < η ∧ (∀x:real. x ∈ s ∧ |x - c| < η ⇒ |f(x) - f(c)| < ε)",
				By(near.At(c, ε), centre, pos))
			held := a.Conjuncts(
				within,
				"η is positive",
				"and inside it the points of s keep f within ε of f(c)")

			a.Take(a.TermAs[Real]("min(δ, η)"))
			a.Do(SplitConj(
				Case(
					"the smaller of δ and η is positive",
					By(positive, held[0], real_sup_inf.LessThanMin.At(δ, η, a.TermAs[Real]("&0")))),
				Case(
					"a point closer to c than both lies in s and within η of c",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						inside := b.Assume()
						b.Show(
							"so f(x) is within ε of f(c)",
							By(ball.At(x), held[1].At(x), inside, real_sup_inf.LessThanMin.At(δ, η, b.TermAs[Real]("|x - c|"))))
					})),
			))
		}),
})}

// ContinuousOnSubset — a function continuous on s is continuous on every
// subset t of s. A point of t is a point of s, and the radius continuity
// on s gives there serves t, whose points are points of s.
var ContinuousOnSubset = continuousOnSubsetThm{family.Add(registry.ProofEntry{
	Name: "ContinuousOnSubset",
	Key:  "prop_581bb44194458884",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀s t:set(real).",
		Hypotheses: []string{
			"real_continuous_on(s, f)",
			"t ⊆ s",
		},
		Conclusion: "real_continuous_on(t, f)",
	},
		func(a *Argument, f *Arrow[Real, Real], s, t *Expr[Set[Real]], given Fact) {
			parts := a.Conjuncts(
				given,
				"f is continuous on s",
				"t lies in s")
			near := a.Unfolded(parts[0], RealContinuousOnDef)
			tInS := a.Unfolded(parts[1], set_basic.SubsetDef)
			a.Do(Unfold(RealContinuousOnDef))
			c := a.FixAs[Real]()
			inT := a.Assume()
			inS := a.Have(
				"c, a point of t, is a point of s",
				"c ∈ s",
				By(tInS.At(c), inT))
			eps := a.FixAs[Real]()
			pos := a.Assume()
			d0, radius := a.ObtainAs[Real](
				"continuity on s answers ε at c with a radius δ₀",
				"∃δ:real. &0 < δ ∧ ∀x:real. x ∈ s ∧ |x - c| < δ ⇒ |f(x) - f(c)| < ε",
				By(near.At(c, eps), inS, pos))
			held := a.Conjuncts(
				radius,
				"δ₀ is positive",
				"inside δ₀ the values at points of s are within ε of f(c)")
			a.Take(d0)
			a.Do(SplitConj(
				Case(
					"the radius δ₀ is positive",
					By(held[0])),
				Case(
					"and a point of t inside it is a point of s inside it",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						inside := b.Conjuncts(
							b.Assume(),
							"x lies in t",
							"and within δ₀ of c")
						xInS := b.Have(
							"x lies in s",
							"x ∈ s",
							By(tInS.At(x), inside[0]))
						b.Show(
							"so its value is within ε of f(c)",
							By(held[1].At(x), xInS, inside[1]))
					})),
			))
		}),
})}
