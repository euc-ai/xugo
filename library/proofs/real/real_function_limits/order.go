// order.go — order, uniqueness and locality (README, "Order, uniqueness
// and locality"): limits respect ≤ — and so a limit is one number —, the
// squeeze, locality, and the sign a positive limit keeps near its point.
//
// Its members share one hypothesis shape: a fact about the values on a
// GIVEN punctured ball of radius d, and a limit whose own ball must be cut
// down to it — the radius real_min(d, δ₀), a distance below which is below
// both. Uniqueness is the order theorem read for a function against itself.
// Sign preservation runs the other way: its ball is the limit's own, handed
// out as the conclusion.

package real_function_limits

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/registry"
)

// LimitAtLessEq — limits respect ≤ on a punctured ball.
//
// Were m < l, let ε = (l − m)/2, which is positive. The two limits share
// a punctured ball on which f is within ε of l and g within ε of m; the
// smaller of its radius and d is still positive, and a distance below it
// is below both. At the point halfway out along that smaller radius,
// then, f ≤ g, while f lies above l − ε and g below m + ε — and those two
// bounds are the same number, the midpoint of l and m, so the values
// would cross.
var LimitAtLessEq = limitAtLessEqThm{family.Add(registry.ProofEntry{
	Name: "LimitAtLessEq",
	Key:  "prop_61d026f055e1b1f6",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀c l m d:real.",
		Hypotheses: []string{
			"&0 < d",
			"∀x:real. &0 < |x - c| ∧ |x - c| < d ⇒ f(x) ≤ g(x)",
			"f ⟶ l (at c)",
			"g ⟶ m (at c)",
		},
		Conclusion: "l ≤ m",
	},
		func(a *Argument, f, g *Arrow[Real, Real], c, l, m, d *Expr[Real], given Fact) {
			reversed := a.SupposeNot()
			pos := a.Have(
				"half the gap is a positive ε",
				"&0 < (l - m) / &2",
				ByArith(reversed))

			sharedRadius, radius := a.ObtainAs[Real](
				"the two limits share a punctured ball of some radius "+
					"δ₀ on which f is within ε of l and g within ε of m",
				"∃δ:real. "+
					"    &0 < δ ∧ "+
					"    ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - l| < (l - m) / &2 ∧ |g(x) - m| < (l - m) / &2",
				By(LimitAtCommonRadius, given, pos))
			within := a.Have(
				"on that ball f is within ε of l and g within ε of m",
				"∀x:real. &0 < |x - c| ∧ |x - c| < δ₀ ⇒ |f(x) - l| < (l - m) / &2 ∧ |g(x) - m| < (l - m) / &2",
				By(radius))
			dominated := a.Have(
				"on the punctured ball of radius d, f ≤ g",
				"∀x:real. &0 < |x - c| ∧ |x - c| < d ⇒ f(x) ≤ g(x)",
				By(given))

			cut := a.TermAs[Real]("min(d, δ₀)")
			cutPos := a.Have(
				"the smaller of d and δ₀ is positive, both being positive",
				"&0 < min(d, δ₀)",
				By(real_sup_inf.LessThanMin.At(d, sharedRadius, a.TermAs[Real]("&0")), given, radius))

			point := a.TermAs[Real]("c + min(d, δ₀) / &2")
			inBall := a.Have(
				"halfway out along the smaller radius is a point of its punctured ball",
				"&0 < |(c + min(d, δ₀) / &2) - c| ∧ |(c + min(d, δ₀) / &2) - c| < min(d, δ₀)",
				By(PuncturedBallPoint.At(c, cut), cutPos))
			distance := a.TermAs[Real]("|(c + min(d, δ₀) / &2) - c|")
			inBoth := a.Have(
				"a distance below the smaller radius is below d and below δ₀",
				"|(c + min(d, δ₀) / &2) - c| < d ∧ |(c + min(d, δ₀) / &2) - c| < δ₀",
				By(real_sup_inf.LessThanMin.At(d, sharedRadius, distance), inBall))

			ordered := a.Have(
				"the point lies in the ball of radius d, so there f ≤ g",
				"f(c + min(d, δ₀) / &2) ≤ g(c + min(d, δ₀) / &2)",
				By(dominated.At(point), inBall, inBoth))
			near := a.Have(
				"and it lies in the shared ball, so there f is within ε of l and g within ε of m",
				"|f(c + min(d, δ₀) / &2) - l| < (l - m) / &2 ∧ |g(c + min(d, δ₀) / &2) - m| < (l - m) / &2",
				By(within.At(point), inBall, inBoth))

			a.Show(
				"yet at the point f lies above l − ε and g below m + ε, "+
					"and those are the same number, the midpoint of l and m",
				ByArith(ordered, near))
		}),
})}

// LimitAtUnique — a function has at most one limit at a point.
//
// Limits respect ≤, and a function lies below itself on every punctured
// ball; so each of two limits of one function at c is at most the other,
// and they are equal.
var LimitAtUnique = limitAtUniqueThm{family.Add(registry.ProofEntry{
	Name: "LimitAtUnique",
	Key:  "prop_59d1565bfb3f9f9d",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c l m:real.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"f ⟶ m (at c)",
		},
		Conclusion: "l = m",
	},
		func(a *Argument, f *Arrow[Real, Real], c, l, m *Expr[Real], toL, toM Fact) {
			self := a.Have(
				"a function lies below itself on the punctured ball of radius 1",
				"∀x:real. &0 < |x - c| ∧ |x - c| < &1 ⇒ f(x) ≤ f(x)",
				Derive(func(g *Argument) {
					x := g.FixAs[Real]()
					g.Assume()
					g.Show(
						"f(x) ≤ f(x)",
						By(real_order_ring.LessEqRefl.At(f.Apply(x))))
				}))
			radius := a.TermAs[Real]("&1")
			below := a.Have(
				"so l ≤ m, limits respecting ≤",
				"l ≤ m",
				By(real_order_ring.ZeroLessThanOne, self, toL, toM, LimitAtLessEq.At(f, f, c, l, m, radius)))
			above := a.Have(
				"and m ≤ l, read the other way",
				"m ≤ l",
				By(real_order_ring.ZeroLessThanOne, self, toM, toL, LimitAtLessEq.At(f, f, c, m, l, radius)))
			a.Show(
				"each limit is at most the other, so they are equal",
				By(below, above, real_construction.LessEqAntisym.At(l, m)))
		}),
})}

// LimitAtSqueeze — a function pinned between two functions with one
// limit has that limit.
//
// Fix ε > 0. The two outer limits share a punctured ball on which f and
// h are both within ε of l; the smaller of its radius and d is still
// positive, and a distance below it is below both. At any point of that
// smaller ball, then, f(x) ≤ g(x) ≤ h(x) with l − ε < f(x) and h(x) < l + ε,
// so g(x) is within ε of l as well.
var LimitAtSqueeze = limitAtSqueezeThm{family.Add(registry.ProofEntry{
	Name: "LimitAtSqueeze",
	Key:  "prop_3f3655b0030c79c",
	Build: family.Theorem(Statement{
		Binders: "∀f g h:(real → real). ∀c l d:real.",
		Hypotheses: []string{
			"&0 < d",
			"∀x:real. &0 < |x - c| ∧ |x - c| < d ⇒ f(x) ≤ g(x) ∧ g(x) ≤ h(x)",
			"f ⟶ l (at c)",
			"h ⟶ l (at c)",
		},
		Conclusion: "g ⟶ l (at c)",
	},
		func(a *Argument, f, g, h *Arrow[Real, Real], c, l, d *Expr[Real], given Fact) {
			shared := a.Have(
				"the two outer limits share, for every positive ε, one "+
					"punctured ball on which f and h are both within ε of l",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ (∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - l| < ε ∧ |h(x) - l| < ε)",
				},
				By(LimitAtCommonRadius, given))
			dPos := a.Have(
				"the radius d of the ball on which g is pinned is positive",
				"&0 < d",
				By(given))
			// Stated before the goal is unfolded: that Unfold also unfolds the
			// limit hypotheses inside `given`, after which it has no successor.
			sandwiched := a.Have(
				"on the punctured ball of radius d, f ≤ g ≤ h",
				"∀x:real. &0 < |x - c| ∧ |x - c| < d ⇒ f(x) ≤ g(x) ∧ g(x) ≤ h(x)",
				By(given))
			a.Do(Unfold(RealLimitAtDef))
			eps := a.FixAs[Real]()
			pos := a.Assume()
			sharedRadius, radius := a.ObtainAs[Real](
				"the shared ball at ε has some radius δ₀, inside which f and h are both within ε of l",
				"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - l| < ε ∧ |h(x) - l| < ε",
				By(shared.At(eps), pos))
			within := a.Have(
				"on the punctured ball of radius δ₀, f and h are both within ε of l",
				"∀x:real. &0 < |x - c| ∧ |x - c| < δ₀ ⇒ |f(x) - l| < ε ∧ |h(x) - l| < ε",
				By(radius))

			a.Take(a.TermAs[Real]("min(d, δ₀)"))
			a.Do(SplitConj(
				Case(
					"the radius is the smaller of d and δ₀, which is positive, both being positive",
					By(real_sup_inf.LessThanMin.At(d, sharedRadius, a.TermAs[Real]("&0")), dPos, radius)),
				Case(
					"and at every point of its punctured ball the value of g is within ε of l",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						ball := b.Assume()
						distance := b.TermAs[Real]("|x - c|")
						inBoth := b.Have(
							"a distance below the smaller radius is below d and below δ₀",
							"|x - c| < d ∧ |x - c| < δ₀",
							By(real_sup_inf.LessThanMin.At(d, sharedRadius, distance), ball))
						pinned := b.Have(
							"x lies in the ball of radius d, so f(x) ≤ g(x) ≤ h(x)",
							"f(x) ≤ g(x) ∧ g(x) ≤ h(x)",
							By(sandwiched.At(x), ball, inBoth))
						near := b.Have(
							"and in the shared ball, so f(x) and h(x) are both within ε of l",
							"|f(x) - l| < ε ∧ |h(x) - l| < ε",
							By(within.At(x), ball, inBoth))
						b.Show(
							"l − ε < f(x) ≤ g(x) ≤ h(x) < l + ε, so |g(x) − l| < ε",
							ByArith(pinned, near))
					})),
			))
		}),
})}

// LimitAtLocal — two functions that agree near a point have the same
// limits there.
//
// A limit is about the values NEAR the point, so the predicate "is a
// limit of f at c" cannot tell f from a function that agrees with it on
// a punctured ball around c. One lemma serves both directions — the
// transport: a function g that agrees with f near c is pinned between f
// and f there, so by the squeeze at (f, g, f) every limit of f is a limit
// of g. Read from g to f it gives the converse, and function
// extensionality equates the two predicates.
var LimitAtLocal = limitAtLocalThm{family.Add(registry.ProofEntry{
	Name: "LimitAtLocal",
	Key:  "prop_13d18a5080b960b5",
	Build: family.Sections(Statement{
		Binders: "∀f g:(real → real). ∀c d:real.",
		Hypotheses: []string{
			"&0 < d",
			"∀x:real. &0 < |x - c| ∧ |x - c| < d ⇒ f(x) = g(x)",
		},
		Conclusion: "real_limit_at(f, c) = real_limit_at(g, c)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			transport := ctx.Lemma(Statement{
				Binders: "∀f g:(real → real). ∀c l d:real.",
				Hypotheses: []string{
					"&0 < d",
					"∀x:real. &0 < |x - c| ∧ |x - c| < d ⇒ f(x) = g(x)",
					"f ⟶ l (at c)",
				},
				Conclusion: "g ⟶ l (at c)",
			},
				func(a *Argument, f, g *Arrow[Real, Real], c, l, d *Expr[Real], given Fact) {
					agree := a.Have(
						"on the punctured ball of radius d, f and g agree",
						"∀x:real. &0 < |x - c| ∧ |x - c| < d ⇒ f(x) = g(x)",
						By(given))
					pinned := a.Have(
						"so on that ball g is pinned between f and f",
						"∀x:real. &0 < |x - c| ∧ |x - c| < d ⇒ f(x) ≤ g(x) ∧ g(x) ≤ f(x)",
						Derive(func(b *Argument) {
							x := b.FixAs[Real]()
							ball := b.Assume()
							b.Show(
								"f(x) = g(x) there, and ≤ is reflexive",
								By(agree.At(x), ball, real_order_ring.LessEqRefl))
						}))
					a.Show(
						"f ≤ g ≤ f near c, and f — both outer functions of the squeeze — tends to l, so g ⟶ l (at c)",
						By(LimitAtSqueeze, given, pinned))
				})

			return ctx.Theorem(headline,
				func(a *Argument, f, g *Arrow[Real, Real], c, d *Expr[Real], given Fact) {
					// The two predicates are equal when they agree at every value l.
					a.Do(Funext())
					l := a.FixAs[Real]("l")
					a.Iff()
					a.Forward(
						"a limit of f is a limit of g, which agrees with f near c",
						func(b *Argument, fLimit Fact) {
							b.Show(
								"every limit of f is a limit of g",
								By(At(transport, f, g, c, l, d), given, fLimit))
						})
					a.Backward(
						"a limit of g is a limit of f, which agrees with g near c",
						func(b *Argument, gLimit Fact) {
							// The transport is stated with the agreement as f(x) = g(x); read
							// at (g, f) it asks for g(x) = f(x), and a By does not match an
							// equation up to its orientation.
							agreeRev := b.Have(
								"the agreement read from g to f",
								"∀x:real. &0 < |x - c| ∧ |x - c| < d ⇒ g(x) = f(x)",
								Derive(func(e *Argument) {
									e.FixAs[Real]()
									ball := e.Assume()
									e.Do(Symm())
									e.Show(
										"f(x) = g(x) there",
										By(given, ball))
								}))
							b.Show(
								"every limit of g is a limit of f",
								By(At(transport, g, f, c, l, d), given, agreeRev, gLimit))
						})
				})
		}),
})}

// LimitAtPositive — a function with a positive limit is positive on some
// punctured ball.
//
// The limit read at ε = l hands a radius inside which f(x) is within l of
// l, and a number less than l away from l is above 0.
var LimitAtPositive = limitAtPositiveThm{family.Add(registry.ProofEntry{
	Name: "LimitAtPositive",
	Key:  "prop_951416b01809c87a",
	Build: family.Theorem(Statement{
		Binders: "∀f:(real → real). ∀c l:real.",
		Hypotheses: []string{
			"f ⟶ l (at c)",
			"&0 < l",
		},
		Conclusion: "∃d:real. &0 < d ∧ (∀x:real. &0 < |x - c| ∧ |x - c| < d ⇒ &0 < f(x))",
	},
		func(a *Argument, f *Arrow[Real, Real], c, l *Expr[Real], given Fact) {
			parts := a.Conjuncts(
				given,
				"f tends to l at c",
				"and l is positive")
			near, pos := a.Unfolded(parts[0], RealLimitAtDef), parts[1]
			d0, radius := a.ObtainAs[Real](
				"the limit at ε = l hands over a radius δ₀ inside which f is within l of l",
				"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f(x) - l| < l",
				By(near.At(l), pos))
			within := a.Have(
				"on the punctured ball of radius δ₀ the values of f are within l of l",
				"∀x:real. &0 < |x - c| ∧ |x - c| < δ₀ ⇒ |f(x) - l| < l",
				By(radius))
			a.Take(d0)
			a.Do(SplitConj(
				Case(
					"the radius δ₀ is positive, as it was obtained",
					By(radius)),
				Case(
					"and at every point of the ball f is positive",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						ball := b.Assume()
						estimate := b.Have(
							"x lies in the ball, so f(x) is within l of l",
							"|f(x) - l| < l",
							By(within.At(x), ball))
						b.Show(
							"a number less than l away from l is above 0",
							ByArith(estimate))
					})),
			))
		}),
})}
