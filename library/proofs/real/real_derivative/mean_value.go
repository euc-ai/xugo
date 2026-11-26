// mean_value.go — Rolle's theorem and the mean value theorem (README,
// "Rolle and the mean value theorem"). A function continuous on ⟦a, b⟧,
// with a derivative strictly between a and b and equal values at the
// ends, has derivative 0 at some point strictly between them — where it is
// largest or least, by Fermat's theorem, or at the midpoint when both of
// those points are ends, f being largest there as at every point. Tilting
// f by the slope of its chord makes the ends equal, and Rolle's theorem
// becomes the mean value theorem; read between any two points of ⟦a, b⟧,
// it is the form the monotonicity criteria use, and read between two
// points of an interval at every point of which f has a derivative, the
// form the mean value inequality uses: with the derivative bounded in size
// it bounds the change of f by that bound times the distance, and with the
// derivative within K of a slope d, the change of f less d times the step
// by K times the step (f tilted by the line of slope d). Bounded in
// size by the derivative of a second function g, it bounds the change of f
// by the change of g, g − f and g + f both rising by the monotonicity
// criterion (the comparison form). Read twice, for a derivative and for the
// function itself, the mean value inequality bounds a function whose second
// derivative is bounded by a quadratic, and its derivative by a linear
// function.

package real_derivative

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_pow"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/real/real_topology"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/set_basic"
	"github.com/euc-ai/xugo/library/registry"
)

// Rolle — a function taking the same value at both ends of ⟦a, b⟧ has
// derivative 0 somewhere strictly between them (Rolle's theorem).
//
// A point z strictly inside ⟦a, b⟧ where f is largest on ⟦a, b⟧ is a
// local maximum: the ball of radius min(z − a, b − z) about z lies in
// ⟦a, b⟧, so f is largest at z on that ball, and Fermat's theorem gives
// derivative 0 there; the same holds where f is least. By the extreme
// value theorem f is largest at some point p₀ of ⟦a, b⟧ and least at
// some q₀. If either lies strictly inside, it is the point. Otherwise
// both are ends, where f takes its one value f(a) = f(b), so every value
// on ⟦a, b⟧ is at most f(p₀) = f(a) = f(q₀), which is at most every
// value: f is largest at every point, the midpoint among them.
var Rolle = rolleThm{family.Add(registry.ProofEntry{
	Name: "Rolle",
	Key:  "prop_6cf7342963af4e2a",
	Build: family.Sections(Statement{
		Binders: "∀f f':(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a < b",
			"f(a) = f(b)",
			"real_continuous_on(⟦a, b⟧, f)",
			"∀x:real. a < x ∧ x < b ⇒ real_derivative_at(f, x, f'(x))",
		},
		Conclusion: "∃z:real. a < z ∧ z < b ∧ f'(z) = &0",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// A point strictly inside ⟦a, b⟧ where f is largest on ⟦a, b⟧ is a
			// maximum on the ball of radius min(z − a, b − z) about it, a ball
			// inside ⟦a, b⟧: Fermat's theorem there.
			interiorMax := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀a b z l:real.",
				Hypotheses: []string{
					"a < z",
					"z < b",
					"∀y:real. a ≤ y ∧ y ≤ b ⇒ f(y) ≤ f(z)",
					"real_derivative_at(f, z, l)",
				},
				Conclusion: "l = &0",
			},
				func(arg *Argument, f *Arrow[Real, Real], a, b, z, l *Expr[Real], given Fact) {
					held := arg.Conjuncts(
						given,
						"z lies right of a",
						"z lies left of b",
						"f is largest at z on ⟦a, b⟧",
						"f has derivative l at z")
					toA, toB := arg.TermAs[Real]("z - a"), arg.TermAs[Real]("b - z")
					radius := arg.TermAs[Real]("min(z - a, b - z)")
					positive := arg.Have(
						"z is a positive distance from the nearer end",
						"&0 < min(z - a, b - z)",
						ByArith(held[0], held[1], real_sup_inf.LessThanMin.At(toA, toB, arg.TermAs[Real]("&0"))))
					largest := arg.Have(
						"the ball of that radius about z lies in ⟦a, b⟧, so f is largest at z on it",
						"∀x:real. |x - z| < min(z - a, b - z) ⇒ f(x) ≤ f(z)",
						Derive(func(c *Argument) {
							x := c.FixAs[Real]()
							near := c.Assume()
							inside := c.Have(
								"x is nearer to z than both ends are, so it lies in ⟦a, b⟧",
								"a ≤ x ∧ x ≤ b",
								ByArith(near, real_sup_inf.LessThanMin.At(toA, toB, c.TermAs[Real]("|x - z|"))))
							c.Show(
								"so f(x) ≤ f(z)",
								By(held[2].At(x), inside))
						}))
					arg.Show(
						"so l = 0, by Fermat's theorem at the maximum",
						By(LocalMaxDerivativeZero.At(f, z, radius, l), positive, largest, held[3]))
				})

			// The mirror: a point strictly inside ⟦a, b⟧ where f is least on
			// ⟦a, b⟧ is a minimum on the same ball.
			interiorMin := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀a b z l:real.",
				Hypotheses: []string{
					"a < z",
					"z < b",
					"∀y:real. a ≤ y ∧ y ≤ b ⇒ f(z) ≤ f(y)",
					"real_derivative_at(f, z, l)",
				},
				Conclusion: "l = &0",
			},
				func(arg *Argument, f *Arrow[Real, Real], a, b, z, l *Expr[Real], given Fact) {
					held := arg.Conjuncts(
						given,
						"z lies right of a",
						"z lies left of b",
						"f is least at z on ⟦a, b⟧",
						"f has derivative l at z")
					toA, toB := arg.TermAs[Real]("z - a"), arg.TermAs[Real]("b - z")
					radius := arg.TermAs[Real]("min(z - a, b - z)")
					positive := arg.Have(
						"z is a positive distance from the nearer end",
						"&0 < min(z - a, b - z)",
						ByArith(held[0], held[1], real_sup_inf.LessThanMin.At(toA, toB, arg.TermAs[Real]("&0"))))
					least := arg.Have(
						"the ball of that radius about z lies in ⟦a, b⟧, so f is least at z on it",
						"∀x:real. |x - z| < min(z - a, b - z) ⇒ f(z) ≤ f(x)",
						Derive(func(c *Argument) {
							x := c.FixAs[Real]()
							near := c.Assume()
							inside := c.Have(
								"x is nearer to z than both ends are, so it lies in ⟦a, b⟧",
								"a ≤ x ∧ x ≤ b",
								ByArith(near, real_sup_inf.LessThanMin.At(toA, toB, c.TermAs[Real]("|x - z|"))))
							c.Show(
								"so f(z) ≤ f(x)",
								By(held[2].At(x), inside))
						}))
					arg.Show(
						"so l = 0, by Fermat's theorem at the minimum",
						By(LocalMinDerivativeZero.At(f, z, radius, l), positive, least, held[3]))
				})

			// A point of ⟦a, b⟧ not strictly inside it is a or b, and at either
			// end f takes the value f(a).
			endValue := ctx.Lemma(Statement{
				Binders: "∀f:(real → real). ∀a b x:real.",
				Hypotheses: []string{
					"a ≤ x",
					"x ≤ b",
					"¬(a < x ∧ x < b)",
					"f(a) = f(b)",
				},
				Conclusion: "f(x) = f(a)",
			},
				func(arg *Argument, f *Arrow[Real, Real], a, b, x *Expr[Real], given Fact) {
					held := arg.Conjuncts(
						given,
						"a ≤ x",
						"x ≤ b",
						"x is not strictly inside ⟦a, b⟧",
						"f(a) = f(b)")
					arg.Cases(arg.Term("x = a"))
					arg.When(
						"x is a",
						func(c *Argument, atA Fact) {
							c.Show(
								"f(x) = f(a)",
								By(Normalized, atA))
						})
					arg.Otherwise(
						"x is b, where f takes the same value",
						func(c *Argument, notA Fact) {
							atB := c.Have(
								"x is the other end, b",
								"x = b",
								ByArith(held[0], held[1], held[2], notA))
							c.Show(
								"so f(x) = f(b) = f(a)",
								atB.Rw(),
								By(held[3]))
						})
				})

			return ctx.Theorem(headline, func(
				arg *Argument,
				f, fPrime *Arrow[Real, Real],
				a, b *Expr[Real],
				given Fact,
			) {
				held := arg.Conjuncts(
					given,
					"a < b",
					"f(a) = f(b)",
					"f is continuous on ⟦a, b⟧",
					"f has derivative f'(x) at every x strictly between a and b")
				ordered := arg.Have(
					"a ≤ b, a being less than b",
					"a ≤ b",
					ByArith(held[0]))
				p, largest := arg.ObtainAs[Real](
					"by the extreme value theorem f is largest on ⟦a, b⟧ at some point p₀ of it",
					"∃p:real. a ≤ p ∧ p ≤ b ∧ ∀y:real. a ≤ y ∧ y ≤ b ⇒ f(y) ≤ f(p)",
					By(real_continuous.ExtremeValueMax.At(f, a, b), ordered, held[2]))
				q, least := arg.ObtainAs[Real](
					"and least at some point q₀ of it",
					"∃q:real. a ≤ q ∧ q ≤ b ∧ ∀y:real. a ≤ y ∧ y ≤ b ⇒ f(q) ≤ f(y)",
					By(real_continuous.ExtremeValueMin.At(f, a, b), ordered, held[2]))
				atMax := arg.Conjuncts(
					largest,
					"a ≤ p₀",
					"p₀ ≤ b",
					"f is largest at p₀")
				atMin := arg.Conjuncts(
					least,
					"a ≤ q₀",
					"q₀ ≤ b",
					"f is least at q₀")

				arg.Cases(arg.Term("a < p₀ ∧ p₀ < b"))
				arg.When(
					"p₀ lies strictly inside ⟦a, b⟧: the derivative vanishes at the maximum",
					func(c *Argument, inside Fact) {
						zero := c.Have(
							"so f'(p₀) = 0",
							"f'(p₀) = &0",
							By(At(interiorMax, f, a, b, p, fPrime.Apply(p)), inside, atMax[2], held[3].At(p)))
						c.Take(p)
						c.Show(
							"p₀ is the point",
							By(inside, zero))
					})
				arg.Otherwise(
					"p₀ is an end",
					func(c *Argument, maxAtEnd Fact) {
						maxValue := c.Have(
							"so the largest value is f(a)",
							"f(p₀) = f(a)",
							By(At(endValue, f, a, b, p), atMax[0], atMax[1], maxAtEnd, held[1]))
						c.Cases(c.Term("a < q₀ ∧ q₀ < b"))
						c.When(
							"q₀ lies strictly inside ⟦a, b⟧: the derivative vanishes at the minimum",
							func(d *Argument, inside Fact) {
								zero := d.Have(
									"so f'(q₀) = 0",
									"f'(q₀) = &0",
									By(At(interiorMin, f, a, b, q, fPrime.Apply(q)), inside, atMin[2], held[3].At(q)))
								d.Take(q)
								d.Show(
									"q₀ is the point",
									By(inside, zero))
							})
						c.Otherwise(
							"q₀ is an end too: f is largest everywhere on ⟦a, b⟧, at the midpoint as well",
							func(d *Argument, minAtEnd Fact) {
								minValue := d.Have(
									"so the least value is f(a) as well",
									"f(q₀) = f(a)",
									By(At(endValue, f, a, b, q), atMin[0], atMin[1], minAtEnd, held[1]))
								mid := d.TermAs[Real]("(a + b) / &2")
								inside := d.Have(
									"the midpoint lies strictly between a and b",
									"a < (a + b) / &2 ∧ (a + b) / &2 < b",
									ByArith(held[0]))
								inSegment := d.Have(
									"so it lies in ⟦a, b⟧",
									"a ≤ (a + b) / &2 ∧ (a + b) / &2 ≤ b",
									ByArith(inside))
								everywhere := d.Have(
									"f is largest at the midpoint: f(y) ≤ f(p₀) = f(a) = f(q₀) ≤ f((a + b)/2)",
									"∀y:real. a ≤ y ∧ y ≤ b ⇒ f(y) ≤ f((a + b) / &2)",
									Derive(func(e *Argument) {
										y := e.FixAs[Real]()
										between := e.Assume()
										e.Show(
											"f(y) is at most the largest value f(p₀) and the midpoint's "+
												"value at least the least f(q₀), both of them f(a)",
											ByArith(atMax[2].At(y), between, maxValue, minValue, atMin[2].At(mid), inSegment))
									}))
								zero := d.Have(
									"so f' vanishes at the midpoint",
									"f'((a + b) / &2) = &0",
									By(At(interiorMax, f, a, b, mid, fPrime.Apply(mid)), inside, everywhere, held[3].At(mid)))
								d.Take(mid)
								d.Show(
									"the midpoint is the point",
									By(inside, zero))
							})
					})
			})
		}),
})}

// MeanValue — the mean value theorem: somewhere strictly between a and b
// the derivative is the slope of the chord from (a, f(a)) to (b, f(b)).
//
// Tilt f by the chord's slope k = (f(b) − f(a))/(b − a): h(x) = f(x) − k·x
// takes equal values at a and b, since k·(b − a) = f(b) − f(a). The line
// x ↦ k·x has derivative k at every point, so it is continuous, and h is
// continuous on ⟦a, b⟧ with derivative f'(x) − k inside. Rolle's theorem
// gives a point z where f'(z) − k = 0.
var MeanValue = meanValueThm{family.Add(registry.ProofEntry{
	Name: "MeanValue",
	Key:  "prop_283dd769b1d0816e",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a < b",
			"real_continuous_on(⟦a, b⟧, f)",
			"∀x:real. a < x ∧ x < b ⇒ real_derivative_at(f, x, f'(x))",
		},
		Conclusion: "∃z:real. a < z ∧ z < b ∧ f(b) - f(a) = f'(z) * (b - a)",
		Abbrev: Abbrev{
			{Name: "chordSlope", Text: "(f(b) - f(a)) / (b - a)"},
		},
	},
		func(arg *Argument, f, fPrime *Arrow[Real, Real], a, b *Expr[Real], given Fact) {
			held := arg.Conjuncts(
				given,
				"a < b",
				"f is continuous on ⟦a, b⟧",
				"f has derivative f'(x) at every x strictly between a and b")
			k := arg.TermAs[Real]("«chordSlope»")
			line := arg.TermAs[Fun[Real, Real]]("λx:real. «chordSlope» * x")
			h := arg.TermAs[Fun[Real, Real]]("λx:real. f(x) - «chordSlope» * x")
			hPrime := arg.TermAs[Fun[Real, Real]]("λx:real. f'(x) - «chordSlope» * &1")

			rise := arg.Have(
				"the slope times the run is the rise, the run b − a being positive",
				"«chordSlope» * (b - a) = f(b) - f(a)",
				ByArith(held[0]))

			// The line's derivative is k·1, the form DerivativeScale gives for k
			// times the identity; the last step reads f'(z₀) − k·1 = 0 as
			// f'(z₀) = k.
			lineDerivative := arg.Have(
				"the line x ↦ k·x has derivative k·1 at every point",
				"∀y:real. real_derivative_at(λx:real. «chordSlope» * x, y, «chordSlope» * &1)",
				Derive(func(d *Argument) {
					y := d.FixAs[Real]()
					d.Show(
						"it is k times the identity, whose derivative is 1",
						By(
							DerivativeScale.At(d.TermAs[Fun[Real, Real]]("λx:real. x"), y, d.TermAs[Real]("&1"), k),
							DerivativeId.At(y)))
				}))
			lineContinuous := arg.Have(
				"so the line, having a derivative everywhere, is continuous on ⟦a, b⟧",
				"real_continuous_on(⟦a, b⟧, λx:real. «chordSlope» * x)",
				By(
					lineDerivative,
					DerivativeContinuousOn.At(line, arg.TermAs[Fun[Real, Real]]("λx:real. «chordSlope» * &1"),
						arg.TermAs[Set[Real]]("⟦a, b⟧"))))

			hContinuous := arg.Have(
				"h = f minus the line is continuous on ⟦a, b⟧",
				"real_continuous_on(⟦a, b⟧, λx:real. f(x) - «chordSlope» * x)",
				By(real_continuous.ContinuousOnSub, held[1], lineContinuous))
			hDerivative := arg.Have(
				"and has derivative f'(y) − k at every y strictly between a and b",
				Statement{
					Binders: "∀y:real.",
					Hypotheses: []string{
						"a < y",
						"y < b",
					},
					Conclusion: "real_derivative_at(λx:real. f(x) - «chordSlope» * x, y, f'(y) - «chordSlope» * &1)",
				},
				Derive(func(d *Argument) {
					y := d.FixAs[Real]()
					inside := d.Assume()
					d.Show(
						"the difference of f's derivative and the line's",
						By(
							DerivativeSub.At(f, line, y, fPrime.Apply(y), d.TermAs[Real]("«chordSlope» * &1")),
							held[2].At(y),
							inside,
							lineDerivative.At(y)))
				}))
			level := arg.Have(
				"h takes the same value at a and at b: k·(b − a) = f(b) − f(a)",
				"f(a) - «chordSlope» * a = f(b) - «chordSlope» * b",
				ByArith(rise))

			z0, found := arg.ObtainAs[Real](
				"Rolle's theorem for h hands a point z₀ strictly between a and b where f'(z₀) − k = 0",
				"∃z:real. a < z ∧ z < b ∧ f'(z) - «chordSlope» * &1 = &0",
				By(Rolle.At(h, hPrime, a, b), held[0], level, hContinuous, hDerivative))
			parts := arg.Conjuncts(
				found,
				"a < z₀",
				"z₀ < b",
				"f'(z₀) − k = 0")
			atZ := arg.Have(
				"so f'(z₀) is the slope k",
				"f'(z₀) = «chordSlope»",
				ByArith(parts[2]))
			arg.Take(z0)
			arg.Do(SplitConjAll(
				Case(
					"a < z₀",
					By(parts[0])),
				Case(
					"z₀ < b",
					By(parts[1])),
				Case(
					"the rise is f'(z₀) times the run",
					Derive(func(d *Argument) {
						d.Do(atZ.Rw())
						d.Show(
							"the slope times the run is the rise",
							By(rise))
					})),
			))
		}),
})}

// MeanValueBetween — the mean value theorem between any two points of
// ⟦a, b⟧.
//
// For a ≤ x < y ≤ b, ⟦x, y⟧ lies in ⟦a, b⟧, so f is continuous on it,
// and every point strictly between x and y is strictly between a and b,
// where f has its derivative: the mean value theorem on ⟦x, y⟧.
var MeanValueBetween = meanValueBetweenThm{family.Add(registry.ProofEntry{
	Name: "MeanValueBetween",
	Key:  "prop_e6f812f0bb61306d",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(real → real). ∀a b x y:real.",
		Hypotheses: []string{
			"real_continuous_on(⟦a, b⟧, f)",
			"∀t:real. a < t ∧ t < b ⇒ real_derivative_at(f, t, f'(t))",
			"a ≤ x",
			"x < y",
			"y ≤ b",
		},
		Conclusion: "∃z:real. x < z ∧ z < y ∧ f(y) - f(x) = f'(z) * (y - x)",
	},
		func(arg *Argument, f, fPrime *Arrow[Real, Real], a, b *Expr[Real], given Fact) {
			held := arg.Conjuncts(
				given,
				"f is continuous on ⟦a, b⟧",
				"f has derivative f'(x) at every x strictly between a and b")
			x := arg.FixAs[Real]()
			y := arg.FixAs[Real]()
			// The three bounds are read off the pair before the subset
			// unfold below, which splits a resident conjunction.
			bounds := arg.Conjuncts(
				arg.Assume(),
				"a ≤ x",
				"x < y",
				"y ≤ b")
			lower, ordered, upper := bounds[0], bounds[1], bounds[2]
			inside := arg.Have(
				"⟦x, y⟧ lies in ⟦a, b⟧",
				"⟦x, y⟧ ⊆ ⟦a, b⟧",
				Derive(func(d *Argument) {
					d.Do(Unfold(set_basic.SubsetDef))
					// Named: unnamed, the point would take the subset
					// definition's binder name, x, which is already the
					// interval's left end here.
					d.FixAs[Real]("t")
					in := d.Assume()
					between := d.Have(
						"x ≤ t ≤ y",
						"x ≤ t ∧ t ≤ y",
						BySets(in))
					wide := d.Have(
						"so a ≤ t ≤ b",
						"a ≤ t ∧ t ≤ b",
						ByArith(between, lower, upper))
					d.Show(
						"t is a point of ⟦a, b⟧",
						BySets(wide))
				}))
			continuous := arg.Have(
				"so f is continuous on ⟦x, y⟧",
				"real_continuous_on(⟦x, y⟧, f)",
				By(real_continuous.ContinuousOnSubset, held[0], inside))
			derivatives := arg.Have(
				"and has derivative f'(t) at every t strictly between x and y",
				"∀t:real. x < t ∧ t < y ⇒ real_derivative_at(f, t, f'(t))",
				Derive(func(d *Argument) {
					t := d.FixAs[Real]()
					between := d.Assume()
					wide := d.Have(
						"t is strictly between a and b",
						"a < t ∧ t < b",
						ByArith(between, lower, upper))
					d.Show(
						"where f has its derivative",
						By(held[1].At(t), wide))
				}))
			arg.Show(
				"the mean value theorem on ⟦x, y⟧",
				By(MeanValue.At(f, fPrime, x, y), ordered, continuous, derivatives))
		}),
})}

// MeanValueOnInterval — the mean value theorem inside an interval where f
// has a derivative at every point: between two of its points x < y there
// is a z with f(y) − f(x) = f'(z)·(y − x). The interval holds ⟦x, y⟧, so
// f is continuous there and has its derivative strictly inside, which is
// what the mean value theorem asks.
var MeanValueOnInterval = meanValueOnIntervalThm{family.Add(registry.ProofEntry{
	Name: "MeanValueOnInterval",
	Key:  "prop_cbe48df6f4381d03",
	Build: family.Theorem(Statement{
		Binders: "∀f f':real → real. ∀s:set(real). ∀x y:real.",
		Hypotheses: []string{
			"real_interval(s)",
			"∀t:real. t ∈ s ⇒ real_derivative_at(f, t, f'(t))",
			"x ∈ s",
			"y ∈ s",
			"x < y",
		},
		Conclusion: "∃z:real. x < z ∧ z < y ∧ f(y) - f(x) = f'(z) * (y - x)",
	}, func(a *Argument, f, fPrime *Arrow[Real, Real], s *Expr[Set[Real]], x, y *Expr[Real],
		interval, derivative, xIn, yIn, xy Fact) {
		between := a.Unfolded(interval, real_topology.RealIntervalDef)
		onSegment := a.Have(
			"s holds ⟦x, y⟧, so f has derivative f'(c) at every point c of it",
			"∀c:real. c ∈ ⟦x, y⟧ ⇒ real_derivative_at(f, c, f'(c))",
			By(derivative, between, xIn, yIn),
		)
		inside := a.Have(
			"in particular at every point strictly between x and y",
			"∀t:real. x < t ∧ t < y ⇒ real_derivative_at(f, t, f'(t))",
			By(onSegment, real_order_ring.LessEqOfLessThan),
		)
		a.Show(
			"the mean value theorem on ⟦x, y⟧, where f is continuous, having a derivative at every point",
			By(
				MeanValueBetween.At(f, fPrime, x, y, x, y),
				DerivativeContinuousOn.At(f, fPrime, a.TermAs[Set[Real]]("⟦x, y⟧")),
				onSegment,
				inside,
				xy,
				real_order_ring.LessEqRefl),
		)
	}),
})}

// MeanValueInequality — a function whose derivative is at most K in size
// on an open interval changes, between any two of its points, by at most
// K times their distance.
//
// ⟬a, b⟭ is an interval at every point of which f has its derivative, so
// the mean value theorem on an interval writes f(q) − f(p) as
// f'(z)·(q − p) for some z strictly between two of its points p < q. For
// x ≠ y that hands over, whichever of the two is the smaller, a point z of
// ⟬a, b⟭ with f(y) − f(x) = f'(z)·(y − x), and |f'(z)| ≤ K bounds the
// product. For x = y both sides are 0.
var MeanValueInequality = meanValueInequalityThm{family.Add(registry.ProofEntry{
	Name: "MeanValueInequality",
	Key:  "prop_e51051b526dc26da",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(real → real). ∀a b K x y:real.",
		Hypotheses: []string{
			"∀t:real. a < t ∧ t < b ⇒ real_derivative_at(f, t, f'(t))",
			"∀t:real. a < t ∧ t < b ⇒ |f'(t)| ≤ K",
			"a < x",
			"x < b",
			"a < y",
			"y < b",
		},
		Conclusion: "|f(y) - f(x)| ≤ K * |y - x|",
	},
		func(arg *Argument, f, fPrime *Arrow[Real, Real], a, b, K, x, y *Expr[Real],
			derivative, bound, xAbove, xBelow, yAbove, yBelow Fact) {
			interval := arg.TermAs[Set[Real]]("⟬a, b⟭")
			isInterval := arg.Have(
				"⟬a, b⟭ is an interval: a real between two of its points lies between a and b",
				"real_interval(⟬a, b⟭)",
				Unfold(real_topology.RealIntervalDef),
				ByArith())

			arg.Cases(arg.Term("x = y"))
			arg.When(
				"x = y: both sides are 0",
				func(c *Argument, same Fact) {
					c.Show(
						"|f(y) − f(y)| = |0| = 0 = K·|y − y|",
						same.Rw(),
						Simp(Fwd(real_ring.SubRefl), Fwd(real_sgn_abs.AbsOfZero), Fwd(real_ring.MulRightZero)),
						ByArith())
				})
			arg.Otherwise(
				"x ≠ y: the mean value theorem between them, in whichever order they come",
				func(c *Argument, apart Fact) {
					z, atZ := c.ObtainAs[Real](
						"a point z of ⟬a, b⟭ at which f(y) − f(x) = f'(z)·(y − x)",
						"∃z:real. a < z ∧ z < b ∧ f(y) - f(x) = f'(z) * (y - x)",
						Derive(func(d *Argument) {
							d.Cases(d.Term("x < y"))
							d.When(
								"x < y: the mean value theorem on ⟦x, y⟧",
								func(e *Argument, ordered Fact) {
									w, at := e.UnpackAs[Real](GroupPremises(
										isInterval, derivative, xAbove, xBelow, yAbove, yBelow, ordered,
										MeanValueOnInterval.At(f, fPrime, interval, x, y)))
									e.Take(w)
									e.Show(
										"w lies between x and y, so inside ⟬a, b⟭",
										ByArith(at, xAbove, yBelow))
								})
							d.Otherwise(
								"y < x: the mean value theorem on ⟦y, x⟧, its equation read with both signs turned",
								func(e *Argument, notBefore Fact) {
									reversed := e.Have(
										"y lies below x",
										"y < x",
										ByArith(notBefore, apart))
									w, at := e.UnpackAs[Real](GroupPremises(
										isInterval, derivative, yAbove, yBelow, xAbove, xBelow, reversed,
										MeanValueOnInterval.At(f, fPrime, interval, y, x)))
									e.Take(w)
									e.Show(
										"w lies between y and x, so inside ⟬a, b⟭, and f(x) − f(y) = f'(w)·(x − y) is the same equation",
										ByArith(at, yAbove, xBelow))
								})
						}))
					parts := c.Conjuncts(
						atZ,
						"z lies above a",
						"and below b",
						"f(y) − f(x) = f'(z)·(y − x)")
					gap := c.TermAs[Real]("y - x")
					slope := c.Have(
						"the derivative at z is at most K in size",
						"|f'(z)| ≤ K",
						By(bound.At(z), parts[0], parts[1]))
					size := c.Have(
						"|f(y) − f(x)| = |f'(z)|·|y − x|",
						"|f(y) - f(x)| = |f'(z)| * |y - x|",
						By(parts[2], real_sgn_abs.AbsMul.At(fPrime.Apply(z), gap)))
					c.Show(
						"and |f'(z)|·|y − x| ≤ K·|y − x|, as |y − x| is nonnegative",
						ByArith(size, slope, real_sgn_abs.AbsNonneg.At(gap)))
				})
		}),
})}

// MeanValueNearSlope — the mean value inequality against a slope: where f'
// stays within K of d on an open interval, f moves between two of its
// points by d times the step, to within K times the step. It is the mean
// value inequality for f tilted by the line of slope d, whose derivative
// f' − d is at most K in size.
var MeanValueNearSlope = meanValueNearSlopeThm{family.Add(registry.ProofEntry{
	Name: "MeanValueNearSlope",
	Key:  "prop_d54955f3b8b94d16",
	Build: family.Theorem(Statement{
		Binders: "∀f f':(real → real). ∀a b d K x y:real.",
		Hypotheses: []string{
			"∀t:real. a < t ∧ t < b ⇒ real_derivative_at(f, t, f'(t))",
			"∀t:real. a < t ∧ t < b ⇒ |f'(t) - d| ≤ K",
			"a < x",
			"x < b",
			"a < y",
			"y < b",
		},
		Conclusion: "|f(y) - f(x) - d * (y - x)| ≤ K * |y - x|",
	},
		func(arg *Argument, f, fPrime *Arrow[Real, Real], a, b, d, K, x, y *Expr[Real],
			derivative, near, xAbove, xBelow, yAbove, yBelow Fact) {
			tilted := arg.TermAs[Fun[Real, Real]]("λs:real. f(s) - d * s")
			tiltedPrime := arg.TermAs[Fun[Real, Real]]("λs:real. f'(s) - d")
			identity := arg.TermAs[Fun[Real, Real]]("λs:real. s")
			one := arg.TermAs[Real]("&1")
			slopes := arg.Have(
				"f tilted by the line of slope d has derivative f' − d",
				"∀t:real. a < t ∧ t < b ⇒ real_derivative_at(λs:real. f(s) - d * s, t, f'(t) - d)",
				Derive(func(e *Argument) {
					t := e.FixAs[Real]("t")
					inside := e.Assume()
					e.Show(
						"the difference of f and s ↦ d·s, whose derivative is d·1",
						By(
							derivative.At(t),
							inside,
							DerivativeSub.At(
								f,
								e.TermAs[Fun[Real, Real]]("λs:real. d * s"),
								t,
								fPrime.Apply(t),
								e.TermAs[Real]("d * &1")),
							DerivativeScale.At(identity, t, one, d),
							DerivativeId.At(t),
							real_ring.MulRightId.At(d)))
				}))
			tiltedMoves := arg.Have(
				"so by the mean value inequality the tilted function moves by at most K|y − x|",
				"|f(y) - d * y - (f(x) - d * x)| ≤ K * |y - x|",
				By(
					slopes,
					near,
					xAbove,
					xBelow,
					yAbove,
					yBelow,
					MeanValueInequality.At(tilted, tiltedPrime, a, b, K, x, y)))
			arg.Show(
				"which is the increment of f less d(y − x)",
				ByArith(tiltedMoves))
		}),
})}

// MeanValueComparison — a function whose derivative is bounded in size by
// the derivative of another changes by no more than the other does: where
// |f'| ≤ g' strictly between a and b, |f(b) − f(a)| ≤ g(b) − g(a).
//
// The functions g − f and g + f have the nonnegative derivatives g' − f'
// and g' + f' there, so both rise from a to b.
var MeanValueComparison = meanValueComparisonThm{family.Add(registry.ProofEntry{
	Name: "MeanValueComparison",
	Key:  "prop_1c0866e06b85b57c",
	Build: family.Theorem(Statement{
		Binders: "∀f f' g g':(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a ≤ b",
			"real_continuous_on(⟦a, b⟧, f)",
			"real_continuous_on(⟦a, b⟧, g)",
			"∀t:real. a < t ∧ t < b ⇒ real_derivative_at(f, t, f'(t))",
			"∀t:real. a < t ∧ t < b ⇒ real_derivative_at(g, t, g'(t))",
			"∀t:real. a < t ∧ t < b ⇒ |f'(t)| ≤ g'(t)",
		},
		Conclusion: "|f(b) - f(a)| ≤ g(b) - g(a)",
	},
		func(arg *Argument, f, fPrime, g, gPrime *Arrow[Real, Real], a, b *Expr[Real], given Fact) {
			held := arg.Conjuncts(
				given,
				"a ≤ b",
				"f is continuous on ⟦a, b⟧",
				"g is continuous on ⟦a, b⟧",
				"f has derivative f'(t) strictly between a and b",
				"g has derivative g'(t) there",
				"|f'| ≤ g' there")
			ordered, fContinuous, gContinuous, fSlope, gSlope, bound :=
				held[0], held[1], held[2], held[3], held[4], held[5]
			interval := arg.TermAs[Set[Real]]("⟦a, b⟧")
			slopes := arg.Have(
				"between a and b, g − f and g + f have derivatives g' − f' and g' + f'",
				Statement{
					Binders: "∀t:real.",
					Hypotheses: []string{
						"a < t",
						"t < b",
					},
					Conclusion: "real_derivative_at(λs:real. g(s) - f(s), t, g'(t) - f'(t)) ∧ " +
						"real_derivative_at(λs:real. g(s) + f(s), t, g'(t) + f'(t))",
				},
				By(fSlope, gSlope, DerivativeSub, DerivativeAdd))
			signs := arg.Have(
				"both derivatives are nonnegative there, as |f'| ≤ g'",
				"∀t:real. a < t ∧ t < b ⇒ &0 ≤ g'(t) - f'(t) ∧ &0 ≤ g'(t) + f'(t)",
				arg.ForEach(func(t *Expr[Real]) Action { return ByArith(bound.At(t)) }))
			below := arg.Have(
				"so g − f, continuous on ⟦a, b⟧, rises from a to b",
				"g(a) - f(a) ≤ g(b) - f(b)",
				By(
					signs,
					slopes,
					fContinuous,
					gContinuous,
					ordered,
					real_continuous.ContinuousOnSub.At(g, f, interval),
					real_order_ring.LessEqRefl.At(a),
					real_order_ring.LessEqRefl.At(b),
					DerivativeNonnegIncreasing.At(
						arg.TermAs[Fun[Real, Real]]("λs:real. g(s) - f(s)"),
						arg.TermAs[Fun[Real, Real]]("λs:real. g'(s) - f'(s)"),
						a, b, a, b)))
			above := arg.Have(
				"and so does g + f",
				"g(a) + f(a) ≤ g(b) + f(b)",
				By(
					signs,
					slopes,
					fContinuous,
					gContinuous,
					ordered,
					real_continuous.ContinuousOnAdd.At(g, f, interval),
					real_order_ring.LessEqRefl.At(a),
					real_order_ring.LessEqRefl.At(b),
					DerivativeNonnegIncreasing.At(
						arg.TermAs[Fun[Real, Real]]("λs:real. g(s) + f(s)"),
						arg.TermAs[Fun[Real, Real]]("λs:real. g'(s) + f'(s)"),
						a, b, a, b)))
			arg.Show(
				"hence −(g(b) − g(a)) ≤ f(b) − f(a) ≤ g(b) − g(a)",
				ByArith(below, above))
		}),
})}

// BoundedSecondDerivativeGrowth — a function whose second derivative is
// bounded on the line grows at most quadratically, and its derivative at most
// linearly: where f' = g, g' = h and |h| ≤ M everywhere, one K ≥ 0 bounds
// |f(x)| by K(1 + x²) and |g(x)| by K(1 + |x|) at every x.
//
// Between 0 and x, inside the open interval of radius |x| + 1 about 0, the
// mean value inequality bounds the change of g by M|x|. So |g| is at most
// |g(0)| + M(|x| + 1) on that interval, and the mean value inequality read for
// f bounds its change by that times |x|. K = 2(|f(0)| + |g(0)| + M + 1)
// covers both bounds, since |x| ≤ 1 + x².
var BoundedSecondDerivativeGrowth = boundedSecondDerivativeGrowthThm{family.Add(registry.ProofEntry{
	Name: "BoundedSecondDerivativeGrowth",
	Key:  "prop_79e188879b1b37ce",
	Build: family.Theorem(Statement{
		Binders: "∀f g h:(real → real). ∀M:real.",
		Hypotheses: []string{
			"∀t:real. real_derivative_at(f, t, g(t))",
			"∀t:real. real_derivative_at(g, t, h(t))",
			"∀t:real. |h(t)| ≤ M",
		},
		Conclusion: "∃K:real. &0 ≤ K ∧ (∀x:real. |f(x)| ≤ K * (&1 + x * x) ∧ |g(x)| ≤ K * (&1 + |x|))",
	}, func(a *Argument, f, g, h *Arrow[Real, Real], M *Expr[Real], fSlope, gSlope, bounded Fact) {
		zero := a.TermAs[Real]("&0")
		nonneg := a.Have(
			"M is nonnegative, as it bounds |h(0)|",
			"&0 ≤ M",
			ByArith(bounded.At(zero), real_sgn_abs.AbsNonneg.At(h.Apply(zero))))
		window := a.Have(
			"the open interval of radius |x| + 1 about 0 holds 0 and x",
			"∀x:real. -(|x| + &1) < &0 ∧ &0 < |x| + &1 ∧ -(|x| + &1) < x ∧ x < |x| + &1",
			Derive(func(b *Argument) {
				x := b.FixAs[Real]("x")
				b.Show(
					"−|x| ≤ x ≤ |x|, with |x| nonnegative",
					ByArith(
						real_sgn_abs.AbsNonneg.At(x),
						real_sgn_abs.AbsDominates.At(x),
						real_sgn_abs.AbsDominates.At(b.TermAs[Real]("-x")),
						real_sgn_abs.AbsEven.At(x)))
			}))
		within := a.Have(
			"and its points t have |t| ≤ |x| + 1",
			"∀x t:real. -(|x| + &1) < t ∧ t < |x| + &1 ⇒ |t| ≤ |x| + &1",
			Derive(func(b *Argument) {
				b.FixAs[Real]("x")
				t := b.FixAs[Real]("t")
				inside := b.Assume()
				b.Show(
					"|t| ≤ r exactly when −r ≤ t ≤ r",
					ByArith(inside, real_sgn_abs.AbsBounds.At(t, b.TermAs[Real]("|x| + &1"))))
			}))
		linearG := a.Have(
			"between 0 and x the mean value inequality bounds the change of g by M|x|",
			"∀x:real. |g(x)| ≤ |g(&0)| + M * |x|",
			Derive(func(b *Argument) {
				x := b.FixAs[Real]("x")
				change := b.Have(
					"|h| ≤ M on the interval of radius |x| + 1 about 0, which holds 0 and x",
					"|g(x) - g(&0)| ≤ M * |x - &0|",
					By(
						gSlope,
						bounded,
						window.At(x),
						MeanValueInequality.At(
							g, h, b.TermAs[Real]("-(|x| + &1)"), b.TermAs[Real]("|x| + &1"), M, zero, x)))
				b.Show(
					"and |g(x)| − |g(0)| is at most |g(x) − g(0)|",
					ByArith(
						change,
						real_ring.SubRightZero.At(x),
						real_sgn_abs.AbsReverseTriangle.At(g.Apply(x), g.Apply(zero)),
						real_sgn_abs.AbsDominates.At(b.TermAs[Real]("|g(x)| - |g(&0)|"))))
			}))
		quadraticF := a.Have(
			"read for f on the same interval, the mean value inequality bounds the change of f",
			"∀x:real. |f(x)| ≤ |f(&0)| + (|g(&0)| + M * (|x| + &1)) * |x|",
			Derive(func(b *Argument) {
				x := b.FixAs[Real]("x")
				radius := b.TermAs[Real]("|x| + &1")
				slopes := b.Have(
					"on the interval of radius |x| + 1 about 0, |g| is at most |g(0)| + M(|x| + 1)",
					"∀t:real. -(|x| + &1) < t ∧ t < |x| + &1 ⇒ |g(t)| ≤ |g(&0)| + M * (|x| + &1)",
					Derive(func(c *Argument) {
						t := c.FixAs[Real]("t")
						inside := c.Assume()
						near := c.Have(
							"t lies within |x| + 1 of 0",
							"|t| ≤ |x| + &1",
							By(inside, within.At(x, t)))
						c.Show(
							"|g(t)| ≤ |g(0)| + M|t|, and M|t| ≤ M(|x| + 1)",
							ByArith(
								linearG.At(t),
								real_order_ring.LessEqMulLeft.At(M, c.TermAs[Real]("|t|"), radius),
								nonneg,
								near))
					}))
				change := b.Have(
					"so the change of f between 0 and x is at most that bound times |x|",
					"|f(x) - f(&0)| ≤ (|g(&0)| + M * (|x| + &1)) * |x - &0|",
					By(
						fSlope,
						slopes,
						window.At(x),
						MeanValueInequality.At(
							f,
							g,
							b.TermAs[Real]("-(|x| + &1)"),
							radius,
							b.TermAs[Real]("|g(&0)| + M * (|x| + &1)"),
							zero,
							x)))
				b.Show(
					"and |f(x)| − |f(0)| is at most |f(x) − f(0)|",
					ByArith(
						change,
						real_ring.SubRightZero.At(x),
						real_sgn_abs.AbsReverseTriangle.At(f.Apply(x), f.Apply(zero)),
						real_sgn_abs.AbsDominates.At(b.TermAs[Real]("|f(x)| - |f(&0)|"))))
			}))
		sizes := a.Have(
			"|f(0)| and |g(0)| are nonnegative",
			"&0 ≤ |f(&0)| ∧ &0 ≤ |g(&0)|",
			By(real_sgn_abs.AbsNonneg.At(f.Apply(zero)), real_sgn_abs.AbsNonneg.At(g.Apply(zero))))
		K, kDef := a.LetAs[Real]("K", "&2 * (|f(&0)| + |g(&0)| + M + &1)")
		positive := a.Have(
			"so K is nonnegative, M being so",
			"&0 ≤ K",
			kDef.Rw(),
			ByArith(sizes, nonneg))
		fBound := a.Have(
			"K(1 + x²) dominates the bound on |f|, since |x| ≤ 1 + x²",
			"∀x:real. |f(x)| ≤ K * (&1 + x * x)",
			Derive(func(b *Argument) {
				x := b.FixAs[Real]("x")
				square := b.TermAs[Real]("&1 + x * x")
				absX := b.TermAs[Real]("|x|")
				linear := b.Have(
					"|x| ≤ 1 + x², so |g(0)||x| and M|x| are at most |g(0)|(1 + x²) and M(1 + x²)",
					"|g(&0)| * |x| ≤ |g(&0)| * (&1 + x * x) ∧ M * |x| ≤ M * (&1 + x * x)",
					By(
						sizes,
						nonneg,
						real_sgn_abs.AbsQuadraticBound.At(x),
						real_order_ring.LessEqMulLeft.At(b.TermAs[Real]("|g(&0)|"), absX, square),
						real_order_ring.LessEqMulLeft.At(M, absX, square)))
				xSquared := b.TermAs[Real]("x * x")
				signs := b.Have(
					"|f(0)|x² and |g(0)|x² are nonnegative",
					"&0 ≤ |f(&0)| * (x * x) ∧ &0 ≤ |g(&0)| * (x * x)",
					By(
						sizes,
						real_order_ring.SquareNonneg.At(x),
						real_construction.LessEqMul.At(b.TermAs[Real]("|f(&0)|"), xSquared),
						real_construction.LessEqMul.At(b.TermAs[Real]("|g(&0)|"), xSquared)))
				b.Show(
					"|f(0)| + |g(0)||x| + M|x|² + M|x| is at most 2(|f(0)| + |g(0)| + M + 1)(1 + x²)",
					kDef.Rw(),
					ByArith(quadraticF.At(x), sizes, signs, nonneg, linear, Scaled(M, real_pow.SquareOfAbs.At(x))))
			}))
		gBound := a.Have(
			"K(1 + |x|) dominates the bound on |g|",
			"∀x:real. |g(x)| ≤ K * (&1 + |x|)",
			Derive(func(b *Argument) {
				x := b.FixAs[Real]("x")
				b.Show(
					"|g(0)| + M|x| is at most 2(|f(0)| + |g(0)| + M + 1)(1 + |x|)",
					kDef.Rw(),
					ByArith(linearG.At(x), sizes, nonneg, real_sgn_abs.AbsNonneg.At(x)))
			}))
		a.Take(K)
		a.Show(
			"K is nonnegative and bounds both",
			By(positive, fBound, gBound))
	}),
})}
