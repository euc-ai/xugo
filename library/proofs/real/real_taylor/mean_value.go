// mean_value.go — Cauchy's mean value theorem and its corollary, L'Hôpital's rule.

package real_taylor

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_function_limits"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/registry"
)

// CauchyMeanValue — Cauchy's mean value theorem: somewhere strictly
// between a and b the derivatives of f and g stand in the ratio of the
// increments of f and g over ⟦a, b⟧.
//
// h(x) = (f(b) − f(a))·g(x) − (g(b) − g(a))·f(x) takes the value
// f(b)·g(a) − g(b)·f(a) at both ends. It is continuous on ⟦a, b⟧, a
// difference of products of continuous functions, its constant factors
// among them, and it has derivative (f(b) − f(a))·g'(y) − (g(b) − g(a))·f'(y)
// strictly inside.
// Rolle's theorem gives a point where that derivative is 0.
var CauchyMeanValue = cauchyMeanValueThm{family.Add(registry.ProofEntry{
	Name: "CauchyMeanValue",
	Key:  "prop_fe8b476e0b573750",
	Build: family.Theorem(Statement{
		Binders: "∀f g f' g':(real → real). ∀a b:real.",
		Hypotheses: []string{
			"a < b",
			"real_continuous_on(⟦a, b⟧, f)",
			"real_continuous_on(⟦a, b⟧, g)",
			"∀x:real. a < x ∧ x < b ⇒ real_derivative_at(f, x, f'(x)) ∧ real_derivative_at(g, x, g'(x))",
		},
		Conclusion: "∃z:real. a < z ∧ z < b ∧ (f(b) - f(a)) * g'(z) = (g(b) - g(a)) * f'(z)",
		Abbrev: Abbrev{
			{Name: "h", Text: "λx:real. (f(b) - f(a)) * g(x) - (g(b) - g(a)) * f(x)"},
		},
	},
		func(arg *Argument, f, g, fPrime, gPrime *Arrow[Real, Real], a, b *Expr[Real],
			ordered, fContinuous, gContinuous, derivatives Fact) {
			segment := arg.TermAs[Set[Real]]("⟦a, b⟧")
			riseF := arg.TermAs[Fun[Real, Real]]("λx:real. f(b) - f(a)")
			riseG := arg.TermAs[Fun[Real, Real]]("λx:real. g(b) - g(a)")
			h := arg.TermAs[Fun[Real, Real]]("«h»")
			hPrime := arg.TermAs[Fun[Real, Real]]("λx:real. (f(b) - f(a)) * g'(x) - (g(b) - g(a)) * f'(x)")

			hContinuous := arg.Have(
				"h, a difference of products of f and g with constants, is continuous on ⟦a, b⟧",
				"real_continuous_on(⟦a, b⟧, «h»)",
				By(
					fContinuous,
					gContinuous,
					real_continuous.ContinuousOnConst.At(arg.TermAs[Real]("f(b) - f(a)"), segment),
					real_continuous.ContinuousOnConst.At(arg.TermAs[Real]("g(b) - g(a)"), segment),
					real_continuous.ContinuousOnMul.At(riseF, g, segment),
					real_continuous.ContinuousOnMul.At(riseG, f, segment),
					real_continuous.ContinuousOnSub.At(
						arg.TermAs[Fun[Real, Real]]("λx:real. (f(b) - f(a)) * g(x)"),
						arg.TermAs[Fun[Real, Real]]("λx:real. (g(b) - g(a)) * f(x)"),
						segment)))
			hDerivative := arg.Have(
				"and h has derivative (f(b) − f(a))·g'(y) − (g(b) "+
					"− g(a))·f'(y) at every y strictly between a and b",
				Statement{
					Binders: "∀y:real.",
					Hypotheses: []string{
						"a < y",
						"y < b",
					},
					Conclusion: "real_derivative_at(«h», y, (f(b) - f(a)) * g'(y) - (g(b) - g(a)) * f'(y))",
				},
				Derive(func(d *Argument) {
					y := d.FixAs[Real]()
					inside := d.Assume()
					scaledG := d.TermAs[Real]("(f(b) - f(a)) * g'(y)")
					scaledF := d.TermAs[Real]("(g(b) - g(a)) * f'(y)")
					d.Show(
						"the difference of the scaled derivatives of g and f",
						By(
							derivatives.At(y),
							inside,
							real_derivative.DerivativeScale.At(g, y, gPrime.Apply(y), d.TermAs[Real]("f(b) - f(a)")),
							real_derivative.DerivativeScale.At(f, y, fPrime.Apply(y), d.TermAs[Real]("g(b) - g(a)")),
							real_derivative.DerivativeSub.At(
								d.TermAs[Fun[Real, Real]]("λx:real. (f(b) - f(a)) * g(x)"),
								d.TermAs[Fun[Real, Real]]("λx:real. (g(b) - g(a)) * f(x)"),
								y,
								scaledG,
								scaledF)))
				}))
			level := arg.Have(
				"h takes the value f(b)·g(a) − g(b)·f(a) at both ends",
				"(f(b) - f(a)) * g(a) - (g(b) - g(a)) * f(a) = (f(b) - f(a)) * g(b) - (g(b) - g(a)) * f(b)",
				ByArith())

			z, found := arg.ObtainAs[Real](
				"Rolle's theorem for h hands a point z strictly between a and b where its derivative vanishes",
				"∃z:real. a < z ∧ z < b ∧ (f(b) - f(a)) * g'(z) - (g(b) - g(a)) * f'(z) = &0",
				By(real_derivative.Rolle.At(h, hPrime, a, b), ordered, level, hContinuous, hDerivative))
			arg.Take(z)
			arg.Show(
				"there the two products of an increment and a derivative agree",
				ByArith(found))
		}),
})}

// LHopital — L'Hôpital's rule for 0/0 at a point: where f and g vanish
// at c and are continuous there, have derivatives on a punctured ball
// about c with g' nowhere 0, and f'/g' tends to L at c, f/g tends to L
// at c as well.
//
// For 0 < |x − c| < d, f and g are continuous at every point between c
// and x — at c by hypothesis, elsewhere because they have derivatives
// there — so Cauchy's mean value theorem on that interval gives z
// strictly between c and x with f(x)·g'(z) = g(x)·f'(z), f(c) and g(c)
// being 0; g(x) ≠ 0, or Rolle's theorem would give g' a zero between c
// and x. So f(x)/g(x) = f'(z)/g'(z) with 0 < |z − c| < |x − c|, and the
// radius that serves f'/g' at ε, cut down to d, serves f/g.
var LHopital = lHopitalThm{family.Add(registry.ProofEntry{
	Name: "LHopital",
	Key:  "prop_c25ad39f8fdfd8c4",
	Build: family.Sections(Statement{
		Binders: "∀f g f' g':(real → real). ∀c d L:real.",
		Hypotheses: []string{
			"&0 < d",
			"f(c) = &0",
			"g(c) = &0",
			"real_continuous_at(f, c)",
			"real_continuous_at(g, c)",
			"∀x:real. " +
				"    &0 < |x - c| ∧ |x - c| < d ⇒ " +
				"    real_derivative_at(f, x, f'(x)) ∧ real_derivative_at(g, x, g'(x)) ∧ g'(x) ≠ &0",
			"(λx:real. f'(x) / g'(x)) ⟶ L (at c)",
		},
		Conclusion: "(λx:real. f(x) / g(x)) ⟶ L (at c)",
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// Cauchy's mean value theorem on an interval ⟦a, b⟧ whose two ends
			// are c and x, in either order, inside the ball of radius d about
			// c where f and g are continuous and, off c, have derivatives with
			// g' nowhere 0 — and then g takes different values at the ends.
			ratio := ctx.Lemma(Statement{
				Binders: "∀f g f' g':(real → real). ∀a b c d x:real.",
				Hypotheses: []string{
					"a < b",
					"c = a ∧ x = b ∨ c = b ∧ x = a",
					"|x - c| < d",
					"∀y:real. |y - c| < d ⇒ real_continuous_at(f, y) ∧ real_continuous_at(g, y)",
					"∀y:real. " +
						"    &0 < |y - c| ∧ |y - c| < d ⇒ " +
						"    real_derivative_at(f, y, f'(y)) ∧ real_derivative_at(g, y, g'(y)) ∧ g'(y) ≠ &0",
				},
				Conclusion: "g(a) ≠ g(b) ∧ ∃z:real. a < z ∧ z < b ∧ (f(b) - f(a)) * g'(z) = (g(b) - g(a)) * f'(z)",
			},
				func(arg *Argument, f, g, fPrime, gPrime *Arrow[Real, Real], a, b, c, d, x *Expr[Real],
					ordered, ends, near, ballContinuity, ballDerivatives Fact) {
					segment := arg.TermAs[Set[Real]]("⟦a, b⟧")
					continuous := arg.Have(
						"⟦a, b⟧ lies within d of c, x being its far end, so f and g are continuous at each of its points",
						"∀y:real. a ≤ y ∧ y ≤ b ⇒ real_continuous_at(f, y) ∧ real_continuous_at(g, y)",
						Derive(func(h *Argument) {
							y := h.FixAs[Real]()
							between := h.Assume()
							h.Show(
								"y is no farther from c than x",
								ByArith(ballContinuity.At(y), between, ends, near))
						}))
					derivatives := arg.Have(
						"strictly inside ⟦a, b⟧ a point is off c and within d "+
							"of it, so f and g have derivatives there and g' is not 0",
						Statement{
							Binders: "∀y:real.",
							Hypotheses: []string{
								"a < y",
								"y < b",
							},
							Conclusion: "real_derivative_at(f, y, f'(y)) ∧ real_derivative_at(g, y, g'(y)) ∧ g'(y) ≠ &0",
						},
						Derive(func(h *Argument) {
							y := h.FixAs[Real]()
							between := h.Assume()
							h.Show(
								"y lies in the punctured ball",
								ByArith(ballDerivatives.At(y), between, ends, near))
						}))
					onSegment := arg.Have(
						"f and g, continuous at every point of ⟦a, b⟧, are continuous on it",
						"real_continuous_on(⟦a, b⟧, f) ∧ real_continuous_on(⟦a, b⟧, g)",
						By(
							continuous,
							real_continuous.ContinuousAtOn.At(f, segment),
							real_continuous.ContinuousAtOn.At(g, segment)))
					distinct := arg.Have(
						"g(a) ≠ g(b): were they equal, Rolle's theorem would give g' a zero strictly between a and b",
						"g(a) ≠ g(b)",
						Derive(func(e *Argument) {
							supposed := e.SupposeNot()
							equal := e.Have(
								"that is, g(a) = g(b)",
								"g(a) = g(b)",
								By(supposed))
							z, root := e.ObtainAs[Real](
								"Rolle's theorem for g gives z strictly between a and b with g'(z) = 0",
								"∃z:real. a < z ∧ z < b ∧ g'(z) = &0",
								By(real_derivative.Rolle.At(g, gPrime, a, b), ordered, equal, onSegment, derivatives))
							e.Show(
								"but g' vanishes nowhere strictly between a and b",
								By(root, derivatives.At(z)))
						}))
					arg.Show(
						"Cauchy's mean value theorem on ⟦a, b⟧ supplies the point",
						By(At(CauchyMeanValue, f, g, fPrime, gPrime, a, b), distinct, ordered, onSegment, derivatives))
				})

			return ctx.Theorem(headline, func(
				arg *Argument,
				f, g, fPrime, gPrime *Arrow[Real, Real],
				c, d, L *Expr[Real],
				radius, fZero, gZero, fAtC, gAtC, derivatives, quotientLimit Fact,
			) {
				ballContinuity := arg.Have(
					"f and g are continuous at every point within d of c — "+
						"at c by hypothesis, elsewhere having derivatives there",
					"∀y:real. |y - c| < d ⇒ real_continuous_at(f, y) ∧ real_continuous_at(g, y)",
					Derive(func(b *Argument) {
						y := b.FixAs[Real]()
						inBall := b.Assume()
						b.Cases(b.Term("y = c"))
						b.When(
							"at c continuity is given",
							func(e *Argument, atC Fact) {
								e.Show(
									"f and g are continuous at c",
									By(Normalized, atC, fAtC, gAtC))
							})
						b.Otherwise(
							"off c the point lies in the punctured ball, where f and g have derivatives",
							func(e *Argument, offC Fact) {
								punctured := e.Have(
									"y ≠ c puts y at a positive distance from c",
									"&0 < |y - c|",
									ByArith(offC))
								e.Show(
									"a function with a derivative at a point is continuous there",
									By(
										derivatives.At(y),
										punctured,
										inBall,
										real_derivative.DerivativeContinuous.At(f, y, fPrime.Apply(y)),
										real_derivative.DerivativeContinuous.At(g, y, gPrime.Apply(y))))
							})
					}))

				pointRatio := arg.Have(
					"near c, f(x)·g'(z) = g(x)·f'(z) at a point z nearer to c than x, and g(x) ≠ 0",
					Statement{
						Binders: "∀x:real.",
						Hypotheses: []string{
							"&0 < |x - c|",
							"|x - c| < d",
						},
						Conclusion: "∃z:real. &0 < |z - c| ∧ |z - c| < |x - c| ∧ g(x) ≠ &0 ∧ f(x) * g'(z) = g(x) * f'(z)",
					},
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						nearC := b.Assume()
						b.Cases(b.Term("x < c"))
						b.When(
							"x lies left of c: Cauchy's theorem on ⟦x, c⟧",
							func(e *Argument, left Fact) {
								ends := e.Have(
									"x is the left end of ⟦x, c⟧ and c the right",
									"c = x ∧ x = c ∨ c = c ∧ x = x",
									ByArith())
								parts := e.Conjuncts(
									GroupPremises(
										left, ends, nearC, ballContinuity, derivatives, At(ratio, f, g, fPrime, gPrime, x, c, c, d, x)),
									"g(x) ≠ g(c)",
									"some z strictly between x and c has (f(c) − f(x))·g'(z) = (g(c) − g(x))·f'(z)")
								z, at := e.UnpackAs[Real](parts[1], "z")
								e.Take(z)
								e.Show(
									"f(c) = g(c) = 0, and z is nearer to c than x",
									ByArith(at, parts[0], fZero, gZero))
							})
						b.Otherwise(
							"x lies right of c: Cauchy's theorem on ⟦c, x⟧",
							func(e *Argument, notLeft Fact) {
								right := e.Have(
									"x ≠ c, so c < x",
									"c < x",
									ByArith(notLeft, nearC))
								ends := e.Have(
									"c is the left end of ⟦c, x⟧ and x the right",
									"c = c ∧ x = x ∨ c = x ∧ x = c",
									ByArith())
								parts := e.Conjuncts(
									GroupPremises(
										right, ends, nearC, ballContinuity, derivatives, At(ratio, f, g, fPrime, gPrime, c, x, c, d, x)),
									"g(c) ≠ g(x)",
									"some z strictly between c and x has (f(x) − f(c))·g'(z) = (g(x) − g(c))·f'(z)")
								z, at := e.UnpackAs[Real](parts[1], "z")
								e.Take(z)
								e.Show(
									"f(c) = g(c) = 0, and z is nearer to c than x",
									ByArith(at, parts[0], fZero, gZero))
							})
					}))

				quotientNear := arg.Unfolded(quotientLimit, real_function_limits.RealLimitAtDef)
				arg.Do(Unfold(real_function_limits.RealLimitAtDef))
				eps := arg.FixAs[Real]()
				positive := arg.Assume()
				d0, served := arg.ObtainAs[Real](
					"f'/g' ⟶ L (at c) at ε hands over a radius δ₀ inside which, off c, f'/g' is within ε of L",
					"∃δ:real. &0 < δ ∧ ∀x:real. &0 < |x - c| ∧ |x - c| < δ ⇒ |f'(x) / g'(x) - L| < ε",
					By(quotientNear.At(eps), positive))
				bound := arg.Conjuncts(
					served,
					"δ₀ is positive",
					"off c and within δ₀ of it, f'/g' is within ε of L")
				arg.Take(arg.TermAs[Real]("min(δ₀, d)"))
				arg.Do(SplitConj(
					Case(
						"the smaller of δ₀ and d is positive",
						ByArith(bound[0], radius, real_sup_inf.LessThanMin.At(d0, d, arg.TermAs[Real]("&0")))),
					Case(
						"and off c and within it, f/g is within ε of L",
						Derive(func(b *Argument) {
							x := b.FixAs[Real]()
							ball := b.Assume()
							within := b.Have(
								"x lies within δ₀ and within d of c",
								"|x - c| < δ₀ ∧ |x - c| < d",
								By(ball, real_sup_inf.LessThanMin.At(d0, d, b.TermAs[Real]("|x - c|"))))
							z, found := b.UnpackAs[Real](GroupPremises(ball, within, pointRatio.At(x)), "z")
							parts := b.Conjuncts(
								found,
								"z is off c",
								"z is nearer to c than x",
								"g(x) ≠ 0",
								"f(x)·g'(z) = g(x)·f'(z)")
							gPrimeNonzero := b.Have(
								"z lies in the punctured ball of radius d, where g' is not 0",
								"g'(z) ≠ &0",
								ByArith(derivatives.At(z), parts[0], parts[1], within))
							scaled := b.Have(
								"dividing by g'(z): f(x) = (f'(z)/g'(z))·g(x)",
								"f(x) = f'(z) / g'(z) * g(x)",
								ByArith(gPrimeNonzero, Scaled(b.TermAs[Real]("real_inv(g'(z))"), parts[3])))
							quotients := b.Have(
								"dividing by g(x): f(x)/g(x) = f'(z)/g'(z)",
								"f(x) / g(x) = f'(z) / g'(z)",
								ByArith(parts[2], Scaled(b.TermAs[Real]("real_inv(g(x))"), scaled)))
							b.Show(
								"f'(z)/g'(z) is within ε of L, z being off c and within δ₀ of it",
								ByArith(quotients, bound[1].At(z), parts[0], parts[1], within))
						})),
				))
			})
		}),
})}
