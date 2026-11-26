// caratheodory.go — Carathéodory's characterization of the derivative:
// f has derivative l at c exactly when f(x) − f(c) factors as
// φ(x)·(x − c) through a function φ continuous at c with φ(c) = l. The
// chain rule is read through it: the factorizations of the inner and
// the outer function compose into one for the composite, and so is the
// derivative of an inverse function (DerivativeInverse).

package real_derivative

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_field"
	"github.com/euc-ai/xugo/library/proofs/real/real_function_limits"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/tower/real_construction"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// DerivativeCaratheodory — the derivative at c is the value at c of a
// slope function continuous there: one whose product with x − c is the
// increment of f from c.
//
// Off the centre the factorization says that φ(x) IS the difference
// quotient, and a limit at c ignores the value at c: so the quotient
// tends to l at c — the derivative — exactly when φ does, which is φ's
// continuity at c once φ(c) = l. Forward, φ is the quotient patched at
// the centre with the value l; backward, φ is given, and dividing the
// factorization by x − c ≠ 0 shows the quotient agrees with it off c.
var DerivativeCaratheodory = derivativeCaratheodoryThm{family.Add(registry.ProofEntry{
	Name: "DerivativeCaratheodory",
	Key:  "prop_6bf63e3a28d0d420",
	Build: family.Sections("∀f:(real → real). ∀c l:real. "+
		"    real_derivative_at(f, c, l) ⇔ "+
		"    ∃φ:(real → real). "+
		"        (∀x:real. f(x) - f(c) = φ(x) * (x - c)) ∧ real_continuous_at(φ, c) ∧ φ(c) = l",
		func(ctx *Script, headline string) *GoalStackNode {
			// A limit at c ignores the value at c: a function that agrees
			// with f off the centre has f's limits there.
			offCentre := ctx.Lemma(Statement{
				Binders: "∀f g:(real → real). ∀c l:real.",
				Hypotheses: []string{
					"∀x:real. x ≠ c ⇒ f(x) = g(x)",
					"f ⟶ l (at c)",
				},
				Conclusion: "g ⟶ l (at c)",
			},
				func(a *Argument, f, g *Arrow[Real, Real], c, l *Expr[Real], given Fact) {
					parts := a.Conjuncts(
						given,
						"f and g agree off the centre",
						"f ⟶ l (at c)")
					ball := a.Have(
						"in particular f and g agree on the punctured ball of radius 1",
						"∀x:real. &0 < |x - c| ∧ |x - c| < &1 ⇒ f(x) = g(x)",
						Derive(func(b *Argument) {
							x := b.FixAs[Real]()
							punctured := b.Assume()
							b.Show(
								"a point at positive distance from c is not c, where f and g agree",
								By(
									parts[0].At(x),
									punctured,
									real_sgn_abs.AbsPosIffNonzero.At(b.TermAs[Real]("x - c")),
									real_ring.SubEqZero.At(x, c)))
						}))
					same := a.Have(
						"so f and g have the same limits at c",
						"real_limit_at(f, c) = real_limit_at(g, c)",
						By(real_function_limits.LimitAtLocal, real_order_ring.ZeroLessThanOne, ball))
					a.Show(
						"and f's limit l is g's",
						same.RwRev(),
						By(parts[1]))
				})

			return ctx.Theorem(headline,
				func(a *Argument, f *Arrow[Real, Real], c, l *Expr[Real]) {
					quotient := a.TermAs[Fun[Real, Real]]("λx:real. (f(x) - f(c)) / (x - c)")
					a.Iff()

					a.Forward(
						"φ is the difference quotient, patched at the centre with the value l",
						func(b *Argument, derivative Fact) {
							quotientTends := b.Unfolded(derivative, RealDerivativeAtDef)
							slope := b.TermAs[Fun[Real, Real]]("λx:real. COND(x = c, l, (f(x) - f(c)) / (x - c))")
							b.Take(slope)
							b.Do(SplitConjAll(
								Case(
									"f(x) − f(c) = φ(x)·(x − c) at every x",
									Derive(func(d *Argument) {
										d.FixAs[Real]()
										d.Cases(d.Term("x = c"))
										d.When(
											"at the centre both sides vanish",
											func(e *Argument, atCentre Fact) {
												e.Show(
													"f(c) − f(c) = 0 = l·(c − c)",
													atCentre.Subst(),
													ByArith())
											})
										d.Otherwise(
											"off the centre φ(x) is the quotient, and x − c ≠ 0 multiplies it back to f(x) − f(c)",
											func(e *Argument, offC Fact) {
												e.Show(
													"the quotient times x − c is f(x) − f(c)",
													ByArith(offC))
											})
									})),
								Case(
									"φ agrees with the quotient off c, so tends to its limit l = φ(c): φ is continuous at c",
									By(
										real_continuous.ContinuousAtIffLimit.At(slope, c),
										At(offCentre, quotient, slope, c, l),
										quotientTends)),
								Case(
									"φ(c) = l: at the centre φ takes the value l",
									TrivialNormalized()),
							))
						})

					a.Backward(
						"off the centre the quotient is φ(x), and φ tends to φ(c) = l",
						func(b *Argument, factored Fact) {
							phi, held := b.UnpackAs[Fun[Real, Real]](factored)
							parts := b.Conjuncts(
								held,
								"f(x) − f(c) = φ(x)·(x − c) at every x",
								"φ is continuous at c",
								"φ(c) = l")
							phiTends := b.Have(
								"φ is continuous at c with value l there, so φ ⟶ l (at c)",
								"φ ⟶ l (at c)",
								By(Normalized, real_continuous.ContinuousAtIffLimit.At(phi, c), parts[1], parts[2]))
							agree := b.Have(
								"off the centre φ(x) is the difference quotient",
								"∀x:real. x ≠ c ⇒ φ(x) = (f(x) - f(c)) / (x - c)",
								Derive(func(d *Argument) {
									x := d.FixAs[Real]()
									offC := d.Assume()
									factoredAt := d.Have(
										"f(x) − f(c) = φ(x)·(x − c) at this x",
										"f(x) - f(c) = φ(x) * (x - c)",
										By(parts[0].At(x)))
									d.Do(factoredAt.Rw())
									d.Show(
										"the numerator is φ(x)·(x − c), and x − c is not 0: the quotient is φ(x)",
										ByArith(offC))
								}))
							b.Show(
								"the derivative is the quotient's limit, and the "+
									"quotient agrees with φ off c, so tends to l as φ does",
								Unfold(RealDerivativeAtDef),
								By(At(offCentre, phi, quotient, c, l), agree, phiTends))
						})
				})
		}),
})}

// DerivativeChain — the chain rule: the derivative of f ∘ g at c is the
// derivative of f at g(c) times the derivative of g at c.
//
// Read both derivatives through Carathéodory: g's increment from c is
// ψ(x)·(x − c) with ψ continuous at c and ψ(c) = m, and f's increment from
// g(c) is φ(y)·(y − g(c)) with φ continuous at g(c) and φ(g(c)) = l. At the
// point y = g(x) the two factorizations compose, so the slope
// χ(x) = φ(g(x))·ψ(x) factors the increment of f ∘ g from c. It is
// continuous at c — g is continuous there, having a derivative, so φ ∘ g
// is, and so is its product with ψ — and χ(c) = φ(g(c))·ψ(c) = l·m.
// The goal, rewritten by Carathéodory into its slope form at f ∘ g, asks for
// such a slope with value l·m, and χ is one.
var DerivativeChain = derivativeChainThm{family.Add(registry.ProofEntry{
	Name: "DerivativeChain",
	Key:  "prop_e6017dc2f5a1c09c",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀c l m:real.",
		Hypotheses: []string{
			"real_derivative_at(g, c, m)",
			"real_derivative_at(f, g(c), l)",
		},
		Conclusion: "real_derivative_at(f ∘ g, c, l * m)",
	},
		func(a *Argument, f, g *Arrow[Real, Real], c, l, m *Expr[Real], derivatives Fact) {
			parts := a.Conjuncts(
				derivatives,
				"g has derivative m at c",
				"f has derivative l at g(c)")
			innerSlope := a.Have(
				"g's increment from c factors through a slope ψ continuous at c, with ψ(c) = m",
				"∃ψ:(real → real). (∀x:real. g(x) - g(c) = ψ(x) * (x - c)) ∧ real_continuous_at(ψ, c) ∧ ψ(c) = m",
				// The claim rewritten back to a derivative, which the hypothesis is.
				Simp(Rev(DerivativeCaratheodory)),
				By(parts[0]))
			_, psiFactors := a.Unpack(innerSlope)
			psi := a.Conjuncts(
				psiFactors,
				"g(x) − g(c) = ψ(x)·(x − c) at every x",
				"ψ is continuous at c",
				"ψ(c) = m")
			outerSlope := a.Have(
				"f's increment from g(c) factors through a slope φ continuous at g(c), with φ(g(c)) = l",
				"∃φ:(real → real). "+
					"    (∀y:real. f(y) - f(g(c)) = φ(y) * (y - g(c))) ∧ real_continuous_at(φ, g(c)) ∧ φ(g(c)) = l",
				Simp(Rev(DerivativeCaratheodory)),
				By(parts[1]))
			_, phiFactors := a.Unpack(outerSlope)
			phi := a.Conjuncts(
				phiFactors,
				"f(y) − f(g(c)) = φ(y)·(y − g(c)) at every y",
				"φ is continuous at g(c)",
				"φ(g(c)) = l")

			composed := a.Have(
				"the factorizations compose: the increment of f ∘ g from c is φ(g(x))·ψ(x)·(x − c) at every x",
				"∀x:real. (f ∘ g)(x) - (f ∘ g)(c) = φ(g(x)) * ψ(x) * (x - c)",
				Derive(func(b *Argument) {
					x := b.FixAs[Real]()
					b.Show(
						"f's factorization at the point g(x), then g's at x",
						CalcEq(
							Leg(
								b.TermAs[Real]("f(g(x)) - f(g(c))"),
								"the values of f ∘ g are the values of f at those of g",
								Unfold(functions.ComposeApply)),
							Leg(
								b.TermAs[Real]("φ(g(x)) * (g(x) - g(c))"),
								"f's increment from g(c) to g(x) is φ(g(x)) times g's increment",
								By(phi[0].At(g.Apply(x)))),
							Leg(
								b.TermAs[Real]("φ(g(x)) * (ψ(x) * (x - c))"),
								"and g's increment from c to x is ψ(x)·(x − c)",
								By(Normalized, psi[0].At(x))),
							FinalLeg(
								"regroup the product",
								Cite(real_construction.MulAssoc)),
						))
				}))

			composite := a.Have(
				"g, having a derivative at c, is continuous there, so φ ∘ g is too, φ being continuous at g(c)",
				"real_continuous_at(φ ∘ g, c)",
				By(real_continuous.ContinuousAtCompose, DerivativeContinuous.At(g, c, m), parts[0], phi[1]))
			phiOfG := a.Unfolded(composite, functions.ComposeApply)
			slopeContinuous := a.Have(
				"the slope χ(x) = φ(g(x))·ψ(x) is continuous at c, the product of x ↦ φ(g(x)) and ψ",
				"real_continuous_at(λx:real. φ(g(x)) * ψ(x), c)",
				By(real_continuous.ContinuousAtMul, phiOfG, psi[1]))
			value := a.Have(
				"and at c the slope is φ(g(c))·ψ(c) = l·m",
				"φ(g(c)) * ψ(c) = l * m",
				By(Normalized, phi[2], psi[2]))

			// The goal rewritten into its slope form.
			a.Do(Simp(Fwd(DerivativeCaratheodory)))
			a.Take(a.TermAs[Fun[Real, Real]]("λx:real. φ(g(x)) * ψ(x)"))
			a.Show(
				"χ factors the increment of f ∘ g, is continuous at c and takes the value l·m there",
				By(composed, slopeContinuous, value))
		}),
})}

// DerivativeInverse — the derivative of an inverse function: where f has
// derivative l ≠ 0 at g(y), g is continuous at y and f undoes g on a ball
// about y, g has derivative 1/l at y.
//
// Read f's derivative through Carathéodory: f(z) − f(g(y)) = φ(z)·(z − g(y))
// with φ continuous at g(y) and φ(g(y)) = l. For x in the ball f undoes g at
// x and at y, so at z = g(x) the factorization reads
// x − y = φ(g(x))·(g(x) − g(y)). Off the centre x − y is not 0, so φ(g(x))
// times g's difference quotient is (x − y)/(x − y) = 1: on the punctured
// ball the quotient IS 1/φ(g(x)), and that φ(g(x)) ≠ 0 there comes with it.
// The slope x ↦ φ(g(x)) is continuous at y, g being continuous there, with
// value l ≠ 0, so its reciprocal tends to 1/l; a limit at y sees only the
// punctured ball, so g's quotient tends to 1/l too.
var DerivativeInverse = derivativeInverseThm{family.Add(registry.ProofEntry{
	Name: "DerivativeInverse",
	Key:  "prop_4ea66aa975aa3397",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(real → real). ∀y l d:real.",
		Hypotheses: []string{
			"real_derivative_at(f, g(y), l)",
			"l ≠ &0",
			"real_continuous_at(g, y)",
			"&0 < d",
			"∀x:real. |x - y| < d ⇒ f(g(x)) = x",
		},
		Conclusion: "real_derivative_at(g, y, real_inv(l))",
	},
		func(a *Argument, f, g *Arrow[Real, Real], y, l, d *Expr[Real], given Fact) {
			held := a.Conjuncts(
				given,
				"f has derivative l at g(y)",
				"l is not 0",
				"g is continuous at y",
				"the radius d is positive",
				"f undoes g on the ball of radius d about y")
			derivative, nonzero, gContinuous, radius, undoes := held[0], held[1], held[2], held[3], held[4]

			_, slope := a.Obtain(
				"f's increment from g(y) factors through a slope φ continuous at g(y), with φ(g(y)) = l",
				"∃φ:(real → real). "+
					"    (∀z:real. f(z) - f(g(y)) = φ(z) * (z - g(y))) ∧ real_continuous_at(φ, g(y)) ∧ φ(g(y)) = l",
				// The claim rewritten back to a derivative, which the hypothesis is.
				Simp(Rev(DerivativeCaratheodory)),
				By(derivative))
			phi := a.Conjuncts(
				slope,
				"f(z) − f(g(y)) = φ(z)·(z − g(y)) at every z",
				"φ is continuous at g(y)",
				"φ(g(y)) = l")
			increment, phiContinuous, phiValue := phi[0], phi[1], phi[2]

			centre := a.Have(
				"y lies in the ball, so f undoes g at y itself",
				"f(g(y)) = y",
				ByArith(undoes.At(y), radius))
			factored := a.Have(
				"on the ball, f's factorization at g(x) factors x − y through g's increment",
				"∀x:real. |x - y| < d ⇒ x - y = φ(g(x)) * (g(x) - g(y))",
				Derive(func(b *Argument) {
					x := b.FixAs[Real]()
					inBall := b.Assume()
					b.Show(
						"x − y = f(g(x)) − f(g(y)), which is f's factorization at g(x)",
						By(increment.At(g.Apply(x)), undoes.At(x), inBall, centre))
				}))
			reciprocal := a.Have(
				"so off the centre g's difference quotient is 1/φ(g(x))",
				"∀x:real. &0 < |x - y| ∧ |x - y| < d ⇒ (g(x) - g(y)) / (x - y) = real_inv(φ(g(x)))",
				Derive(func(b *Argument) {
					x := b.FixAs[Real]()
					punctured := b.Assume()
					product := b.Have(
						"φ(g(x)) times the quotient is 1",
						"φ(g(x)) * ((g(x) - g(y)) / (x - y)) = &1",
						CalcEq(
							Leg(
								b.TermAs[Real]("φ(g(x)) * (g(x) - g(y)) / (x - y)"),
								"the factor φ(g(x)) joins the numerator",
								ByArith()),
							Leg(
								b.TermAs[Real]("(x - y) / (x - y)"),
								"the numerator is x − y",
								By(factored.At(x), punctured)),
							FinalLeg(
								"and x − y is not 0",
								ByArith(punctured)),
						))
					b.Show(
						"a number whose product with φ(g(x)) is 1 is its reciprocal",
						By(field.InvRightUnique.Read(real_field.Field), product))
				}))

			composite := a.Have(
				"g is continuous at y and φ at g(y), so φ ∘ g is continuous at y",
				"real_continuous_at(φ ∘ g, y)",
				By(real_continuous.ContinuousAtCompose, gContinuous, phiContinuous))
			slopeContinuous := a.Unfolded(composite, functions.ComposeApply)
			slopeAlongG := a.TermAs[Fun[Real, Real]]("λx:real. φ(g(x))")
			slopeLimit := a.Have(
				"so φ(g(x)) tends to its value φ(g(y)) = l",
				"(λx:real. φ(g(x))) ⟶ l (at y)",
				By(Normalized, real_continuous.ContinuousAtIffLimit.At(slopeAlongG, y), slopeContinuous, phiValue))
			inverseLimit := a.Have(
				"and, l being not 0, its reciprocal tends to 1/l",
				"(λx:real. real_inv(φ(g(x)))) ⟶ real_inv(l) (at y)",
				By(real_function_limits.LimitAtInv, slopeLimit, nonzero))
			sameLimits := a.Have(
				"a limit at y sees only the punctured ball, where g's quotient is 1/φ(g(x))",
				"real_limit_at(λx:real. (g(x) - g(y)) / (x - y), y) = real_limit_at(λx:real. real_inv(φ(g(x))), y)",
				By(real_function_limits.LimitAtLocal, radius, reciprocal))
			a.Show(
				"the derivative is the limit of g's quotient, which is that of 1/φ(g(x)): 1/l",
				// Simp, not Unfold as in DerivativeCaratheodory: a goal-side Unfold also
				// rewrites the resident facts, f's derivative among them, and closes unseen.
				Simp(Fwd(RealDerivativeAtDef)),
				sameLimits.Rw(),
				By(inverseLimit))
		}),
})}
