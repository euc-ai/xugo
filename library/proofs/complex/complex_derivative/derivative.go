// derivative.go — the derivative at a point: a function has at most one
// derivative there, and it is the linear approximation whose error is
// small against the distance (the increment form) and the value at the
// point of a slope continuous there (Carathéodory's form); a function is
// continuous where it has a derivative, and the derivative sees the
// function only near the point; the rules for constants, the identity,
// sums, negatives, differences, multiples, products, inverses and
// quotients; the chain rule; and the powers.
//
// The rules for sums, negatives, differences, multiples and products end
// the same way. Two facts are established first: the rearranged function's
// limit, and the equation between the goal's difference quotient and that
// function. The last step unfolds the goal to its limit statement,
// rewrites the goal's quotient by the equation into the rearranged
// function, and closes on that function's limit. The constant's rule ends
// so too, the constant 0's limit cited at the close. Where the equation
// holds only off the centre, or only near it — the identity, the inverse —
// it is asked there alone: a limit sees only a punctured disc, so the two
// functions have the same limits (complex_topology.LimitAtLocal), and the
// goal is rewritten by that equation of limits instead. The equations
// between quotients are closed by the ring of ℂ: it reads a quotient as
// its numerator times the inverse of its divisor, and a divisor x cancels
// against its inverse where the field's inverse law, read at x ≠ 0, is
// named beside it. Where x·x⁻¹ stands under a further factor once the
// identity is multiplied out, the law is named scaled by that cofactor,
// which the closer does not find for itself.

package complex_derivative

import (
	"github.com/euc-ai/xugo/ext"
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/algebra/field/field"
	"github.com/euc-ai/xugo/library/proofs/algebra/group/comm_monoid"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_abs"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_field"
	"github.com/euc-ai/xugo/library/proofs/complex/complex_topology"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_arith"
	"github.com/euc-ai/xugo/library/proofs/nat_num/nat_monus"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/proofs/sets/functions"
	"github.com/euc-ai/xugo/library/registry"
)

// DerivativeUnique — a function has at most one derivative at a point.
//
// Both are limits of the same difference quotient, and a limit is one
// number.
var DerivativeUnique = derivativeUniqueThm{family.Add(registry.ProofEntry{
	Name: "DerivativeUnique",
	Key:  "prop_2980e47b37b2545f",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c l m:complex.",
		Hypotheses: []string{
			"complex_derivative_at(f, c, l)",
			"complex_derivative_at(f, c, m)",
		},
		Conclusion: "l = m",
	},
		func(a *Argument, f *Arrow[Complex, Complex], c, l, m *Expr[Complex], derivatives Fact) {
			a.Show(
				"l and m are both limits of f's difference quotient at c",
				By(complex_topology.LimitAtUnique, a.Unfolded(derivatives, ComplexDerivativeAtDef)))
		}),
})}

// DerivativeIncrement — f has derivative l at c exactly when, for every
// ε > 0, near c the increment f(z) − f(c) lies within ε·|z − c| of
// l·(z − c).
//
// Off the centre the quotient less l, times z − c, is the increment less
// l·(z − c), so the increment's distance from l·(z − c) is the quotient's
// distance from l times |z − c| > 0; the one is below ε·|z − c| exactly
// when the other is below ε, and the definition's limit and this bound ask
// the same of the same punctured discs.
var DerivativeIncrement = derivativeIncrementThm{family.Add(registry.ProofEntry{
	Name: "DerivativeIncrement",
	Key:  "prop_34c96a6034c71bd0",
	Build: family.Theorem("∀f:(complex → complex). ∀c l:complex. "+
		"    complex_derivative_at(f, c, l) ⇔ "+
		"    ∀ε:real. "+
		"        &0 < ε ⇒ "+
		"        ∃δ:real. "+
		"            &0 < δ ∧ "+
		"            ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - f(c) - l * (z - c)| < ε * |z - c|",
		func(arg *Argument, f *Arrow[Complex, Complex], c, l *Expr[Complex]) {
			pointwise := arg.Have(
				"off the centre the quotient is within ε of l exactly "+
					"when the increment is within ε·|z − c| of l·(z − c)",
				Statement{
					Binders: "∀z:complex.",
					Hypotheses: []string{
						"&0 < |z - c|",
					},
					Conclusion: "∀ε:real. " +
						"    |(f(z) - f(c)) / (z - c) - l| < ε ⇔ |f(z) - f(c) - l * (z - c)| < ε * |z - c|",
				},
				Derive(func(b *Argument) {
					b.FixAs[Complex]()
					apart := b.Assume()
					ε := b.FixAs[Real]()
					offset := b.TermAs[Complex]("z - c")
					nonzero := b.Have(
						"z lies a positive distance from c, so z − c is not zero",
						"z - c ≠ &0",
						By(apart, complex_abs.AbsPosIffNonzero.At(offset)))
					deviation := b.TermAs[Complex]("(f(z) - f(c)) / (z - c) - l")
					cancelled := b.Have(
						"the quotient less l, times z − c, is the increment "+
							"less l·(z − c): z − c cancels against its inverse",
						"((f(z) - f(c)) / (z - c) - l) * (z - c) = f(z) - f(c) - l * (z - c)",
						ByArith(nonzero))
					size := b.Have(
						"so the increment's distance from l·(z − c) is the quotient's distance from l times |z − c|",
						"|f(z) - f(c) - l * (z - c)| = |(f(z) - f(c)) / (z - c) - l| * |z - c|",
						By(cancelled, complex_abs.AbsMul.At(deviation, offset)))
					b.Show(
						"and multiplying by the positive |z − c| keeps the order",
						By(
							size,
							real_order_ring.LessThanMulRightEq.At(
								b.TermAs[Real]("|(f(z) - f(c)) / (z - c) - l|"),
								ε,
								b.TermAs[Real]("|z - c|")),
							apart))
				}))

			arg.Do(Unfold(ComplexDerivativeAtDef), Unfold(complex_topology.ComplexLimitAtDef))
			arg.Iff()
			arg.Forward(
				"a radius that keeps the quotient within ε of l keeps the increment within ε·|z − c| of l·(z − c)",
				func(b *Argument, quotients Fact) {
					ε := b.FixAs[Real]()
					pos := b.Assume()
					δ, ball := b.ObtainAs[Real](
						"a radius inside which the quotient is within ε of l",
						"∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |(f(z) - f(c)) / (z - c) - l| < ε",
						By(quotients.At(ε), pos),
						Named("δ"))
					b.Take(δ)
					b.Show(
						"the same radius serves the increment, point by point",
						By(pointwise, ball))
				})
			arg.Backward(
				"a radius that keeps the increment within ε·|z − c| of l·(z − c) keeps the quotient within ε of l",
				func(b *Argument, increments Fact) {
					ε := b.FixAs[Real]()
					pos := b.Assume()
					δ, ball := b.ObtainAs[Real](
						"a radius inside which the increment is within ε·|z − c| of l·(z − c)",
						"∃δ:real. "+
							"    &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - f(c) - l * (z - c)| < ε * |z - c|",
						By(increments.At(ε), pos),
						Named("δ"))
					b.Take(δ)
					b.Show(
						"the same radius serves the quotient, point by point",
						By(pointwise, ball))
				})
		}),
})}

// DerivativeFromQuadraticRemainder — f has derivative L at c when, on a
// disc about c, the increment f(c + h) − f(c) is L·h to within a constant
// times |h|². Shown on the increment form: given ε, the radius is
// min(d, ε/(|K| + 1)) — |K| + 1 rather than K, so that the quotient is
// defined and positive whatever the sign of K. For z ≠ c in that disc put
// h = z − c: the increment's distance from L·h is at most K·|h|², at most
// (|K| + 1)·|h|·|h|, which is below ε·|h| since (|K| + 1)·|h| < ε and
// |h| > 0.
var DerivativeFromQuadraticRemainder = derivativeFromQuadraticRemainderThm{family.Add(registry.ProofEntry{
	Name: "DerivativeFromQuadraticRemainder",
	Key:  "prop_8a3de35110473f04",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c L:complex. ∀K d:real.",
		Hypotheses: []string{
			"&0 < d",
			"∀h:complex. |h| < d ⇒ |f(c + h) - f(c) - L * h| ≤ K * real_pow(|h|, 2)",
		},
		Conclusion: "complex_derivative_at(f, c, L)",
	},
		func(
			arg *Argument,
			f *Arrow[Complex, Complex],
			c, L *Expr[Complex],
			K, d *Expr[Real],
			radius, bound Fact,
		) {
			zero := arg.TermAs[Real]("&0")
			scale := arg.TermAs[Real]("|K| + &1")
			scalePositive := arg.Have(
				"|K| + 1 is positive",
				"&0 < |K| + &1",
				ByArith())
			increment := arg.Have(
				"for each ε > 0 the increment is within ε·|z − c| of L·(z − c) near c",
				Statement{
					Binders: "∀ε:real.",
					Hypotheses: []string{
						"&0 < ε",
					},
					Conclusion: "∃δ:real. " +
						"    &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |f(z) - f(c) - L * (z - c)| < ε * |z - c|",
				},
				Derive(func(b *Argument) {
					ε := b.FixAs[Real]("ε")
					positive := b.Assume()
					epsRadius := b.TermAs[Real]("ε / (|K| + &1)")
					radiusPositive := b.Have(
						"ε/(|K| + 1) is positive, ε and |K| + 1 being positive",
						"&0 < ε / (|K| + &1)",
						ByArith(positive, scalePositive))
					b.Take(b.TermAs[Real]("min(d, ε / (|K| + &1))"))
					smaller := b.Have(
						"the radius, the smaller of d and ε/(|K| + 1), is positive, both being positive",
						"&0 < min(d, ε / (|K| + &1))",
						ByArith(radius, radiusPositive, real_sup_inf.LessThanMin.At(d, epsRadius, zero)))
					within := b.Have(
						"and on the punctured disc of that radius the increment is within ε·|z − c| of L·(z − c)",
						Statement{
							Binders: "∀z:complex.",
							Hypotheses: []string{
								"&0 < |z - c|",
								"|z - c| < min(d, ε / (|K| + &1))",
							},
							Conclusion: "|f(z) - f(c) - L * (z - c)| < ε * |z - c|",
						},
						Derive(func(e *Argument) {
							e.FixAs[Complex]()
							ball := e.Assume()
							h := e.TermAs[Complex]("z - c")
							distance := e.TermAs[Real]("|z - c|")
							near := e.Have(
								"a distance below the smaller radius is below d and below ε/(|K| + 1)",
								"|z - c| < d ∧ |z - c| < ε / (|K| + &1)",
								By(ball, real_sup_inf.LessThanMin.At(d, epsRadius, distance)))
							shift := e.Have(
								"c + (z − c) is z",
								"c + (z - c) = z",
								ByArith())
							remainder := e.Have(
								"the bound at h = z − c: the increment is within K·|z − c|² of L·(z − c)",
								"|f(z) - f(c) - L * (z - c)| ≤ K * (|z - c| * |z - c|)",
								ByArith(bound.At(h), shift, near))
							e.Show(
								"K·|z − c|² is at most (|K| + 1)·|z − c|·|z − c|, below "+
									"ε·|z − c| as (|K| + 1)·|z − c| < ε and |z − c| > 0",
								ByArith(
									remainder,
									near,
									ball,
									scalePositive,
									complex_abs.AbsNonneg.At(h),
									real_order_ring.LessThanMulLeft.At(scale, distance, epsRadius),
									real_order_ring.LessEqMulRight.At(K, scale, e.TermAs[Real]("|z - c| * |z - c|")),
									real_order_ring.LessThanMulRight.At(e.TermAs[Real]("(|K| + &1) * |z - c|"), ε, distance)))
						}))
					b.Show(
						"so that radius serves ε",
						By(smaller, within))
				}))
			arg.Show(
				"which is the increment form of the derivative",
				By(increment, DerivativeIncrement.At(f, c, L)))
		}),
})}

// DerivativeCaratheodory — the derivative at c is the value at c of a
// slope function continuous there: one whose product with z − c is the
// increment of f from c.
//
// Off the centre the factorization says that φ(z) IS the difference
// quotient, and a limit at c ignores the value at c: so the quotient
// tends to l at c — the derivative — exactly when φ does, which is φ's
// continuity at c once φ(c) = l. Forward, φ is the quotient patched at
// the centre with the value l; backward, φ is given, and dividing the
// factorization by z − c ≠ 0 shows the quotient agrees with it off c.
var DerivativeCaratheodory = derivativeCaratheodoryThm{family.Add(registry.ProofEntry{
	Name: "DerivativeCaratheodory",
	Key:  "prop_dddf4e153578ab33",
	Build: family.Sections("∀f:(complex → complex). ∀c l:complex. "+
		"    complex_derivative_at(f, c, l) ⇔ "+
		"    ∃φ:(complex → complex). "+
		"        (∀z:complex. f(z) - f(c) = φ(z) * (z - c)) ∧ complex_continuous_at(φ, c) ∧ φ(c) = l",
		func(ctx *Script, headline string) *GoalStackNode {
			// A limit at c ignores the value at c: a function that agrees
			// with f off the centre has f's limits there.
			offCentre := ctx.Lemma(Statement{
				Binders: "∀f g:(complex → complex). ∀c l:complex.",
				Hypotheses: []string{
					"∀z:complex. z ≠ c ⇒ f(z) = g(z)",
					"f ⟶ l (at c)",
				},
				Conclusion: "g ⟶ l (at c)",
			},
				func(a *Argument, f, g *Arrow[Complex, Complex], c, l *Expr[Complex], given Fact) {
					parts := a.Conjuncts(
						given,
						"f and g agree off the centre",
						"f ⟶ l (at c)")
					disc := a.Have(
						"in particular f and g agree on the punctured disc of radius 1",
						"∀z:complex. &0 < |z - c| ∧ |z - c| < &1 ⇒ f(z) = g(z)",
						Derive(func(b *Argument) {
							z := b.FixAs[Complex]()
							punctured := b.Assume()
							apart := b.Have(
								"a point at positive distance from c is not c",
								"z ≠ c",
								ByArith(punctured, complex_abs.AbsPosIffNonzero.At(b.TermAs[Complex]("z - c"))))
							b.Show(
								"and off the centre f and g agree",
								By(apart, parts[0].At(z)))
						}))
					same := a.Have(
						"a limit sees only a punctured disc, so f and g have the same limits at c",
						"complex_limit_at(f, c) = complex_limit_at(g, c)",
						By(complex_topology.LimitAtLocal, real_order_ring.ZeroLessThanOne, disc))
					a.Show(
						"and f's limit l is g's",
						same.RwRev(),
						By(parts[1]))
				})

			return ctx.Theorem(headline,
				func(a *Argument, f *Arrow[Complex, Complex], c, l *Expr[Complex]) {
					quotient := a.TermAs[Fun[Complex, Complex]]("λz:complex. (f(z) - f(c)) / (z - c)")
					a.Iff()

					a.Forward(
						"φ is the difference quotient, patched at the centre with the value l",
						func(b *Argument, derivative Fact) {
							quotientTends := b.Unfolded(derivative, ComplexDerivativeAtDef)
							slope := b.TermAs[Fun[Complex, Complex]]("λz:complex. COND(z = c, l, (f(z) - f(c)) / (z - c))")
							b.Take(slope)
							b.Do(SplitConjAll(
								Case(
									"f(z) − f(c) = φ(z)·(z − c) at every z",
									Derive(func(d *Argument) {
										d.FixAs[Complex]()
										d.Cases(d.Term("z = c"))
										d.When(
											"at the centre both sides vanish",
											func(e *Argument, atCentre Fact) {
												e.Show(
													"f(c) − f(c) = 0 = l·(c − c)",
													atCentre.Subst(),
													ByArith())
											})
										d.Otherwise(
											"off the centre φ(z) is the quotient, and z − c ≠ 0 multiplies it back to f(z) − f(c)",
											func(e *Argument, offC Fact) {
												nonzero := e.Have(
													"z ≠ c, so z − c is not zero",
													"z - c ≠ &0",
													ByArith(offC))
												e.Show(
													"the quotient times z − c is f(z) − f(c): z − c cancels against its inverse",
													ByArith(offC, nonzero))
											})
									})),
								Case(
									"φ agrees with the quotient off c, so tends to its limit l = φ(c): φ is continuous at c",
									By(
										complex_topology.ContinuousAtIffLimit.At(slope, c),
										At(offCentre, quotient, slope, c, l),
										quotientTends)),
								Case(
									"φ(c) = l: at the centre φ takes the value l",
									TrivialNormalized()),
							))
						})

					a.Backward(
						"off the centre the quotient is φ(z), and φ tends to φ(c) = l",
						func(b *Argument, factored Fact) {
							phi, held := b.UnpackAs[Fun[Complex, Complex]](factored)
							parts := b.Conjuncts(
								held,
								"f(z) − f(c) = φ(z)·(z − c) at every z",
								"φ is continuous at c",
								"φ(c) = l")
							phiTends := b.Have(
								"φ is continuous at c with value l there, so φ ⟶ l (at c)",
								"φ ⟶ l (at c)",
								By(Normalized, complex_topology.ContinuousAtIffLimit.At(phi, c), parts[1], parts[2]))
							agree := b.Have(
								"off the centre φ(z) is the difference quotient",
								"∀z:complex. z ≠ c ⇒ φ(z) = (f(z) - f(c)) / (z - c)",
								Derive(func(d *Argument) {
									z := d.FixAs[Complex]()
									offC := d.Assume()
									nonzero := d.Have(
										"z ≠ c, so z − c is not zero",
										"z - c ≠ &0",
										ByArith(offC))
									d.Do(parts[0].At(z).Rw())
									d.Show(
										"the numerator is φ(z)·(z − c), and z − c cancels against its inverse: the quotient is φ(z)",
										ByArith(nonzero))
								}))
							b.Show(
								"the derivative is the quotient's limit, and the "+
									"quotient agrees with φ off c, so tends to l as φ does",
								Unfold(ComplexDerivativeAtDef),
								By(At(offCentre, phi, quotient, c, l), agree, phiTends))
						})
				})
		}),
})}

// DerivativeContinuous — a function with a derivative at a point is
// continuous there.
//
// By Carathéodory the increment of f from c factors through a slope φ
// continuous at c, so f(z) = f(c) + φ(z)·(z − c) at every z, the centre
// included. The right-hand side is continuous at c — a constant plus the
// product of φ and z − c — and it is f.
var DerivativeContinuous = derivativeContinuousThm{family.Add(registry.ProofEntry{
	Name: "DerivativeContinuous",
	Key:  "prop_76939e2ec463bad8",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c l:complex.",
		Hypotheses: []string{
			"complex_derivative_at(f, c, l)",
		},
		Conclusion: "complex_continuous_at(f, c)",
	},
		func(a *Argument, f *Arrow[Complex, Complex], c, l *Expr[Complex], derivative Fact) {
			slope := a.Have(
				"by Carathéodory, f's increment from c factors through a slope φ continuous at c",
				"∃φ:(complex → complex). "+
					"    (∀z:complex. f(z) - f(c) = φ(z) * (z - c)) ∧ complex_continuous_at(φ, c) ∧ φ(c) = l",
				By(derivative, DerivativeCaratheodory.At(f, c, l)))
			_, phiFactors := a.Unpack(slope)
			phiFacts := a.Conjuncts(
				phiFactors,
				"f(z) − f(c) = φ(z)·(z − c) at every z",
				"φ is continuous at c",
				"φ(c) = l")
			offset := a.Have(
				"z − c is continuous at c, the identity less a constant",
				"complex_continuous_at(λz:complex. z - c, c)",
				By(
					complex_topology.ContinuousAtSub,
					complex_topology.ContinuousAtId.At(c),
					complex_topology.ContinuousAtConst.At(c, c)))
			through := a.Have(
				"so is f(c) + φ(z)·(z − c), the constant f(c) plus the product of φ and z − c",
				"complex_continuous_at(λz:complex. f(c) + φ(z) * (z - c), c)",
				By(
					complex_topology.ContinuousAtAdd,
					complex_topology.ContinuousAtMul,
					complex_topology.ContinuousAtConst.At(c, f.Apply(c)),
					phiFacts[1],
					offset))
			identity := a.Have(
				"and that function is f: f(z) = f(c) + φ(z)·(z − c) at every z",
				"(λz:complex. f(c) + φ(z) * (z - c)) = f",
				Derive(func(b *Argument) {
					b.Do(Funext())
					z := b.FixAs[Complex]()
					b.Show(
						"the factorization at z",
						ByArith(phiFacts[0].At(z)))
				}))
			a.Show(
				"so f is continuous at c",
				By(identity, through))
		}),
})}

// DerivativeLocal — two functions that agree on a disc about c have the
// same derivative at c.
//
// The centre lies in the disc, so f(c) = g(c), and then the two
// difference quotients agree at every other point of the disc. A limit
// sees only a punctured disc (complex_topology.LimitAtLocal), so the two
// quotients have the same limits, and f's tends to l as g's does.
var DerivativeLocal = derivativeLocalThm{family.Add(registry.ProofEntry{
	Name: "DerivativeLocal",
	Key:  "prop_3ad4e344e0e8f5f4",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c l:complex. ∀d:real.",
		Hypotheses: []string{
			"&0 < d",
			"∀z:complex. |z - c| < d ⇒ f(z) = g(z)",
			"complex_derivative_at(g, c, l)",
		},
		Conclusion: "complex_derivative_at(f, c, l)",
	},
		func(
			a *Argument,
			f, g *Arrow[Complex, Complex],
			c, l *Expr[Complex],
			d *Expr[Real],
			radius, agree, gDerivative Fact,
		) {
			atCentre := a.Have(
				"the centre lies in the disc, |c − c| = 0 < d, so f(c) = g(c)",
				"f(c) = g(c)",
				ByArith(agree.At(c), radius, complex_abs.AbsEqZero.At(a.TermAs[Complex]("c - c"))))
			quotients := a.Have(
				"off the centre the two difference quotients agree on the disc",
				"∀z:complex. &0 < |z - c| ∧ |z - c| < d ⇒ (f(z) - f(c)) / (z - c) = (g(z) - g(c)) / (z - c)",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]()
					inDisc := b.Assume()
					b.Show(
						"f(z) = g(z) in the disc, and f(c) = g(c)",
						By(agree.At(z), inDisc, atCentre))
				}))
			limits := a.Have(
				"a limit sees only a punctured disc, so the two quotients have the same limits at c",
				"complex_limit_at(λz:complex. (f(z) - f(c)) / (z - c), c) = "+
					"complex_limit_at(λz:complex. (g(z) - g(c)) / (z - c), c)",
				By(complex_topology.LimitAtLocal, radius, quotients))
			gQuotient := a.Unfolded(gDerivative, ComplexDerivativeAtDef)
			a.Show(
				"f's quotient has the limits of g's, and g's tends to l",
				Unfold(ComplexDerivativeAtDef),
				limits.Rw(),
				By(gQuotient))
		}),
})}

// DerivativeConst — a constant function has derivative 0.
//
// Its difference quotient is (k − k)/(z − c) = 0 at every z — at the
// centre too, since 0 times anything is 0 — and the constant 0 tends to 0.
var DerivativeConst = derivativeConstThm{family.Add(registry.ProofEntry{
	Name: "DerivativeConst",
	Key:  "prop_c2d08162ff45aca2",
	Build: family.Theorem("∀c k:complex. complex_derivative_at(λz:complex. k, c, &0)",
		func(a *Argument, c, k *Expr[Complex]) {
			// Nothing in a λ-body fixes a numeral's type, and a bare &0 there
			// is the real 0: the complex 0 is spelled &(&0).
			quotient := a.Have(
				"the difference quotient of a constant is 0 everywhere",
				"(λz:complex. (k - k) / (z - c)) = (λz:complex. &(&0))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Complex]()
					b.Show(
						"k − k = 0, and 0 divided by anything is 0",
						ByArith())
				}))
			a.Do(Unfold(ComplexDerivativeAtDef), quotient.Rw())
			a.Show(
				"the quotient is the constant 0, which tends to 0",
				Cite(complex_topology.LimitAtConst))
		}),
})}

// DerivativeId — the identity has derivative 1.
//
// Its difference quotient (z − c)/(z − c) is 1 at every z off the centre,
// where z − c cancels against its inverse; at the centre it is 0, which a
// limit never sees. So on the punctured disc of radius 1 the quotient is
// the constant 1, and it tends to 1 as that constant does.
var DerivativeId = derivativeIdThm{family.Add(registry.ProofEntry{
	Name: "DerivativeId",
	Key:  "prop_f12cca54d847a12a",
	Build: family.Theorem("∀c:complex. complex_derivative_at(λz:complex. z, c, &1)",
		func(a *Argument, c *Expr[Complex]) {
			one := a.Have(
				"off the centre the identity's difference quotient (z − c)/(z − c) is 1",
				"∀z:complex. &0 < |z - c| ∧ |z - c| < &1 ⇒ (z - c) / (z - c) = &1",
				Derive(func(b *Argument) {
					b.FixAs[Complex]()
					punctured := b.Assume()
					offset := b.TermAs[Complex]("z - c")
					nonzero := b.Have(
						"z lies a positive distance from c, so z − c is not zero",
						"z - c ≠ &0",
						By(punctured, complex_abs.AbsPosIffNonzero.At(offset)))
					b.Show(
						"z − c cancels against its inverse",
						ByArith(nonzero))
				}))
			limits := a.Have(
				"a limit sees only a punctured disc, where the quotient "+
					"is the constant 1, so the two have the same limits at c",
				"complex_limit_at(λz:complex. (z - c) / (z - c), c) = complex_limit_at(λz:complex. &1, c)",
				By(complex_topology.LimitAtLocal, real_order_ring.ZeroLessThanOne, one))
			a.Show(
				"the quotient has the limits of the constant 1, which tends to 1",
				Unfold(ComplexDerivativeAtDef),
				limits.Rw(),
				Cite(complex_topology.LimitAtConst))
		}),
})}

// DerivativeAdd — the derivative of a sum is the sum of the derivatives.
//
// The difference quotient of f + g is the sum of the two quotients —
// dividing by z − c is multiplying by its inverse, which distributes over
// the sum — so it tends to l + m by the limit of a sum.
var DerivativeAdd = derivativeAddThm{family.Add(registry.ProofEntry{
	Name: "DerivativeAdd",
	Key:  "prop_3a2105c96897a8fd",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c l m:complex.",
		Hypotheses: []string{
			"complex_derivative_at(f, c, l)",
			"complex_derivative_at(g, c, m)",
		},
		Conclusion: "complex_derivative_at(λz:complex. f(z) + g(z), c, l + m)",
		Abbrev: Abbrev{
			{Name: "quotientSum", Text: "(λz:complex. (f(z) - f(c)) / (z - c) + (g(z) - g(c)) / (z - c))"},
		},
	},
		func(a *Argument, f, g *Arrow[Complex, Complex], c, l, m *Expr[Complex], derivatives Fact) {
			quotients := a.Unfolded(derivatives, ComplexDerivativeAtDef)
			sum := a.Have(
				"the quotients of f and g tend to l and m, so their sum tends to l + m",
				"«quotientSum» ⟶ l + m (at c)",
				By(complex_topology.LimitAtAdd, quotients))
			quotient := a.Have(
				"the difference quotient of f + g is the sum of the quotients of f and g",
				"(λz:complex. (f(z) + g(z) - (f(c) + g(c))) / (z - c)) = «quotientSum»",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Complex]()
					b.Show(
						"dividing by z − c distributes over the sum",
						ByArith())
				}))
			a.Do(Unfold(ComplexDerivativeAtDef), quotient.Rw())
			a.Show(
				"the quotient of f + g is the sum of the quotients, which tends to l + m",
				By(sum))
		}),
})}

// DerivativeNeg — the derivative of −f is −l.
//
// The difference quotient of −f is the negative of f's, so it tends to
// −l by the limit of a negative.
var DerivativeNeg = derivativeNegThm{family.Add(registry.ProofEntry{
	Name: "DerivativeNeg",
	Key:  "prop_6c80f007b4ec81c8",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c l:complex.",
		Hypotheses: []string{
			"complex_derivative_at(f, c, l)",
		},
		Conclusion: "complex_derivative_at(λz:complex. -f(z), c, -l)",
	},
		func(a *Argument, f *Arrow[Complex, Complex], c, l *Expr[Complex], derivative Fact) {
			quotient := a.Unfolded(derivative, ComplexDerivativeAtDef)
			negative := a.Have(
				"f's quotient tends to l, so its negative tends to −l",
				"(λz:complex. -((f(z) - f(c)) / (z - c))) ⟶ -l (at c)",
				By(complex_topology.LimitAtNeg, quotient))
			negated := a.Have(
				"the difference quotient of −f is the negative of f's",
				"(λz:complex. (-f(z) - -f(c)) / (z - c)) = (λz:complex. -((f(z) - f(c)) / (z - c)))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Complex]()
					b.Show(
						"dividing by z − c commutes with the negation",
						ByArith())
				}))
			a.Do(Unfold(ComplexDerivativeAtDef), negated.Rw())
			a.Show(
				"the quotient of −f is the negative of f's, which tends to −l",
				By(negative))
		}),
})}

// DerivativeSub — the derivative of a difference is the difference of the
// derivatives.
//
// The difference quotient of f − g is the difference of the two
// quotients, so it tends to l − m by the limit of a difference.
var DerivativeSub = derivativeSubThm{family.Add(registry.ProofEntry{
	Name: "DerivativeSub",
	Key:  "prop_8466fa2fac27558",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c l m:complex.",
		Hypotheses: []string{
			"complex_derivative_at(f, c, l)",
			"complex_derivative_at(g, c, m)",
		},
		Conclusion: "complex_derivative_at(λz:complex. f(z) - g(z), c, l - m)",
		Abbrev: Abbrev{
			{Name: "quotientDifference", Text: "(λz:complex. " +
				"    (f(z) - f(c)) / (z - c) - (g(z) - g(c)) / (z - c))"},
		},
	},
		func(a *Argument, f, g *Arrow[Complex, Complex], c, l, m *Expr[Complex], derivatives Fact) {
			quotients := a.Unfolded(derivatives, ComplexDerivativeAtDef)
			difference := a.Have(
				"the quotients of f and g tend to l and m, so their difference tends to l − m",
				"«quotientDifference» ⟶ l - m (at c)",
				By(complex_topology.LimitAtSub, quotients))
			quotient := a.Have(
				"the difference quotient of f − g is the difference of the quotients of f and g",
				"(λz:complex. (f(z) - g(z) - (f(c) - g(c))) / (z - c)) = «quotientDifference»",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Complex]()
					b.Show(
						"dividing by z − c distributes over the difference",
						ByArith())
				}))
			a.Do(Unfold(ComplexDerivativeAtDef), quotient.Rw())
			a.Show(
				"the quotient of f − g is the difference of the quotients, which tends to l − m",
				By(difference))
		}),
})}

// DerivativeScale — the derivative of k·f is k·l.
//
// The difference quotient of k·f is k times f's, so it tends to k·l by the
// limit of a product, the constant k tending to k.
var DerivativeScale = derivativeScaleThm{family.Add(registry.ProofEntry{
	Name: "DerivativeScale",
	Key:  "prop_e8342afa234996af",
	Build: family.Theorem(Statement{
		Binders: "∀f:(complex → complex). ∀c l k:complex.",
		Hypotheses: []string{
			"complex_derivative_at(f, c, l)",
		},
		Conclusion: "complex_derivative_at(λz:complex. k * f(z), c, k * l)",
	},
		func(a *Argument, f *Arrow[Complex, Complex], c, l, k *Expr[Complex], derivative Fact) {
			quotient := a.Unfolded(derivative, ComplexDerivativeAtDef)
			multiple := a.Have(
				"the constant k tends to k and f's quotient to l, so their product tends to k·l",
				"(λz:complex. k * ((f(z) - f(c)) / (z - c))) ⟶ k * l (at c)",
				By(complex_topology.LimitAtMul, complex_topology.LimitAtConst.At(c, k), quotient))
			scaled := a.Have(
				"the difference quotient of k·f is k times f's",
				"(λz:complex. (k * f(z) - k * f(c)) / (z - c)) = (λz:complex. k * ((f(z) - f(c)) / (z - c)))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Complex]()
					b.Show(
						"the factor k comes out of the difference",
						ByArith())
				}))
			a.Do(Unfold(ComplexDerivativeAtDef), scaled.Rw())
			a.Show(
				"the quotient of k·f is k times f's, which tends to k·l",
				By(multiple))
		}),
})}

// DerivativeMul — the product rule: f·g has derivative l·g(c) + f(c)·m.
//
// The difference quotient of f·g splits as f(z) times g's quotient plus
// g(c) times f's: f(z)g(z) − f(c)g(c) = f(z)(g(z) − g(c)) + g(c)(f(z) − f(c)).
// A function with a derivative is continuous, so f(z) tends to f(c), and
// the limits of products and a sum give f(c)·m + g(c)·l.
var DerivativeMul = derivativeMulThm{family.Add(registry.ProofEntry{
	Name: "DerivativeMul",
	Key:  "prop_d2545d6a3f8b01ce",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c l m:complex.",
		Hypotheses: []string{
			"complex_derivative_at(f, c, l)",
			"complex_derivative_at(g, c, m)",
		},
		Conclusion: "complex_derivative_at(λz:complex. f(z) * g(z), c, l * g(c) + f(c) * m)",
		Abbrev: Abbrev{
			{Name: "splitQuotient", Text: "(λz:complex. " +
				"    f(z) * ((g(z) - g(c)) / (z - c)) + g(c) * ((f(z) - f(c)) / (z - c)))"},
		},
	},
		func(a *Argument, f, g *Arrow[Complex, Complex], c, l, m *Expr[Complex], derivatives Fact) {
			parts := a.Conjuncts(
				derivatives,
				"f has derivative l at c",
				"g has derivative m at c")
			fLimit := a.Have(
				"f has a derivative at c, so it is continuous there: f ⟶ f(c) (at c)",
				"f ⟶ f(c) (at c)",
				By(complex_topology.ContinuousAtIffLimit.At(f, c), DerivativeContinuous.At(f, c, l), parts[0]))
			quotients := a.Unfolded(derivatives, ComplexDerivativeAtDef)
			moving := a.Have(
				"f(z) times g's quotient tends to f(c)·m",
				"(λz:complex. f(z) * ((g(z) - g(c)) / (z - c))) ⟶ f(c) * m (at c)",
				By(complex_topology.LimitAtMul, fLimit, quotients))
			fixed := a.Have(
				"g(c) times f's quotient tends to g(c)·l, the constant g(c) tending to itself",
				"(λz:complex. g(c) * ((f(z) - f(c)) / (z - c))) ⟶ g(c) * l (at c)",
				By(complex_topology.LimitAtMul, complex_topology.LimitAtConst.At(c, g.Apply(c)), quotients))
			value := a.Have(
				"f(c)·m + g(c)·l is l·g(c) + f(c)·m",
				"f(c) * m + g(c) * l = l * g(c) + f(c) * m",
				ByArith())
			sum := a.Have(
				"so their sum tends to l·g(c) + f(c)·m",
				"«splitQuotient» ⟶ l * g(c) + f(c) * m (at c)",
				Derive(func(b *Argument) {
					b.Do(value.RwRev())
					b.Show(
						"the limit of a sum is the sum of the limits",
						By(complex_topology.LimitAtAdd, moving, fixed))
				}))
			quotient := a.Have(
				"the difference quotient of f·g is that sum",
				"(λz:complex. (f(z) * g(z) - f(c) * g(c)) / (z - c)) = «splitQuotient»",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Complex]()
					b.Show(
						"f(z)g(z) − f(c)g(c) = f(z)(g(z) − g(c)) + g(c)(f(z) − f(c)), each term divided by z − c",
						ByArith())
				}))
			a.Do(Unfold(ComplexDerivativeAtDef), quotient.Rw())
			a.Show(
				"the quotient of f·g is that sum, which tends to l·g(c) + f(c)·m",
				By(sum))
		}),
})}

// DerivativeInv — the reciprocal rule: where g has derivative m at c and
// g(c) ≠ 0, 1/g has derivative −m/g(c)².
//
// Wherever g(z) ≠ 0 the difference quotient of 1/g factors as −1/g(c)
// times g's quotient times 1/g(z): multiplied out, the two sides differ
// only by the factors g(c)·(1/g(c)) and g(z)·(1/g(z)), both 1. g has a
// derivative, so it is continuous at c, and its limit read at ε = |g(c)|
// gives a punctured disc on which g(z) lies nearer to g(c) than 0 does, so
// the factorization holds there. A limit at c sees only such a disc, so
// the quotient of 1/g tends to what the factored function tends to,
// −(1/g(c))·(m·(1/g(c))) = −m/g(c)², by the limits of an inverse and of
// products.
var DerivativeInv = derivativeInvThm{family.Add(registry.ProofEntry{
	Name: "DerivativeInv",
	Key:  "prop_f8b7f300b37d89f5",
	Build: family.Theorem(Statement{
		Binders: "∀g:(complex → complex). ∀c m:complex.",
		Hypotheses: []string{
			"complex_derivative_at(g, c, m)",
			"g(c) ≠ &0",
		},
		Conclusion: "complex_derivative_at(λz:complex. complex_inv(g(z)), c, -(m / g(c) ^ 2))",
		Abbrev: Abbrev{
			{Name: "factoredReciprocal", Text: "(λz:complex. " +
				"    -complex_inv(g(c)) * ((g(z) - g(c)) / (z - c) * complex_inv(g(z))))"},
		},
	},
		func(a *Argument, g *Arrow[Complex, Complex], c, m *Expr[Complex], given Fact) {
			parts := a.Conjuncts(
				given,
				"g has derivative m at c",
				"and g(c) is not zero")
			derivative, nonzero := parts[0], parts[1]
			gc := g.Apply(c)
			quotient := a.Unfolded(derivative, ComplexDerivativeAtDef)
			gLimit := a.Have(
				"g has a derivative at c, so it is continuous there: g ⟶ g(c) (at c)",
				"g ⟶ g(c) (at c)",
				By(complex_topology.ContinuousAtIffLimit.At(g, c), DerivativeContinuous.At(g, c, m), derivative))

			reciprocal := a.Have(
				"g tends to g(c) ≠ 0, so 1/g tends to 1/g(c)",
				"(λz:complex. complex_inv(g(z))) ⟶ complex_inv(g(c)) (at c)",
				By(complex_topology.LimitAtInv, gLimit, nonzero))
			product := a.Have(
				"so g's quotient times 1/g tends to m·(1/g(c))",
				"(λz:complex. (g(z) - g(c)) / (z - c) * complex_inv(g(z))) ⟶ m * complex_inv(g(c)) (at c)",
				By(complex_topology.LimitAtMul, quotient, reciprocal))
			value := a.Have(
				"−(1/g(c))·(m·(1/g(c))) is −m/g(c)²: g(c)² is "+
					"g(c)·g(c), whose inverse is the product of the inverses",
				"-complex_inv(g(c)) * (m * complex_inv(g(c))) = -(m / g(c) ^ 2)",
				Simp(
					Fwd(comm_monoid.PowTwo.Read(complex_field.MulMonoid)),
					Fwd(field.InvMul.Read(complex_field.Field)),
					Fwd(complex_field.ComplexDivDef)),
				ByArith())
			factored := a.Have(
				"and −1/g(c) times that product tends to −m/g(c)²",
				"«factoredReciprocal» ⟶ -(m / g(c) ^ 2) (at c)",
				Derive(func(b *Argument) {
					b.Do(value.RwRev())
					b.Show(
						"the constant −1/g(c) tends to itself, and the limit of a product is the product of the limits",
						By(
							complex_topology.LimitAtMul,
							complex_topology.LimitAtConst.At(c, b.TermAs[Complex]("-complex_inv(g(c))")),
							product))
				}))

			near := a.Unfolded(gLimit, complex_topology.ComplexLimitAtDef)
			_, radius := a.ObtainAs[Real](
				"g(c) ≠ 0 makes |g(c)| positive, and g ⟶ g(c) (at c) at |g(c)| "+
					"hands over a radius δ inside which g(z) is nearer to g(c) than 0 is",
				"∃δ:real. &0 < δ ∧ ∀z:complex. &0 < |z - c| ∧ |z - c| < δ ⇒ |g(z) - g(c)| < |g(c)|",
				By(near.At(a.TermAs[Real]("|g(c)|")), complex_abs.AbsPosIffNonzero.At(gc), nonzero),
				Named("δ"))
			disc := a.Conjuncts(
				radius,
				"the radius δ is positive",
				"and on the punctured disc of radius δ, g(z) is within |g(c)| of g(c)")
			radiusPos, within := disc[0], disc[1]
			agree := a.Have(
				"on that disc the quotient of 1/g is −1/g(c) times g's quotient times 1/g(z)",
				Statement{
					Binders: "∀z:complex.",
					Hypotheses: []string{
						"&0 < |z - c|",
						"|z - c| < δ",
					},
					Conclusion: "(complex_inv(g(z)) - complex_inv(g(c))) / (z - c) = " +
						"-complex_inv(g(c)) * ((g(z) - g(c)) / (z - c) * complex_inv(g(z)))",
				},
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]()
					inDisc := b.Assume()
					gz := g.Apply(z)
					gzSize := b.Have(
						"z lies in the disc, so |g(z)| is positive: |g(c)| − |g(z)| ≤ |g(z) − g(c)| < |g(c)|",
						"&0 < |g(z)|",
						ByArith(within.At(z), inDisc, complex_abs.AbsTriangleReverse.At(gz, gc)))
					gzNonzero := b.Have(
						"so g(z) is not zero",
						"g(z) ≠ &0",
						By(gzSize, complex_abs.AbsPosIffNonzero.At(gz)))
					b.Show(
						"g(z) and g(c) are not zero, so each cancels against "+
							"its own inverse and the two sides multiply out alike",
						ByArith(gzNonzero, nonzero))
				}))
			limits := a.Have(
				"a limit sees only a punctured disc, so the quotient "+
					"of 1/g has, at c, the limits of the factored function",
				"complex_limit_at(λz:complex. (complex_inv(g(z)) - complex_inv(g(c))) / (z - c), c) = "+
					"complex_limit_at(«factoredReciprocal», c)",
				By(complex_topology.LimitAtLocal, radiusPos, agree))
			a.Show(
				"the quotient of 1/g has the factored function's limits, and that function tends to −m/g(c)²",
				Unfold(ComplexDerivativeAtDef),
				limits.Rw(),
				By(factored))
		}),
})}

// DerivativeDiv — the quotient rule: where g(c) ≠ 0, f/g has derivative
// (l·g(c) − f(c)·m)/g(c)².
//
// f/g is f times 1/g, so the product rule applies to f and the reciprocal
// of g, whose derivative −m/g(c)² the reciprocal rule gives. The value
// l·(1/g(c)) + f(c)·(−m/g(c)²) is the quotient rule's once l·(1/g(c)) is
// written as l·g(c)·(1/g(c))·(1/g(c)) — g(c) times its inverse is 1.
var DerivativeDiv = derivativeDivThm{family.Add(registry.ProofEntry{
	Name: "DerivativeDiv",
	Key:  "prop_7f6026c5db41c354",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c l m:complex.",
		Hypotheses: []string{
			"complex_derivative_at(f, c, l)",
			"complex_derivative_at(g, c, m)",
			"g(c) ≠ &0",
		},
		Conclusion: "complex_derivative_at(λz:complex. f(z) / g(z), c, (l * g(c) - f(c) * m) / g(c) ^ 2)",
	},
		func(a *Argument, f, g *Arrow[Complex, Complex], c, l, m *Expr[Complex], given Fact) {
			held := a.Conjuncts(
				given,
				"f has derivative l at c",
				"g has derivative m at c",
				"g(c) is not 0")
			reciprocal := a.Have(
				"1/g has derivative −m/g(c)² at c",
				"complex_derivative_at(λz:complex. complex_inv(g(z)), c, -(m / g(c) ^ 2))",
				By(DerivativeInv, held[1], held[2]))
			product := a.Have(
				"so f times 1/g has derivative l·(1/g(c)) + f(c)·(−m/g(c)²)",
				"complex_derivative_at(λz:complex. f(z) * complex_inv(g(z)), "+
					"    c, "+
					"    l * complex_inv(g(c)) + f(c) * -(m / g(c) ^ 2))",
				By(
					At(DerivativeMul,
						f,
						a.TermAs[Fun[Complex, Complex]]("λz:complex. complex_inv(g(z))"),
						c,
						l,
						a.TermAs[Complex]("-(m / g(c) ^ 2)")),
					held[0],
					reciprocal))
			value := a.Have(
				"that value is the quotient rule's: g(c) is not zero, so l·(1/g(c)) is l·g(c)·(1/g(c))·(1/g(c))",
				"l * complex_inv(g(c)) + f(c) * -(m / g(c) ^ 2) = (l * g(c) - f(c) * m) / g(c) ^ 2",
				Simp(
					Fwd(comm_monoid.PowTwo.Read(complex_field.MulMonoid)),
					Fwd(field.InvMul.Read(complex_field.Field)),
					Fwd(complex_field.ComplexDivDef)),
				ByArith(held[2]))
			quotient := a.Have(
				"f/g is f times 1/g",
				"(λz:complex. f(z) / g(z)) = (λz:complex. f(z) * complex_inv(g(z)))",
				Derive(func(b *Argument) {
					b.Do(Funext())
					b.FixAs[Complex]()
					b.Show(
						"division is multiplication by the inverse",
						Cite(complex_field.ComplexDivDef))
				}))
			a.Do(quotient.Rw(), value.RwRev())
			a.Show(
				"f times 1/g has that derivative",
				By(product))
		}),
})}

// DerivativeChain — the chain rule: the derivative of f ∘ g at c is the
// derivative of f at g(c) times the derivative of g at c.
//
// Read both derivatives through Carathéodory: g's increment from c is
// ψ(z)·(z − c) with ψ continuous at c and ψ(c) = m, and f's increment from
// g(c) is φ(w)·(w − g(c)) with φ continuous at g(c) and φ(g(c)) = l. At the
// point w = g(z) the two factorizations compose, so the slope
// χ(z) = φ(g(z))·ψ(z) factors the increment of f ∘ g from c. It is
// continuous at c — g is continuous there, having a derivative, so φ ∘ g
// is, and so is its product with ψ — and χ(c) = φ(g(c))·ψ(c) = l·m. No
// division by g(z) − g(c) is made, which is what the naive proof trips on
// where g takes the value g(c) near c. The goal, rewritten by Carathéodory
// into its slope form at f ∘ g, asks for such a slope with value l·m, and
// χ is one.
var DerivativeChain = derivativeChainThm{family.Add(registry.ProofEntry{
	Name: "DerivativeChain",
	Key:  "prop_677a0775974f45ea",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c l m:complex.",
		Hypotheses: []string{
			"complex_derivative_at(g, c, m)",
			"complex_derivative_at(f, g(c), l)",
		},
		Conclusion: "complex_derivative_at(f ∘ g, c, l * m)",
	},
		func(a *Argument, f, g *Arrow[Complex, Complex], c, l, m *Expr[Complex], derivatives Fact) {
			parts := a.Conjuncts(
				derivatives,
				"g has derivative m at c",
				"f has derivative l at g(c)")
			innerSlope := a.Have(
				"g's increment from c factors through a slope ψ continuous at c, with ψ(c) = m",
				"∃ψ:(complex → complex). "+
					"    (∀z:complex. g(z) - g(c) = ψ(z) * (z - c)) ∧ complex_continuous_at(ψ, c) ∧ ψ(c) = m",
				By(parts[0], DerivativeCaratheodory.At(g, c, m)))
			_, psiFactors := a.Unpack(innerSlope)
			psiFacts := a.Conjuncts(
				psiFactors,
				"g(z) − g(c) = ψ(z)·(z − c) at every z",
				"ψ is continuous at c",
				"ψ(c) = m")
			outerSlope := a.Have(
				"f's increment from g(c) factors through a slope φ continuous at g(c), with φ(g(c)) = l",
				"∃φ:(complex → complex). "+
					"    (∀w:complex. f(w) - f(g(c)) = φ(w) * (w - g(c))) ∧ "+
					"    complex_continuous_at(φ, g(c)) ∧ "+
					"    φ(g(c)) = l",
				By(parts[1], DerivativeCaratheodory.At(f, g.Apply(c), l)))
			_, phiFactors := a.Unpack(outerSlope)
			phiFacts := a.Conjuncts(
				phiFactors,
				"f(w) − f(g(c)) = φ(w)·(w − g(c)) at every w",
				"φ is continuous at g(c)",
				"φ(g(c)) = l")

			composed := a.Have(
				"the factorizations compose: the increment of f ∘ g from c is φ(g(z))·ψ(z)·(z − c) at every z",
				"∀z:complex. (f ∘ g)(z) - (f ∘ g)(c) = φ(g(z)) * ψ(z) * (z - c)",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]()
					b.Show(
						"f's factorization at the point g(z), then g's at z",
						CalcEq(
							Leg(
								b.TermAs[Complex]("f(g(z)) - f(g(c))"),
								"the values of f ∘ g are the values of f at those of g",
								Unfold(functions.ComposeApply)),
							Leg(
								b.TermAs[Complex]("φ(g(z)) * (g(z) - g(c))"),
								"f's increment from g(c) to g(z) is φ(g(z)) times g's increment",
								By(phiFacts[0].At(g.Apply(z)))),
							Leg(
								b.TermAs[Complex]("φ(g(z)) * (ψ(z) * (z - c))"),
								"and g's increment from c to z is ψ(z)·(z − c)",
								By(Normalized, psiFacts[0].At(z))),
							FinalLeg(
								"regroup the product",
								ByArith()),
						))
				}))

			composite := a.Have(
				"g, having a derivative at c, is continuous there, so φ ∘ g is too, φ being continuous at g(c)",
				"complex_continuous_at(φ ∘ g, c)",
				By(complex_topology.ContinuousAtCompose, DerivativeContinuous.At(g, c, m), parts[0], phiFacts[1]))
			phiOfG := a.Unfolded(composite, functions.ComposeApply)
			slopeContinuous := a.Have(
				"the slope χ(z) = φ(g(z))·ψ(z) is continuous at c, the product of z ↦ φ(g(z)) and ψ",
				"complex_continuous_at(λz:complex. φ(g(z)) * ψ(z), c)",
				By(complex_topology.ContinuousAtMul, phiOfG, psiFacts[1]))
			value := a.Have(
				"and at c the slope is φ(g(c))·ψ(c) = l·m",
				"φ(g(c)) * ψ(c) = l * m",
				By(Normalized, phiFacts[2], psiFacts[2]))

			// The goal rewritten into its slope form.
			a.Do(Simp(Fwd(DerivativeCaratheodory)))
			a.Take(a.TermAs[Fun[Complex, Complex]]("λz:complex. φ(g(z)) * ψ(z)"))
			a.Show(
				"χ factors the increment of f ∘ g, is continuous at c and takes the value l·m there",
				By(composed, slopeContinuous, value))
		}),
})}

// DerivativeInverse — the derivative of an inverse function: where g is
// continuous at c and undoes f on a disc about c, and f has a nonzero
// derivative l at g(c), g has derivative 1/l at c.
//
// Read f's derivative through Carathéodory: f(w) − f(g(c)) = φ(w)·(w − g(c))
// with φ continuous at g(c) and φ(g(c)) = l. At the point w = g(z) of a z in
// the disc this says z − c = φ(g(z))·(g(z) − g(c)), as f(g(z)) = z and
// f(g(c)) = c. Off the centre z − c ≠ 0, so the difference quotient of g
// times φ(g(z)) is 1, and the quotient is 1/φ(g(z)) — no division by
// φ(g(z)) is made before it is known not to vanish. φ ∘ g is continuous at
// c, g being continuous there, with the nonzero value l, so 1/φ(g(z)) tends
// to 1/l; and a limit sees only a punctured disc, so the quotient of g tends
// to 1/l as well.
var DerivativeInverse = derivativeInverseThm{family.Add(registry.ProofEntry{
	Name: "DerivativeInverse",
	Key:  "prop_bc2f8dfb6e2d3267",
	Build: family.Theorem(Statement{
		Binders: "∀f g:(complex → complex). ∀c l:complex. ∀d:real.",
		Hypotheses: []string{
			"complex_continuous_at(g, c)",
			"&0 < d",
			"∀z:complex. |z - c| < d ⇒ f(g(z)) = z",
			"complex_derivative_at(f, g(c), l)",
			"l ≠ &0",
		},
		Conclusion: "complex_derivative_at(g, c, complex_inv(l))",
	},
		func(
			a *Argument,
			f, g *Arrow[Complex, Complex],
			c, l *Expr[Complex],
			d *Expr[Real],
			continuous, radius, inverse, derivative, nonzero Fact,
		) {
			outerSlope := a.Have(
				"f's increment from g(c) factors through a slope φ continuous at g(c), with φ(g(c)) = l",
				"∃φ:(complex → complex). "+
					"    (∀w:complex. f(w) - f(g(c)) = φ(w) * (w - g(c))) ∧ "+
					"    complex_continuous_at(φ, g(c)) ∧ "+
					"    φ(g(c)) = l",
				By(derivative, DerivativeCaratheodory.At(f, g.Apply(c), l)))
			_, phiFactors := a.Unpack(outerSlope)
			phiFacts := a.Conjuncts(
				phiFactors,
				"f(w) − f(g(c)) = φ(w)·(w − g(c)) at every w",
				"φ is continuous at g(c)",
				"φ(g(c)) = l")
			centre := a.Have(
				"the centre lies in the disc, |c − c| = 0 < d, so f(g(c)) = c",
				"f(g(c)) = c",
				ByArith(inverse.At(c), radius, complex_abs.AbsEqZero.At(a.TermAs[Complex]("c - c"))))
			quotients := a.Have(
				"off the centre, on the disc, the difference quotient of g is 1/φ(g(z))",
				"∀z:complex. &0 < |z - c| ∧ |z - c| < d ⇒ (g(z) - g(c)) / (z - c) = complex_inv(φ(g(z)))",
				Derive(func(b *Argument) {
					z := b.FixAs[Complex]()
					inDisc := b.Assume()
					apart := b.Have(
						"z ≠ c, so z − c is not zero",
						"z - c ≠ &0",
						ByArith(inDisc, complex_abs.AbsPosIffNonzero.At(b.TermAs[Complex]("z - c"))))
					factored := b.Have(
						"f's factorization at g(z), with f(g(z)) = z and f(g(c)) = c, reads z − c = φ(g(z))·(g(z) − g(c))",
						"z - c = φ(g(z)) * (g(z) - g(c))",
						ByArith(phiFacts[0].At(g.Apply(z)), inverse.At(z), centre, inDisc))
					unit := b.Have(
						"so the quotient times φ(g(z)) is (z − c)·1/(z − c) = 1",
						"(g(z) - g(c)) / (z - c) * φ(g(z)) = &1",
						ByArith(apart, Scaled(b.TermAs[Complex]("complex_inv(z - c)"), factored)))
					b.Show(
						"and what φ(g(z)) multiplies to 1 is its inverse",
						By(
							unit,
							field.InvLeftUnique.Read(complex_field.Field).At(
								b.TermAs[Complex]("(g(z) - g(c)) / (z - c)"),
								b.TermAs[Complex]("φ(g(z))"))))
				}))
			composite := a.Have(
				"g is continuous at c and φ at g(c), so φ ∘ g is continuous at c",
				"complex_continuous_at(φ ∘ g, c)",
				By(complex_topology.ContinuousAtCompose, continuous, phiFacts[1]))
			phiOfG := a.Unfolded(composite, functions.ComposeApply)
			reciprocal := a.Have(
				"so 1/φ(g(z)) tends to 1/φ(g(c)) = 1/l at c, φ(g(c)) = l being nonzero",
				"(λz:complex. complex_inv(φ(g(z)))) ⟶ complex_inv(l) (at c)",
				By(
					Normalized,
					nonzero,
					phiFacts[2],
					phiOfG,
					complex_topology.ContinuousAtInv.At(a.TermAs[Fun[Complex, Complex]]("λz:complex. φ(g(z))"), c),
					complex_topology.ContinuousAtIffLimit.At(
						a.TermAs[Fun[Complex, Complex]]("λz:complex. complex_inv(φ(g(z)))"),
						c)))
			limits := a.Have(
				"a limit sees only a punctured disc, where the quotient of g is 1/φ(g(z))",
				"complex_limit_at(λz:complex. (g(z) - g(c)) / (z - c), c) = "+
					"complex_limit_at(λz:complex. complex_inv(φ(g(z))), c)",
				By(complex_topology.LimitAtLocal, radius, quotients))
			a.Show(
				"so the quotient of g tends to 1/l as 1/φ(g(z)) does",
				Unfold(ComplexDerivativeAtDef),
				limits.Rw(),
				By(reciprocal))
		}),
})}

// DerivativePow — the power rule: z ↦ zⁿ has derivative n·zⁿ⁻¹, the
// coefficient the real number n read in ℂ.
//
// The exponent is 0 or a successor. z⁰ is the constant 1, with derivative
// 0; ℕ's subtraction truncates, so the stated value there is 0 times
// c^(0 − 1), which is 0 whatever that power is. At a successor m + 1 the
// derivative is (m + 1)·cᵐ, by induction on m: z¹ is the identity, with
// derivative 1 = 1·c⁰, and z^(m+2) is z·z^(m+1), whose derivative by the
// product rule is 1·c^(m+1) + c·((m+1)·cᵐ), which is (m+2)·c^(m+1).
var DerivativePow = derivativePowThm{family.Add(registry.ProofEntry{
	Name: "DerivativePow",
	Key:  "prop_b729ba1f91bbd464",
	Build: family.Theorem("∀n:num. ∀c:complex. "+
		"    complex_derivative_at(λz:complex. z ^ n, c, &(&n) * c ^ (n - 1))",
		func(a *Argument) {
			successor := a.Have(
				"at a successor exponent, z^(m+1) has derivative (m+1)·cᵐ",
				"∀m:num. ∀c:complex. complex_derivative_at(λz:complex. z ^ (m + 1), c, &(&(m + 1)) * c ^ m)",
				Derive(func(s *Argument) {
					zero := s.TermAs[Nat]("0")
					// The exponent read as suc(m).
					s.Do(Simp(Rev(nat_arith.Add1)))
					s.Induct("m")
					s.Base(
						"z¹ is the identity, and its derivative 1 is 1·c⁰",
						func(b *Argument) {
							c := b.FixAs[Complex]()
							firstPower := b.Have(
								"z¹ = z·z⁰ = z·1 = z at every z",
								"(λz:complex. z ^ suc(0)) = (λz:complex. z)",
								Derive(func(d *Argument) {
									d.Do(Funext())
									d.FixAs[Complex]()
									d.Show(
										"the power's two clauses, and 1 is a unit",
										Simp(Fwd(comm_monoid.MonoidPowDef)),
										ByArith())
								}))
							value := b.Have(
								"1·c⁰ = 1",
								"&(&suc(0)) * c ^ 0 = &1",
								ByArith(comm_monoid.MonoidPowDef, real_ring.OfNumSuc.At(zero)))
							b.Show(
								"so z¹ has the identity's derivative",
								By(firstPower, value, DerivativeId.At(c)))
						})
					s.Step(
						"z^(m+2) is z·z^(m+1), a product of two functions whose derivatives are known",
						func(b *Argument, ih Fact) {
							c := b.FixAs[Complex]()
							identity := b.TermAs[Fun[Complex, Complex]]("λz:complex. z")
							power := b.TermAs[Fun[Complex, Complex]]("λz:complex. z ^ suc(m)")
							one := b.TermAs[Complex]("&1")
							product := b.Have(
								"by the product rule, z·z^(m+1) has derivative 1·c^(m+1) + c·((m+1)·cᵐ)",
								"complex_derivative_at(λz:complex. z * z ^ suc(m), c, &1 * c ^ suc(m) + c * (&(&suc(m)) * c ^ m))",
								By(
									DerivativeMul.At(identity, power, c, one, b.TermAs[Complex]("&(&suc(m)) * c ^ m")),
									DerivativeId.At(c),
									ih.At(c)))
							value := b.Have(
								"that value is (m+2)·c^(m+1): c^(m+1) = c·cᵐ, and m + 2 = m + 1 + 1 read in ℂ",
								"&1 * c ^ suc(m) + c * (&(&suc(m)) * c ^ m) = &(&suc(suc(m))) * c ^ suc(m)",
								Simp(Fwd(comm_monoid.MonoidPowDef), Fwd(real_ring.OfNumSuc), Fwd(complex_field.OfRealAdd)),
								ByArith())
							stepClause := b.Have(
								"z^(m+2) is z·z^(m+1), by the power's step clause",
								"(λz:complex. z ^ suc(suc(m))) = (λz:complex. z * z ^ suc(m))",
								Simp(Fwd(comm_monoid.MonoidPowDef)),
								Refl())
							b.Show(
								"so z^(m+2) has derivative (m+2)·c^(m+1)",
								By(value, stepClause, product))
						})
				}))
			nBinder := a.Binder("n")
			n := ext.As[Nat](nBinder)
			// The induction is ℕ's case split: the step never reads its
			// hypothesis.
			a.Induct(nBinder)
			a.Base(
				"z⁰ is the constant 1, whose derivative 0 is 0 times c^(0 − 1)",
				func(b *Argument) {
					c := b.FixAs[Complex]()
					constant := b.Have(
						"z⁰ = 1 at every z",
						"(λz:complex. z ^ 0) = (λz:complex. &(&1))",
						Derive(func(d *Argument) {
							d.Do(Funext())
							d.FixAs[Complex]()
							d.Show(
								"the power's zero clause",
								Simp(Fwd(comm_monoid.MonoidPowDef)),
								ByArith())
						}))
					value := b.Have(
						"0 times c^(0 − 1) is 0",
						"&(&0) * c ^ (0 - 1) = &0",
						ByArith())
					b.Show(
						"a constant has derivative 0",
						By(constant, value, DerivativeConst.At(c, b.TermAs[Complex]("&1"))))
				})
			a.Step(
				"z^(n+1) is a successor power, and (n + 1) − 1 = n",
				a.ForEach(func(c *Expr[Complex]) Action {
					return By(Normalized, successor.At(n, c), nat_arith.Add1.At(n), nat_monus.SucSubOne.At(n))
				}))
		}),
})}
