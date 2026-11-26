// limits.go — what a uniform limit keeps: a uniform limit of continuous
// functions is continuous, and a uniform limit of differentiable functions
// whose derivatives converge uniformly is differentiable, its derivative
// the limit of the derivatives.

package real_uniform_convergence

import (
	. "github.com/euc-ai/xugo/library/authoring"
	"github.com/euc-ai/xugo/library/proofs/real/real_continuous"
	"github.com/euc-ai/xugo/library/proofs/real/real_derivative"
	"github.com/euc-ai/xugo/library/proofs/real/real_order_ring"
	"github.com/euc-ai/xugo/library/proofs/real/real_sequences"
	"github.com/euc-ai/xugo/library/proofs/real/real_sgn_abs"
	"github.com/euc-ai/xugo/library/proofs/real/real_sup_inf"
	"github.com/euc-ai/xugo/library/registry"
)

// UniformLimitCongruence — the limit of a sequence converging uniformly
// on s may be replaced by any function agreeing with it on s: past the
// index that brings every member within ε of g at every point of s, the
// members are as close to h, which takes g's values there.
var UniformLimitCongruence = uniformLimitCongruenceThm{family.Add(registry.ProofEntry{
	Name: "UniformLimitCongruence",
	Key:  "prop_916b2cf4eaf988e5",
	Build: family.Theorem(Statement{
		Binders: "∀f:(num → real → real). ∀g h:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"real_converges_uniformly_on(s, f, g)",
			"∀x:real. x ∈ s ⇒ g(x) = h(x)",
		},
		Conclusion: "real_converges_uniformly_on(s, f, h)",
	},
		func(
			a *Argument,
			f *Arrow2[Nat, Real, Real],
			g, h *Arrow[Real, Real],
			s *Expr[Set[Real]],
			uniform, agree Fact,
		) {
			near := a.Unfolded(uniform, RealConvergesUniformlyOnDef)
			a.Do(Unfold(RealConvergesUniformlyOnDef))
			ε := a.FixAs[Real]()
			pos := a.Assume()
			N, tail := a.ObtainAs[Nat](
				"past some index N every member is within ε of g on all of s",
				"∃N:num. ∀n:num. ∀x:real. N ≤ n ∧ x ∈ s ⇒ |f(n)(x) - g(x)| < ε",
				By(near.At(ε), pos))
			a.Take(N)
			n := a.FixAs[Nat]()
			x := a.FixAs[Real]()
			given := a.Assume()
			a.Show(
				"and at a point of s, h(x) is g(x)",
				ByArith(tail.At(n, x), agree.At(x), given))
		}),
})}

// UniformLimitContinuous — a uniform limit of functions continuous on s
// is continuous on s.
//
// The ε/3 argument. Given c in s and ε > 0, one member f(N) lies within
// ε/3 of g at every point of s at once, and f(N), being continuous at c,
// keeps its values on s within ε/3 of f(N)(c) inside some radius δ. Inside
// that radius g(x) is within ε/3 of f(N)(x), which is within ε/3 of
// f(N)(c), which is within ε/3 of g(c).
var UniformLimitContinuous = uniformLimitContinuousThm{family.Add(registry.ProofEntry{
	Name: "UniformLimitContinuous",
	Key:  "prop_a6575982d75f6649",
	Build: family.Theorem(Statement{
		Binders: "∀f:(num → real → real). ∀g:(real → real). ∀s:set(real).",
		Hypotheses: []string{
			"∀n:num. real_continuous_on(s, f(n))",
			"real_converges_uniformly_on(s, f, g)",
		},
		Conclusion: "real_continuous_on(s, g)",
	},
		func(
			a *Argument,
			f *Arrow2[Nat, Real, Real],
			g *Arrow[Real, Real],
			s *Expr[Set[Real]],
			continuous, uniform Fact,
		) {
			near := a.Unfolded(uniform, RealConvergesUniformlyOnDef)
			radii := a.Unfolded(continuous, real_continuous.RealContinuousOnDef)

			a.Do(Unfold(real_continuous.RealContinuousOnDef))
			c := a.FixAs[Real]()
			cIn := a.Assume()
			a.FixAs[Real]()
			pos := a.Assume()
			third := a.TermAs[Real]("ε / &3")
			thirdPos := a.Have(
				"a third of ε is again a positive distance",
				"&0 < ε / &3",
				ByArith(pos))
			N, tail := a.ObtainAs[Nat](
				"one index past which every member is within ε/3 of g on all of s",
				"∃N:num. ∀n:num. ∀x:real. N ≤ n ∧ x ∈ s ⇒ |f(n)(x) - g(x)| < ε / &3",
				By(near.At(third), thirdPos))
			δ, ball := a.ObtainAs[Real](
				"f(N) is continuous at c: inside some radius δ its values on s stay within ε/3 of f(N)(c)",
				"∃δ:real. &0 < δ ∧ ∀x:real. x ∈ s ∧ |x - c| < δ ⇒ |f(N)(x) - f(N)(c)| < ε / &3",
				By(radii.At(N, c, third), cIn, thirdPos))
			held := a.Conjuncts(
				ball,
				"δ is positive",
				"and inside it f(N) stays within ε/3 of f(N)(c)")

			a.Take(δ)
			a.Do(SplitConj(
				Case(
					"the radius δ is positive",
					By(held[0])),
				Case(
					"inside it g(x) is within ε/3 of f(N)(x), which is "+
						"within ε/3 of f(N)(c), which is within ε/3 of g(c)",
					Derive(func(b *Argument) {
						x := b.FixAs[Real]()
						inside := b.Assume()
						b.Show(
							"|g(x) − g(c)| < ε/3 + ε/3 + ε/3 = ε",
							ByArith(tail.At(N, x), tail.At(N, c), held[1].At(x), cIn, inside))
					})),
			))
		}),
})}

// UniformLimitDerivative — on an open interval ⟬a, b⟭, a sequence of
// differentiable functions whose derivatives converge uniformly, and which
// converges at one point c, converges uniformly to a differentiable
// function g, with g(c) the limit at c and g' the limit of the
// derivatives.
//
// Everything rests on one estimate, the member's first section, read at
// a tolerance η. Read against c, where the values converge, it makes the
// f(n) uniformly Cauchy on ⟬a, b⟭: f(m)(x) − f(n)(x) is its value at c
// plus its increment from c, at most η·(b − a). So they converge
// uniformly, to some g, and g(c) is the limit of the values at c. For the
// derivative at x, given ε, fix one n far enough that f'(n) is within ε/5
// of h and the estimate holds at ε/5, and a radius inside which f(n)'s
// increment from x is within ε/5·|y − x| of f'(n)(x)·(y − x). For y
// inside it, a member f(m) further on, within ε/5·|y − x| of g at y and
// at x, carries the estimate over to g: g's increment is within
// 3ε/5·|y − x| of f(n)'s. The three bounds and |f'(n)(x) − h(x)| < ε/5
// put g's increment within ε·|y − x| of h(x)·(y − x), which is the
// derivative read as a bound on the increment.
var UniformLimitDerivative = uniformLimitDerivativeThm{family.Add(registry.ProofEntry{
	Name: "UniformLimitDerivative",
	Key:  "prop_c2c4594000b3a1a8",
	Build: family.Sections(Statement{
		Binders: "∀f f':(num → real → real). ∀h:(real → real). ∀a b c l:real.",
		Hypotheses: []string{
			"∀n:num. ∀x:real. a < x ∧ x < b ⇒ real_derivative_at(f(n), x, f'(n)(x))",
			"real_converges_uniformly_on(«interval», f', h)",
			"a < c",
			"c < b",
			"(λn:num. f(n)(c)) ⟶ l",
		},
		Conclusion: "∃g:(real → real). " +
			"    real_converges_uniformly_on(«interval», f, g) ∧ " +
			"    g(c) = l ∧ " +
			"    ∀x:real. a < x ∧ x < b ⇒ real_derivative_at(g, x, h(x))",
		Abbrev: Abbrev{
			{Name: "interval", Text: "⟬a, b⟭"},
		},
	},
		func(ctx *Script, headline string) *GoalStackNode {
			// The estimate everything rests on: when the derivatives of a sequence of
			// functions converge uniformly on ⟬a, b⟭, past some index the increments
			// of any two members between two points of ⟬a, b⟭ differ by at most η
			// times the distance between the points.
			//
			// The derivatives, converging uniformly, are uniformly Cauchy: past some
			// N any two of them are within η of each other on ⟬a, b⟭. For m and n
			// past N, f(m) − f(n) has derivative f'(m) − f'(n) on ⟬a, b⟭, at most η
			// in size, and the mean value inequality bounds its increment between x
			// and y by η·|y − x|.
			increments := ctx.Lemma(Statement{
				Binders: "∀f f':(num → real → real). ∀h:(real → real). ∀a b η:real.",
				Hypotheses: []string{
					"∀n:num. ∀x:real. a < x ∧ x < b ⇒ real_derivative_at(f(n), x, f'(n)(x))",
					"real_converges_uniformly_on(«interval», f', h)",
					"&0 < η",
				},
				Conclusion: "∃N:num. ∀m n:num. ∀x y:real. " +
					"    N ≤ m ∧ N ≤ n ∧ a < x ∧ x < b ∧ a < y ∧ y < b ⇒ " +
					"    |f(m)(y) - f(n)(y) - (f(m)(x) - f(n)(x))| ≤ η * |y - x|",
			},
				func(arg *Argument, f, fPrime *Arrow2[Nat, Real, Real], h *Arrow[Real, Real], a, b, η *Expr[Real],
					derivatives, derivativesConverge, pos Fact) {
					derivativesCauchy := arg.Have(
						"the derivatives converge uniformly, so they are uniformly Cauchy on ⟬a, b⟭",
						Statement{
							Binders: "∀ε:real.",
							Hypotheses: []string{
								"&0 < ε",
							},
							Conclusion: "∃N:num. ∀m n:num. ∀t:real. N ≤ m ∧ N ≤ n ∧ t ∈ «interval» ⇒ |f'(m)(t) - f'(n)(t)| < ε",
						},
						By(derivativesConverge, UniformCauchy))
					N, derivativesNear := arg.ObtainAs[Nat](
						"past some N any two derivatives are within η of each other on ⟬a, b⟭",
						"∃N:num. ∀m n:num. ∀t:real. N ≤ m ∧ N ≤ n ∧ t ∈ «interval» ⇒ |f'(m)(t) - f'(n)(t)| < η",
						By(derivativesCauchy.At(η), pos))
					arg.Take(N)
					m := arg.FixAs[Nat]()
					n := arg.FixAs[Nat]()
					x := arg.FixAs[Real]()
					y := arg.FixAs[Real]()
					guards := arg.Conjuncts(
						arg.Assume(),
						"m is past N",
						"n is past N",
						"x lies above a",
						"and below b",
						"y lies above a",
						"and below b")
					difference := arg.Have(
						"f(m) − f(n) has derivative f'(m)(t) − f'(n)(t) at every t of ⟬a, b⟭",
						"∀t:real. a < t ∧ t < b ⇒ real_derivative_at(λx:real. f(m)(x) - f(n)(x), t, f'(m)(t) - f'(n)(t))",
						Derive(func(e *Argument) {
							t := e.FixAs[Real]()
							within := e.Assume()
							e.Show(
								"the difference of the two derivatives",
								By(
									derivatives.At(m, t),
									derivatives.At(n, t),
									within,
									real_derivative.DerivativeSub.At(
										e.TermAs[Fun[Real, Real]]("f(m)"),
										e.TermAs[Fun[Real, Real]]("f(n)"),
										t,
										e.TermAs[Real]("f'(m)(t)"),
										e.TermAs[Real]("f'(n)(t)"))))
						}))
					small := arg.Have(
						"and that derivative is at most η in size",
						"∀t:real. a < t ∧ t < b ⇒ |f'(m)(t) - f'(n)(t)| ≤ η",
						Derive(func(e *Argument) {
							t := e.FixAs[Real]()
							within := e.Assume()
							e.Show(
								"m and n are past N",
								ByArith(derivativesNear.At(m, n, t), guards[0], guards[1], within))
						}))
					arg.Show(
						"the mean value inequality on f(m) − f(n)",
						By(
							difference,
							small,
							guards[2],
							guards[3],
							guards[4],
							guards[5],
							real_derivative.MeanValueInequality.At(
								arg.TermAs[Fun[Real, Real]]("λx:real. f(m)(x) - f(n)(x)"),
								arg.TermAs[Fun[Real, Real]]("λt:real. f'(m)(t) - f'(n)(t)"),
								a,
								b,
								η,
								x,
								y)))
				})

			return ctx.Theorem(headline,
				func(
					arg *Argument,
					f, fPrime *Arrow2[Nat, Real, Real],
					h *Arrow[Real, Real],
					a, b, c, l *Expr[Real],
					derivatives, derivativesConverge, above, below, atC Fact,
				) {
					interval := arg.TermAs[Set[Real]]("«interval»")
					valuesAtC := arg.TermAs[Fun[Nat, Real]]("λn:num. f(n)(c)")

					cauchy := arg.Have(
						"the f(n) are uniformly Cauchy on ⟬a, b⟭: f(m)(x) − "+
							"f(n)(x) is its value at c plus its increment from c",
						Statement{
							Binders: "∀ε:real.",
							Hypotheses: []string{
								"&0 < ε",
							},
							Conclusion: "∃N:num. ∀m n:num. ∀x:real. N ≤ m ∧ N ≤ n ∧ x ∈ «interval» ⇒ |f(m)(x) - f(n)(x)| < ε",
						},
						Derive(func(d *Argument) {
							d.FixAs[Real]()
							pos := d.Assume()
							η := d.TermAs[Real]("ε / &2 / (b - a)")
							ηPos := d.Have(
								"ε/2 spread over the length b − a is again positive",
								"&0 < ε / &2 / (b - a)",
								ByArith(pos, above, below))
							halfPos := d.Have(
								"and so is ε/2",
								"&0 < ε / &2",
								ByArith(pos))
							// The first section at η: past some N₁ the increments of two members
							// differ by at most η·|q − p|.
							_, varies := d.UnpackAs[Nat](
								GroupPremises(derivatives, derivativesConverge, ηPos, At(increments, f, fPrime, h, a, b, η)),
								"N₁")
							valuesCauchy := d.Unfolded(
								GroupPremises(atC, real_sequences.ConvergentImpCauchy.At(valuesAtC, l)),
								real_sequences.RealCauchyDef)
							_, settled := d.ObtainAs[Nat](
								"the values at c converge, so past some N₂ any two of them are within ε/2 of each other",
								"∃N₂:num. ∀m n:num. N₂ ≤ m ∧ N₂ ≤ n ⇒ |f(m)(c) - f(n)(c)| < ε / &2",
								By(valuesCauchy.At(d.TermAs[Real]("ε / &2")), halfPos))
							d.Take(d.TermAs[Nat]("N₁ + N₂"))
							m := d.FixAs[Nat]()
							n := d.FixAs[Nat]()
							x := d.FixAs[Real]()
							guards := d.Conjuncts(
								d.Assume(),
								"m is past N₁ + N₂",
								"n is past N₁ + N₂",
								"x is a point of ⟬a, b⟭")
							inside := d.Conjuncts(
								guards[2],
								"x lies above a",
								"and below b")
							d.Show(
								"|f(m)(x) − f(n)(x)| ≤ η·|x − c| + |f(m)(c) − f(n)(c)| < η·(b − a) + ε/2 = ε",
								ByArith(
									varies.At(m, n, c, x),
									settled.At(m, n),
									guards[0],
									guards[1],
									above,
									inside[0],
									below,
									inside[1],
									ηPos,
									real_order_ring.LessEqMulLeft.At(η, d.TermAs[Real]("|x - c|"), d.TermAs[Real]("b - a"))))
						}))

					g, uniform := arg.ObtainAs[Fun[Real, Real]](
						"so, by the Cauchy criterion, they converge uniformly on ⟬a, b⟭ to some g",
						"∃g:(real → real). real_converges_uniformly_on(«interval», f, g)",
						By(cauchy, UniformCauchy))
					arg.Take(g)
					value := arg.Have(
						"the values at c converge both to g(c) and to l, so g(c) = l",
						"g(c) = l",
						By(
							uniform,
							above,
							below,
							atC,
							UniformImpPointwise.At(f, g, interval, c),
							real_sequences.LimitUnique.At(valuesAtC, arg.TermAs[Real]("g(c)"), l)))

					nearG := arg.Unfolded(uniform, RealConvergesUniformlyOnDef)
					nearH := arg.Unfolded(derivativesConverge, RealConvergesUniformlyOnDef)
					derivative := arg.Have(
						"at every x of ⟬a, b⟭, g has derivative h(x)",
						"∀x:real. a < x ∧ x < b ⇒ real_derivative_at(g, x, h(x))",
						Derive(func(d *Argument) {
							x := d.FixAs[Real]()
							inside := d.Conjuncts(
								d.Assume(),
								"x lies above a",
								"and below b")
							increment := d.Have(
								"for every ε > 0, near x the increment of g lies within ε·|y − x| of h(x)·(y − x)",
								Statement{
									Binders: "∀ε:real.",
									Hypotheses: []string{
										"&0 < ε",
									},
									Conclusion: "∃δ:real. " +
										"    &0 < δ ∧ (∀y:real. &0 < |y - x| ∧ |y - x| < δ ⇒ |g(y) - g(x) - h(x) * (y - x)| < ε * |y - x|)",
								},
								Derive(func(e *Argument) {
									e.FixAs[Real]()
									pos := e.Assume()
									η := e.TermAs[Real]("ε / &5")
									ηPos := e.Have(
										"a fifth of ε is again a positive distance",
										"&0 < ε / &5",
										ByArith(pos))
									// The first section at η = ε/5: past some N₁ the increments of two
									// members differ by at most ε/5 times the distance.
									_, varies := e.UnpackAs[Nat](
										GroupPremises(derivatives, derivativesConverge, ηPos, At(increments, f, fPrime, h, a, b, η)),
										"N₁")
									_, nearDerivative := e.ObtainAs[Nat](
										"past some N₂ every derivative is within ε/5 of h on ⟬a, b⟭",
										"∃N₂:num. ∀n:num. ∀t:real. N₂ ≤ n ∧ t ∈ «interval» ⇒ |f'(n)(t) - h(t)| < ε / &5",
										By(nearH.At(η), ηPos))
									n, nDef := e.LetAs[Nat]("n", "N₁ + N₂")
									δ1, ball := e.ObtainAs[Real](
										"f(n) has derivative f'(n)(x): near x its increment is within ε/5·|y − x| of f'(n)(x)·(y − x)",
										"∃δ₁:real. "+
											"    &0 < δ₁ ∧ "+
											"    ∀y:real. "+
											"        &0 < |y - x| ∧ |y - x| < δ₁ ⇒ |f(n)(y) - f(n)(x) - f'(n)(x) * (y - x)| < ε / &5 * |y - x|",
										By(
											derivatives.At(n, x),
											inside[0],
											inside[1],
											ηPos,
											real_derivative.DerivativeIncrement.At(
												e.TermAs[Fun[Real, Real]]("f(n)"), x, e.TermAs[Real]("f'(n)(x)"))))
									radius := e.Conjuncts(
										ball,
										"δ₁ is positive",
										"and inside it the increment of f(n) is that close to f'(n)(x)·(y − x)")
									room := e.TermAs[Real]("min(x - a, b - x)")
									toA, toB := e.TermAs[Real]("x - a"), e.TermAs[Real]("b - x")
									e.Take(e.TermAs[Real]("min(δ₁, min(x - a, b - x))"))
									e.Do(SplitConj(
										Case(
											"the radius is positive: δ₁ is, and x lies strictly inside ⟬a, b⟭",
											ByArith(
												radius[0],
												inside[0],
												inside[1],
												real_sup_inf.LessThanMin.At(δ1, room, e.TermAs[Real]("&0")),
												real_sup_inf.LessThanMin.At(toA, toB, e.TermAs[Real]("&0")))),
										Case(
											"inside it g's increment is within ε·|y − x| of h(x)·(y − x)",
											Derive(func(k *Argument) {
												y := k.FixAs[Real]()
												near := k.Conjuncts(
													k.Assume(),
													"y is not x",
													"and lies within the radius of x")
												distance := k.TermAs[Real]("|y - x|")
												within := k.Conjuncts(
													k.Have(
														"so y is within δ₁ of x and lies in ⟬a, b⟭",
														"|y - x| < δ₁ ∧ a < y ∧ y < b",
														ByArith(
															near[1],
															real_sup_inf.LessThanMin.At(δ1, room, distance),
															real_sup_inf.LessThanMin.At(toA, toB, distance))),
													"y is within δ₁ of x",
													"y lies above a",
													"and below b")
												θ := k.TermAs[Real]("ε / &5 * |y - x|")
												θPos := k.Have(
													"ε/5·|y − x| is positive, y not being x",
													"&0 < ε / &5 * |y - x|",
													ByArith(ηPos, near[0]))
												_, approx := k.ObtainAs[Nat](
													"past some N₃ every member is within ε/5·|y − x| of g on ⟬a, b⟭",
													"∃N₃:num. ∀m:num. ∀t:real. N₃ ≤ m ∧ t ∈ «interval» ⇒ |f(m)(t) - g(t)| < ε / &5 * |y - x|",
													By(nearG.At(θ), θPos))
												m, mDef := k.LetAs[Nat]("m", "n + N₃")
												order := k.Conjuncts(
													k.Have(
														"m and n are past N₁, n past N₂ and m past N₃",
														"N₁ ≤ m ∧ N₁ ≤ n ∧ N₂ ≤ n ∧ N₃ ≤ m",
														ByArith(mDef, nDef)),
													"m is past N₁",
													"n is past N₁",
													"n is past N₂",
													"m is past N₃")
												limitStep := k.Have(
													"through f(m), within ε/5·|y − x| of g at y and at "+
														"x, g's increment is within 3ε/5·|y − x| of f(n)'s",
													"|g(y) - g(x) - (f(n)(y) - f(n)(x))| < &3 * (ε / &5 * |y - x|)",
													ByArith(
														varies.At(m, n, x, y),
														approx.At(m, y),
														approx.At(m, x),
														order[0],
														order[1],
														order[3],
														inside[0],
														within[1],
														inside[1],
														within[2]))
												gap := k.TermAs[Real]("y - x")
												derivativeStep := k.Have(
													"f'(n)(x) is within ε/5 of h(x), so their difference times y − x is within ε/5·|y − x|",
													"|(f'(n)(x) - h(x)) * (y - x)| ≤ ε / &5 * |y - x|",
													ByArith(
														nearDerivative.At(n, x),
														order[2],
														inside[0],
														inside[1],
														real_sgn_abs.AbsMul.At(k.TermAs[Real]("f'(n)(x) - h(x)"), gap),
														real_order_ring.LessEqMulRight.At(k.TermAs[Real]("|f'(n)(x) - h(x)|"), η, distance),
														real_sgn_abs.AbsNonneg.At(gap)))
												k.Show(
													"3ε/5 + ε/5 + ε/5 of |y − x|: the step to f(n), f(n)'s own increment, and f'(n)(x) against h(x)",
													ByArith(
														radius[1].At(y),
														near[0],
														within[0],
														limitStep,
														derivativeStep,
														real_sgn_abs.AbsBounds.At(k.TermAs[Real]("(f'(n)(x) - h(x)) * (y - x)"), θ)))
											})),
									))
								}))
							d.Show(
								"which is the derivative, read as a bound on the increment",
								By(increment, real_derivative.DerivativeIncrement))
						}))
					arg.Show(
						"g is the uniform limit, takes the value l at c, and has derivative h on ⟬a, b⟭",
						By(uniform, value, derivative))
				})
		}),
})}
